-- Prove2me | solution 1 for syracuse_descends_range_2237435_2239435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:18:55.375454+00:00
-- url     : https://prove2.me/submissions/063e122c-a756-42a0-a514-7aa9b0fc32eb

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

theorem B3185725 : Blo 2237435 3185725 := bbase (se 3 (by rfl) ⟨597323, by rfl⟩ : syracuseStep 3185725 = 1194647) (by norm_num)
theorem B4247633 : Blo 2237435 4247633 := bstep (se 2 (by rfl) ⟨1592862, by rfl⟩ : syracuseStep 4247633 = 3185725) B3185725
theorem B2831755 : Blo 2237435 2831755 := bstep (se 1 (by rfl) ⟨2123816, by rfl⟩ : syracuseStep 2831755 = 4247633) B4247633
theorem B3775673 : Blo 2237435 3775673 := bstep (se 2 (by rfl) ⟨1415877, by rfl⟩ : syracuseStep 3775673 = 2831755) B2831755
theorem B2517115 : Blo 2237435 2517115 := bstep (se 1 (by rfl) ⟨1887836, by rfl⟩ : syracuseStep 2517115 = 3775673) B3775673
theorem B3356153 : Blo 2237435 3356153 := bstep (se 2 (by rfl) ⟨1258557, by rfl⟩ : syracuseStep 3356153 = 2517115) B2517115
theorem B2237435 : Blo 2237435 2237435 := bstep (se 1 (by rfl) ⟨1678076, by rfl⟩ : syracuseStep 2237435 = 3356153) B3356153
theorem B13607797 : Blo 2237435 13607797 := bbase (se 5 (by rfl) ⟨637865, by rfl⟩ : syracuseStep 13607797 = 1275731) (by norm_num)
theorem B18143729 : Blo 2237435 18143729 := bstep (se 2 (by rfl) ⟨6803898, by rfl⟩ : syracuseStep 18143729 = 13607797) B13607797
theorem B12095819 : Blo 2237435 12095819 := bstep (se 1 (by rfl) ⟨9071864, by rfl⟩ : syracuseStep 12095819 = 18143729) B18143729
theorem B8063879 : Blo 2237435 8063879 := bstep (se 1 (by rfl) ⟨6047909, by rfl⟩ : syracuseStep 8063879 = 12095819) B12095819
theorem B86014709 : Blo 2237435 86014709 := bstep (se 5 (by rfl) ⟨4031939, by rfl⟩ : syracuseStep 86014709 = 8063879) B8063879
theorem B57343139 : Blo 2237435 57343139 := bstep (se 1 (by rfl) ⟨43007354, by rfl⟩ : syracuseStep 57343139 = 86014709) B86014709
theorem B38228759 : Blo 2237435 38228759 := bstep (se 1 (by rfl) ⟨28671569, by rfl⟩ : syracuseStep 38228759 = 57343139) B57343139
theorem B25485839 : Blo 2237435 25485839 := bstep (se 1 (by rfl) ⟨19114379, by rfl⟩ : syracuseStep 25485839 = 38228759) B38228759
theorem B16990559 : Blo 2237435 16990559 := bstep (se 1 (by rfl) ⟨12742919, by rfl⟩ : syracuseStep 16990559 = 25485839) B25485839
theorem B11327039 : Blo 2237435 11327039 := bstep (se 1 (by rfl) ⟨8495279, by rfl⟩ : syracuseStep 11327039 = 16990559) B16990559
theorem B7551359 : Blo 2237435 7551359 := bstep (se 1 (by rfl) ⟨5663519, by rfl⟩ : syracuseStep 7551359 = 11327039) B11327039
theorem B5034239 : Blo 2237435 5034239 := bstep (se 1 (by rfl) ⟨3775679, by rfl⟩ : syracuseStep 5034239 = 7551359) B7551359
theorem B3356159 : Blo 2237435 3356159 := bstep (se 1 (by rfl) ⟨2517119, by rfl⟩ : syracuseStep 3356159 = 5034239) B5034239
theorem B2237439 : Blo 2237435 2237439 := bstep (se 1 (by rfl) ⟨1678079, by rfl⟩ : syracuseStep 2237439 = 3356159) B3356159
theorem B3356165 : Blo 2237435 3356165 := bbase (se 4 (by rfl) ⟨314640, by rfl⟩ : syracuseStep 3356165 = 629281) (by norm_num)
theorem B2237443 : Blo 2237435 2237443 := bstep (se 1 (by rfl) ⟨1678082, by rfl⟩ : syracuseStep 2237443 = 3356165) B3356165
theorem B3775693 : Blo 2237435 3775693 := bbase (se 3 (by rfl) ⟨707942, by rfl⟩ : syracuseStep 3775693 = 1415885) (by norm_num)
theorem B5034257 : Blo 2237435 5034257 := bstep (se 2 (by rfl) ⟨1887846, by rfl⟩ : syracuseStep 5034257 = 3775693) B3775693
theorem B3356171 : Blo 2237435 3356171 := bstep (se 1 (by rfl) ⟨2517128, by rfl⟩ : syracuseStep 3356171 = 5034257) B5034257
theorem B2237447 : Blo 2237435 2237447 := bstep (se 1 (by rfl) ⟨1678085, by rfl⟩ : syracuseStep 2237447 = 3356171) B3356171
theorem B2517133 : Blo 2237435 2517133 := bbase (se 3 (by rfl) ⟨471962, by rfl⟩ : syracuseStep 2517133 = 943925) (by norm_num)
theorem B3356177 : Blo 2237435 3356177 := bstep (se 2 (by rfl) ⟨1258566, by rfl⟩ : syracuseStep 3356177 = 2517133) B2517133
theorem B2237451 : Blo 2237435 2237451 := bstep (se 1 (by rfl) ⟨1678088, by rfl⟩ : syracuseStep 2237451 = 3356177) B3356177
theorem B7551413 : Blo 2237435 7551413 := bbase (se 5 (by rfl) ⟨353972, by rfl⟩ : syracuseStep 7551413 = 707945) (by norm_num)
theorem B5034275 : Blo 2237435 5034275 := bstep (se 1 (by rfl) ⟨3775706, by rfl⟩ : syracuseStep 5034275 = 7551413) B7551413
theorem B3356183 : Blo 2237435 3356183 := bstep (se 1 (by rfl) ⟨2517137, by rfl⟩ : syracuseStep 3356183 = 5034275) B5034275
theorem B2237455 : Blo 2237435 2237455 := bstep (se 1 (by rfl) ⟨1678091, by rfl⟩ : syracuseStep 2237455 = 3356183) B3356183
theorem B3356189 : Blo 2237435 3356189 := bbase (se 3 (by rfl) ⟨629285, by rfl⟩ : syracuseStep 3356189 = 1258571) (by norm_num)
theorem B2237459 : Blo 2237435 2237459 := bstep (se 1 (by rfl) ⟨1678094, by rfl⟩ : syracuseStep 2237459 = 3356189) B3356189
theorem B5034293 : Blo 2237435 5034293 := bbase (se 5 (by rfl) ⟨235982, by rfl⟩ : syracuseStep 5034293 = 471965) (by norm_num)
theorem B3356195 : Blo 2237435 3356195 := bstep (se 1 (by rfl) ⟨2517146, by rfl⟩ : syracuseStep 3356195 = 5034293) B5034293
theorem B2237463 : Blo 2237435 2237463 := bstep (se 1 (by rfl) ⟨1678097, by rfl⟩ : syracuseStep 2237463 = 3356195) B3356195
theorem B8747029 : Blo 2237435 8747029 := bbase (se 6 (by rfl) ⟨205008, by rfl⟩ : syracuseStep 8747029 = 410017) (by norm_num)
theorem B46650821 : Blo 2237435 46650821 := bstep (se 4 (by rfl) ⟨4373514, by rfl⟩ : syracuseStep 46650821 = 8747029) B8747029
theorem B124402189 : Blo 2237435 124402189 := bstep (se 3 (by rfl) ⟨23325410, by rfl⟩ : syracuseStep 124402189 = 46650821) B46650821
theorem B165869585 : Blo 2237435 165869585 := bstep (se 2 (by rfl) ⟨62201094, by rfl⟩ : syracuseStep 165869585 = 124402189) B124402189
theorem B110579723 : Blo 2237435 110579723 := bstep (se 1 (by rfl) ⟨82934792, by rfl⟩ : syracuseStep 110579723 = 165869585) B165869585
theorem B73719815 : Blo 2237435 73719815 := bstep (se 1 (by rfl) ⟨55289861, by rfl⟩ : syracuseStep 73719815 = 110579723) B110579723
theorem B196586173 : Blo 2237435 196586173 := bstep (se 3 (by rfl) ⟨36859907, by rfl⟩ : syracuseStep 196586173 = 73719815) B73719815
theorem B1048459589 : Blo 2237435 1048459589 := bstep (se 4 (by rfl) ⟨98293086, by rfl⟩ : syracuseStep 1048459589 = 196586173) B196586173
theorem B698973059 : Blo 2237435 698973059 := bstep (se 1 (by rfl) ⟨524229794, by rfl⟩ : syracuseStep 698973059 = 1048459589) B1048459589
theorem B1863928157 : Blo 2237435 1863928157 := bstep (se 3 (by rfl) ⟨349486529, by rfl⟩ : syracuseStep 1863928157 = 698973059) B698973059
theorem B4970475085 : Blo 2237435 4970475085 := bstep (se 3 (by rfl) ⟨931964078, by rfl⟩ : syracuseStep 4970475085 = 1863928157) B1863928157
theorem B6627300113 : Blo 2237435 6627300113 := bstep (se 2 (by rfl) ⟨2485237542, by rfl⟩ : syracuseStep 6627300113 = 4970475085) B4970475085
theorem B4418200075 : Blo 2237435 4418200075 := bstep (se 1 (by rfl) ⟨3313650056, by rfl⟩ : syracuseStep 4418200075 = 6627300113) B6627300113
theorem B5890933433 : Blo 2237435 5890933433 := bstep (se 2 (by rfl) ⟨2209100037, by rfl⟩ : syracuseStep 5890933433 = 4418200075) B4418200075
theorem B3927288955 : Blo 2237435 3927288955 := bstep (se 1 (by rfl) ⟨2945466716, by rfl⟩ : syracuseStep 3927288955 = 5890933433) B5890933433
theorem B5236385273 : Blo 2237435 5236385273 := bstep (se 2 (by rfl) ⟨1963644477, by rfl⟩ : syracuseStep 5236385273 = 3927288955) B3927288955
theorem B3490923515 : Blo 2237435 3490923515 := bstep (se 1 (by rfl) ⟨2618192636, by rfl⟩ : syracuseStep 3490923515 = 5236385273) B5236385273
theorem B9309129373 : Blo 2237435 9309129373 := bstep (se 3 (by rfl) ⟨1745461757, by rfl⟩ : syracuseStep 9309129373 = 3490923515) B3490923515
theorem B49648689989 : Blo 2237435 49648689989 := bstep (se 4 (by rfl) ⟨4654564686, by rfl⟩ : syracuseStep 49648689989 = 9309129373) B9309129373
theorem B33099126659 : Blo 2237435 33099126659 := bstep (se 1 (by rfl) ⟨24824344994, by rfl⟩ : syracuseStep 33099126659 = 49648689989) B49648689989
theorem B22066084439 : Blo 2237435 22066084439 := bstep (se 1 (by rfl) ⟨16549563329, by rfl⟩ : syracuseStep 22066084439 = 33099126659) B33099126659
theorem B14710722959 : Blo 2237435 14710722959 := bstep (se 1 (by rfl) ⟨11033042219, by rfl⟩ : syracuseStep 14710722959 = 22066084439) B22066084439
theorem B9807148639 : Blo 2237435 9807148639 := bstep (se 1 (by rfl) ⟨7355361479, by rfl⟩ : syracuseStep 9807148639 = 14710722959) B14710722959
theorem B52304792741 : Blo 2237435 52304792741 := bstep (se 4 (by rfl) ⟨4903574319, by rfl⟩ : syracuseStep 52304792741 = 9807148639) B9807148639
theorem B34869861827 : Blo 2237435 34869861827 := bstep (se 1 (by rfl) ⟨26152396370, by rfl⟩ : syracuseStep 34869861827 = 52304792741) B52304792741
theorem B23246574551 : Blo 2237435 23246574551 := bstep (se 1 (by rfl) ⟨17434930913, by rfl⟩ : syracuseStep 23246574551 = 34869861827) B34869861827
theorem B15497716367 : Blo 2237435 15497716367 := bstep (se 1 (by rfl) ⟨11623287275, by rfl⟩ : syracuseStep 15497716367 = 23246574551) B23246574551
theorem B10331810911 : Blo 2237435 10331810911 := bstep (se 1 (by rfl) ⟨7748858183, by rfl⟩ : syracuseStep 10331810911 = 15497716367) B15497716367
theorem B13775747881 : Blo 2237435 13775747881 := bstep (se 2 (by rfl) ⟨5165905455, by rfl⟩ : syracuseStep 13775747881 = 10331810911) B10331810911
theorem B18367663841 : Blo 2237435 18367663841 := bstep (se 2 (by rfl) ⟨6887873940, by rfl⟩ : syracuseStep 18367663841 = 13775747881) B13775747881
theorem B12245109227 : Blo 2237435 12245109227 := bstep (se 1 (by rfl) ⟨9183831920, by rfl⟩ : syracuseStep 12245109227 = 18367663841) B18367663841
theorem B8163406151 : Blo 2237435 8163406151 := bstep (se 1 (by rfl) ⟨6122554613, by rfl⟩ : syracuseStep 8163406151 = 12245109227) B12245109227
theorem B5442270767 : Blo 2237435 5442270767 := bstep (se 1 (by rfl) ⟨4081703075, by rfl⟩ : syracuseStep 5442270767 = 8163406151) B8163406151
theorem B3628180511 : Blo 2237435 3628180511 := bstep (se 1 (by rfl) ⟨2721135383, by rfl⟩ : syracuseStep 3628180511 = 5442270767) B5442270767
theorem B2418787007 : Blo 2237435 2418787007 := bstep (se 1 (by rfl) ⟨1814090255, by rfl⟩ : syracuseStep 2418787007 = 3628180511) B3628180511
theorem B1612524671 : Blo 2237435 1612524671 := bstep (se 1 (by rfl) ⟨1209393503, by rfl⟩ : syracuseStep 1612524671 = 2418787007) B2418787007
theorem B1075016447 : Blo 2237435 1075016447 := bstep (se 1 (by rfl) ⟨806262335, by rfl⟩ : syracuseStep 1075016447 = 1612524671) B1612524671
theorem B716677631 : Blo 2237435 716677631 := bstep (se 1 (by rfl) ⟨537508223, by rfl⟩ : syracuseStep 716677631 = 1075016447) B1075016447
theorem B477785087 : Blo 2237435 477785087 := bstep (se 1 (by rfl) ⟨358338815, by rfl⟩ : syracuseStep 477785087 = 716677631) B716677631
theorem B318523391 : Blo 2237435 318523391 := bstep (se 1 (by rfl) ⟨238892543, by rfl⟩ : syracuseStep 318523391 = 477785087) B477785087
theorem B212348927 : Blo 2237435 212348927 := bstep (se 1 (by rfl) ⟨159261695, by rfl⟩ : syracuseStep 212348927 = 318523391) B318523391
theorem B141565951 : Blo 2237435 141565951 := bstep (se 1 (by rfl) ⟨106174463, by rfl⟩ : syracuseStep 141565951 = 212348927) B212348927
theorem B755018405 : Blo 2237435 755018405 := bstep (se 4 (by rfl) ⟨70782975, by rfl⟩ : syracuseStep 755018405 = 141565951) B141565951
theorem B503345603 : Blo 2237435 503345603 := bstep (se 1 (by rfl) ⟨377509202, by rfl⟩ : syracuseStep 503345603 = 755018405) B755018405
theorem B335563735 : Blo 2237435 335563735 := bstep (se 1 (by rfl) ⟨251672801, by rfl⟩ : syracuseStep 335563735 = 503345603) B503345603
theorem B447418313 : Blo 2237435 447418313 := bstep (se 2 (by rfl) ⟨167781867, by rfl⟩ : syracuseStep 447418313 = 335563735) B335563735
theorem B298278875 : Blo 2237435 298278875 := bstep (se 1 (by rfl) ⟨223709156, by rfl⟩ : syracuseStep 298278875 = 447418313) B447418313
theorem B198852583 : Blo 2237435 198852583 := bstep (se 1 (by rfl) ⟨149139437, by rfl⟩ : syracuseStep 198852583 = 298278875) B298278875
theorem B265136777 : Blo 2237435 265136777 := bstep (se 2 (by rfl) ⟨99426291, by rfl⟩ : syracuseStep 265136777 = 198852583) B198852583
theorem B176757851 : Blo 2237435 176757851 := bstep (se 1 (by rfl) ⟨132568388, by rfl⟩ : syracuseStep 176757851 = 265136777) B265136777
theorem B117838567 : Blo 2237435 117838567 := bstep (se 1 (by rfl) ⟨88378925, by rfl⟩ : syracuseStep 117838567 = 176757851) B176757851
theorem B157118089 : Blo 2237435 157118089 := bstep (se 2 (by rfl) ⟨58919283, by rfl⟩ : syracuseStep 157118089 = 117838567) B117838567
theorem B209490785 : Blo 2237435 209490785 := bstep (se 2 (by rfl) ⟨78559044, by rfl⟩ : syracuseStep 209490785 = 157118089) B157118089
theorem B139660523 : Blo 2237435 139660523 := bstep (se 1 (by rfl) ⟨104745392, by rfl⟩ : syracuseStep 139660523 = 209490785) B209490785
theorem B93107015 : Blo 2237435 93107015 := bstep (se 1 (by rfl) ⟨69830261, by rfl⟩ : syracuseStep 93107015 = 139660523) B139660523
theorem B62071343 : Blo 2237435 62071343 := bstep (se 1 (by rfl) ⟨46553507, by rfl⟩ : syracuseStep 62071343 = 93107015) B93107015
theorem B41380895 : Blo 2237435 41380895 := bstep (se 1 (by rfl) ⟨31035671, by rfl⟩ : syracuseStep 41380895 = 62071343) B62071343
theorem B27587263 : Blo 2237435 27587263 := bstep (se 1 (by rfl) ⟨20690447, by rfl⟩ : syracuseStep 27587263 = 41380895) B41380895
theorem B36783017 : Blo 2237435 36783017 := bstep (se 2 (by rfl) ⟨13793631, by rfl⟩ : syracuseStep 36783017 = 27587263) B27587263
theorem B24522011 : Blo 2237435 24522011 := bstep (se 1 (by rfl) ⟨18391508, by rfl⟩ : syracuseStep 24522011 = 36783017) B36783017
theorem B16348007 : Blo 2237435 16348007 := bstep (se 1 (by rfl) ⟨12261005, by rfl⟩ : syracuseStep 16348007 = 24522011) B24522011
theorem B10898671 : Blo 2237435 10898671 := bstep (se 1 (by rfl) ⟨8174003, by rfl⟩ : syracuseStep 10898671 = 16348007) B16348007
theorem B14531561 : Blo 2237435 14531561 := bstep (se 2 (by rfl) ⟨5449335, by rfl⟩ : syracuseStep 14531561 = 10898671) B10898671
theorem B9687707 : Blo 2237435 9687707 := bstep (se 1 (by rfl) ⟨7265780, by rfl⟩ : syracuseStep 9687707 = 14531561) B14531561
theorem B6458471 : Blo 2237435 6458471 := bstep (se 1 (by rfl) ⟨4843853, by rfl⟩ : syracuseStep 6458471 = 9687707) B9687707
theorem B4305647 : Blo 2237435 4305647 := bstep (se 1 (by rfl) ⟨3229235, by rfl⟩ : syracuseStep 4305647 = 6458471) B6458471
theorem B11481725 : Blo 2237435 11481725 := bstep (se 3 (by rfl) ⟨2152823, by rfl⟩ : syracuseStep 11481725 = 4305647) B4305647
theorem B7654483 : Blo 2237435 7654483 := bstep (se 1 (by rfl) ⟨5740862, by rfl⟩ : syracuseStep 7654483 = 11481725) B11481725
theorem B40823909 : Blo 2237435 40823909 := bstep (se 4 (by rfl) ⟨3827241, by rfl⟩ : syracuseStep 40823909 = 7654483) B7654483
theorem B27215939 : Blo 2237435 27215939 := bstep (se 1 (by rfl) ⟨20411954, by rfl⟩ : syracuseStep 27215939 = 40823909) B40823909
theorem B72575837 : Blo 2237435 72575837 := bstep (se 3 (by rfl) ⟨13607969, by rfl⟩ : syracuseStep 72575837 = 27215939) B27215939
theorem B48383891 : Blo 2237435 48383891 := bstep (se 1 (by rfl) ⟨36287918, by rfl⟩ : syracuseStep 48383891 = 72575837) B72575837
theorem B32255927 : Blo 2237435 32255927 := bstep (se 1 (by rfl) ⟨24191945, by rfl⟩ : syracuseStep 32255927 = 48383891) B48383891
theorem B21503951 : Blo 2237435 21503951 := bstep (se 1 (by rfl) ⟨16127963, by rfl⟩ : syracuseStep 21503951 = 32255927) B32255927
theorem B14335967 : Blo 2237435 14335967 := bstep (se 1 (by rfl) ⟨10751975, by rfl⟩ : syracuseStep 14335967 = 21503951) B21503951
theorem B9557311 : Blo 2237435 9557311 := bstep (se 1 (by rfl) ⟨7167983, by rfl⟩ : syracuseStep 9557311 = 14335967) B14335967
theorem B12743081 : Blo 2237435 12743081 := bstep (se 2 (by rfl) ⟨4778655, by rfl⟩ : syracuseStep 12743081 = 9557311) B9557311
theorem B8495387 : Blo 2237435 8495387 := bstep (se 1 (by rfl) ⟨6371540, by rfl⟩ : syracuseStep 8495387 = 12743081) B12743081
theorem B5663591 : Blo 2237435 5663591 := bstep (se 1 (by rfl) ⟨4247693, by rfl⟩ : syracuseStep 5663591 = 8495387) B8495387
theorem B3775727 : Blo 2237435 3775727 := bstep (se 1 (by rfl) ⟨2831795, by rfl⟩ : syracuseStep 3775727 = 5663591) B5663591
theorem B2517151 : Blo 2237435 2517151 := bstep (se 1 (by rfl) ⟨1887863, by rfl⟩ : syracuseStep 2517151 = 3775727) B3775727
theorem B3356201 : Blo 2237435 3356201 := bstep (se 2 (by rfl) ⟨1258575, by rfl⟩ : syracuseStep 3356201 = 2517151) B2517151
theorem B2237467 : Blo 2237435 2237467 := bstep (se 1 (by rfl) ⟨1678100, by rfl⟩ : syracuseStep 2237467 = 3356201) B3356201
theorem B2724673 : Blo 2237435 2724673 := bbase (se 2 (by rfl) ⟨1021752, by rfl⟩ : syracuseStep 2724673 = 2043505) (by norm_num)
theorem B3632897 : Blo 2237435 3632897 := bstep (se 2 (by rfl) ⟨1362336, by rfl⟩ : syracuseStep 3632897 = 2724673) B2724673
theorem B2421931 : Blo 2237435 2421931 := bstep (se 1 (by rfl) ⟨1816448, by rfl⟩ : syracuseStep 2421931 = 3632897) B3632897
theorem B3229241 : Blo 2237435 3229241 := bstep (se 2 (by rfl) ⟨1210965, by rfl⟩ : syracuseStep 3229241 = 2421931) B2421931
theorem B8611309 : Blo 2237435 8611309 := bstep (se 3 (by rfl) ⟨1614620, by rfl⟩ : syracuseStep 8611309 = 3229241) B3229241
theorem B11481745 : Blo 2237435 11481745 := bstep (se 2 (by rfl) ⟨4305654, by rfl⟩ : syracuseStep 11481745 = 8611309) B8611309
theorem B15308993 : Blo 2237435 15308993 := bstep (se 2 (by rfl) ⟨5740872, by rfl⟩ : syracuseStep 15308993 = 11481745) B11481745
theorem B10205995 : Blo 2237435 10205995 := bstep (se 1 (by rfl) ⟨7654496, by rfl⟩ : syracuseStep 10205995 = 15308993) B15308993
theorem B13607993 : Blo 2237435 13607993 := bstep (se 2 (by rfl) ⟨5102997, by rfl⟩ : syracuseStep 13607993 = 10205995) B10205995
theorem B9071995 : Blo 2237435 9071995 := bstep (se 1 (by rfl) ⟨6803996, by rfl⟩ : syracuseStep 9071995 = 13607993) B13607993
theorem B12095993 : Blo 2237435 12095993 := bstep (se 2 (by rfl) ⟨4535997, by rfl⟩ : syracuseStep 12095993 = 9071995) B9071995
theorem B32255981 : Blo 2237435 32255981 := bstep (se 3 (by rfl) ⟨6047996, by rfl⟩ : syracuseStep 32255981 = 12095993) B12095993
theorem B21503987 : Blo 2237435 21503987 := bstep (se 1 (by rfl) ⟨16127990, by rfl⟩ : syracuseStep 21503987 = 32255981) B32255981
theorem B14335991 : Blo 2237435 14335991 := bstep (se 1 (by rfl) ⟨10751993, by rfl⟩ : syracuseStep 14335991 = 21503987) B21503987
theorem B9557327 : Blo 2237435 9557327 := bstep (se 1 (by rfl) ⟨7167995, by rfl⟩ : syracuseStep 9557327 = 14335991) B14335991
theorem B6371551 : Blo 2237435 6371551 := bstep (se 1 (by rfl) ⟨4778663, by rfl⟩ : syracuseStep 6371551 = 9557327) B9557327
theorem B8495401 : Blo 2237435 8495401 := bstep (se 2 (by rfl) ⟨3185775, by rfl⟩ : syracuseStep 8495401 = 6371551) B6371551
theorem B11327201 : Blo 2237435 11327201 := bstep (se 2 (by rfl) ⟨4247700, by rfl⟩ : syracuseStep 11327201 = 8495401) B8495401
theorem B7551467 : Blo 2237435 7551467 := bstep (se 1 (by rfl) ⟨5663600, by rfl⟩ : syracuseStep 7551467 = 11327201) B11327201
theorem B5034311 : Blo 2237435 5034311 := bstep (se 1 (by rfl) ⟨3775733, by rfl⟩ : syracuseStep 5034311 = 7551467) B7551467
theorem B3356207 : Blo 2237435 3356207 := bstep (se 1 (by rfl) ⟨2517155, by rfl⟩ : syracuseStep 3356207 = 5034311) B5034311
theorem B2237471 : Blo 2237435 2237471 := bstep (se 1 (by rfl) ⟨1678103, by rfl⟩ : syracuseStep 2237471 = 3356207) B3356207
theorem B3356213 : Blo 2237435 3356213 := bbase (se 5 (by rfl) ⟨157322, by rfl⟩ : syracuseStep 3356213 = 314645) (by norm_num)
theorem B2237475 : Blo 2237435 2237475 := bstep (se 1 (by rfl) ⟨1678106, by rfl⟩ : syracuseStep 2237475 = 3356213) B3356213
theorem B5663621 : Blo 2237435 5663621 := bbase (se 4 (by rfl) ⟨530964, by rfl⟩ : syracuseStep 5663621 = 1061929) (by norm_num)
theorem B3775747 : Blo 2237435 3775747 := bstep (se 1 (by rfl) ⟨2831810, by rfl⟩ : syracuseStep 3775747 = 5663621) B5663621
theorem B5034329 : Blo 2237435 5034329 := bstep (se 2 (by rfl) ⟨1887873, by rfl⟩ : syracuseStep 5034329 = 3775747) B3775747
theorem B3356219 : Blo 2237435 3356219 := bstep (se 1 (by rfl) ⟨2517164, by rfl⟩ : syracuseStep 3356219 = 5034329) B5034329
theorem B2237479 : Blo 2237435 2237479 := bstep (se 1 (by rfl) ⟨1678109, by rfl⟩ : syracuseStep 2237479 = 3356219) B3356219
theorem B2517169 : Blo 2237435 2517169 := bbase (se 2 (by rfl) ⟨943938, by rfl⟩ : syracuseStep 2517169 = 1887877) (by norm_num)
theorem B3356225 : Blo 2237435 3356225 := bstep (se 2 (by rfl) ⟨1258584, by rfl⟩ : syracuseStep 3356225 = 2517169) B2517169
theorem B2237483 : Blo 2237435 2237483 := bstep (se 1 (by rfl) ⟨1678112, by rfl⟩ : syracuseStep 2237483 = 3356225) B3356225
theorem B2389349 : Blo 2237435 2389349 := bbase (se 4 (by rfl) ⟨224001, by rfl⟩ : syracuseStep 2389349 = 448003) (by norm_num)
theorem B6371597 : Blo 2237435 6371597 := bstep (se 3 (by rfl) ⟨1194674, by rfl⟩ : syracuseStep 6371597 = 2389349) B2389349
theorem B4247731 : Blo 2237435 4247731 := bstep (se 1 (by rfl) ⟨3185798, by rfl⟩ : syracuseStep 4247731 = 6371597) B6371597
theorem B5663641 : Blo 2237435 5663641 := bstep (se 2 (by rfl) ⟨2123865, by rfl⟩ : syracuseStep 5663641 = 4247731) B4247731
theorem B7551521 : Blo 2237435 7551521 := bstep (se 2 (by rfl) ⟨2831820, by rfl⟩ : syracuseStep 7551521 = 5663641) B5663641
theorem B5034347 : Blo 2237435 5034347 := bstep (se 1 (by rfl) ⟨3775760, by rfl⟩ : syracuseStep 5034347 = 7551521) B7551521
theorem B3356231 : Blo 2237435 3356231 := bstep (se 1 (by rfl) ⟨2517173, by rfl⟩ : syracuseStep 3356231 = 5034347) B5034347
theorem B2237487 : Blo 2237435 2237487 := bstep (se 1 (by rfl) ⟨1678115, by rfl⟩ : syracuseStep 2237487 = 3356231) B3356231
theorem B3356237 : Blo 2237435 3356237 := bbase (se 3 (by rfl) ⟨629294, by rfl⟩ : syracuseStep 3356237 = 1258589) (by norm_num)
theorem B2237491 : Blo 2237435 2237491 := bstep (se 1 (by rfl) ⟨1678118, by rfl⟩ : syracuseStep 2237491 = 3356237) B3356237
theorem B5034365 : Blo 2237435 5034365 := bbase (se 3 (by rfl) ⟨943943, by rfl⟩ : syracuseStep 5034365 = 1887887) (by norm_num)
theorem B3356243 : Blo 2237435 3356243 := bstep (se 1 (by rfl) ⟨2517182, by rfl⟩ : syracuseStep 3356243 = 5034365) B5034365
theorem B2237495 : Blo 2237435 2237495 := bstep (se 1 (by rfl) ⟨1678121, by rfl⟩ : syracuseStep 2237495 = 3356243) B3356243
theorem B3775781 : Blo 2237435 3775781 := bbase (se 4 (by rfl) ⟨353979, by rfl⟩ : syracuseStep 3775781 = 707959) (by norm_num)
theorem B2517187 : Blo 2237435 2517187 := bstep (se 1 (by rfl) ⟨1887890, by rfl⟩ : syracuseStep 2517187 = 3775781) B3775781
theorem B3356249 : Blo 2237435 3356249 := bstep (se 2 (by rfl) ⟨1258593, by rfl⟩ : syracuseStep 3356249 = 2517187) B2517187
theorem B2237499 : Blo 2237435 2237499 := bstep (se 1 (by rfl) ⟨1678124, by rfl⟩ : syracuseStep 2237499 = 3356249) B3356249
theorem B3185821 : Blo 2237435 3185821 := bbase (se 3 (by rfl) ⟨597341, by rfl⟩ : syracuseStep 3185821 = 1194683) (by norm_num)
theorem B16991045 : Blo 2237435 16991045 := bstep (se 4 (by rfl) ⟨1592910, by rfl⟩ : syracuseStep 16991045 = 3185821) B3185821
theorem B11327363 : Blo 2237435 11327363 := bstep (se 1 (by rfl) ⟨8495522, by rfl⟩ : syracuseStep 11327363 = 16991045) B16991045
theorem B7551575 : Blo 2237435 7551575 := bstep (se 1 (by rfl) ⟨5663681, by rfl⟩ : syracuseStep 7551575 = 11327363) B11327363
theorem B5034383 : Blo 2237435 5034383 := bstep (se 1 (by rfl) ⟨3775787, by rfl⟩ : syracuseStep 5034383 = 7551575) B7551575
theorem B3356255 : Blo 2237435 3356255 := bstep (se 1 (by rfl) ⟨2517191, by rfl⟩ : syracuseStep 3356255 = 5034383) B5034383
theorem B2237503 : Blo 2237435 2237503 := bstep (se 1 (by rfl) ⟨1678127, by rfl⟩ : syracuseStep 2237503 = 3356255) B3356255
theorem B3356261 : Blo 2237435 3356261 := bbase (se 4 (by rfl) ⟨314649, by rfl⟩ : syracuseStep 3356261 = 629299) (by norm_num)
theorem B2237507 : Blo 2237435 2237507 := bstep (se 1 (by rfl) ⟨1678130, by rfl⟩ : syracuseStep 2237507 = 3356261) B3356261
theorem B2870489 : Blo 2237435 2870489 := bbase (se 2 (by rfl) ⟨1076433, by rfl⟩ : syracuseStep 2870489 = 2152867) (by norm_num)
theorem B7654637 : Blo 2237435 7654637 := bstep (se 3 (by rfl) ⟨1435244, by rfl⟩ : syracuseStep 7654637 = 2870489) B2870489
theorem B5103091 : Blo 2237435 5103091 := bstep (se 1 (by rfl) ⟨3827318, by rfl⟩ : syracuseStep 5103091 = 7654637) B7654637
theorem B27216485 : Blo 2237435 27216485 := bstep (se 4 (by rfl) ⟨2551545, by rfl⟩ : syracuseStep 27216485 = 5103091) B5103091
theorem B18144323 : Blo 2237435 18144323 := bstep (se 1 (by rfl) ⟨13608242, by rfl⟩ : syracuseStep 18144323 = 27216485) B27216485
theorem B12096215 : Blo 2237435 12096215 := bstep (se 1 (by rfl) ⟨9072161, by rfl⟩ : syracuseStep 12096215 = 18144323) B18144323
theorem B8064143 : Blo 2237435 8064143 := bstep (se 1 (by rfl) ⟨6048107, by rfl⟩ : syracuseStep 8064143 = 12096215) B12096215
theorem B5376095 : Blo 2237435 5376095 := bstep (se 1 (by rfl) ⟨4032071, by rfl⟩ : syracuseStep 5376095 = 8064143) B8064143
theorem B3584063 : Blo 2237435 3584063 := bstep (se 1 (by rfl) ⟨2688047, by rfl⟩ : syracuseStep 3584063 = 5376095) B5376095
theorem B2389375 : Blo 2237435 2389375 := bstep (se 1 (by rfl) ⟨1792031, by rfl⟩ : syracuseStep 2389375 = 3584063) B3584063
theorem B3185833 : Blo 2237435 3185833 := bstep (se 2 (by rfl) ⟨1194687, by rfl⟩ : syracuseStep 3185833 = 2389375) B2389375
theorem B4247777 : Blo 2237435 4247777 := bstep (se 2 (by rfl) ⟨1592916, by rfl⟩ : syracuseStep 4247777 = 3185833) B3185833
theorem B2831851 : Blo 2237435 2831851 := bstep (se 1 (by rfl) ⟨2123888, by rfl⟩ : syracuseStep 2831851 = 4247777) B4247777
theorem B3775801 : Blo 2237435 3775801 := bstep (se 2 (by rfl) ⟨1415925, by rfl⟩ : syracuseStep 3775801 = 2831851) B2831851
theorem B5034401 : Blo 2237435 5034401 := bstep (se 2 (by rfl) ⟨1887900, by rfl⟩ : syracuseStep 5034401 = 3775801) B3775801
theorem B3356267 : Blo 2237435 3356267 := bstep (se 1 (by rfl) ⟨2517200, by rfl⟩ : syracuseStep 3356267 = 5034401) B5034401
theorem B2237511 : Blo 2237435 2237511 := bstep (se 1 (by rfl) ⟨1678133, by rfl⟩ : syracuseStep 2237511 = 3356267) B3356267
theorem B2517205 : Blo 2237435 2517205 := bbase (se 7 (by rfl) ⟨29498, by rfl⟩ : syracuseStep 2517205 = 58997) (by norm_num)
theorem B3356273 : Blo 2237435 3356273 := bstep (se 2 (by rfl) ⟨1258602, by rfl⟩ : syracuseStep 3356273 = 2517205) B2517205
theorem B2237515 : Blo 2237435 2237515 := bstep (se 1 (by rfl) ⟨1678136, by rfl⟩ : syracuseStep 2237515 = 3356273) B3356273
theorem B2831861 : Blo 2237435 2831861 := bbase (se 5 (by rfl) ⟨132743, by rfl⟩ : syracuseStep 2831861 = 265487) (by norm_num)
theorem B7551629 : Blo 2237435 7551629 := bstep (se 3 (by rfl) ⟨1415930, by rfl⟩ : syracuseStep 7551629 = 2831861) B2831861
theorem B5034419 : Blo 2237435 5034419 := bstep (se 1 (by rfl) ⟨3775814, by rfl⟩ : syracuseStep 5034419 = 7551629) B7551629
theorem B3356279 : Blo 2237435 3356279 := bstep (se 1 (by rfl) ⟨2517209, by rfl⟩ : syracuseStep 3356279 = 5034419) B5034419
theorem B2237519 : Blo 2237435 2237519 := bstep (se 1 (by rfl) ⟨1678139, by rfl⟩ : syracuseStep 2237519 = 3356279) B3356279
theorem B3356285 : Blo 2237435 3356285 := bbase (se 3 (by rfl) ⟨629303, by rfl⟩ : syracuseStep 3356285 = 1258607) (by norm_num)
theorem B2237523 : Blo 2237435 2237523 := bstep (se 1 (by rfl) ⟨1678142, by rfl⟩ : syracuseStep 2237523 = 3356285) B3356285
theorem B5034437 : Blo 2237435 5034437 := bbase (se 4 (by rfl) ⟨471978, by rfl⟩ : syracuseStep 5034437 = 943957) (by norm_num)
theorem B3356291 : Blo 2237435 3356291 := bstep (se 1 (by rfl) ⟨2517218, by rfl⟩ : syracuseStep 3356291 = 5034437) B5034437
theorem B2237527 : Blo 2237435 2237527 := bstep (se 1 (by rfl) ⟨1678145, by rfl⟩ : syracuseStep 2237527 = 3356291) B3356291
theorem B4305773 : Blo 2237435 4305773 := bbase (se 3 (by rfl) ⟨807332, by rfl⟩ : syracuseStep 4305773 = 1614665) (by norm_num)
theorem B2870515 : Blo 2237435 2870515 := bstep (se 1 (by rfl) ⟨2152886, by rfl⟩ : syracuseStep 2870515 = 4305773) B4305773
theorem B3827353 : Blo 2237435 3827353 := bstep (se 2 (by rfl) ⟨1435257, by rfl⟩ : syracuseStep 3827353 = 2870515) B2870515
theorem B5103137 : Blo 2237435 5103137 := bstep (se 2 (by rfl) ⟨1913676, by rfl⟩ : syracuseStep 5103137 = 3827353) B3827353
theorem B3402091 : Blo 2237435 3402091 := bstep (se 1 (by rfl) ⟨2551568, by rfl⟩ : syracuseStep 3402091 = 5103137) B5103137
theorem B4536121 : Blo 2237435 4536121 := bstep (se 2 (by rfl) ⟨1701045, by rfl⟩ : syracuseStep 4536121 = 3402091) B3402091
theorem B6048161 : Blo 2237435 6048161 := bstep (se 2 (by rfl) ⟨2268060, by rfl⟩ : syracuseStep 6048161 = 4536121) B4536121
theorem B4032107 : Blo 2237435 4032107 := bstep (se 1 (by rfl) ⟨3024080, by rfl⟩ : syracuseStep 4032107 = 6048161) B6048161
theorem B2688071 : Blo 2237435 2688071 := bstep (se 1 (by rfl) ⟨2016053, by rfl⟩ : syracuseStep 2688071 = 4032107) B4032107
theorem B7168189 : Blo 2237435 7168189 := bstep (se 3 (by rfl) ⟨1344035, by rfl⟩ : syracuseStep 7168189 = 2688071) B2688071
theorem B9557585 : Blo 2237435 9557585 := bstep (se 2 (by rfl) ⟨3584094, by rfl⟩ : syracuseStep 9557585 = 7168189) B7168189
theorem B6371723 : Blo 2237435 6371723 := bstep (se 1 (by rfl) ⟨4778792, by rfl⟩ : syracuseStep 6371723 = 9557585) B9557585
theorem B4247815 : Blo 2237435 4247815 := bstep (se 1 (by rfl) ⟨3185861, by rfl⟩ : syracuseStep 4247815 = 6371723) B6371723
theorem B5663753 : Blo 2237435 5663753 := bstep (se 2 (by rfl) ⟨2123907, by rfl⟩ : syracuseStep 5663753 = 4247815) B4247815
theorem B3775835 : Blo 2237435 3775835 := bstep (se 1 (by rfl) ⟨2831876, by rfl⟩ : syracuseStep 3775835 = 5663753) B5663753
theorem B2517223 : Blo 2237435 2517223 := bstep (se 1 (by rfl) ⟨1887917, by rfl⟩ : syracuseStep 2517223 = 3775835) B3775835
theorem B3356297 : Blo 2237435 3356297 := bstep (se 2 (by rfl) ⟨1258611, by rfl⟩ : syracuseStep 3356297 = 2517223) B2517223
theorem B2237531 : Blo 2237435 2237531 := bstep (se 1 (by rfl) ⟨1678148, by rfl⟩ : syracuseStep 2237531 = 3356297) B3356297
theorem B11327525 : Blo 2237435 11327525 := bbase (se 4 (by rfl) ⟨1061955, by rfl⟩ : syracuseStep 11327525 = 2123911) (by norm_num)
theorem B7551683 : Blo 2237435 7551683 := bstep (se 1 (by rfl) ⟨5663762, by rfl⟩ : syracuseStep 7551683 = 11327525) B11327525
theorem B5034455 : Blo 2237435 5034455 := bstep (se 1 (by rfl) ⟨3775841, by rfl⟩ : syracuseStep 5034455 = 7551683) B7551683
theorem B3356303 : Blo 2237435 3356303 := bstep (se 1 (by rfl) ⟨2517227, by rfl⟩ : syracuseStep 3356303 = 5034455) B5034455
theorem B2237535 : Blo 2237435 2237535 := bstep (se 1 (by rfl) ⟨1678151, by rfl⟩ : syracuseStep 2237535 = 3356303) B3356303
theorem B3356309 : Blo 2237435 3356309 := bbase (se 6 (by rfl) ⟨78663, by rfl⟩ : syracuseStep 3356309 = 157327) (by norm_num)
theorem B2237539 : Blo 2237435 2237539 := bstep (se 1 (by rfl) ⟨1678154, by rfl⟩ : syracuseStep 2237539 = 3356309) B3356309
theorem B2688085 : Blo 2237435 2688085 := bbase (se 8 (by rfl) ⟨15750, by rfl⟩ : syracuseStep 2688085 = 31501) (by norm_num)
theorem B14336453 : Blo 2237435 14336453 := bstep (se 4 (by rfl) ⟨1344042, by rfl⟩ : syracuseStep 14336453 = 2688085) B2688085
theorem B9557635 : Blo 2237435 9557635 := bstep (se 1 (by rfl) ⟨7168226, by rfl⟩ : syracuseStep 9557635 = 14336453) B14336453
theorem B12743513 : Blo 2237435 12743513 := bstep (se 2 (by rfl) ⟨4778817, by rfl⟩ : syracuseStep 12743513 = 9557635) B9557635
theorem B8495675 : Blo 2237435 8495675 := bstep (se 1 (by rfl) ⟨6371756, by rfl⟩ : syracuseStep 8495675 = 12743513) B12743513
theorem B5663783 : Blo 2237435 5663783 := bstep (se 1 (by rfl) ⟨4247837, by rfl⟩ : syracuseStep 5663783 = 8495675) B8495675
theorem B3775855 : Blo 2237435 3775855 := bstep (se 1 (by rfl) ⟨2831891, by rfl⟩ : syracuseStep 3775855 = 5663783) B5663783
theorem B5034473 : Blo 2237435 5034473 := bstep (se 2 (by rfl) ⟨1887927, by rfl⟩ : syracuseStep 5034473 = 3775855) B3775855
theorem B3356315 : Blo 2237435 3356315 := bstep (se 1 (by rfl) ⟨2517236, by rfl⟩ : syracuseStep 3356315 = 5034473) B5034473
theorem B2237543 : Blo 2237435 2237543 := bstep (se 1 (by rfl) ⟨1678157, by rfl⟩ : syracuseStep 2237543 = 3356315) B3356315
theorem B2517241 : Blo 2237435 2517241 := bbase (se 2 (by rfl) ⟨943965, by rfl⟩ : syracuseStep 2517241 = 1887931) (by norm_num)
theorem B3356321 : Blo 2237435 3356321 := bstep (se 2 (by rfl) ⟨1258620, by rfl⟩ : syracuseStep 3356321 = 2517241) B2517241
theorem B2237547 : Blo 2237435 2237547 := bstep (se 1 (by rfl) ⟨1678160, by rfl⟩ : syracuseStep 2237547 = 3356321) B3356321
theorem B9557669 : Blo 2237435 9557669 := bbase (se 4 (by rfl) ⟨896031, by rfl⟩ : syracuseStep 9557669 = 1792063) (by norm_num)
theorem B6371779 : Blo 2237435 6371779 := bstep (se 1 (by rfl) ⟨4778834, by rfl⟩ : syracuseStep 6371779 = 9557669) B9557669
theorem B8495705 : Blo 2237435 8495705 := bstep (se 2 (by rfl) ⟨3185889, by rfl⟩ : syracuseStep 8495705 = 6371779) B6371779
theorem B5663803 : Blo 2237435 5663803 := bstep (se 1 (by rfl) ⟨4247852, by rfl⟩ : syracuseStep 5663803 = 8495705) B8495705
theorem B7551737 : Blo 2237435 7551737 := bstep (se 2 (by rfl) ⟨2831901, by rfl⟩ : syracuseStep 7551737 = 5663803) B5663803
theorem B5034491 : Blo 2237435 5034491 := bstep (se 1 (by rfl) ⟨3775868, by rfl⟩ : syracuseStep 5034491 = 7551737) B7551737
theorem B3356327 : Blo 2237435 3356327 := bstep (se 1 (by rfl) ⟨2517245, by rfl⟩ : syracuseStep 3356327 = 5034491) B5034491
theorem B2237551 : Blo 2237435 2237551 := bstep (se 1 (by rfl) ⟨1678163, by rfl⟩ : syracuseStep 2237551 = 3356327) B3356327
theorem B3356333 : Blo 2237435 3356333 := bbase (se 3 (by rfl) ⟨629312, by rfl⟩ : syracuseStep 3356333 = 1258625) (by norm_num)
theorem B2237555 : Blo 2237435 2237555 := bstep (se 1 (by rfl) ⟨1678166, by rfl⟩ : syracuseStep 2237555 = 3356333) B3356333
theorem B5034509 : Blo 2237435 5034509 := bbase (se 3 (by rfl) ⟨943970, by rfl⟩ : syracuseStep 5034509 = 1887941) (by norm_num)
theorem B3356339 : Blo 2237435 3356339 := bstep (se 1 (by rfl) ⟨2517254, by rfl⟩ : syracuseStep 3356339 = 5034509) B5034509
theorem B2237559 : Blo 2237435 2237559 := bstep (se 1 (by rfl) ⟨1678169, by rfl⟩ : syracuseStep 2237559 = 3356339) B3356339
theorem B2831917 : Blo 2237435 2831917 := bbase (se 3 (by rfl) ⟨530984, by rfl⟩ : syracuseStep 2831917 = 1061969) (by norm_num)
theorem B3775889 : Blo 2237435 3775889 := bstep (se 2 (by rfl) ⟨1415958, by rfl⟩ : syracuseStep 3775889 = 2831917) B2831917
theorem B2517259 : Blo 2237435 2517259 := bstep (se 1 (by rfl) ⟨1887944, by rfl⟩ : syracuseStep 2517259 = 3775889) B3775889
theorem B3356345 : Blo 2237435 3356345 := bstep (se 2 (by rfl) ⟨1258629, by rfl⟩ : syracuseStep 3356345 = 2517259) B2517259
theorem B2237563 : Blo 2237435 2237563 := bstep (se 1 (by rfl) ⟨1678172, by rfl⟩ : syracuseStep 2237563 = 3356345) B3356345
theorem B8064341 : Blo 2237435 8064341 := bbase (se 11 (by rfl) ⟨5906, by rfl⟩ : syracuseStep 8064341 = 11813) (by norm_num)
theorem B5376227 : Blo 2237435 5376227 := bstep (se 1 (by rfl) ⟨4032170, by rfl⟩ : syracuseStep 5376227 = 8064341) B8064341
theorem B14336605 : Blo 2237435 14336605 := bstep (se 3 (by rfl) ⟨2688113, by rfl⟩ : syracuseStep 14336605 = 5376227) B5376227
theorem B19115473 : Blo 2237435 19115473 := bstep (se 2 (by rfl) ⟨7168302, by rfl⟩ : syracuseStep 19115473 = 14336605) B14336605
theorem B25487297 : Blo 2237435 25487297 := bstep (se 2 (by rfl) ⟨9557736, by rfl⟩ : syracuseStep 25487297 = 19115473) B19115473
theorem B16991531 : Blo 2237435 16991531 := bstep (se 1 (by rfl) ⟨12743648, by rfl⟩ : syracuseStep 16991531 = 25487297) B25487297
theorem B11327687 : Blo 2237435 11327687 := bstep (se 1 (by rfl) ⟨8495765, by rfl⟩ : syracuseStep 11327687 = 16991531) B16991531
theorem B7551791 : Blo 2237435 7551791 := bstep (se 1 (by rfl) ⟨5663843, by rfl⟩ : syracuseStep 7551791 = 11327687) B11327687
theorem B5034527 : Blo 2237435 5034527 := bstep (se 1 (by rfl) ⟨3775895, by rfl⟩ : syracuseStep 5034527 = 7551791) B7551791
theorem B3356351 : Blo 2237435 3356351 := bstep (se 1 (by rfl) ⟨2517263, by rfl⟩ : syracuseStep 3356351 = 5034527) B5034527
theorem B2237567 : Blo 2237435 2237567 := bstep (se 1 (by rfl) ⟨1678175, by rfl⟩ : syracuseStep 2237567 = 3356351) B3356351
theorem B3356357 : Blo 2237435 3356357 := bbase (se 4 (by rfl) ⟨314658, by rfl⟩ : syracuseStep 3356357 = 629317) (by norm_num)
theorem B2237571 : Blo 2237435 2237571 := bstep (se 1 (by rfl) ⟨1678178, by rfl⟩ : syracuseStep 2237571 = 3356357) B3356357
theorem B3775909 : Blo 2237435 3775909 := bbase (se 4 (by rfl) ⟨353991, by rfl⟩ : syracuseStep 3775909 = 707983) (by norm_num)
theorem B5034545 : Blo 2237435 5034545 := bstep (se 2 (by rfl) ⟨1887954, by rfl⟩ : syracuseStep 5034545 = 3775909) B3775909
theorem B3356363 : Blo 2237435 3356363 := bstep (se 1 (by rfl) ⟨2517272, by rfl⟩ : syracuseStep 3356363 = 5034545) B5034545
theorem B2237575 : Blo 2237435 2237575 := bstep (se 1 (by rfl) ⟨1678181, by rfl⟩ : syracuseStep 2237575 = 3356363) B3356363
theorem B2517277 : Blo 2237435 2517277 := bbase (se 3 (by rfl) ⟨471989, by rfl⟩ : syracuseStep 2517277 = 943979) (by norm_num)
theorem B3356369 : Blo 2237435 3356369 := bstep (se 2 (by rfl) ⟨1258638, by rfl⟩ : syracuseStep 3356369 = 2517277) B2517277
theorem B2237579 : Blo 2237435 2237579 := bstep (se 1 (by rfl) ⟨1678184, by rfl⟩ : syracuseStep 2237579 = 3356369) B3356369
theorem B7551845 : Blo 2237435 7551845 := bbase (se 4 (by rfl) ⟨707985, by rfl⟩ : syracuseStep 7551845 = 1415971) (by norm_num)
theorem B5034563 : Blo 2237435 5034563 := bstep (se 1 (by rfl) ⟨3775922, by rfl⟩ : syracuseStep 5034563 = 7551845) B7551845
theorem B3356375 : Blo 2237435 3356375 := bstep (se 1 (by rfl) ⟨2517281, by rfl⟩ : syracuseStep 3356375 = 5034563) B5034563
theorem B2237583 : Blo 2237435 2237583 := bstep (se 1 (by rfl) ⟨1678187, by rfl⟩ : syracuseStep 2237583 = 3356375) B3356375
theorem B3356381 : Blo 2237435 3356381 := bbase (se 3 (by rfl) ⟨629321, by rfl⟩ : syracuseStep 3356381 = 1258643) (by norm_num)
theorem B2237587 : Blo 2237435 2237587 := bstep (se 1 (by rfl) ⟨1678190, by rfl⟩ : syracuseStep 2237587 = 3356381) B3356381
theorem B5034581 : Blo 2237435 5034581 := bbase (se 8 (by rfl) ⟨29499, by rfl⟩ : syracuseStep 5034581 = 58999) (by norm_num)
theorem B3356387 : Blo 2237435 3356387 := bstep (se 1 (by rfl) ⟨2517290, by rfl⟩ : syracuseStep 3356387 = 5034581) B5034581
theorem B2237591 : Blo 2237435 2237591 := bstep (se 1 (by rfl) ⟨1678193, by rfl⟩ : syracuseStep 2237591 = 3356387) B3356387
theorem B3584197 : Blo 2237435 3584197 := bbase (se 4 (by rfl) ⟨336018, by rfl⟩ : syracuseStep 3584197 = 672037) (by norm_num)
theorem B4778929 : Blo 2237435 4778929 := bstep (se 2 (by rfl) ⟨1792098, by rfl⟩ : syracuseStep 4778929 = 3584197) B3584197
theorem B6371905 : Blo 2237435 6371905 := bstep (se 2 (by rfl) ⟨2389464, by rfl⟩ : syracuseStep 6371905 = 4778929) B4778929
theorem B8495873 : Blo 2237435 8495873 := bstep (se 2 (by rfl) ⟨3185952, by rfl⟩ : syracuseStep 8495873 = 6371905) B6371905
theorem B5663915 : Blo 2237435 5663915 := bstep (se 1 (by rfl) ⟨4247936, by rfl⟩ : syracuseStep 5663915 = 8495873) B8495873
theorem B3775943 : Blo 2237435 3775943 := bstep (se 1 (by rfl) ⟨2831957, by rfl⟩ : syracuseStep 3775943 = 5663915) B5663915
theorem B2517295 : Blo 2237435 2517295 := bstep (se 1 (by rfl) ⟨1887971, by rfl⟩ : syracuseStep 2517295 = 3775943) B3775943
theorem B3356393 : Blo 2237435 3356393 := bstep (se 2 (by rfl) ⟨1258647, by rfl⟩ : syracuseStep 3356393 = 2517295) B2517295
theorem B2237595 : Blo 2237435 2237595 := bstep (se 1 (by rfl) ⟨1678196, by rfl⟩ : syracuseStep 2237595 = 3356393) B3356393
theorem B28673621 : Blo 2237435 28673621 := bbase (se 8 (by rfl) ⟨168009, by rfl⟩ : syracuseStep 28673621 = 336019) (by norm_num)
theorem B19115747 : Blo 2237435 19115747 := bstep (se 1 (by rfl) ⟨14336810, by rfl⟩ : syracuseStep 19115747 = 28673621) B28673621
theorem B12743831 : Blo 2237435 12743831 := bstep (se 1 (by rfl) ⟨9557873, by rfl⟩ : syracuseStep 12743831 = 19115747) B19115747
theorem B8495887 : Blo 2237435 8495887 := bstep (se 1 (by rfl) ⟨6371915, by rfl⟩ : syracuseStep 8495887 = 12743831) B12743831
theorem B11327849 : Blo 2237435 11327849 := bstep (se 2 (by rfl) ⟨4247943, by rfl⟩ : syracuseStep 11327849 = 8495887) B8495887
theorem B7551899 : Blo 2237435 7551899 := bstep (se 1 (by rfl) ⟨5663924, by rfl⟩ : syracuseStep 7551899 = 11327849) B11327849
theorem B5034599 : Blo 2237435 5034599 := bstep (se 1 (by rfl) ⟨3775949, by rfl⟩ : syracuseStep 5034599 = 7551899) B7551899
theorem B3356399 : Blo 2237435 3356399 := bstep (se 1 (by rfl) ⟨2517299, by rfl⟩ : syracuseStep 3356399 = 5034599) B5034599
theorem B2237599 : Blo 2237435 2237599 := bstep (se 1 (by rfl) ⟨1678199, by rfl⟩ : syracuseStep 2237599 = 3356399) B3356399
theorem B3356405 : Blo 2237435 3356405 := bbase (se 5 (by rfl) ⟨157331, by rfl⟩ : syracuseStep 3356405 = 314663) (by norm_num)
theorem B2237603 : Blo 2237435 2237603 := bstep (se 1 (by rfl) ⟨1678202, by rfl⟩ : syracuseStep 2237603 = 3356405) B3356405
theorem B9557909 : Blo 2237435 9557909 := bbase (se 6 (by rfl) ⟨224013, by rfl⟩ : syracuseStep 9557909 = 448027) (by norm_num)
theorem B6371939 : Blo 2237435 6371939 := bstep (se 1 (by rfl) ⟨4778954, by rfl⟩ : syracuseStep 6371939 = 9557909) B9557909
theorem B4247959 : Blo 2237435 4247959 := bstep (se 1 (by rfl) ⟨3185969, by rfl⟩ : syracuseStep 4247959 = 6371939) B6371939
theorem B5663945 : Blo 2237435 5663945 := bstep (se 2 (by rfl) ⟨2123979, by rfl⟩ : syracuseStep 5663945 = 4247959) B4247959
theorem B3775963 : Blo 2237435 3775963 := bstep (se 1 (by rfl) ⟨2831972, by rfl⟩ : syracuseStep 3775963 = 5663945) B5663945
theorem B5034617 : Blo 2237435 5034617 := bstep (se 2 (by rfl) ⟨1887981, by rfl⟩ : syracuseStep 5034617 = 3775963) B3775963
theorem B3356411 : Blo 2237435 3356411 := bstep (se 1 (by rfl) ⟨2517308, by rfl⟩ : syracuseStep 3356411 = 5034617) B5034617
theorem B2237607 : Blo 2237435 2237607 := bstep (se 1 (by rfl) ⟨1678205, by rfl⟩ : syracuseStep 2237607 = 3356411) B3356411
theorem B2517313 : Blo 2237435 2517313 := bbase (se 2 (by rfl) ⟨943992, by rfl⟩ : syracuseStep 2517313 = 1887985) (by norm_num)
theorem B3356417 : Blo 2237435 3356417 := bstep (se 2 (by rfl) ⟨1258656, by rfl⟩ : syracuseStep 3356417 = 2517313) B2517313
theorem B2237611 : Blo 2237435 2237611 := bstep (se 1 (by rfl) ⟨1678208, by rfl⟩ : syracuseStep 2237611 = 3356417) B3356417
theorem B5663965 : Blo 2237435 5663965 := bbase (se 3 (by rfl) ⟨1061993, by rfl⟩ : syracuseStep 5663965 = 2123987) (by norm_num)
theorem B7551953 : Blo 2237435 7551953 := bstep (se 2 (by rfl) ⟨2831982, by rfl⟩ : syracuseStep 7551953 = 5663965) B5663965
theorem B5034635 : Blo 2237435 5034635 := bstep (se 1 (by rfl) ⟨3775976, by rfl⟩ : syracuseStep 5034635 = 7551953) B7551953
theorem B3356423 : Blo 2237435 3356423 := bstep (se 1 (by rfl) ⟨2517317, by rfl⟩ : syracuseStep 3356423 = 5034635) B5034635
theorem B2237615 : Blo 2237435 2237615 := bstep (se 1 (by rfl) ⟨1678211, by rfl⟩ : syracuseStep 2237615 = 3356423) B3356423
theorem B3356429 : Blo 2237435 3356429 := bbase (se 3 (by rfl) ⟨629330, by rfl⟩ : syracuseStep 3356429 = 1258661) (by norm_num)
theorem B2237619 : Blo 2237435 2237619 := bstep (se 1 (by rfl) ⟨1678214, by rfl⟩ : syracuseStep 2237619 = 3356429) B3356429
theorem B5034653 : Blo 2237435 5034653 := bbase (se 3 (by rfl) ⟨943997, by rfl⟩ : syracuseStep 5034653 = 1887995) (by norm_num)
theorem B3356435 : Blo 2237435 3356435 := bstep (se 1 (by rfl) ⟨2517326, by rfl⟩ : syracuseStep 3356435 = 5034653) B5034653
theorem B2237623 : Blo 2237435 2237623 := bstep (se 1 (by rfl) ⟨1678217, by rfl⟩ : syracuseStep 2237623 = 3356435) B3356435
theorem B3775997 : Blo 2237435 3775997 := bbase (se 3 (by rfl) ⟨707999, by rfl⟩ : syracuseStep 3775997 = 1415999) (by norm_num)
theorem B2517331 : Blo 2237435 2517331 := bstep (se 1 (by rfl) ⟨1887998, by rfl⟩ : syracuseStep 2517331 = 3775997) B3775997
theorem B3356441 : Blo 2237435 3356441 := bstep (se 2 (by rfl) ⟨1258665, by rfl⟩ : syracuseStep 3356441 = 2517331) B2517331
theorem B2237627 : Blo 2237435 2237627 := bstep (se 1 (by rfl) ⟨1678220, by rfl⟩ : syracuseStep 2237627 = 3356441) B3356441
theorem B4779005 : Blo 2237435 4779005 := bbase (se 3 (by rfl) ⟨896063, by rfl⟩ : syracuseStep 4779005 = 1792127) (by norm_num)
theorem B12744013 : Blo 2237435 12744013 := bstep (se 3 (by rfl) ⟨2389502, by rfl⟩ : syracuseStep 12744013 = 4779005) B4779005
theorem B16992017 : Blo 2237435 16992017 := bstep (se 2 (by rfl) ⟨6372006, by rfl⟩ : syracuseStep 16992017 = 12744013) B12744013
theorem B11328011 : Blo 2237435 11328011 := bstep (se 1 (by rfl) ⟨8496008, by rfl⟩ : syracuseStep 11328011 = 16992017) B16992017
theorem B7552007 : Blo 2237435 7552007 := bstep (se 1 (by rfl) ⟨5664005, by rfl⟩ : syracuseStep 7552007 = 11328011) B11328011
theorem B5034671 : Blo 2237435 5034671 := bstep (se 1 (by rfl) ⟨3776003, by rfl⟩ : syracuseStep 5034671 = 7552007) B7552007
theorem B3356447 : Blo 2237435 3356447 := bstep (se 1 (by rfl) ⟨2517335, by rfl⟩ : syracuseStep 3356447 = 5034671) B5034671
theorem B2237631 : Blo 2237435 2237631 := bstep (se 1 (by rfl) ⟨1678223, by rfl⟩ : syracuseStep 2237631 = 3356447) B3356447
theorem B3356453 : Blo 2237435 3356453 := bbase (se 4 (by rfl) ⟨314667, by rfl⟩ : syracuseStep 3356453 = 629335) (by norm_num)
theorem B2237635 : Blo 2237435 2237635 := bstep (se 1 (by rfl) ⟨1678226, by rfl⟩ : syracuseStep 2237635 = 3356453) B3356453
theorem B2832013 : Blo 2237435 2832013 := bbase (se 3 (by rfl) ⟨531002, by rfl⟩ : syracuseStep 2832013 = 1062005) (by norm_num)
theorem B3776017 : Blo 2237435 3776017 := bstep (se 2 (by rfl) ⟨1416006, by rfl⟩ : syracuseStep 3776017 = 2832013) B2832013
theorem B5034689 : Blo 2237435 5034689 := bstep (se 2 (by rfl) ⟨1888008, by rfl⟩ : syracuseStep 5034689 = 3776017) B3776017
theorem B3356459 : Blo 2237435 3356459 := bstep (se 1 (by rfl) ⟨2517344, by rfl⟩ : syracuseStep 3356459 = 5034689) B5034689
theorem B2237639 : Blo 2237435 2237639 := bstep (se 1 (by rfl) ⟨1678229, by rfl⟩ : syracuseStep 2237639 = 3356459) B3356459
theorem B2517349 : Blo 2237435 2517349 := bbase (se 4 (by rfl) ⟨236001, by rfl⟩ : syracuseStep 2517349 = 472003) (by norm_num)
theorem B3356465 : Blo 2237435 3356465 := bstep (se 2 (by rfl) ⟨1258674, by rfl⟩ : syracuseStep 3356465 = 2517349) B2517349
theorem B2237643 : Blo 2237435 2237643 := bstep (se 1 (by rfl) ⟨1678232, by rfl⟩ : syracuseStep 2237643 = 3356465) B3356465
theorem B6372053 : Blo 2237435 6372053 := bbase (se 7 (by rfl) ⟨74672, by rfl⟩ : syracuseStep 6372053 = 149345) (by norm_num)
theorem B4248035 : Blo 2237435 4248035 := bstep (se 1 (by rfl) ⟨3186026, by rfl⟩ : syracuseStep 4248035 = 6372053) B6372053
theorem B2832023 : Blo 2237435 2832023 := bstep (se 1 (by rfl) ⟨2124017, by rfl⟩ : syracuseStep 2832023 = 4248035) B4248035
theorem B7552061 : Blo 2237435 7552061 := bstep (se 3 (by rfl) ⟨1416011, by rfl⟩ : syracuseStep 7552061 = 2832023) B2832023
theorem B5034707 : Blo 2237435 5034707 := bstep (se 1 (by rfl) ⟨3776030, by rfl⟩ : syracuseStep 5034707 = 7552061) B7552061
theorem B3356471 : Blo 2237435 3356471 := bstep (se 1 (by rfl) ⟨2517353, by rfl⟩ : syracuseStep 3356471 = 5034707) B5034707
theorem B2237647 : Blo 2237435 2237647 := bstep (se 1 (by rfl) ⟨1678235, by rfl⟩ : syracuseStep 2237647 = 3356471) B3356471
theorem B3356477 : Blo 2237435 3356477 := bbase (se 3 (by rfl) ⟨629339, by rfl⟩ : syracuseStep 3356477 = 1258679) (by norm_num)
theorem B2237651 : Blo 2237435 2237651 := bstep (se 1 (by rfl) ⟨1678238, by rfl⟩ : syracuseStep 2237651 = 3356477) B3356477
theorem B5034725 : Blo 2237435 5034725 := bbase (se 4 (by rfl) ⟨472005, by rfl⟩ : syracuseStep 5034725 = 944011) (by norm_num)
theorem B3356483 : Blo 2237435 3356483 := bstep (se 1 (by rfl) ⟨2517362, by rfl⟩ : syracuseStep 3356483 = 5034725) B5034725
theorem B2237655 : Blo 2237435 2237655 := bstep (se 1 (by rfl) ⟨1678241, by rfl⟩ : syracuseStep 2237655 = 3356483) B3356483
theorem B5664077 : Blo 2237435 5664077 := bbase (se 3 (by rfl) ⟨1062014, by rfl⟩ : syracuseStep 5664077 = 2124029) (by norm_num)
theorem B3776051 : Blo 2237435 3776051 := bstep (se 1 (by rfl) ⟨2832038, by rfl⟩ : syracuseStep 3776051 = 5664077) B5664077
theorem B2517367 : Blo 2237435 2517367 := bstep (se 1 (by rfl) ⟨1888025, by rfl⟩ : syracuseStep 2517367 = 3776051) B3776051
theorem B3356489 : Blo 2237435 3356489 := bstep (se 2 (by rfl) ⟨1258683, by rfl⟩ : syracuseStep 3356489 = 2517367) B2517367
theorem B2237659 : Blo 2237435 2237659 := bstep (se 1 (by rfl) ⟨1678244, by rfl⟩ : syracuseStep 2237659 = 3356489) B3356489
theorem B2389537 : Blo 2237435 2389537 := bbase (se 2 (by rfl) ⟨896076, by rfl⟩ : syracuseStep 2389537 = 1792153) (by norm_num)
theorem B3186049 : Blo 2237435 3186049 := bstep (se 2 (by rfl) ⟨1194768, by rfl⟩ : syracuseStep 3186049 = 2389537) B2389537
theorem B4248065 : Blo 2237435 4248065 := bstep (se 2 (by rfl) ⟨1593024, by rfl⟩ : syracuseStep 4248065 = 3186049) B3186049
theorem B11328173 : Blo 2237435 11328173 := bstep (se 3 (by rfl) ⟨2124032, by rfl⟩ : syracuseStep 11328173 = 4248065) B4248065
theorem B7552115 : Blo 2237435 7552115 := bstep (se 1 (by rfl) ⟨5664086, by rfl⟩ : syracuseStep 7552115 = 11328173) B11328173
theorem B5034743 : Blo 2237435 5034743 := bstep (se 1 (by rfl) ⟨3776057, by rfl⟩ : syracuseStep 5034743 = 7552115) B7552115
theorem B3356495 : Blo 2237435 3356495 := bstep (se 1 (by rfl) ⟨2517371, by rfl⟩ : syracuseStep 3356495 = 5034743) B5034743
theorem B2237663 : Blo 2237435 2237663 := bstep (se 1 (by rfl) ⟨1678247, by rfl⟩ : syracuseStep 2237663 = 3356495) B3356495
theorem B3356501 : Blo 2237435 3356501 := bbase (se 9 (by rfl) ⟨9833, by rfl⟩ : syracuseStep 3356501 = 19667) (by norm_num)
theorem B2237667 : Blo 2237435 2237667 := bstep (se 1 (by rfl) ⟨1678250, by rfl⟩ : syracuseStep 2237667 = 3356501) B3356501
theorem B27589781 : Blo 2237435 27589781 := bbase (se 6 (by rfl) ⟨646635, by rfl⟩ : syracuseStep 27589781 = 1293271) (by norm_num)
theorem B73572749 : Blo 2237435 73572749 := bstep (se 3 (by rfl) ⟨13794890, by rfl⟩ : syracuseStep 73572749 = 27589781) B27589781
theorem B49048499 : Blo 2237435 49048499 := bstep (se 1 (by rfl) ⟨36786374, by rfl⟩ : syracuseStep 49048499 = 73572749) B73572749
theorem B32698999 : Blo 2237435 32698999 := bstep (se 1 (by rfl) ⟨24524249, by rfl⟩ : syracuseStep 32698999 = 49048499) B49048499
theorem B43598665 : Blo 2237435 43598665 := bstep (se 2 (by rfl) ⟨16349499, by rfl⟩ : syracuseStep 43598665 = 32698999) B32698999
theorem B58131553 : Blo 2237435 58131553 := bstep (se 2 (by rfl) ⟨21799332, by rfl⟩ : syracuseStep 58131553 = 43598665) B43598665
theorem B77508737 : Blo 2237435 77508737 := bstep (se 2 (by rfl) ⟨29065776, by rfl⟩ : syracuseStep 77508737 = 58131553) B58131553
theorem B51672491 : Blo 2237435 51672491 := bstep (se 1 (by rfl) ⟨38754368, by rfl⟩ : syracuseStep 51672491 = 77508737) B77508737
theorem B34448327 : Blo 2237435 34448327 := bstep (se 1 (by rfl) ⟨25836245, by rfl⟩ : syracuseStep 34448327 = 51672491) B51672491
theorem B22965551 : Blo 2237435 22965551 := bstep (se 1 (by rfl) ⟨17224163, by rfl⟩ : syracuseStep 22965551 = 34448327) B34448327
theorem B15310367 : Blo 2237435 15310367 := bstep (se 1 (by rfl) ⟨11482775, by rfl⟩ : syracuseStep 15310367 = 22965551) B22965551
theorem B10206911 : Blo 2237435 10206911 := bstep (se 1 (by rfl) ⟨7655183, by rfl⟩ : syracuseStep 10206911 = 15310367) B15310367
theorem B6804607 : Blo 2237435 6804607 := bstep (se 1 (by rfl) ⟨5103455, by rfl⟩ : syracuseStep 6804607 = 10206911) B10206911
theorem B9072809 : Blo 2237435 9072809 := bstep (se 2 (by rfl) ⟨3402303, by rfl⟩ : syracuseStep 9072809 = 6804607) B6804607
theorem B6048539 : Blo 2237435 6048539 := bstep (se 1 (by rfl) ⟨4536404, by rfl⟩ : syracuseStep 6048539 = 9072809) B9072809
theorem B4032359 : Blo 2237435 4032359 := bstep (se 1 (by rfl) ⟨3024269, by rfl⟩ : syracuseStep 4032359 = 6048539) B6048539
theorem B2688239 : Blo 2237435 2688239 := bstep (se 1 (by rfl) ⟨2016179, by rfl⟩ : syracuseStep 2688239 = 4032359) B4032359
theorem B7168637 : Blo 2237435 7168637 := bstep (se 3 (by rfl) ⟨1344119, by rfl⟩ : syracuseStep 7168637 = 2688239) B2688239
theorem B4779091 : Blo 2237435 4779091 := bstep (se 1 (by rfl) ⟨3584318, by rfl⟩ : syracuseStep 4779091 = 7168637) B7168637
theorem B6372121 : Blo 2237435 6372121 := bstep (se 2 (by rfl) ⟨2389545, by rfl⟩ : syracuseStep 6372121 = 4779091) B4779091
theorem B8496161 : Blo 2237435 8496161 := bstep (se 2 (by rfl) ⟨3186060, by rfl⟩ : syracuseStep 8496161 = 6372121) B6372121
theorem B5664107 : Blo 2237435 5664107 := bstep (se 1 (by rfl) ⟨4248080, by rfl⟩ : syracuseStep 5664107 = 8496161) B8496161
theorem B3776071 : Blo 2237435 3776071 := bstep (se 1 (by rfl) ⟨2832053, by rfl⟩ : syracuseStep 3776071 = 5664107) B5664107
theorem B5034761 : Blo 2237435 5034761 := bstep (se 2 (by rfl) ⟨1888035, by rfl⟩ : syracuseStep 5034761 = 3776071) B3776071
theorem B3356507 : Blo 2237435 3356507 := bstep (se 1 (by rfl) ⟨2517380, by rfl⟩ : syracuseStep 3356507 = 5034761) B5034761
theorem B2237671 : Blo 2237435 2237671 := bstep (se 1 (by rfl) ⟨1678253, by rfl⟩ : syracuseStep 2237671 = 3356507) B3356507
theorem B2517385 : Blo 2237435 2517385 := bbase (se 2 (by rfl) ⟨944019, by rfl⟩ : syracuseStep 2517385 = 1888039) (by norm_num)
theorem B3356513 : Blo 2237435 3356513 := bstep (se 2 (by rfl) ⟨1258692, by rfl⟩ : syracuseStep 3356513 = 2517385) B2517385
theorem B2237675 : Blo 2237435 2237675 := bstep (se 1 (by rfl) ⟨1678256, by rfl⟩ : syracuseStep 2237675 = 3356513) B3356513
theorem B6804629 : Blo 2237435 6804629 := bbase (se 6 (by rfl) ⟨159483, by rfl⟩ : syracuseStep 6804629 = 318967) (by norm_num)
theorem B4536419 : Blo 2237435 4536419 := bstep (se 1 (by rfl) ⟨3402314, by rfl⟩ : syracuseStep 4536419 = 6804629) B6804629
theorem B12097117 : Blo 2237435 12097117 := bstep (se 3 (by rfl) ⟨2268209, by rfl⟩ : syracuseStep 12097117 = 4536419) B4536419
theorem B64517957 : Blo 2237435 64517957 := bstep (se 4 (by rfl) ⟨6048558, by rfl⟩ : syracuseStep 64517957 = 12097117) B12097117
theorem B43011971 : Blo 2237435 43011971 := bstep (se 1 (by rfl) ⟨32258978, by rfl⟩ : syracuseStep 43011971 = 64517957) B64517957
theorem B28674647 : Blo 2237435 28674647 := bstep (se 1 (by rfl) ⟨21505985, by rfl⟩ : syracuseStep 28674647 = 43011971) B43011971
theorem B19116431 : Blo 2237435 19116431 := bstep (se 1 (by rfl) ⟨14337323, by rfl⟩ : syracuseStep 19116431 = 28674647) B28674647
theorem B12744287 : Blo 2237435 12744287 := bstep (se 1 (by rfl) ⟨9558215, by rfl⟩ : syracuseStep 12744287 = 19116431) B19116431
theorem B8496191 : Blo 2237435 8496191 := bstep (se 1 (by rfl) ⟨6372143, by rfl⟩ : syracuseStep 8496191 = 12744287) B12744287
theorem B5664127 : Blo 2237435 5664127 := bstep (se 1 (by rfl) ⟨4248095, by rfl⟩ : syracuseStep 5664127 = 8496191) B8496191
theorem B7552169 : Blo 2237435 7552169 := bstep (se 2 (by rfl) ⟨2832063, by rfl⟩ : syracuseStep 7552169 = 5664127) B5664127
theorem B5034779 : Blo 2237435 5034779 := bstep (se 1 (by rfl) ⟨3776084, by rfl⟩ : syracuseStep 5034779 = 7552169) B7552169
theorem B3356519 : Blo 2237435 3356519 := bstep (se 1 (by rfl) ⟨2517389, by rfl⟩ : syracuseStep 3356519 = 5034779) B5034779
theorem B2237679 : Blo 2237435 2237679 := bstep (se 1 (by rfl) ⟨1678259, by rfl⟩ : syracuseStep 2237679 = 3356519) B3356519
theorem B3356525 : Blo 2237435 3356525 := bbase (se 3 (by rfl) ⟨629348, by rfl⟩ : syracuseStep 3356525 = 1258697) (by norm_num)
theorem B2237683 : Blo 2237435 2237683 := bstep (se 1 (by rfl) ⟨1678262, by rfl⟩ : syracuseStep 2237683 = 3356525) B3356525
theorem B5034797 : Blo 2237435 5034797 := bbase (se 3 (by rfl) ⟨944024, by rfl⟩ : syracuseStep 5034797 = 1888049) (by norm_num)
theorem B3356531 : Blo 2237435 3356531 := bstep (se 1 (by rfl) ⟨2517398, by rfl⟩ : syracuseStep 3356531 = 5034797) B5034797
theorem B2237687 : Blo 2237435 2237687 := bstep (se 1 (by rfl) ⟨1678265, by rfl⟩ : syracuseStep 2237687 = 3356531) B3356531
theorem B18145781 : Blo 2237435 18145781 := bbase (se 5 (by rfl) ⟨850583, by rfl⟩ : syracuseStep 18145781 = 1701167) (by norm_num)
theorem B12097187 : Blo 2237435 12097187 := bstep (se 1 (by rfl) ⟨9072890, by rfl⟩ : syracuseStep 12097187 = 18145781) B18145781
theorem B8064791 : Blo 2237435 8064791 := bstep (se 1 (by rfl) ⟨6048593, by rfl⟩ : syracuseStep 8064791 = 12097187) B12097187
theorem B5376527 : Blo 2237435 5376527 := bstep (se 1 (by rfl) ⟨4032395, by rfl⟩ : syracuseStep 5376527 = 8064791) B8064791
theorem B3584351 : Blo 2237435 3584351 := bstep (se 1 (by rfl) ⟨2688263, by rfl⟩ : syracuseStep 3584351 = 5376527) B5376527
theorem B9558269 : Blo 2237435 9558269 := bstep (se 3 (by rfl) ⟨1792175, by rfl⟩ : syracuseStep 9558269 = 3584351) B3584351
theorem B6372179 : Blo 2237435 6372179 := bstep (se 1 (by rfl) ⟨4779134, by rfl⟩ : syracuseStep 6372179 = 9558269) B9558269
theorem B4248119 : Blo 2237435 4248119 := bstep (se 1 (by rfl) ⟨3186089, by rfl⟩ : syracuseStep 4248119 = 6372179) B6372179
theorem B2832079 : Blo 2237435 2832079 := bstep (se 1 (by rfl) ⟨2124059, by rfl⟩ : syracuseStep 2832079 = 4248119) B4248119
theorem B3776105 : Blo 2237435 3776105 := bstep (se 2 (by rfl) ⟨1416039, by rfl⟩ : syracuseStep 3776105 = 2832079) B2832079
theorem B2517403 : Blo 2237435 2517403 := bstep (se 1 (by rfl) ⟨1888052, by rfl⟩ : syracuseStep 2517403 = 3776105) B3776105
theorem B3356537 : Blo 2237435 3356537 := bstep (se 2 (by rfl) ⟨1258701, by rfl⟩ : syracuseStep 3356537 = 2517403) B2517403
theorem B2237691 : Blo 2237435 2237691 := bstep (se 1 (by rfl) ⟨1678268, by rfl⟩ : syracuseStep 2237691 = 3356537) B3356537
theorem B3024301 : Blo 2237435 3024301 := bbase (se 3 (by rfl) ⟨567056, by rfl⟩ : syracuseStep 3024301 = 1134113) (by norm_num)
theorem B4032401 : Blo 2237435 4032401 := bstep (se 2 (by rfl) ⟨1512150, by rfl⟩ : syracuseStep 4032401 = 3024301) B3024301
theorem B10753069 : Blo 2237435 10753069 := bstep (se 3 (by rfl) ⟨2016200, by rfl⟩ : syracuseStep 10753069 = 4032401) B4032401
theorem B14337425 : Blo 2237435 14337425 := bstep (se 2 (by rfl) ⟨5376534, by rfl⟩ : syracuseStep 14337425 = 10753069) B10753069
theorem B38233133 : Blo 2237435 38233133 := bstep (se 3 (by rfl) ⟨7168712, by rfl⟩ : syracuseStep 38233133 = 14337425) B14337425
theorem B25488755 : Blo 2237435 25488755 := bstep (se 1 (by rfl) ⟨19116566, by rfl⟩ : syracuseStep 25488755 = 38233133) B38233133
theorem B16992503 : Blo 2237435 16992503 := bstep (se 1 (by rfl) ⟨12744377, by rfl⟩ : syracuseStep 16992503 = 25488755) B25488755
theorem B11328335 : Blo 2237435 11328335 := bstep (se 1 (by rfl) ⟨8496251, by rfl⟩ : syracuseStep 11328335 = 16992503) B16992503
theorem B7552223 : Blo 2237435 7552223 := bstep (se 1 (by rfl) ⟨5664167, by rfl⟩ : syracuseStep 7552223 = 11328335) B11328335
theorem B5034815 : Blo 2237435 5034815 := bstep (se 1 (by rfl) ⟨3776111, by rfl⟩ : syracuseStep 5034815 = 7552223) B7552223
theorem B3356543 : Blo 2237435 3356543 := bstep (se 1 (by rfl) ⟨2517407, by rfl⟩ : syracuseStep 3356543 = 5034815) B5034815
theorem B2237695 : Blo 2237435 2237695 := bstep (se 1 (by rfl) ⟨1678271, by rfl⟩ : syracuseStep 2237695 = 3356543) B3356543
theorem B3356549 : Blo 2237435 3356549 := bbase (se 4 (by rfl) ⟨314676, by rfl⟩ : syracuseStep 3356549 = 629353) (by norm_num)
theorem B2237699 : Blo 2237435 2237699 := bstep (se 1 (by rfl) ⟨1678274, by rfl⟩ : syracuseStep 2237699 = 3356549) B3356549
theorem B3776125 : Blo 2237435 3776125 := bbase (se 3 (by rfl) ⟨708023, by rfl⟩ : syracuseStep 3776125 = 1416047) (by norm_num)
theorem B5034833 : Blo 2237435 5034833 := bstep (se 2 (by rfl) ⟨1888062, by rfl⟩ : syracuseStep 5034833 = 3776125) B3776125
theorem B3356555 : Blo 2237435 3356555 := bstep (se 1 (by rfl) ⟨2517416, by rfl⟩ : syracuseStep 3356555 = 5034833) B5034833
theorem B2237703 : Blo 2237435 2237703 := bstep (se 1 (by rfl) ⟨1678277, by rfl⟩ : syracuseStep 2237703 = 3356555) B3356555
theorem B2517421 : Blo 2237435 2517421 := bbase (se 3 (by rfl) ⟨472016, by rfl⟩ : syracuseStep 2517421 = 944033) (by norm_num)
theorem B3356561 : Blo 2237435 3356561 := bstep (se 2 (by rfl) ⟨1258710, by rfl⟩ : syracuseStep 3356561 = 2517421) B2517421
theorem B2237707 : Blo 2237435 2237707 := bstep (se 1 (by rfl) ⟨1678280, by rfl⟩ : syracuseStep 2237707 = 3356561) B3356561
theorem B7552277 : Blo 2237435 7552277 := bbase (se 6 (by rfl) ⟨177006, by rfl⟩ : syracuseStep 7552277 = 354013) (by norm_num)
theorem B5034851 : Blo 2237435 5034851 := bstep (se 1 (by rfl) ⟨3776138, by rfl⟩ : syracuseStep 5034851 = 7552277) B7552277
theorem B3356567 : Blo 2237435 3356567 := bstep (se 1 (by rfl) ⟨2517425, by rfl⟩ : syracuseStep 3356567 = 5034851) B5034851
theorem B2237711 : Blo 2237435 2237711 := bstep (se 1 (by rfl) ⟨1678283, by rfl⟩ : syracuseStep 2237711 = 3356567) B3356567
theorem B3356573 : Blo 2237435 3356573 := bbase (se 3 (by rfl) ⟨629357, by rfl⟩ : syracuseStep 3356573 = 1258715) (by norm_num)
theorem B2237715 : Blo 2237435 2237715 := bstep (se 1 (by rfl) ⟨1678286, by rfl⟩ : syracuseStep 2237715 = 3356573) B3356573
theorem B5034869 : Blo 2237435 5034869 := bbase (se 5 (by rfl) ⟨236009, by rfl⟩ : syracuseStep 5034869 = 472019) (by norm_num)
theorem B3356579 : Blo 2237435 3356579 := bstep (se 1 (by rfl) ⟨2517434, by rfl⟩ : syracuseStep 3356579 = 5034869) B5034869
theorem B2237719 : Blo 2237435 2237719 := bstep (se 1 (by rfl) ⟨1678289, by rfl⟩ : syracuseStep 2237719 = 3356579) B3356579
theorem B9196805 : Blo 2237435 9196805 := bbase (se 4 (by rfl) ⟨862200, by rfl⟩ : syracuseStep 9196805 = 1724401) (by norm_num)
theorem B24524813 : Blo 2237435 24524813 := bstep (se 3 (by rfl) ⟨4598402, by rfl⟩ : syracuseStep 24524813 = 9196805) B9196805
theorem B65399501 : Blo 2237435 65399501 := bstep (se 3 (by rfl) ⟨12262406, by rfl⟩ : syracuseStep 65399501 = 24524813) B24524813
theorem B43599667 : Blo 2237435 43599667 := bstep (se 1 (by rfl) ⟨32699750, by rfl⟩ : syracuseStep 43599667 = 65399501) B65399501
theorem B58132889 : Blo 2237435 58132889 := bstep (se 2 (by rfl) ⟨21799833, by rfl⟩ : syracuseStep 58132889 = 43599667) B43599667
theorem B38755259 : Blo 2237435 38755259 := bstep (se 1 (by rfl) ⟨29066444, by rfl⟩ : syracuseStep 38755259 = 58132889) B58132889
theorem B25836839 : Blo 2237435 25836839 := bstep (se 1 (by rfl) ⟨19377629, by rfl⟩ : syracuseStep 25836839 = 38755259) B38755259
theorem B17224559 : Blo 2237435 17224559 := bstep (se 1 (by rfl) ⟨12918419, by rfl⟩ : syracuseStep 17224559 = 25836839) B25836839
theorem B11483039 : Blo 2237435 11483039 := bstep (se 1 (by rfl) ⟨8612279, by rfl⟩ : syracuseStep 11483039 = 17224559) B17224559
theorem B7655359 : Blo 2237435 7655359 := bstep (se 1 (by rfl) ⟨5741519, by rfl⟩ : syracuseStep 7655359 = 11483039) B11483039
theorem B10207145 : Blo 2237435 10207145 := bstep (se 2 (by rfl) ⟨3827679, by rfl⟩ : syracuseStep 10207145 = 7655359) B7655359
theorem B27219053 : Blo 2237435 27219053 := bstep (se 3 (by rfl) ⟨5103572, by rfl⟩ : syracuseStep 27219053 = 10207145) B10207145
theorem B18146035 : Blo 2237435 18146035 := bstep (se 1 (by rfl) ⟨13609526, by rfl⟩ : syracuseStep 18146035 = 27219053) B27219053
theorem B24194713 : Blo 2237435 24194713 := bstep (se 2 (by rfl) ⟨9073017, by rfl⟩ : syracuseStep 24194713 = 18146035) B18146035
theorem B32259617 : Blo 2237435 32259617 := bstep (se 2 (by rfl) ⟨12097356, by rfl⟩ : syracuseStep 32259617 = 24194713) B24194713
theorem B21506411 : Blo 2237435 21506411 := bstep (se 1 (by rfl) ⟨16129808, by rfl⟩ : syracuseStep 21506411 = 32259617) B32259617
theorem B14337607 : Blo 2237435 14337607 := bstep (se 1 (by rfl) ⟨10753205, by rfl⟩ : syracuseStep 14337607 = 21506411) B21506411
theorem B19116809 : Blo 2237435 19116809 := bstep (se 2 (by rfl) ⟨7168803, by rfl⟩ : syracuseStep 19116809 = 14337607) B14337607
theorem B12744539 : Blo 2237435 12744539 := bstep (se 1 (by rfl) ⟨9558404, by rfl⟩ : syracuseStep 12744539 = 19116809) B19116809
theorem B8496359 : Blo 2237435 8496359 := bstep (se 1 (by rfl) ⟨6372269, by rfl⟩ : syracuseStep 8496359 = 12744539) B12744539
theorem B5664239 : Blo 2237435 5664239 := bstep (se 1 (by rfl) ⟨4248179, by rfl⟩ : syracuseStep 5664239 = 8496359) B8496359
theorem B3776159 : Blo 2237435 3776159 := bstep (se 1 (by rfl) ⟨2832119, by rfl⟩ : syracuseStep 3776159 = 5664239) B5664239
theorem B2517439 : Blo 2237435 2517439 := bstep (se 1 (by rfl) ⟨1888079, by rfl⟩ : syracuseStep 2517439 = 3776159) B3776159
theorem B3356585 : Blo 2237435 3356585 := bstep (se 2 (by rfl) ⟨1258719, by rfl⟩ : syracuseStep 3356585 = 2517439) B2517439
theorem B2237723 : Blo 2237435 2237723 := bstep (se 1 (by rfl) ⟨1678292, by rfl⟩ : syracuseStep 2237723 = 3356585) B3356585
theorem B8496373 : Blo 2237435 8496373 := bbase (se 5 (by rfl) ⟨398267, by rfl⟩ : syracuseStep 8496373 = 796535) (by norm_num)
theorem B11328497 : Blo 2237435 11328497 := bstep (se 2 (by rfl) ⟨4248186, by rfl⟩ : syracuseStep 11328497 = 8496373) B8496373
theorem B7552331 : Blo 2237435 7552331 := bstep (se 1 (by rfl) ⟨5664248, by rfl⟩ : syracuseStep 7552331 = 11328497) B11328497
theorem B5034887 : Blo 2237435 5034887 := bstep (se 1 (by rfl) ⟨3776165, by rfl⟩ : syracuseStep 5034887 = 7552331) B7552331
theorem B3356591 : Blo 2237435 3356591 := bstep (se 1 (by rfl) ⟨2517443, by rfl⟩ : syracuseStep 3356591 = 5034887) B5034887
theorem B2237727 : Blo 2237435 2237727 := bstep (se 1 (by rfl) ⟨1678295, by rfl⟩ : syracuseStep 2237727 = 3356591) B3356591
theorem B3356597 : Blo 2237435 3356597 := bbase (se 5 (by rfl) ⟨157340, by rfl⟩ : syracuseStep 3356597 = 314681) (by norm_num)
theorem B2237731 : Blo 2237435 2237731 := bstep (se 1 (by rfl) ⟨1678298, by rfl⟩ : syracuseStep 2237731 = 3356597) B3356597
theorem B5664269 : Blo 2237435 5664269 := bbase (se 3 (by rfl) ⟨1062050, by rfl⟩ : syracuseStep 5664269 = 2124101) (by norm_num)
theorem B3776179 : Blo 2237435 3776179 := bstep (se 1 (by rfl) ⟨2832134, by rfl⟩ : syracuseStep 3776179 = 5664269) B5664269
theorem B5034905 : Blo 2237435 5034905 := bstep (se 2 (by rfl) ⟨1888089, by rfl⟩ : syracuseStep 5034905 = 3776179) B3776179
theorem B3356603 : Blo 2237435 3356603 := bstep (se 1 (by rfl) ⟨2517452, by rfl⟩ : syracuseStep 3356603 = 5034905) B5034905
theorem B2237735 : Blo 2237435 2237735 := bstep (se 1 (by rfl) ⟨1678301, by rfl⟩ : syracuseStep 2237735 = 3356603) B3356603
theorem B2517457 : Blo 2237435 2517457 := bbase (se 2 (by rfl) ⟨944046, by rfl⟩ : syracuseStep 2517457 = 1888093) (by norm_num)
theorem B3356609 : Blo 2237435 3356609 := bstep (se 2 (by rfl) ⟨1258728, by rfl⟩ : syracuseStep 3356609 = 2517457) B2517457
theorem B2237739 : Blo 2237435 2237739 := bstep (se 1 (by rfl) ⟨1678304, by rfl⟩ : syracuseStep 2237739 = 3356609) B3356609
theorem B4779245 : Blo 2237435 4779245 := bbase (se 3 (by rfl) ⟨896108, by rfl⟩ : syracuseStep 4779245 = 1792217) (by norm_num)
theorem B3186163 : Blo 2237435 3186163 := bstep (se 1 (by rfl) ⟨2389622, by rfl⟩ : syracuseStep 3186163 = 4779245) B4779245
theorem B4248217 : Blo 2237435 4248217 := bstep (se 2 (by rfl) ⟨1593081, by rfl⟩ : syracuseStep 4248217 = 3186163) B3186163
theorem B5664289 : Blo 2237435 5664289 := bstep (se 2 (by rfl) ⟨2124108, by rfl⟩ : syracuseStep 5664289 = 4248217) B4248217
theorem B7552385 : Blo 2237435 7552385 := bstep (se 2 (by rfl) ⟨2832144, by rfl⟩ : syracuseStep 7552385 = 5664289) B5664289
theorem B5034923 : Blo 2237435 5034923 := bstep (se 1 (by rfl) ⟨3776192, by rfl⟩ : syracuseStep 5034923 = 7552385) B7552385
theorem B3356615 : Blo 2237435 3356615 := bstep (se 1 (by rfl) ⟨2517461, by rfl⟩ : syracuseStep 3356615 = 5034923) B5034923
theorem B2237743 : Blo 2237435 2237743 := bstep (se 1 (by rfl) ⟨1678307, by rfl⟩ : syracuseStep 2237743 = 3356615) B3356615
theorem B3356621 : Blo 2237435 3356621 := bbase (se 3 (by rfl) ⟨629366, by rfl⟩ : syracuseStep 3356621 = 1258733) (by norm_num)
theorem B2237747 : Blo 2237435 2237747 := bstep (se 1 (by rfl) ⟨1678310, by rfl⟩ : syracuseStep 2237747 = 3356621) B3356621
theorem B5034941 : Blo 2237435 5034941 := bbase (se 3 (by rfl) ⟨944051, by rfl⟩ : syracuseStep 5034941 = 1888103) (by norm_num)
theorem B3356627 : Blo 2237435 3356627 := bstep (se 1 (by rfl) ⟨2517470, by rfl⟩ : syracuseStep 3356627 = 5034941) B5034941
theorem B2237751 : Blo 2237435 2237751 := bstep (se 1 (by rfl) ⟨1678313, by rfl⟩ : syracuseStep 2237751 = 3356627) B3356627
theorem B3776213 : Blo 2237435 3776213 := bbase (se 7 (by rfl) ⟨44252, by rfl⟩ : syracuseStep 3776213 = 88505) (by norm_num)
theorem B2517475 : Blo 2237435 2517475 := bstep (se 1 (by rfl) ⟨1888106, by rfl⟩ : syracuseStep 2517475 = 3776213) B3776213
theorem B3356633 : Blo 2237435 3356633 := bstep (se 2 (by rfl) ⟨1258737, by rfl⟩ : syracuseStep 3356633 = 2517475) B2517475
theorem B2237755 : Blo 2237435 2237755 := bstep (se 1 (by rfl) ⟨1678316, by rfl⟩ : syracuseStep 2237755 = 3356633) B3356633
theorem B4032517 : Blo 2237435 4032517 := bbase (se 4 (by rfl) ⟨378048, by rfl⟩ : syracuseStep 4032517 = 756097) (by norm_num)
theorem B5376689 : Blo 2237435 5376689 := bstep (se 2 (by rfl) ⟨2016258, by rfl⟩ : syracuseStep 5376689 = 4032517) B4032517
theorem B3584459 : Blo 2237435 3584459 := bstep (se 1 (by rfl) ⟨2688344, by rfl⟩ : syracuseStep 3584459 = 5376689) B5376689
theorem B9558557 : Blo 2237435 9558557 := bstep (se 3 (by rfl) ⟨1792229, by rfl⟩ : syracuseStep 9558557 = 3584459) B3584459
theorem B6372371 : Blo 2237435 6372371 := bstep (se 1 (by rfl) ⟨4779278, by rfl⟩ : syracuseStep 6372371 = 9558557) B9558557
theorem B16992989 : Blo 2237435 16992989 := bstep (se 3 (by rfl) ⟨3186185, by rfl⟩ : syracuseStep 16992989 = 6372371) B6372371
theorem B11328659 : Blo 2237435 11328659 := bstep (se 1 (by rfl) ⟨8496494, by rfl⟩ : syracuseStep 11328659 = 16992989) B16992989
theorem B7552439 : Blo 2237435 7552439 := bstep (se 1 (by rfl) ⟨5664329, by rfl⟩ : syracuseStep 7552439 = 11328659) B11328659
theorem B5034959 : Blo 2237435 5034959 := bstep (se 1 (by rfl) ⟨3776219, by rfl⟩ : syracuseStep 5034959 = 7552439) B7552439
theorem B3356639 : Blo 2237435 3356639 := bstep (se 1 (by rfl) ⟨2517479, by rfl⟩ : syracuseStep 3356639 = 5034959) B5034959
theorem B2237759 : Blo 2237435 2237759 := bstep (se 1 (by rfl) ⟨1678319, by rfl⟩ : syracuseStep 2237759 = 3356639) B3356639
theorem B3356645 : Blo 2237435 3356645 := bbase (se 4 (by rfl) ⟨314685, by rfl⟩ : syracuseStep 3356645 = 629371) (by norm_num)
theorem B2237763 : Blo 2237435 2237763 := bstep (se 1 (by rfl) ⟨1678322, by rfl⟩ : syracuseStep 2237763 = 3356645) B3356645
theorem B5376709 : Blo 2237435 5376709 := bbase (se 4 (by rfl) ⟨504066, by rfl⟩ : syracuseStep 5376709 = 1008133) (by norm_num)
theorem B7168945 : Blo 2237435 7168945 := bstep (se 2 (by rfl) ⟨2688354, by rfl⟩ : syracuseStep 7168945 = 5376709) B5376709
theorem B9558593 : Blo 2237435 9558593 := bstep (se 2 (by rfl) ⟨3584472, by rfl⟩ : syracuseStep 9558593 = 7168945) B7168945
theorem B6372395 : Blo 2237435 6372395 := bstep (se 1 (by rfl) ⟨4779296, by rfl⟩ : syracuseStep 6372395 = 9558593) B9558593
theorem B4248263 : Blo 2237435 4248263 := bstep (se 1 (by rfl) ⟨3186197, by rfl⟩ : syracuseStep 4248263 = 6372395) B6372395
theorem B2832175 : Blo 2237435 2832175 := bstep (se 1 (by rfl) ⟨2124131, by rfl⟩ : syracuseStep 2832175 = 4248263) B4248263
theorem B3776233 : Blo 2237435 3776233 := bstep (se 2 (by rfl) ⟨1416087, by rfl⟩ : syracuseStep 3776233 = 2832175) B2832175
theorem B5034977 : Blo 2237435 5034977 := bstep (se 2 (by rfl) ⟨1888116, by rfl⟩ : syracuseStep 5034977 = 3776233) B3776233
theorem B3356651 : Blo 2237435 3356651 := bstep (se 1 (by rfl) ⟨2517488, by rfl⟩ : syracuseStep 3356651 = 5034977) B5034977
theorem B2237767 : Blo 2237435 2237767 := bstep (se 1 (by rfl) ⟨1678325, by rfl⟩ : syracuseStep 2237767 = 3356651) B3356651
theorem B2517493 : Blo 2237435 2517493 := bbase (se 5 (by rfl) ⟨118007, by rfl⟩ : syracuseStep 2517493 = 236015) (by norm_num)
theorem B3356657 : Blo 2237435 3356657 := bstep (se 2 (by rfl) ⟨1258746, by rfl⟩ : syracuseStep 3356657 = 2517493) B2517493
theorem B2237771 : Blo 2237435 2237771 := bstep (se 1 (by rfl) ⟨1678328, by rfl⟩ : syracuseStep 2237771 = 3356657) B3356657
theorem B2832185 : Blo 2237435 2832185 := bbase (se 2 (by rfl) ⟨1062069, by rfl⟩ : syracuseStep 2832185 = 2124139) (by norm_num)
theorem B7552493 : Blo 2237435 7552493 := bstep (se 3 (by rfl) ⟨1416092, by rfl⟩ : syracuseStep 7552493 = 2832185) B2832185
theorem B5034995 : Blo 2237435 5034995 := bstep (se 1 (by rfl) ⟨3776246, by rfl⟩ : syracuseStep 5034995 = 7552493) B7552493
theorem B3356663 : Blo 2237435 3356663 := bstep (se 1 (by rfl) ⟨2517497, by rfl⟩ : syracuseStep 3356663 = 5034995) B5034995
theorem B2237775 : Blo 2237435 2237775 := bstep (se 1 (by rfl) ⟨1678331, by rfl⟩ : syracuseStep 2237775 = 3356663) B3356663
theorem B3356669 : Blo 2237435 3356669 := bbase (se 3 (by rfl) ⟨629375, by rfl⟩ : syracuseStep 3356669 = 1258751) (by norm_num)
theorem B2237779 : Blo 2237435 2237779 := bstep (se 1 (by rfl) ⟨1678334, by rfl⟩ : syracuseStep 2237779 = 3356669) B3356669
theorem B5035013 : Blo 2237435 5035013 := bbase (se 4 (by rfl) ⟨472032, by rfl⟩ : syracuseStep 5035013 = 944065) (by norm_num)
theorem B3356675 : Blo 2237435 3356675 := bstep (se 1 (by rfl) ⟨2517506, by rfl⟩ : syracuseStep 3356675 = 5035013) B5035013
theorem B2237783 : Blo 2237435 2237783 := bstep (se 1 (by rfl) ⟨1678337, by rfl⟩ : syracuseStep 2237783 = 3356675) B3356675
theorem B4248301 : Blo 2237435 4248301 := bbase (se 3 (by rfl) ⟨796556, by rfl⟩ : syracuseStep 4248301 = 1593113) (by norm_num)
theorem B5664401 : Blo 2237435 5664401 := bstep (se 2 (by rfl) ⟨2124150, by rfl⟩ : syracuseStep 5664401 = 4248301) B4248301
theorem B3776267 : Blo 2237435 3776267 := bstep (se 1 (by rfl) ⟨2832200, by rfl⟩ : syracuseStep 3776267 = 5664401) B5664401
theorem B2517511 : Blo 2237435 2517511 := bstep (se 1 (by rfl) ⟨1888133, by rfl⟩ : syracuseStep 2517511 = 3776267) B3776267
theorem B3356681 : Blo 2237435 3356681 := bstep (se 2 (by rfl) ⟨1258755, by rfl⟩ : syracuseStep 3356681 = 2517511) B2517511
theorem B2237787 : Blo 2237435 2237787 := bstep (se 1 (by rfl) ⟨1678340, by rfl⟩ : syracuseStep 2237787 = 3356681) B3356681
theorem B11328821 : Blo 2237435 11328821 := bbase (se 5 (by rfl) ⟨531038, by rfl⟩ : syracuseStep 11328821 = 1062077) (by norm_num)
theorem B7552547 : Blo 2237435 7552547 := bstep (se 1 (by rfl) ⟨5664410, by rfl⟩ : syracuseStep 7552547 = 11328821) B11328821
theorem B5035031 : Blo 2237435 5035031 := bstep (se 1 (by rfl) ⟨3776273, by rfl⟩ : syracuseStep 5035031 = 7552547) B7552547
theorem B3356687 : Blo 2237435 3356687 := bstep (se 1 (by rfl) ⟨2517515, by rfl⟩ : syracuseStep 3356687 = 5035031) B5035031
theorem B2237791 : Blo 2237435 2237791 := bstep (se 1 (by rfl) ⟨1678343, by rfl⟩ : syracuseStep 2237791 = 3356687) B3356687
theorem B3356693 : Blo 2237435 3356693 := bbase (se 6 (by rfl) ⟨78672, by rfl⟩ : syracuseStep 3356693 = 157345) (by norm_num)
theorem B2237795 : Blo 2237435 2237795 := bstep (se 1 (by rfl) ⟨1678346, by rfl⟩ : syracuseStep 2237795 = 3356693) B3356693
theorem B4032589 : Blo 2237435 4032589 := bbase (se 3 (by rfl) ⟨756110, by rfl⟩ : syracuseStep 4032589 = 1512221) (by norm_num)
theorem B5376785 : Blo 2237435 5376785 := bstep (se 2 (by rfl) ⟨2016294, by rfl⟩ : syracuseStep 5376785 = 4032589) B4032589
theorem B14338093 : Blo 2237435 14338093 := bstep (se 3 (by rfl) ⟨2688392, by rfl⟩ : syracuseStep 14338093 = 5376785) B5376785
theorem B19117457 : Blo 2237435 19117457 := bstep (se 2 (by rfl) ⟨7169046, by rfl⟩ : syracuseStep 19117457 = 14338093) B14338093
theorem B12744971 : Blo 2237435 12744971 := bstep (se 1 (by rfl) ⟨9558728, by rfl⟩ : syracuseStep 12744971 = 19117457) B19117457
theorem B8496647 : Blo 2237435 8496647 := bstep (se 1 (by rfl) ⟨6372485, by rfl⟩ : syracuseStep 8496647 = 12744971) B12744971
theorem B5664431 : Blo 2237435 5664431 := bstep (se 1 (by rfl) ⟨4248323, by rfl⟩ : syracuseStep 5664431 = 8496647) B8496647
theorem B3776287 : Blo 2237435 3776287 := bstep (se 1 (by rfl) ⟨2832215, by rfl⟩ : syracuseStep 3776287 = 5664431) B5664431
theorem B5035049 : Blo 2237435 5035049 := bstep (se 2 (by rfl) ⟨1888143, by rfl⟩ : syracuseStep 5035049 = 3776287) B3776287
theorem B3356699 : Blo 2237435 3356699 := bstep (se 1 (by rfl) ⟨2517524, by rfl⟩ : syracuseStep 3356699 = 5035049) B5035049
theorem B2237799 : Blo 2237435 2237799 := bstep (se 1 (by rfl) ⟨1678349, by rfl⟩ : syracuseStep 2237799 = 3356699) B3356699
theorem B2517529 : Blo 2237435 2517529 := bbase (se 2 (by rfl) ⟨944073, by rfl⟩ : syracuseStep 2517529 = 1888147) (by norm_num)
theorem B3356705 : Blo 2237435 3356705 := bstep (se 2 (by rfl) ⟨1258764, by rfl⟩ : syracuseStep 3356705 = 2517529) B2517529
theorem B2237803 : Blo 2237435 2237803 := bstep (se 1 (by rfl) ⟨1678352, by rfl⟩ : syracuseStep 2237803 = 3356705) B3356705
theorem B8496677 : Blo 2237435 8496677 := bbase (se 4 (by rfl) ⟨796563, by rfl⟩ : syracuseStep 8496677 = 1593127) (by norm_num)
theorem B5664451 : Blo 2237435 5664451 := bstep (se 1 (by rfl) ⟨4248338, by rfl⟩ : syracuseStep 5664451 = 8496677) B8496677
theorem B7552601 : Blo 2237435 7552601 := bstep (se 2 (by rfl) ⟨2832225, by rfl⟩ : syracuseStep 7552601 = 5664451) B5664451
theorem B5035067 : Blo 2237435 5035067 := bstep (se 1 (by rfl) ⟨3776300, by rfl⟩ : syracuseStep 5035067 = 7552601) B7552601
theorem B3356711 : Blo 2237435 3356711 := bstep (se 1 (by rfl) ⟨2517533, by rfl⟩ : syracuseStep 3356711 = 5035067) B5035067
theorem B2237807 : Blo 2237435 2237807 := bstep (se 1 (by rfl) ⟨1678355, by rfl⟩ : syracuseStep 2237807 = 3356711) B3356711
theorem B3356717 : Blo 2237435 3356717 := bbase (se 3 (by rfl) ⟨629384, by rfl⟩ : syracuseStep 3356717 = 1258769) (by norm_num)
theorem B2237811 : Blo 2237435 2237811 := bstep (se 1 (by rfl) ⟨1678358, by rfl⟩ : syracuseStep 2237811 = 3356717) B3356717
theorem B5035085 : Blo 2237435 5035085 := bbase (se 3 (by rfl) ⟨944078, by rfl⟩ : syracuseStep 5035085 = 1888157) (by norm_num)
theorem B3356723 : Blo 2237435 3356723 := bstep (se 1 (by rfl) ⟨2517542, by rfl⟩ : syracuseStep 3356723 = 5035085) B5035085
theorem B2237815 : Blo 2237435 2237815 := bstep (se 1 (by rfl) ⟨1678361, by rfl⟩ : syracuseStep 2237815 = 3356723) B3356723
theorem B2832241 : Blo 2237435 2832241 := bbase (se 2 (by rfl) ⟨1062090, by rfl⟩ : syracuseStep 2832241 = 2124181) (by norm_num)
theorem B3776321 : Blo 2237435 3776321 := bstep (se 2 (by rfl) ⟨1416120, by rfl⟩ : syracuseStep 3776321 = 2832241) B2832241
theorem B2517547 : Blo 2237435 2517547 := bstep (se 1 (by rfl) ⟨1888160, by rfl⟩ : syracuseStep 2517547 = 3776321) B3776321
theorem B3356729 : Blo 2237435 3356729 := bstep (se 2 (by rfl) ⟨1258773, by rfl⟩ : syracuseStep 3356729 = 2517547) B2517547
theorem B2237819 : Blo 2237435 2237819 := bstep (se 1 (by rfl) ⟨1678364, by rfl⟩ : syracuseStep 2237819 = 3356729) B3356729
theorem B10753685 : Blo 2237435 10753685 := bbase (se 6 (by rfl) ⟨252039, by rfl⟩ : syracuseStep 10753685 = 504079) (by norm_num)
theorem B7169123 : Blo 2237435 7169123 := bstep (se 1 (by rfl) ⟨5376842, by rfl⟩ : syracuseStep 7169123 = 10753685) B10753685
theorem B4779415 : Blo 2237435 4779415 := bstep (se 1 (by rfl) ⟨3584561, by rfl⟩ : syracuseStep 4779415 = 7169123) B7169123
theorem B25490213 : Blo 2237435 25490213 := bstep (se 4 (by rfl) ⟨2389707, by rfl⟩ : syracuseStep 25490213 = 4779415) B4779415
theorem B16993475 : Blo 2237435 16993475 := bstep (se 1 (by rfl) ⟨12745106, by rfl⟩ : syracuseStep 16993475 = 25490213) B25490213
theorem B11328983 : Blo 2237435 11328983 := bstep (se 1 (by rfl) ⟨8496737, by rfl⟩ : syracuseStep 11328983 = 16993475) B16993475
theorem B7552655 : Blo 2237435 7552655 := bstep (se 1 (by rfl) ⟨5664491, by rfl⟩ : syracuseStep 7552655 = 11328983) B11328983
theorem B5035103 : Blo 2237435 5035103 := bstep (se 1 (by rfl) ⟨3776327, by rfl⟩ : syracuseStep 5035103 = 7552655) B7552655
theorem B3356735 : Blo 2237435 3356735 := bstep (se 1 (by rfl) ⟨2517551, by rfl⟩ : syracuseStep 3356735 = 5035103) B5035103
theorem B2237823 : Blo 2237435 2237823 := bstep (se 1 (by rfl) ⟨1678367, by rfl⟩ : syracuseStep 2237823 = 3356735) B3356735
theorem B3356741 : Blo 2237435 3356741 := bbase (se 4 (by rfl) ⟨314694, by rfl⟩ : syracuseStep 3356741 = 629389) (by norm_num)
theorem B2237827 : Blo 2237435 2237827 := bstep (se 1 (by rfl) ⟨1678370, by rfl⟩ : syracuseStep 2237827 = 3356741) B3356741
theorem B3776341 : Blo 2237435 3776341 := bbase (se 9 (by rfl) ⟨11063, by rfl⟩ : syracuseStep 3776341 = 22127) (by norm_num)
theorem B5035121 : Blo 2237435 5035121 := bstep (se 2 (by rfl) ⟨1888170, by rfl⟩ : syracuseStep 5035121 = 3776341) B3776341
theorem B3356747 : Blo 2237435 3356747 := bstep (se 1 (by rfl) ⟨2517560, by rfl⟩ : syracuseStep 3356747 = 5035121) B5035121
theorem B2237831 : Blo 2237435 2237831 := bstep (se 1 (by rfl) ⟨1678373, by rfl⟩ : syracuseStep 2237831 = 3356747) B3356747
theorem B2517565 : Blo 2237435 2517565 := bbase (se 3 (by rfl) ⟨472043, by rfl⟩ : syracuseStep 2517565 = 944087) (by norm_num)
theorem B3356753 : Blo 2237435 3356753 := bstep (se 2 (by rfl) ⟨1258782, by rfl⟩ : syracuseStep 3356753 = 2517565) B2517565
theorem B2237835 : Blo 2237435 2237835 := bstep (se 1 (by rfl) ⟨1678376, by rfl⟩ : syracuseStep 2237835 = 3356753) B3356753
theorem B7552709 : Blo 2237435 7552709 := bbase (se 4 (by rfl) ⟨708066, by rfl⟩ : syracuseStep 7552709 = 1416133) (by norm_num)
theorem B5035139 : Blo 2237435 5035139 := bstep (se 1 (by rfl) ⟨3776354, by rfl⟩ : syracuseStep 5035139 = 7552709) B7552709
theorem B3356759 : Blo 2237435 3356759 := bstep (se 1 (by rfl) ⟨2517569, by rfl⟩ : syracuseStep 3356759 = 5035139) B5035139
theorem B2237839 : Blo 2237435 2237839 := bstep (se 1 (by rfl) ⟨1678379, by rfl⟩ : syracuseStep 2237839 = 3356759) B3356759
theorem B3356765 : Blo 2237435 3356765 := bbase (se 3 (by rfl) ⟨629393, by rfl⟩ : syracuseStep 3356765 = 1258787) (by norm_num)
theorem B2237843 : Blo 2237435 2237843 := bstep (se 1 (by rfl) ⟨1678382, by rfl⟩ : syracuseStep 2237843 = 3356765) B3356765
theorem B5035157 : Blo 2237435 5035157 := bbase (se 6 (by rfl) ⟨118011, by rfl⟩ : syracuseStep 5035157 = 236023) (by norm_num)
theorem B3356771 : Blo 2237435 3356771 := bstep (se 1 (by rfl) ⟨2517578, by rfl⟩ : syracuseStep 3356771 = 5035157) B5035157
theorem B2237847 : Blo 2237435 2237847 := bstep (se 1 (by rfl) ⟨1678385, by rfl⟩ : syracuseStep 2237847 = 3356771) B3356771
theorem B3186317 : Blo 2237435 3186317 := bbase (se 3 (by rfl) ⟨597434, by rfl⟩ : syracuseStep 3186317 = 1194869) (by norm_num)
theorem B8496845 : Blo 2237435 8496845 := bstep (se 3 (by rfl) ⟨1593158, by rfl⟩ : syracuseStep 8496845 = 3186317) B3186317
theorem B5664563 : Blo 2237435 5664563 := bstep (se 1 (by rfl) ⟨4248422, by rfl⟩ : syracuseStep 5664563 = 8496845) B8496845
theorem B3776375 : Blo 2237435 3776375 := bstep (se 1 (by rfl) ⟨2832281, by rfl⟩ : syracuseStep 3776375 = 5664563) B5664563
theorem B2517583 : Blo 2237435 2517583 := bstep (se 1 (by rfl) ⟨1888187, by rfl⟩ : syracuseStep 2517583 = 3776375) B3776375
theorem B3356777 : Blo 2237435 3356777 := bstep (se 2 (by rfl) ⟨1258791, by rfl⟩ : syracuseStep 3356777 = 2517583) B2517583
theorem B2237851 : Blo 2237435 2237851 := bstep (se 1 (by rfl) ⟨1678388, by rfl⟩ : syracuseStep 2237851 = 3356777) B3356777
theorem B12098069 : Blo 2237435 12098069 := bbase (se 6 (by rfl) ⟨283548, by rfl⟩ : syracuseStep 12098069 = 567097) (by norm_num)
theorem B8065379 : Blo 2237435 8065379 := bstep (se 1 (by rfl) ⟨6049034, by rfl⟩ : syracuseStep 8065379 = 12098069) B12098069
theorem B21507677 : Blo 2237435 21507677 := bstep (se 3 (by rfl) ⟨4032689, by rfl⟩ : syracuseStep 21507677 = 8065379) B8065379
theorem B14338451 : Blo 2237435 14338451 := bstep (se 1 (by rfl) ⟨10753838, by rfl⟩ : syracuseStep 14338451 = 21507677) B21507677
theorem B9558967 : Blo 2237435 9558967 := bstep (se 1 (by rfl) ⟨7169225, by rfl⟩ : syracuseStep 9558967 = 14338451) B14338451
theorem B12745289 : Blo 2237435 12745289 := bstep (se 2 (by rfl) ⟨4779483, by rfl⟩ : syracuseStep 12745289 = 9558967) B9558967
theorem B8496859 : Blo 2237435 8496859 := bstep (se 1 (by rfl) ⟨6372644, by rfl⟩ : syracuseStep 8496859 = 12745289) B12745289
theorem B11329145 : Blo 2237435 11329145 := bstep (se 2 (by rfl) ⟨4248429, by rfl⟩ : syracuseStep 11329145 = 8496859) B8496859
theorem B7552763 : Blo 2237435 7552763 := bstep (se 1 (by rfl) ⟨5664572, by rfl⟩ : syracuseStep 7552763 = 11329145) B11329145
theorem B5035175 : Blo 2237435 5035175 := bstep (se 1 (by rfl) ⟨3776381, by rfl⟩ : syracuseStep 5035175 = 7552763) B7552763
theorem B3356783 : Blo 2237435 3356783 := bstep (se 1 (by rfl) ⟨2517587, by rfl⟩ : syracuseStep 3356783 = 5035175) B5035175
theorem B2237855 : Blo 2237435 2237855 := bstep (se 1 (by rfl) ⟨1678391, by rfl⟩ : syracuseStep 2237855 = 3356783) B3356783
theorem B3356789 : Blo 2237435 3356789 := bbase (se 5 (by rfl) ⟨157349, by rfl⟩ : syracuseStep 3356789 = 314699) (by norm_num)
theorem B2237859 : Blo 2237435 2237859 := bstep (se 1 (by rfl) ⟨1678394, by rfl⟩ : syracuseStep 2237859 = 3356789) B3356789
theorem B4248445 : Blo 2237435 4248445 := bbase (se 3 (by rfl) ⟨796583, by rfl⟩ : syracuseStep 4248445 = 1593167) (by norm_num)
theorem B5664593 : Blo 2237435 5664593 := bstep (se 2 (by rfl) ⟨2124222, by rfl⟩ : syracuseStep 5664593 = 4248445) B4248445
theorem B3776395 : Blo 2237435 3776395 := bstep (se 1 (by rfl) ⟨2832296, by rfl⟩ : syracuseStep 3776395 = 5664593) B5664593
theorem B5035193 : Blo 2237435 5035193 := bstep (se 2 (by rfl) ⟨1888197, by rfl⟩ : syracuseStep 5035193 = 3776395) B3776395
theorem B3356795 : Blo 2237435 3356795 := bstep (se 1 (by rfl) ⟨2517596, by rfl⟩ : syracuseStep 3356795 = 5035193) B5035193
theorem B2237863 : Blo 2237435 2237863 := bstep (se 1 (by rfl) ⟨1678397, by rfl⟩ : syracuseStep 2237863 = 3356795) B3356795
theorem B2517601 : Blo 2237435 2517601 := bbase (se 2 (by rfl) ⟨944100, by rfl⟩ : syracuseStep 2517601 = 1888201) (by norm_num)
theorem B3356801 : Blo 2237435 3356801 := bstep (se 2 (by rfl) ⟨1258800, by rfl⟩ : syracuseStep 3356801 = 2517601) B2517601
theorem B2237867 : Blo 2237435 2237867 := bstep (se 1 (by rfl) ⟨1678400, by rfl⟩ : syracuseStep 2237867 = 3356801) B3356801
theorem B5664613 : Blo 2237435 5664613 := bbase (se 4 (by rfl) ⟨531057, by rfl⟩ : syracuseStep 5664613 = 1062115) (by norm_num)
theorem B7552817 : Blo 2237435 7552817 := bstep (se 2 (by rfl) ⟨2832306, by rfl⟩ : syracuseStep 7552817 = 5664613) B5664613
theorem B5035211 : Blo 2237435 5035211 := bstep (se 1 (by rfl) ⟨3776408, by rfl⟩ : syracuseStep 5035211 = 7552817) B7552817
theorem B3356807 : Blo 2237435 3356807 := bstep (se 1 (by rfl) ⟨2517605, by rfl⟩ : syracuseStep 3356807 = 5035211) B5035211
theorem B2237871 : Blo 2237435 2237871 := bstep (se 1 (by rfl) ⟨1678403, by rfl⟩ : syracuseStep 2237871 = 3356807) B3356807
theorem B3356813 : Blo 2237435 3356813 := bbase (se 3 (by rfl) ⟨629402, by rfl⟩ : syracuseStep 3356813 = 1258805) (by norm_num)
theorem B2237875 : Blo 2237435 2237875 := bstep (se 1 (by rfl) ⟨1678406, by rfl⟩ : syracuseStep 2237875 = 3356813) B3356813
theorem B5035229 : Blo 2237435 5035229 := bbase (se 3 (by rfl) ⟨944105, by rfl⟩ : syracuseStep 5035229 = 1888211) (by norm_num)
theorem B3356819 : Blo 2237435 3356819 := bstep (se 1 (by rfl) ⟨2517614, by rfl⟩ : syracuseStep 3356819 = 5035229) B5035229
theorem B2237879 : Blo 2237435 2237879 := bstep (se 1 (by rfl) ⟨1678409, by rfl⟩ : syracuseStep 2237879 = 3356819) B3356819
theorem B3776429 : Blo 2237435 3776429 := bbase (se 3 (by rfl) ⟨708080, by rfl⟩ : syracuseStep 3776429 = 1416161) (by norm_num)
theorem B2517619 : Blo 2237435 2517619 := bstep (se 1 (by rfl) ⟨1888214, by rfl⟩ : syracuseStep 2517619 = 3776429) B3776429
theorem B3356825 : Blo 2237435 3356825 := bstep (se 2 (by rfl) ⟨1258809, by rfl⟩ : syracuseStep 3356825 = 2517619) B2517619
theorem B2237883 : Blo 2237435 2237883 := bstep (se 1 (by rfl) ⟨1678412, by rfl⟩ : syracuseStep 2237883 = 3356825) B3356825
theorem B45935509 : Blo 2237435 45935509 := bbase (se 6 (by rfl) ⟨1076613, by rfl⟩ : syracuseStep 45935509 = 2153227) (by norm_num)
theorem B61247345 : Blo 2237435 61247345 := bstep (se 2 (by rfl) ⟨22967754, by rfl⟩ : syracuseStep 61247345 = 45935509) B45935509
theorem B163326253 : Blo 2237435 163326253 := bstep (se 3 (by rfl) ⟨30623672, by rfl⟩ : syracuseStep 163326253 = 61247345) B61247345
theorem B217768337 : Blo 2237435 217768337 := bstep (se 2 (by rfl) ⟨81663126, by rfl⟩ : syracuseStep 217768337 = 163326253) B163326253
theorem B145178891 : Blo 2237435 145178891 := bstep (se 1 (by rfl) ⟨108884168, by rfl⟩ : syracuseStep 145178891 = 217768337) B217768337
theorem B96785927 : Blo 2237435 96785927 := bstep (se 1 (by rfl) ⟨72589445, by rfl⟩ : syracuseStep 96785927 = 145178891) B145178891
theorem B64523951 : Blo 2237435 64523951 := bstep (se 1 (by rfl) ⟨48392963, by rfl⟩ : syracuseStep 64523951 = 96785927) B96785927
theorem B43015967 : Blo 2237435 43015967 := bstep (se 1 (by rfl) ⟨32261975, by rfl⟩ : syracuseStep 43015967 = 64523951) B64523951
theorem B28677311 : Blo 2237435 28677311 := bstep (se 1 (by rfl) ⟨21507983, by rfl⟩ : syracuseStep 28677311 = 43015967) B43015967
theorem B19118207 : Blo 2237435 19118207 := bstep (se 1 (by rfl) ⟨14338655, by rfl⟩ : syracuseStep 19118207 = 28677311) B28677311
theorem B12745471 : Blo 2237435 12745471 := bstep (se 1 (by rfl) ⟨9559103, by rfl⟩ : syracuseStep 12745471 = 19118207) B19118207
theorem B16993961 : Blo 2237435 16993961 := bstep (se 2 (by rfl) ⟨6372735, by rfl⟩ : syracuseStep 16993961 = 12745471) B12745471
theorem B11329307 : Blo 2237435 11329307 := bstep (se 1 (by rfl) ⟨8496980, by rfl⟩ : syracuseStep 11329307 = 16993961) B16993961
theorem B7552871 : Blo 2237435 7552871 := bstep (se 1 (by rfl) ⟨5664653, by rfl⟩ : syracuseStep 7552871 = 11329307) B11329307
theorem B5035247 : Blo 2237435 5035247 := bstep (se 1 (by rfl) ⟨3776435, by rfl⟩ : syracuseStep 5035247 = 7552871) B7552871
theorem B3356831 : Blo 2237435 3356831 := bstep (se 1 (by rfl) ⟨2517623, by rfl⟩ : syracuseStep 3356831 = 5035247) B5035247
theorem B2237887 : Blo 2237435 2237887 := bstep (se 1 (by rfl) ⟨1678415, by rfl⟩ : syracuseStep 2237887 = 3356831) B3356831
theorem B3356837 : Blo 2237435 3356837 := bbase (se 4 (by rfl) ⟨314703, by rfl⟩ : syracuseStep 3356837 = 629407) (by norm_num)
theorem B2237891 : Blo 2237435 2237891 := bstep (se 1 (by rfl) ⟨1678418, by rfl⟩ : syracuseStep 2237891 = 3356837) B3356837
theorem B2832337 : Blo 2237435 2832337 := bbase (se 2 (by rfl) ⟨1062126, by rfl⟩ : syracuseStep 2832337 = 2124253) (by norm_num)
theorem B3776449 : Blo 2237435 3776449 := bstep (se 2 (by rfl) ⟨1416168, by rfl⟩ : syracuseStep 3776449 = 2832337) B2832337
theorem B5035265 : Blo 2237435 5035265 := bstep (se 2 (by rfl) ⟨1888224, by rfl⟩ : syracuseStep 5035265 = 3776449) B3776449
theorem B3356843 : Blo 2237435 3356843 := bstep (se 1 (by rfl) ⟨2517632, by rfl⟩ : syracuseStep 3356843 = 5035265) B5035265
theorem B2237895 : Blo 2237435 2237895 := bstep (se 1 (by rfl) ⟨1678421, by rfl⟩ : syracuseStep 2237895 = 3356843) B3356843
theorem B2517637 : Blo 2237435 2517637 := bbase (se 4 (by rfl) ⟨236028, by rfl⟩ : syracuseStep 2517637 = 472057) (by norm_num)
theorem B3356849 : Blo 2237435 3356849 := bstep (se 2 (by rfl) ⟨1258818, by rfl⟩ : syracuseStep 3356849 = 2517637) B2517637
theorem B2237899 : Blo 2237435 2237899 := bstep (se 1 (by rfl) ⟨1678424, by rfl⟩ : syracuseStep 2237899 = 3356849) B3356849
theorem B7169381 : Blo 2237435 7169381 := bbase (se 4 (by rfl) ⟨672129, by rfl⟩ : syracuseStep 7169381 = 1344259) (by norm_num)
theorem B4779587 : Blo 2237435 4779587 := bstep (se 1 (by rfl) ⟨3584690, by rfl⟩ : syracuseStep 4779587 = 7169381) B7169381
theorem B3186391 : Blo 2237435 3186391 := bstep (se 1 (by rfl) ⟨2389793, by rfl⟩ : syracuseStep 3186391 = 4779587) B4779587
theorem B4248521 : Blo 2237435 4248521 := bstep (se 2 (by rfl) ⟨1593195, by rfl⟩ : syracuseStep 4248521 = 3186391) B3186391
theorem B2832347 : Blo 2237435 2832347 := bstep (se 1 (by rfl) ⟨2124260, by rfl⟩ : syracuseStep 2832347 = 4248521) B4248521
theorem B7552925 : Blo 2237435 7552925 := bstep (se 3 (by rfl) ⟨1416173, by rfl⟩ : syracuseStep 7552925 = 2832347) B2832347
theorem B5035283 : Blo 2237435 5035283 := bstep (se 1 (by rfl) ⟨3776462, by rfl⟩ : syracuseStep 5035283 = 7552925) B7552925
theorem B3356855 : Blo 2237435 3356855 := bstep (se 1 (by rfl) ⟨2517641, by rfl⟩ : syracuseStep 3356855 = 5035283) B5035283
theorem B2237903 : Blo 2237435 2237903 := bstep (se 1 (by rfl) ⟨1678427, by rfl⟩ : syracuseStep 2237903 = 3356855) B3356855
theorem B3356861 : Blo 2237435 3356861 := bbase (se 3 (by rfl) ⟨629411, by rfl⟩ : syracuseStep 3356861 = 1258823) (by norm_num)
theorem B2237907 : Blo 2237435 2237907 := bstep (se 1 (by rfl) ⟨1678430, by rfl⟩ : syracuseStep 2237907 = 3356861) B3356861
theorem B5035301 : Blo 2237435 5035301 := bbase (se 4 (by rfl) ⟨472059, by rfl⟩ : syracuseStep 5035301 = 944119) (by norm_num)
theorem B3356867 : Blo 2237435 3356867 := bstep (se 1 (by rfl) ⟨2517650, by rfl⟩ : syracuseStep 3356867 = 5035301) B5035301
theorem B2237911 : Blo 2237435 2237911 := bstep (se 1 (by rfl) ⟨1678433, by rfl⟩ : syracuseStep 2237911 = 3356867) B3356867
theorem B5664725 : Blo 2237435 5664725 := bbase (se 7 (by rfl) ⟨66383, by rfl⟩ : syracuseStep 5664725 = 132767) (by norm_num)
theorem B3776483 : Blo 2237435 3776483 := bstep (se 1 (by rfl) ⟨2832362, by rfl⟩ : syracuseStep 3776483 = 5664725) B5664725
theorem B2517655 : Blo 2237435 2517655 := bstep (se 1 (by rfl) ⟨1888241, by rfl⟩ : syracuseStep 2517655 = 3776483) B3776483
theorem B3356873 : Blo 2237435 3356873 := bstep (se 2 (by rfl) ⟨1258827, by rfl⟩ : syracuseStep 3356873 = 2517655) B2517655
theorem B2237915 : Blo 2237435 2237915 := bstep (se 1 (by rfl) ⟨1678436, by rfl⟩ : syracuseStep 2237915 = 3356873) B3356873
theorem B16131221 : Blo 2237435 16131221 := bbase (se 6 (by rfl) ⟨378075, by rfl⟩ : syracuseStep 16131221 = 756151) (by norm_num)
theorem B10754147 : Blo 2237435 10754147 := bstep (se 1 (by rfl) ⟨8065610, by rfl⟩ : syracuseStep 10754147 = 16131221) B16131221
theorem B7169431 : Blo 2237435 7169431 := bstep (se 1 (by rfl) ⟨5377073, by rfl⟩ : syracuseStep 7169431 = 10754147) B10754147
theorem B9559241 : Blo 2237435 9559241 := bstep (se 2 (by rfl) ⟨3584715, by rfl⟩ : syracuseStep 9559241 = 7169431) B7169431
theorem B6372827 : Blo 2237435 6372827 := bstep (se 1 (by rfl) ⟨4779620, by rfl⟩ : syracuseStep 6372827 = 9559241) B9559241
theorem B4248551 : Blo 2237435 4248551 := bstep (se 1 (by rfl) ⟨3186413, by rfl⟩ : syracuseStep 4248551 = 6372827) B6372827
theorem B11329469 : Blo 2237435 11329469 := bstep (se 3 (by rfl) ⟨2124275, by rfl⟩ : syracuseStep 11329469 = 4248551) B4248551
theorem B7552979 : Blo 2237435 7552979 := bstep (se 1 (by rfl) ⟨5664734, by rfl⟩ : syracuseStep 7552979 = 11329469) B11329469
theorem B5035319 : Blo 2237435 5035319 := bstep (se 1 (by rfl) ⟨3776489, by rfl⟩ : syracuseStep 5035319 = 7552979) B7552979
theorem B3356879 : Blo 2237435 3356879 := bstep (se 1 (by rfl) ⟨2517659, by rfl⟩ : syracuseStep 3356879 = 5035319) B5035319
theorem B2237919 : Blo 2237435 2237919 := bstep (se 1 (by rfl) ⟨1678439, by rfl⟩ : syracuseStep 2237919 = 3356879) B3356879
theorem B3356885 : Blo 2237435 3356885 := bbase (se 7 (by rfl) ⟨39338, by rfl⟩ : syracuseStep 3356885 = 78677) (by norm_num)
theorem B2237923 : Blo 2237435 2237923 := bstep (se 1 (by rfl) ⟨1678442, by rfl⟩ : syracuseStep 2237923 = 3356885) B3356885
theorem B4032821 : Blo 2237435 4032821 := bbase (se 5 (by rfl) ⟨189038, by rfl⟩ : syracuseStep 4032821 = 378077) (by norm_num)
theorem B2688547 : Blo 2237435 2688547 := bstep (se 1 (by rfl) ⟨2016410, by rfl⟩ : syracuseStep 2688547 = 4032821) B4032821
theorem B3584729 : Blo 2237435 3584729 := bstep (se 2 (by rfl) ⟨1344273, by rfl⟩ : syracuseStep 3584729 = 2688547) B2688547
theorem B2389819 : Blo 2237435 2389819 := bstep (se 1 (by rfl) ⟨1792364, by rfl⟩ : syracuseStep 2389819 = 3584729) B3584729
theorem B3186425 : Blo 2237435 3186425 := bstep (se 2 (by rfl) ⟨1194909, by rfl⟩ : syracuseStep 3186425 = 2389819) B2389819
theorem B8497133 : Blo 2237435 8497133 := bstep (se 3 (by rfl) ⟨1593212, by rfl⟩ : syracuseStep 8497133 = 3186425) B3186425
theorem B5664755 : Blo 2237435 5664755 := bstep (se 1 (by rfl) ⟨4248566, by rfl⟩ : syracuseStep 5664755 = 8497133) B8497133
theorem B3776503 : Blo 2237435 3776503 := bstep (se 1 (by rfl) ⟨2832377, by rfl⟩ : syracuseStep 3776503 = 5664755) B5664755
theorem B5035337 : Blo 2237435 5035337 := bstep (se 2 (by rfl) ⟨1888251, by rfl⟩ : syracuseStep 5035337 = 3776503) B3776503
theorem B3356891 : Blo 2237435 3356891 := bstep (se 1 (by rfl) ⟨2517668, by rfl⟩ : syracuseStep 3356891 = 5035337) B5035337
theorem B2237927 : Blo 2237435 2237927 := bstep (se 1 (by rfl) ⟨1678445, by rfl⟩ : syracuseStep 2237927 = 3356891) B3356891
theorem B2517673 : Blo 2237435 2517673 := bbase (se 2 (by rfl) ⟨944127, by rfl⟩ : syracuseStep 2517673 = 1888255) (by norm_num)
theorem B3356897 : Blo 2237435 3356897 := bstep (se 2 (by rfl) ⟨1258836, by rfl⟩ : syracuseStep 3356897 = 2517673) B2517673
theorem B2237931 : Blo 2237435 2237931 := bstep (se 1 (by rfl) ⟨1678448, by rfl⟩ : syracuseStep 2237931 = 3356897) B3356897
theorem B3584741 : Blo 2237435 3584741 := bbase (se 4 (by rfl) ⟨336069, by rfl⟩ : syracuseStep 3584741 = 672139) (by norm_num)
theorem B9559309 : Blo 2237435 9559309 := bstep (se 3 (by rfl) ⟨1792370, by rfl⟩ : syracuseStep 9559309 = 3584741) B3584741
theorem B12745745 : Blo 2237435 12745745 := bstep (se 2 (by rfl) ⟨4779654, by rfl⟩ : syracuseStep 12745745 = 9559309) B9559309
theorem B8497163 : Blo 2237435 8497163 := bstep (se 1 (by rfl) ⟨6372872, by rfl⟩ : syracuseStep 8497163 = 12745745) B12745745
theorem B5664775 : Blo 2237435 5664775 := bstep (se 1 (by rfl) ⟨4248581, by rfl⟩ : syracuseStep 5664775 = 8497163) B8497163
theorem B7553033 : Blo 2237435 7553033 := bstep (se 2 (by rfl) ⟨2832387, by rfl⟩ : syracuseStep 7553033 = 5664775) B5664775
theorem B5035355 : Blo 2237435 5035355 := bstep (se 1 (by rfl) ⟨3776516, by rfl⟩ : syracuseStep 5035355 = 7553033) B7553033
theorem B3356903 : Blo 2237435 3356903 := bstep (se 1 (by rfl) ⟨2517677, by rfl⟩ : syracuseStep 3356903 = 5035355) B5035355
theorem B2237935 : Blo 2237435 2237935 := bstep (se 1 (by rfl) ⟨1678451, by rfl⟩ : syracuseStep 2237935 = 3356903) B3356903
theorem B3356909 : Blo 2237435 3356909 := bbase (se 3 (by rfl) ⟨629420, by rfl⟩ : syracuseStep 3356909 = 1258841) (by norm_num)
theorem B2237939 : Blo 2237435 2237939 := bstep (se 1 (by rfl) ⟨1678454, by rfl⟩ : syracuseStep 2237939 = 3356909) B3356909
theorem B5035373 : Blo 2237435 5035373 := bbase (se 3 (by rfl) ⟨944132, by rfl⟩ : syracuseStep 5035373 = 1888265) (by norm_num)
theorem B3356915 : Blo 2237435 3356915 := bstep (se 1 (by rfl) ⟨2517686, by rfl⟩ : syracuseStep 3356915 = 5035373) B5035373
theorem B2237943 : Blo 2237435 2237943 := bstep (se 1 (by rfl) ⟨1678457, by rfl⟩ : syracuseStep 2237943 = 3356915) B3356915
theorem B4248605 : Blo 2237435 4248605 := bbase (se 3 (by rfl) ⟨796613, by rfl⟩ : syracuseStep 4248605 = 1593227) (by norm_num)
theorem B2832403 : Blo 2237435 2832403 := bstep (se 1 (by rfl) ⟨2124302, by rfl⟩ : syracuseStep 2832403 = 4248605) B4248605
theorem B3776537 : Blo 2237435 3776537 := bstep (se 2 (by rfl) ⟨1416201, by rfl⟩ : syracuseStep 3776537 = 2832403) B2832403
theorem B2517691 : Blo 2237435 2517691 := bstep (se 1 (by rfl) ⟨1888268, by rfl⟩ : syracuseStep 2517691 = 3776537) B3776537
theorem B3356921 : Blo 2237435 3356921 := bstep (se 2 (by rfl) ⟨1258845, by rfl⟩ : syracuseStep 3356921 = 2517691) B2517691
theorem B2237947 : Blo 2237435 2237947 := bstep (se 1 (by rfl) ⟨1678460, by rfl⟩ : syracuseStep 2237947 = 3356921) B3356921
theorem B2586865 : Blo 2237435 2586865 := bbase (se 2 (by rfl) ⟨970074, by rfl⟩ : syracuseStep 2586865 = 1940149) (by norm_num)
theorem B3449153 : Blo 2237435 3449153 := bstep (se 2 (by rfl) ⟨1293432, by rfl⟩ : syracuseStep 3449153 = 2586865) B2586865
theorem B2299435 : Blo 2237435 2299435 := bstep (se 1 (by rfl) ⟨1724576, by rfl⟩ : syracuseStep 2299435 = 3449153) B3449153
theorem B12263653 : Blo 2237435 12263653 := bstep (se 4 (by rfl) ⟨1149717, by rfl⟩ : syracuseStep 12263653 = 2299435) B2299435
theorem B65406149 : Blo 2237435 65406149 := bstep (se 4 (by rfl) ⟨6131826, by rfl⟩ : syracuseStep 65406149 = 12263653) B12263653
theorem B43604099 : Blo 2237435 43604099 := bstep (se 1 (by rfl) ⟨32703074, by rfl⟩ : syracuseStep 43604099 = 65406149) B65406149
theorem B29069399 : Blo 2237435 29069399 := bstep (se 1 (by rfl) ⟨21802049, by rfl⟩ : syracuseStep 29069399 = 43604099) B43604099
theorem B77518397 : Blo 2237435 77518397 := bstep (se 3 (by rfl) ⟨14534699, by rfl⟩ : syracuseStep 77518397 = 29069399) B29069399
theorem B51678931 : Blo 2237435 51678931 := bstep (se 1 (by rfl) ⟨38759198, by rfl⟩ : syracuseStep 51678931 = 77518397) B77518397
theorem B68905241 : Blo 2237435 68905241 := bstep (se 2 (by rfl) ⟨25839465, by rfl⟩ : syracuseStep 68905241 = 51678931) B51678931
theorem B45936827 : Blo 2237435 45936827 := bstep (se 1 (by rfl) ⟨34452620, by rfl⟩ : syracuseStep 45936827 = 68905241) B68905241
theorem B30624551 : Blo 2237435 30624551 := bstep (se 1 (by rfl) ⟨22968413, by rfl⟩ : syracuseStep 30624551 = 45936827) B45936827
theorem B20416367 : Blo 2237435 20416367 := bstep (se 1 (by rfl) ⟨15312275, by rfl⟩ : syracuseStep 20416367 = 30624551) B30624551
theorem B13610911 : Blo 2237435 13610911 := bstep (se 1 (by rfl) ⟨10208183, by rfl⟩ : syracuseStep 13610911 = 20416367) B20416367
theorem B18147881 : Blo 2237435 18147881 := bstep (se 2 (by rfl) ⟨6805455, by rfl⟩ : syracuseStep 18147881 = 13610911) B13610911
theorem B12098587 : Blo 2237435 12098587 := bstep (se 1 (by rfl) ⟨9073940, by rfl⟩ : syracuseStep 12098587 = 18147881) B18147881
theorem B16131449 : Blo 2237435 16131449 := bstep (se 2 (by rfl) ⟨6049293, by rfl⟩ : syracuseStep 16131449 = 12098587) B12098587
theorem B10754299 : Blo 2237435 10754299 := bstep (se 1 (by rfl) ⟨8065724, by rfl⟩ : syracuseStep 10754299 = 16131449) B16131449
theorem B57356261 : Blo 2237435 57356261 := bstep (se 4 (by rfl) ⟨5377149, by rfl⟩ : syracuseStep 57356261 = 10754299) B10754299
theorem B38237507 : Blo 2237435 38237507 := bstep (se 1 (by rfl) ⟨28678130, by rfl⟩ : syracuseStep 38237507 = 57356261) B57356261
theorem B25491671 : Blo 2237435 25491671 := bstep (se 1 (by rfl) ⟨19118753, by rfl⟩ : syracuseStep 25491671 = 38237507) B38237507
theorem B16994447 : Blo 2237435 16994447 := bstep (se 1 (by rfl) ⟨12745835, by rfl⟩ : syracuseStep 16994447 = 25491671) B25491671
theorem B11329631 : Blo 2237435 11329631 := bstep (se 1 (by rfl) ⟨8497223, by rfl⟩ : syracuseStep 11329631 = 16994447) B16994447
theorem B7553087 : Blo 2237435 7553087 := bstep (se 1 (by rfl) ⟨5664815, by rfl⟩ : syracuseStep 7553087 = 11329631) B11329631
theorem B5035391 : Blo 2237435 5035391 := bstep (se 1 (by rfl) ⟨3776543, by rfl⟩ : syracuseStep 5035391 = 7553087) B7553087
theorem B3356927 : Blo 2237435 3356927 := bstep (se 1 (by rfl) ⟨2517695, by rfl⟩ : syracuseStep 3356927 = 5035391) B5035391
theorem B2237951 : Blo 2237435 2237951 := bstep (se 1 (by rfl) ⟨1678463, by rfl⟩ : syracuseStep 2237951 = 3356927) B3356927
theorem B3356933 : Blo 2237435 3356933 := bbase (se 4 (by rfl) ⟨314712, by rfl⟩ : syracuseStep 3356933 = 629425) (by norm_num)
theorem B2237955 : Blo 2237435 2237955 := bstep (se 1 (by rfl) ⟨1678466, by rfl⟩ : syracuseStep 2237955 = 3356933) B3356933
theorem B3776557 : Blo 2237435 3776557 := bbase (se 3 (by rfl) ⟨708104, by rfl⟩ : syracuseStep 3776557 = 1416209) (by norm_num)
theorem B5035409 : Blo 2237435 5035409 := bstep (se 2 (by rfl) ⟨1888278, by rfl⟩ : syracuseStep 5035409 = 3776557) B3776557
theorem B3356939 : Blo 2237435 3356939 := bstep (se 1 (by rfl) ⟨2517704, by rfl⟩ : syracuseStep 3356939 = 5035409) B5035409
theorem B2237959 : Blo 2237435 2237959 := bstep (se 1 (by rfl) ⟨1678469, by rfl⟩ : syracuseStep 2237959 = 3356939) B3356939
theorem B2517709 : Blo 2237435 2517709 := bbase (se 3 (by rfl) ⟨472070, by rfl⟩ : syracuseStep 2517709 = 944141) (by norm_num)
theorem B3356945 : Blo 2237435 3356945 := bstep (se 2 (by rfl) ⟨1258854, by rfl⟩ : syracuseStep 3356945 = 2517709) B2517709
theorem B2237963 : Blo 2237435 2237963 := bstep (se 1 (by rfl) ⟨1678472, by rfl⟩ : syracuseStep 2237963 = 3356945) B3356945
theorem B7553141 : Blo 2237435 7553141 := bbase (se 5 (by rfl) ⟨354053, by rfl⟩ : syracuseStep 7553141 = 708107) (by norm_num)
theorem B5035427 : Blo 2237435 5035427 := bstep (se 1 (by rfl) ⟨3776570, by rfl⟩ : syracuseStep 5035427 = 7553141) B7553141
theorem B3356951 : Blo 2237435 3356951 := bstep (se 1 (by rfl) ⟨2517713, by rfl⟩ : syracuseStep 3356951 = 5035427) B5035427
theorem B2237967 : Blo 2237435 2237967 := bstep (se 1 (by rfl) ⟨1678475, by rfl⟩ : syracuseStep 2237967 = 3356951) B3356951
theorem B3356957 : Blo 2237435 3356957 := bbase (se 3 (by rfl) ⟨629429, by rfl⟩ : syracuseStep 3356957 = 1258859) (by norm_num)
theorem B2237971 : Blo 2237435 2237971 := bstep (se 1 (by rfl) ⟨1678478, by rfl⟩ : syracuseStep 2237971 = 3356957) B3356957
theorem B5035445 : Blo 2237435 5035445 := bbase (se 5 (by rfl) ⟨236036, by rfl⟩ : syracuseStep 5035445 = 472073) (by norm_num)
theorem B3356963 : Blo 2237435 3356963 := bstep (se 1 (by rfl) ⟨2517722, by rfl⟩ : syracuseStep 3356963 = 5035445) B5035445
theorem B2237975 : Blo 2237435 2237975 := bstep (se 1 (by rfl) ⟨1678481, by rfl⟩ : syracuseStep 2237975 = 3356963) B3356963
theorem B4779749 : Blo 2237435 4779749 := bbase (se 4 (by rfl) ⟨448101, by rfl⟩ : syracuseStep 4779749 = 896203) (by norm_num)
theorem B12745997 : Blo 2237435 12745997 := bstep (se 3 (by rfl) ⟨2389874, by rfl⟩ : syracuseStep 12745997 = 4779749) B4779749
theorem B8497331 : Blo 2237435 8497331 := bstep (se 1 (by rfl) ⟨6372998, by rfl⟩ : syracuseStep 8497331 = 12745997) B12745997
theorem B5664887 : Blo 2237435 5664887 := bstep (se 1 (by rfl) ⟨4248665, by rfl⟩ : syracuseStep 5664887 = 8497331) B8497331
theorem B3776591 : Blo 2237435 3776591 := bstep (se 1 (by rfl) ⟨2832443, by rfl⟩ : syracuseStep 3776591 = 5664887) B5664887
theorem B2517727 : Blo 2237435 2517727 := bstep (se 1 (by rfl) ⟨1888295, by rfl⟩ : syracuseStep 2517727 = 3776591) B3776591
theorem B3356969 : Blo 2237435 3356969 := bstep (se 2 (by rfl) ⟨1258863, by rfl⟩ : syracuseStep 3356969 = 2517727) B2517727
theorem B2237979 : Blo 2237435 2237979 := bstep (se 1 (by rfl) ⟨1678484, by rfl⟩ : syracuseStep 2237979 = 3356969) B3356969
theorem B4779757 : Blo 2237435 4779757 := bbase (se 3 (by rfl) ⟨896204, by rfl⟩ : syracuseStep 4779757 = 1792409) (by norm_num)
theorem B6373009 : Blo 2237435 6373009 := bstep (se 2 (by rfl) ⟨2389878, by rfl⟩ : syracuseStep 6373009 = 4779757) B4779757
theorem B8497345 : Blo 2237435 8497345 := bstep (se 2 (by rfl) ⟨3186504, by rfl⟩ : syracuseStep 8497345 = 6373009) B6373009
theorem B11329793 : Blo 2237435 11329793 := bstep (se 2 (by rfl) ⟨4248672, by rfl⟩ : syracuseStep 11329793 = 8497345) B8497345
theorem B7553195 : Blo 2237435 7553195 := bstep (se 1 (by rfl) ⟨5664896, by rfl⟩ : syracuseStep 7553195 = 11329793) B11329793
theorem B5035463 : Blo 2237435 5035463 := bstep (se 1 (by rfl) ⟨3776597, by rfl⟩ : syracuseStep 5035463 = 7553195) B7553195
theorem B3356975 : Blo 2237435 3356975 := bstep (se 1 (by rfl) ⟨2517731, by rfl⟩ : syracuseStep 3356975 = 5035463) B5035463
theorem B2237983 : Blo 2237435 2237983 := bstep (se 1 (by rfl) ⟨1678487, by rfl⟩ : syracuseStep 2237983 = 3356975) B3356975
theorem B3356981 : Blo 2237435 3356981 := bbase (se 5 (by rfl) ⟨157358, by rfl⟩ : syracuseStep 3356981 = 314717) (by norm_num)
theorem B2237987 : Blo 2237435 2237987 := bstep (se 1 (by rfl) ⟨1678490, by rfl⟩ : syracuseStep 2237987 = 3356981) B3356981
theorem B5664917 : Blo 2237435 5664917 := bbase (se 6 (by rfl) ⟨132771, by rfl⟩ : syracuseStep 5664917 = 265543) (by norm_num)
theorem B3776611 : Blo 2237435 3776611 := bstep (se 1 (by rfl) ⟨2832458, by rfl⟩ : syracuseStep 3776611 = 5664917) B5664917
theorem B5035481 : Blo 2237435 5035481 := bstep (se 2 (by rfl) ⟨1888305, by rfl⟩ : syracuseStep 5035481 = 3776611) B3776611
theorem B3356987 : Blo 2237435 3356987 := bstep (se 1 (by rfl) ⟨2517740, by rfl⟩ : syracuseStep 3356987 = 5035481) B5035481
theorem B2237991 : Blo 2237435 2237991 := bstep (se 1 (by rfl) ⟨1678493, by rfl⟩ : syracuseStep 2237991 = 3356987) B3356987
theorem B2517745 : Blo 2237435 2517745 := bbase (se 2 (by rfl) ⟨944154, by rfl⟩ : syracuseStep 2517745 = 1888309) (by norm_num)
theorem B3356993 : Blo 2237435 3356993 := bstep (se 2 (by rfl) ⟨1258872, by rfl⟩ : syracuseStep 3356993 = 2517745) B2517745
theorem B2237995 : Blo 2237435 2237995 := bstep (se 1 (by rfl) ⟨1678496, by rfl⟩ : syracuseStep 2237995 = 3356993) B3356993
theorem B4087973 : Blo 2237435 4087973 := bbase (se 4 (by rfl) ⟨383247, by rfl⟩ : syracuseStep 4087973 = 766495) (by norm_num)
theorem B2725315 : Blo 2237435 2725315 := bstep (se 1 (by rfl) ⟨2043986, by rfl⟩ : syracuseStep 2725315 = 4087973) B4087973
theorem B14535013 : Blo 2237435 14535013 := bstep (se 4 (by rfl) ⟨1362657, by rfl⟩ : syracuseStep 14535013 = 2725315) B2725315
theorem B19380017 : Blo 2237435 19380017 := bstep (se 2 (by rfl) ⟨7267506, by rfl⟩ : syracuseStep 19380017 = 14535013) B14535013
theorem B51680045 : Blo 2237435 51680045 := bstep (se 3 (by rfl) ⟨9690008, by rfl⟩ : syracuseStep 51680045 = 19380017) B19380017
theorem B34453363 : Blo 2237435 34453363 := bstep (se 1 (by rfl) ⟨25840022, by rfl⟩ : syracuseStep 34453363 = 51680045) B51680045
theorem B45937817 : Blo 2237435 45937817 := bstep (se 2 (by rfl) ⟨17226681, by rfl⟩ : syracuseStep 45937817 = 34453363) B34453363
theorem B30625211 : Blo 2237435 30625211 := bstep (se 1 (by rfl) ⟨22968908, by rfl⟩ : syracuseStep 30625211 = 45937817) B45937817
theorem B20416807 : Blo 2237435 20416807 := bstep (se 1 (by rfl) ⟨15312605, by rfl⟩ : syracuseStep 20416807 = 30625211) B30625211
theorem B27222409 : Blo 2237435 27222409 := bstep (se 2 (by rfl) ⟨10208403, by rfl⟩ : syracuseStep 27222409 = 20416807) B20416807
theorem B36296545 : Blo 2237435 36296545 := bstep (se 2 (by rfl) ⟨13611204, by rfl⟩ : syracuseStep 36296545 = 27222409) B27222409
theorem B48395393 : Blo 2237435 48395393 := bstep (se 2 (by rfl) ⟨18148272, by rfl⟩ : syracuseStep 48395393 = 36296545) B36296545
theorem B32263595 : Blo 2237435 32263595 := bstep (se 1 (by rfl) ⟨24197696, by rfl⟩ : syracuseStep 32263595 = 48395393) B48395393
theorem B21509063 : Blo 2237435 21509063 := bstep (se 1 (by rfl) ⟨16131797, by rfl⟩ : syracuseStep 21509063 = 32263595) B32263595
theorem B14339375 : Blo 2237435 14339375 := bstep (se 1 (by rfl) ⟨10754531, by rfl⟩ : syracuseStep 14339375 = 21509063) B21509063
theorem B9559583 : Blo 2237435 9559583 := bstep (se 1 (by rfl) ⟨7169687, by rfl⟩ : syracuseStep 9559583 = 14339375) B14339375
theorem B6373055 : Blo 2237435 6373055 := bstep (se 1 (by rfl) ⟨4779791, by rfl⟩ : syracuseStep 6373055 = 9559583) B9559583
theorem B4248703 : Blo 2237435 4248703 := bstep (se 1 (by rfl) ⟨3186527, by rfl⟩ : syracuseStep 4248703 = 6373055) B6373055
theorem B5664937 : Blo 2237435 5664937 := bstep (se 2 (by rfl) ⟨2124351, by rfl⟩ : syracuseStep 5664937 = 4248703) B4248703
theorem B7553249 : Blo 2237435 7553249 := bstep (se 2 (by rfl) ⟨2832468, by rfl⟩ : syracuseStep 7553249 = 5664937) B5664937
theorem B5035499 : Blo 2237435 5035499 := bstep (se 1 (by rfl) ⟨3776624, by rfl⟩ : syracuseStep 5035499 = 7553249) B7553249
theorem B3356999 : Blo 2237435 3356999 := bstep (se 1 (by rfl) ⟨2517749, by rfl⟩ : syracuseStep 3356999 = 5035499) B5035499
theorem B2237999 : Blo 2237435 2237999 := bstep (se 1 (by rfl) ⟨1678499, by rfl⟩ : syracuseStep 2237999 = 3356999) B3356999
theorem B3357005 : Blo 2237435 3357005 := bbase (se 3 (by rfl) ⟨629438, by rfl⟩ : syracuseStep 3357005 = 1258877) (by norm_num)
theorem B2238003 : Blo 2237435 2238003 := bstep (se 1 (by rfl) ⟨1678502, by rfl⟩ : syracuseStep 2238003 = 3357005) B3357005
theorem B5035517 : Blo 2237435 5035517 := bbase (se 3 (by rfl) ⟨944159, by rfl⟩ : syracuseStep 5035517 = 1888319) (by norm_num)
theorem B3357011 : Blo 2237435 3357011 := bstep (se 1 (by rfl) ⟨2517758, by rfl⟩ : syracuseStep 3357011 = 5035517) B5035517
theorem B2238007 : Blo 2237435 2238007 := bstep (se 1 (by rfl) ⟨1678505, by rfl⟩ : syracuseStep 2238007 = 3357011) B3357011
theorem B3776645 : Blo 2237435 3776645 := bbase (se 4 (by rfl) ⟨354060, by rfl⟩ : syracuseStep 3776645 = 708121) (by norm_num)
theorem B2517763 : Blo 2237435 2517763 := bstep (se 1 (by rfl) ⟨1888322, by rfl⟩ : syracuseStep 2517763 = 3776645) B3776645
theorem B3357017 : Blo 2237435 3357017 := bstep (se 2 (by rfl) ⟨1258881, by rfl⟩ : syracuseStep 3357017 = 2517763) B2517763
theorem B2238011 : Blo 2237435 2238011 := bstep (se 1 (by rfl) ⟨1678508, by rfl⟩ : syracuseStep 2238011 = 3357017) B3357017
theorem B16994933 : Blo 2237435 16994933 := bbase (se 5 (by rfl) ⟨796637, by rfl⟩ : syracuseStep 16994933 = 1593275) (by norm_num)
theorem B11329955 : Blo 2237435 11329955 := bstep (se 1 (by rfl) ⟨8497466, by rfl⟩ : syracuseStep 11329955 = 16994933) B16994933
theorem B7553303 : Blo 2237435 7553303 := bstep (se 1 (by rfl) ⟨5664977, by rfl⟩ : syracuseStep 7553303 = 11329955) B11329955
theorem B5035535 : Blo 2237435 5035535 := bstep (se 1 (by rfl) ⟨3776651, by rfl⟩ : syracuseStep 5035535 = 7553303) B7553303
theorem B3357023 : Blo 2237435 3357023 := bstep (se 1 (by rfl) ⟨2517767, by rfl⟩ : syracuseStep 3357023 = 5035535) B5035535
theorem B2238015 : Blo 2237435 2238015 := bstep (se 1 (by rfl) ⟨1678511, by rfl⟩ : syracuseStep 2238015 = 3357023) B3357023
theorem B3357029 : Blo 2237435 3357029 := bbase (se 4 (by rfl) ⟨314721, by rfl⟩ : syracuseStep 3357029 = 629443) (by norm_num)
theorem B2238019 : Blo 2237435 2238019 := bstep (se 1 (by rfl) ⟨1678514, by rfl⟩ : syracuseStep 2238019 = 3357029) B3357029
theorem B4248749 : Blo 2237435 4248749 := bbase (se 3 (by rfl) ⟨796640, by rfl⟩ : syracuseStep 4248749 = 1593281) (by norm_num)
theorem B2832499 : Blo 2237435 2832499 := bstep (se 1 (by rfl) ⟨2124374, by rfl⟩ : syracuseStep 2832499 = 4248749) B4248749
theorem B3776665 : Blo 2237435 3776665 := bstep (se 2 (by rfl) ⟨1416249, by rfl⟩ : syracuseStep 3776665 = 2832499) B2832499
theorem B5035553 : Blo 2237435 5035553 := bstep (se 2 (by rfl) ⟨1888332, by rfl⟩ : syracuseStep 5035553 = 3776665) B3776665
theorem B3357035 : Blo 2237435 3357035 := bstep (se 1 (by rfl) ⟨2517776, by rfl⟩ : syracuseStep 3357035 = 5035553) B5035553
theorem B2238023 : Blo 2237435 2238023 := bstep (se 1 (by rfl) ⟨1678517, by rfl⟩ : syracuseStep 2238023 = 3357035) B3357035
theorem B2517781 : Blo 2237435 2517781 := bbase (se 6 (by rfl) ⟨59010, by rfl⟩ : syracuseStep 2517781 = 118021) (by norm_num)
theorem B3357041 : Blo 2237435 3357041 := bstep (se 2 (by rfl) ⟨1258890, by rfl⟩ : syracuseStep 3357041 = 2517781) B2517781
theorem B2238027 : Blo 2237435 2238027 := bstep (se 1 (by rfl) ⟨1678520, by rfl⟩ : syracuseStep 2238027 = 3357041) B3357041
theorem B2832509 : Blo 2237435 2832509 := bbase (se 3 (by rfl) ⟨531095, by rfl⟩ : syracuseStep 2832509 = 1062191) (by norm_num)
theorem B7553357 : Blo 2237435 7553357 := bstep (se 3 (by rfl) ⟨1416254, by rfl⟩ : syracuseStep 7553357 = 2832509) B2832509
theorem B5035571 : Blo 2237435 5035571 := bstep (se 1 (by rfl) ⟨3776678, by rfl⟩ : syracuseStep 5035571 = 7553357) B7553357
theorem B3357047 : Blo 2237435 3357047 := bstep (se 1 (by rfl) ⟨2517785, by rfl⟩ : syracuseStep 3357047 = 5035571) B5035571
theorem B2238031 : Blo 2237435 2238031 := bstep (se 1 (by rfl) ⟨1678523, by rfl⟩ : syracuseStep 2238031 = 3357047) B3357047
theorem B3357053 : Blo 2237435 3357053 := bbase (se 3 (by rfl) ⟨629447, by rfl⟩ : syracuseStep 3357053 = 1258895) (by norm_num)
theorem B2238035 : Blo 2237435 2238035 := bstep (se 1 (by rfl) ⟨1678526, by rfl⟩ : syracuseStep 2238035 = 3357053) B3357053
theorem B5035589 : Blo 2237435 5035589 := bbase (se 4 (by rfl) ⟨472086, by rfl⟩ : syracuseStep 5035589 = 944173) (by norm_num)
theorem B3357059 : Blo 2237435 3357059 := bstep (se 1 (by rfl) ⟨2517794, by rfl⟩ : syracuseStep 3357059 = 5035589) B5035589
theorem B2238039 : Blo 2237435 2238039 := bstep (se 1 (by rfl) ⟨1678529, by rfl⟩ : syracuseStep 2238039 = 3357059) B3357059
theorem B5377373 : Blo 2237435 5377373 := bbase (se 3 (by rfl) ⟨1008257, by rfl⟩ : syracuseStep 5377373 = 2016515) (by norm_num)
theorem B3584915 : Blo 2237435 3584915 := bstep (se 1 (by rfl) ⟨2688686, by rfl⟩ : syracuseStep 3584915 = 5377373) B5377373
theorem B2389943 : Blo 2237435 2389943 := bstep (se 1 (by rfl) ⟨1792457, by rfl⟩ : syracuseStep 2389943 = 3584915) B3584915
theorem B6373181 : Blo 2237435 6373181 := bstep (se 3 (by rfl) ⟨1194971, by rfl⟩ : syracuseStep 6373181 = 2389943) B2389943
theorem B4248787 : Blo 2237435 4248787 := bstep (se 1 (by rfl) ⟨3186590, by rfl⟩ : syracuseStep 4248787 = 6373181) B6373181
theorem B5665049 : Blo 2237435 5665049 := bstep (se 2 (by rfl) ⟨2124393, by rfl⟩ : syracuseStep 5665049 = 4248787) B4248787
theorem B3776699 : Blo 2237435 3776699 := bstep (se 1 (by rfl) ⟨2832524, by rfl⟩ : syracuseStep 3776699 = 5665049) B5665049
theorem B2517799 : Blo 2237435 2517799 := bstep (se 1 (by rfl) ⟨1888349, by rfl⟩ : syracuseStep 2517799 = 3776699) B3776699
theorem B3357065 : Blo 2237435 3357065 := bstep (se 2 (by rfl) ⟨1258899, by rfl⟩ : syracuseStep 3357065 = 2517799) B2517799
theorem B2238043 : Blo 2237435 2238043 := bstep (se 1 (by rfl) ⟨1678532, by rfl⟩ : syracuseStep 2238043 = 3357065) B3357065
theorem B11330117 : Blo 2237435 11330117 := bbase (se 4 (by rfl) ⟨1062198, by rfl⟩ : syracuseStep 11330117 = 2124397) (by norm_num)
theorem B7553411 : Blo 2237435 7553411 := bstep (se 1 (by rfl) ⟨5665058, by rfl⟩ : syracuseStep 7553411 = 11330117) B11330117
theorem B5035607 : Blo 2237435 5035607 := bstep (se 1 (by rfl) ⟨3776705, by rfl⟩ : syracuseStep 5035607 = 7553411) B7553411
theorem B3357071 : Blo 2237435 3357071 := bstep (se 1 (by rfl) ⟨2517803, by rfl⟩ : syracuseStep 3357071 = 5035607) B5035607
theorem B2238047 : Blo 2237435 2238047 := bstep (se 1 (by rfl) ⟨1678535, by rfl⟩ : syracuseStep 2238047 = 3357071) B3357071
theorem B3357077 : Blo 2237435 3357077 := bbase (se 6 (by rfl) ⟨78681, by rfl⟩ : syracuseStep 3357077 = 157363) (by norm_num)
theorem B2238051 : Blo 2237435 2238051 := bstep (se 1 (by rfl) ⟨1678538, by rfl⟩ : syracuseStep 2238051 = 3357077) B3357077
theorem B8066101 : Blo 2237435 8066101 := bbase (se 5 (by rfl) ⟨378098, by rfl⟩ : syracuseStep 8066101 = 756197) (by norm_num)
theorem B10754801 : Blo 2237435 10754801 := bstep (se 2 (by rfl) ⟨4033050, by rfl⟩ : syracuseStep 10754801 = 8066101) B8066101
theorem B7169867 : Blo 2237435 7169867 := bstep (se 1 (by rfl) ⟨5377400, by rfl⟩ : syracuseStep 7169867 = 10754801) B10754801
theorem B4779911 : Blo 2237435 4779911 := bstep (se 1 (by rfl) ⟨3584933, by rfl⟩ : syracuseStep 4779911 = 7169867) B7169867
theorem B12746429 : Blo 2237435 12746429 := bstep (se 3 (by rfl) ⟨2389955, by rfl⟩ : syracuseStep 12746429 = 4779911) B4779911
theorem B8497619 : Blo 2237435 8497619 := bstep (se 1 (by rfl) ⟨6373214, by rfl⟩ : syracuseStep 8497619 = 12746429) B12746429
theorem B5665079 : Blo 2237435 5665079 := bstep (se 1 (by rfl) ⟨4248809, by rfl⟩ : syracuseStep 5665079 = 8497619) B8497619
theorem B3776719 : Blo 2237435 3776719 := bstep (se 1 (by rfl) ⟨2832539, by rfl⟩ : syracuseStep 3776719 = 5665079) B5665079
theorem B5035625 : Blo 2237435 5035625 := bstep (se 2 (by rfl) ⟨1888359, by rfl⟩ : syracuseStep 5035625 = 3776719) B3776719
theorem B3357083 : Blo 2237435 3357083 := bstep (se 1 (by rfl) ⟨2517812, by rfl⟩ : syracuseStep 3357083 = 5035625) B5035625
theorem B2238055 : Blo 2237435 2238055 := bstep (se 1 (by rfl) ⟨1678541, by rfl⟩ : syracuseStep 2238055 = 3357083) B3357083
theorem B2517817 : Blo 2237435 2517817 := bbase (se 2 (by rfl) ⟨944181, by rfl⟩ : syracuseStep 2517817 = 1888363) (by norm_num)
theorem B3357089 : Blo 2237435 3357089 := bstep (se 2 (by rfl) ⟨1258908, by rfl⟩ : syracuseStep 3357089 = 2517817) B2517817
theorem B2238059 : Blo 2237435 2238059 := bstep (se 1 (by rfl) ⟨1678544, by rfl⟩ : syracuseStep 2238059 = 3357089) B3357089
theorem B6373237 : Blo 2237435 6373237 := bbase (se 5 (by rfl) ⟨298745, by rfl⟩ : syracuseStep 6373237 = 597491) (by norm_num)
theorem B8497649 : Blo 2237435 8497649 := bstep (se 2 (by rfl) ⟨3186618, by rfl⟩ : syracuseStep 8497649 = 6373237) B6373237
theorem B5665099 : Blo 2237435 5665099 := bstep (se 1 (by rfl) ⟨4248824, by rfl⟩ : syracuseStep 5665099 = 8497649) B8497649
theorem B7553465 : Blo 2237435 7553465 := bstep (se 2 (by rfl) ⟨2832549, by rfl⟩ : syracuseStep 7553465 = 5665099) B5665099
theorem B5035643 : Blo 2237435 5035643 := bstep (se 1 (by rfl) ⟨3776732, by rfl⟩ : syracuseStep 5035643 = 7553465) B7553465
theorem B3357095 : Blo 2237435 3357095 := bstep (se 1 (by rfl) ⟨2517821, by rfl⟩ : syracuseStep 3357095 = 5035643) B5035643
theorem B2238063 : Blo 2237435 2238063 := bstep (se 1 (by rfl) ⟨1678547, by rfl⟩ : syracuseStep 2238063 = 3357095) B3357095
theorem B3357101 : Blo 2237435 3357101 := bbase (se 3 (by rfl) ⟨629456, by rfl⟩ : syracuseStep 3357101 = 1258913) (by norm_num)
theorem B2238067 : Blo 2237435 2238067 := bstep (se 1 (by rfl) ⟨1678550, by rfl⟩ : syracuseStep 2238067 = 3357101) B3357101
theorem B5035661 : Blo 2237435 5035661 := bbase (se 3 (by rfl) ⟨944186, by rfl⟩ : syracuseStep 5035661 = 1888373) (by norm_num)
theorem B3357107 : Blo 2237435 3357107 := bstep (se 1 (by rfl) ⟨2517830, by rfl⟩ : syracuseStep 3357107 = 5035661) B5035661
theorem B2238071 : Blo 2237435 2238071 := bstep (se 1 (by rfl) ⟨1678553, by rfl⟩ : syracuseStep 2238071 = 3357107) B3357107
theorem B2832565 : Blo 2237435 2832565 := bbase (se 5 (by rfl) ⟨132776, by rfl⟩ : syracuseStep 2832565 = 265553) (by norm_num)
theorem B3776753 : Blo 2237435 3776753 := bstep (se 2 (by rfl) ⟨1416282, by rfl⟩ : syracuseStep 3776753 = 2832565) B2832565
theorem B2517835 : Blo 2237435 2517835 := bstep (se 1 (by rfl) ⟨1888376, by rfl⟩ : syracuseStep 2517835 = 3776753) B3776753
theorem B3357113 : Blo 2237435 3357113 := bstep (se 2 (by rfl) ⟨1258917, by rfl⟩ : syracuseStep 3357113 = 2517835) B2517835
theorem B2238075 : Blo 2237435 2238075 := bstep (se 1 (by rfl) ⟨1678556, by rfl⟩ : syracuseStep 2238075 = 3357113) B3357113
theorem B6637717 : Blo 2237435 6637717 := bbase (se 6 (by rfl) ⟨155571, by rfl⟩ : syracuseStep 6637717 = 311143) (by norm_num)
theorem B35401157 : Blo 2237435 35401157 := bstep (se 4 (by rfl) ⟨3318858, by rfl⟩ : syracuseStep 35401157 = 6637717) B6637717
theorem B23600771 : Blo 2237435 23600771 := bstep (se 1 (by rfl) ⟨17700578, by rfl⟩ : syracuseStep 23600771 = 35401157) B35401157
theorem B15733847 : Blo 2237435 15733847 := bstep (se 1 (by rfl) ⟨11800385, by rfl⟩ : syracuseStep 15733847 = 23600771) B23600771
theorem B10489231 : Blo 2237435 10489231 := bstep (se 1 (by rfl) ⟨7866923, by rfl⟩ : syracuseStep 10489231 = 15733847) B15733847
theorem B13985641 : Blo 2237435 13985641 := bstep (se 2 (by rfl) ⟨5244615, by rfl⟩ : syracuseStep 13985641 = 10489231) B10489231
theorem B18647521 : Blo 2237435 18647521 := bstep (se 2 (by rfl) ⟨6992820, by rfl⟩ : syracuseStep 18647521 = 13985641) B13985641
theorem B397813781 : Blo 2237435 397813781 := bstep (se 6 (by rfl) ⟨9323760, by rfl⟩ : syracuseStep 397813781 = 18647521) B18647521
theorem B265209187 : Blo 2237435 265209187 := bstep (se 1 (by rfl) ⟨198906890, by rfl⟩ : syracuseStep 265209187 = 397813781) B397813781
theorem B353612249 : Blo 2237435 353612249 := bstep (se 2 (by rfl) ⟨132604593, by rfl⟩ : syracuseStep 353612249 = 265209187) B265209187
theorem B235741499 : Blo 2237435 235741499 := bstep (se 1 (by rfl) ⟨176806124, by rfl⟩ : syracuseStep 235741499 = 353612249) B353612249
theorem B157160999 : Blo 2237435 157160999 := bstep (se 1 (by rfl) ⟨117870749, by rfl⟩ : syracuseStep 157160999 = 235741499) B235741499
theorem B104773999 : Blo 2237435 104773999 := bstep (se 1 (by rfl) ⟨78580499, by rfl⟩ : syracuseStep 104773999 = 157160999) B157160999
theorem B139698665 : Blo 2237435 139698665 := bstep (se 2 (by rfl) ⟨52386999, by rfl⟩ : syracuseStep 139698665 = 104773999) B104773999
theorem B93132443 : Blo 2237435 93132443 := bstep (se 1 (by rfl) ⟨69849332, by rfl⟩ : syracuseStep 93132443 = 139698665) B139698665
theorem B62088295 : Blo 2237435 62088295 := bstep (se 1 (by rfl) ⟨46566221, by rfl⟩ : syracuseStep 62088295 = 93132443) B93132443
theorem B82784393 : Blo 2237435 82784393 := bstep (se 2 (by rfl) ⟨31044147, by rfl⟩ : syracuseStep 82784393 = 62088295) B62088295
theorem B55189595 : Blo 2237435 55189595 := bstep (se 1 (by rfl) ⟨41392196, by rfl⟩ : syracuseStep 55189595 = 82784393) B82784393
theorem B36793063 : Blo 2237435 36793063 := bstep (se 1 (by rfl) ⟨27594797, by rfl⟩ : syracuseStep 36793063 = 55189595) B55189595
theorem B49057417 : Blo 2237435 49057417 := bstep (se 2 (by rfl) ⟨18396531, by rfl⟩ : syracuseStep 49057417 = 36793063) B36793063
theorem B65409889 : Blo 2237435 65409889 := bstep (se 2 (by rfl) ⟨24528708, by rfl⟩ : syracuseStep 65409889 = 49057417) B49057417
theorem B87213185 : Blo 2237435 87213185 := bstep (se 2 (by rfl) ⟨32704944, by rfl⟩ : syracuseStep 87213185 = 65409889) B65409889
theorem B58142123 : Blo 2237435 58142123 := bstep (se 1 (by rfl) ⟨43606592, by rfl⟩ : syracuseStep 58142123 = 87213185) B87213185
theorem B38761415 : Blo 2237435 38761415 := bstep (se 1 (by rfl) ⟨29071061, by rfl⟩ : syracuseStep 38761415 = 58142123) B58142123
theorem B25840943 : Blo 2237435 25840943 := bstep (se 1 (by rfl) ⟨19380707, by rfl⟩ : syracuseStep 25840943 = 38761415) B38761415
theorem B17227295 : Blo 2237435 17227295 := bstep (se 1 (by rfl) ⟨12920471, by rfl⟩ : syracuseStep 17227295 = 25840943) B25840943
theorem B11484863 : Blo 2237435 11484863 := bstep (se 1 (by rfl) ⟨8613647, by rfl⟩ : syracuseStep 11484863 = 17227295) B17227295
theorem B7656575 : Blo 2237435 7656575 := bstep (se 1 (by rfl) ⟨5742431, by rfl⟩ : syracuseStep 7656575 = 11484863) B11484863
theorem B81670133 : Blo 2237435 81670133 := bstep (se 5 (by rfl) ⟨3828287, by rfl⟩ : syracuseStep 81670133 = 7656575) B7656575
theorem B54446755 : Blo 2237435 54446755 := bstep (se 1 (by rfl) ⟨40835066, by rfl⟩ : syracuseStep 54446755 = 81670133) B81670133
theorem B72595673 : Blo 2237435 72595673 := bstep (se 2 (by rfl) ⟨27223377, by rfl⟩ : syracuseStep 72595673 = 54446755) B54446755
theorem B48397115 : Blo 2237435 48397115 := bstep (se 1 (by rfl) ⟨36297836, by rfl⟩ : syracuseStep 48397115 = 72595673) B72595673
theorem B32264743 : Blo 2237435 32264743 := bstep (se 1 (by rfl) ⟨24198557, by rfl⟩ : syracuseStep 32264743 = 48397115) B48397115
theorem B43019657 : Blo 2237435 43019657 := bstep (se 2 (by rfl) ⟨16132371, by rfl⟩ : syracuseStep 43019657 = 32264743) B32264743
theorem B28679771 : Blo 2237435 28679771 := bstep (se 1 (by rfl) ⟨21509828, by rfl⟩ : syracuseStep 28679771 = 43019657) B43019657
theorem B19119847 : Blo 2237435 19119847 := bstep (se 1 (by rfl) ⟨14339885, by rfl⟩ : syracuseStep 19119847 = 28679771) B28679771
theorem B25493129 : Blo 2237435 25493129 := bstep (se 2 (by rfl) ⟨9559923, by rfl⟩ : syracuseStep 25493129 = 19119847) B19119847
theorem B16995419 : Blo 2237435 16995419 := bstep (se 1 (by rfl) ⟨12746564, by rfl⟩ : syracuseStep 16995419 = 25493129) B25493129
theorem B11330279 : Blo 2237435 11330279 := bstep (se 1 (by rfl) ⟨8497709, by rfl⟩ : syracuseStep 11330279 = 16995419) B16995419
theorem B7553519 : Blo 2237435 7553519 := bstep (se 1 (by rfl) ⟨5665139, by rfl⟩ : syracuseStep 7553519 = 11330279) B11330279
theorem B5035679 : Blo 2237435 5035679 := bstep (se 1 (by rfl) ⟨3776759, by rfl⟩ : syracuseStep 5035679 = 7553519) B7553519
theorem B3357119 : Blo 2237435 3357119 := bstep (se 1 (by rfl) ⟨2517839, by rfl⟩ : syracuseStep 3357119 = 5035679) B5035679
theorem B2238079 : Blo 2237435 2238079 := bstep (se 1 (by rfl) ⟨1678559, by rfl⟩ : syracuseStep 2238079 = 3357119) B3357119
theorem B3357125 : Blo 2237435 3357125 := bbase (se 4 (by rfl) ⟨314730, by rfl⟩ : syracuseStep 3357125 = 629461) (by norm_num)
theorem B2238083 : Blo 2237435 2238083 := bstep (se 1 (by rfl) ⟨1678562, by rfl⟩ : syracuseStep 2238083 = 3357125) B3357125
theorem B3776773 : Blo 2237435 3776773 := bbase (se 4 (by rfl) ⟨354072, by rfl⟩ : syracuseStep 3776773 = 708145) (by norm_num)
theorem B5035697 : Blo 2237435 5035697 := bstep (se 2 (by rfl) ⟨1888386, by rfl⟩ : syracuseStep 5035697 = 3776773) B3776773
theorem B3357131 : Blo 2237435 3357131 := bstep (se 1 (by rfl) ⟨2517848, by rfl⟩ : syracuseStep 3357131 = 5035697) B5035697
theorem B2238087 : Blo 2237435 2238087 := bstep (se 1 (by rfl) ⟨1678565, by rfl⟩ : syracuseStep 2238087 = 3357131) B3357131
theorem B2517853 : Blo 2237435 2517853 := bbase (se 3 (by rfl) ⟨472097, by rfl⟩ : syracuseStep 2517853 = 944195) (by norm_num)
theorem B3357137 : Blo 2237435 3357137 := bstep (se 2 (by rfl) ⟨1258926, by rfl⟩ : syracuseStep 3357137 = 2517853) B2517853
theorem B2238091 : Blo 2237435 2238091 := bstep (se 1 (by rfl) ⟨1678568, by rfl⟩ : syracuseStep 2238091 = 3357137) B3357137
theorem B7553573 : Blo 2237435 7553573 := bbase (se 4 (by rfl) ⟨708147, by rfl⟩ : syracuseStep 7553573 = 1416295) (by norm_num)
theorem B5035715 : Blo 2237435 5035715 := bstep (se 1 (by rfl) ⟨3776786, by rfl⟩ : syracuseStep 5035715 = 7553573) B7553573
theorem B3357143 : Blo 2237435 3357143 := bstep (se 1 (by rfl) ⟨2517857, by rfl⟩ : syracuseStep 3357143 = 5035715) B5035715
theorem B2238095 : Blo 2237435 2238095 := bstep (se 1 (by rfl) ⟨1678571, by rfl⟩ : syracuseStep 2238095 = 3357143) B3357143
theorem B3357149 : Blo 2237435 3357149 := bbase (se 3 (by rfl) ⟨629465, by rfl⟩ : syracuseStep 3357149 = 1258931) (by norm_num)
theorem B2238099 : Blo 2237435 2238099 := bstep (se 1 (by rfl) ⟨1678574, by rfl⟩ : syracuseStep 2238099 = 3357149) B3357149
theorem B5035733 : Blo 2237435 5035733 := bbase (se 7 (by rfl) ⟨59012, by rfl⟩ : syracuseStep 5035733 = 118025) (by norm_num)
theorem B3357155 : Blo 2237435 3357155 := bstep (se 1 (by rfl) ⟨2517866, by rfl⟩ : syracuseStep 3357155 = 5035733) B5035733
theorem B2238103 : Blo 2237435 2238103 := bstep (se 1 (by rfl) ⟨1678577, by rfl⟩ : syracuseStep 2238103 = 3357155) B3357155
theorem B7656677 : Blo 2237435 7656677 := bbase (se 4 (by rfl) ⟨717813, by rfl⟩ : syracuseStep 7656677 = 1435627) (by norm_num)
theorem B5104451 : Blo 2237435 5104451 := bstep (se 1 (by rfl) ⟨3828338, by rfl⟩ : syracuseStep 5104451 = 7656677) B7656677
theorem B3402967 : Blo 2237435 3402967 := bstep (se 1 (by rfl) ⟨2552225, by rfl⟩ : syracuseStep 3402967 = 5104451) B5104451
theorem B4537289 : Blo 2237435 4537289 := bstep (se 2 (by rfl) ⟨1701483, by rfl⟩ : syracuseStep 4537289 = 3402967) B3402967
theorem B3024859 : Blo 2237435 3024859 := bstep (se 1 (by rfl) ⟨2268644, by rfl⟩ : syracuseStep 3024859 = 4537289) B4537289
theorem B4033145 : Blo 2237435 4033145 := bstep (se 2 (by rfl) ⟨1512429, by rfl⟩ : syracuseStep 4033145 = 3024859) B3024859
theorem B2688763 : Blo 2237435 2688763 := bstep (se 1 (by rfl) ⟨2016572, by rfl⟩ : syracuseStep 2688763 = 4033145) B4033145
theorem B3585017 : Blo 2237435 3585017 := bstep (se 2 (by rfl) ⟨1344381, by rfl⟩ : syracuseStep 3585017 = 2688763) B2688763
theorem B9560045 : Blo 2237435 9560045 := bstep (se 3 (by rfl) ⟨1792508, by rfl⟩ : syracuseStep 9560045 = 3585017) B3585017
theorem B6373363 : Blo 2237435 6373363 := bstep (se 1 (by rfl) ⟨4780022, by rfl⟩ : syracuseStep 6373363 = 9560045) B9560045
theorem B8497817 : Blo 2237435 8497817 := bstep (se 2 (by rfl) ⟨3186681, by rfl⟩ : syracuseStep 8497817 = 6373363) B6373363
theorem B5665211 : Blo 2237435 5665211 := bstep (se 1 (by rfl) ⟨4248908, by rfl⟩ : syracuseStep 5665211 = 8497817) B8497817
theorem B3776807 : Blo 2237435 3776807 := bstep (se 1 (by rfl) ⟨2832605, by rfl⟩ : syracuseStep 3776807 = 5665211) B5665211
theorem B2517871 : Blo 2237435 2517871 := bstep (se 1 (by rfl) ⟨1888403, by rfl⟩ : syracuseStep 2517871 = 3776807) B3776807
theorem B3357161 : Blo 2237435 3357161 := bstep (se 2 (by rfl) ⟨1258935, by rfl⟩ : syracuseStep 3357161 = 2517871) B2517871
theorem B2238107 : Blo 2237435 2238107 := bstep (se 1 (by rfl) ⟨1678580, by rfl⟩ : syracuseStep 2238107 = 3357161) B3357161
theorem B2871257 : Blo 2237435 2871257 := bbase (se 2 (by rfl) ⟨1076721, by rfl⟩ : syracuseStep 2871257 = 2153443) (by norm_num)
theorem B30626741 : Blo 2237435 30626741 := bstep (se 5 (by rfl) ⟨1435628, by rfl⟩ : syracuseStep 30626741 = 2871257) B2871257
theorem B20417827 : Blo 2237435 20417827 := bstep (se 1 (by rfl) ⟨15313370, by rfl⟩ : syracuseStep 20417827 = 30626741) B30626741
theorem B27223769 : Blo 2237435 27223769 := bstep (se 2 (by rfl) ⟨10208913, by rfl⟩ : syracuseStep 27223769 = 20417827) B20417827
theorem B18149179 : Blo 2237435 18149179 := bstep (se 1 (by rfl) ⟨13611884, by rfl⟩ : syracuseStep 18149179 = 27223769) B27223769
theorem B24198905 : Blo 2237435 24198905 := bstep (se 2 (by rfl) ⟨9074589, by rfl⟩ : syracuseStep 24198905 = 18149179) B18149179
theorem B16132603 : Blo 2237435 16132603 := bstep (se 1 (by rfl) ⟨12099452, by rfl⟩ : syracuseStep 16132603 = 24198905) B24198905
theorem B21510137 : Blo 2237435 21510137 := bstep (se 2 (by rfl) ⟨8066301, by rfl⟩ : syracuseStep 21510137 = 16132603) B16132603
theorem B14340091 : Blo 2237435 14340091 := bstep (se 1 (by rfl) ⟨10755068, by rfl⟩ : syracuseStep 14340091 = 21510137) B21510137
theorem B19120121 : Blo 2237435 19120121 := bstep (se 2 (by rfl) ⟨7170045, by rfl⟩ : syracuseStep 19120121 = 14340091) B14340091
theorem B12746747 : Blo 2237435 12746747 := bstep (se 1 (by rfl) ⟨9560060, by rfl⟩ : syracuseStep 12746747 = 19120121) B19120121
theorem B8497831 : Blo 2237435 8497831 := bstep (se 1 (by rfl) ⟨6373373, by rfl⟩ : syracuseStep 8497831 = 12746747) B12746747
theorem B11330441 : Blo 2237435 11330441 := bstep (se 2 (by rfl) ⟨4248915, by rfl⟩ : syracuseStep 11330441 = 8497831) B8497831
theorem B7553627 : Blo 2237435 7553627 := bstep (se 1 (by rfl) ⟨5665220, by rfl⟩ : syracuseStep 7553627 = 11330441) B11330441
theorem B5035751 : Blo 2237435 5035751 := bstep (se 1 (by rfl) ⟨3776813, by rfl⟩ : syracuseStep 5035751 = 7553627) B7553627
theorem B3357167 : Blo 2237435 3357167 := bstep (se 1 (by rfl) ⟨2517875, by rfl⟩ : syracuseStep 3357167 = 5035751) B5035751
theorem B2238111 : Blo 2237435 2238111 := bstep (se 1 (by rfl) ⟨1678583, by rfl⟩ : syracuseStep 2238111 = 3357167) B3357167
theorem B3357173 : Blo 2237435 3357173 := bbase (se 5 (by rfl) ⟨157367, by rfl⟩ : syracuseStep 3357173 = 314735) (by norm_num)
theorem B2238115 : Blo 2237435 2238115 := bstep (se 1 (by rfl) ⟨1678586, by rfl⟩ : syracuseStep 2238115 = 3357173) B3357173
theorem B6373397 : Blo 2237435 6373397 := bbase (se 6 (by rfl) ⟨149376, by rfl⟩ : syracuseStep 6373397 = 298753) (by norm_num)
theorem B4248931 : Blo 2237435 4248931 := bstep (se 1 (by rfl) ⟨3186698, by rfl⟩ : syracuseStep 4248931 = 6373397) B6373397
theorem B5665241 : Blo 2237435 5665241 := bstep (se 2 (by rfl) ⟨2124465, by rfl⟩ : syracuseStep 5665241 = 4248931) B4248931
theorem B3776827 : Blo 2237435 3776827 := bstep (se 1 (by rfl) ⟨2832620, by rfl⟩ : syracuseStep 3776827 = 5665241) B5665241
theorem B5035769 : Blo 2237435 5035769 := bstep (se 2 (by rfl) ⟨1888413, by rfl⟩ : syracuseStep 5035769 = 3776827) B3776827
theorem B3357179 : Blo 2237435 3357179 := bstep (se 1 (by rfl) ⟨2517884, by rfl⟩ : syracuseStep 3357179 = 5035769) B5035769
theorem B2238119 : Blo 2237435 2238119 := bstep (se 1 (by rfl) ⟨1678589, by rfl⟩ : syracuseStep 2238119 = 3357179) B3357179
theorem B2517889 : Blo 2237435 2517889 := bbase (se 2 (by rfl) ⟨944208, by rfl⟩ : syracuseStep 2517889 = 1888417) (by norm_num)
theorem B3357185 : Blo 2237435 3357185 := bstep (se 2 (by rfl) ⟨1258944, by rfl⟩ : syracuseStep 3357185 = 2517889) B2517889
theorem B2238123 : Blo 2237435 2238123 := bstep (se 1 (by rfl) ⟨1678592, by rfl⟩ : syracuseStep 2238123 = 3357185) B3357185
theorem B5665261 : Blo 2237435 5665261 := bbase (se 3 (by rfl) ⟨1062236, by rfl⟩ : syracuseStep 5665261 = 2124473) (by norm_num)
theorem B7553681 : Blo 2237435 7553681 := bstep (se 2 (by rfl) ⟨2832630, by rfl⟩ : syracuseStep 7553681 = 5665261) B5665261
theorem B5035787 : Blo 2237435 5035787 := bstep (se 1 (by rfl) ⟨3776840, by rfl⟩ : syracuseStep 5035787 = 7553681) B7553681
theorem B3357191 : Blo 2237435 3357191 := bstep (se 1 (by rfl) ⟨2517893, by rfl⟩ : syracuseStep 3357191 = 5035787) B5035787
theorem B2238127 : Blo 2237435 2238127 := bstep (se 1 (by rfl) ⟨1678595, by rfl⟩ : syracuseStep 2238127 = 3357191) B3357191
theorem B3357197 : Blo 2237435 3357197 := bbase (se 3 (by rfl) ⟨629474, by rfl⟩ : syracuseStep 3357197 = 1258949) (by norm_num)
theorem B2238131 : Blo 2237435 2238131 := bstep (se 1 (by rfl) ⟨1678598, by rfl⟩ : syracuseStep 2238131 = 3357197) B3357197
theorem B5035805 : Blo 2237435 5035805 := bbase (se 3 (by rfl) ⟨944213, by rfl⟩ : syracuseStep 5035805 = 1888427) (by norm_num)
theorem B3357203 : Blo 2237435 3357203 := bstep (se 1 (by rfl) ⟨2517902, by rfl⟩ : syracuseStep 3357203 = 5035805) B5035805
theorem B2238135 : Blo 2237435 2238135 := bstep (se 1 (by rfl) ⟨1678601, by rfl⟩ : syracuseStep 2238135 = 3357203) B3357203
theorem B3776861 : Blo 2237435 3776861 := bbase (se 3 (by rfl) ⟨708161, by rfl⟩ : syracuseStep 3776861 = 1416323) (by norm_num)
theorem B2517907 : Blo 2237435 2517907 := bstep (se 1 (by rfl) ⟨1888430, by rfl⟩ : syracuseStep 2517907 = 3776861) B3776861
theorem B3357209 : Blo 2237435 3357209 := bstep (se 2 (by rfl) ⟨1258953, by rfl⟩ : syracuseStep 3357209 = 2517907) B2517907
theorem B2238139 : Blo 2237435 2238139 := bstep (se 1 (by rfl) ⟨1678604, by rfl⟩ : syracuseStep 2238139 = 3357209) B3357209
theorem B9560197 : Blo 2237435 9560197 := bbase (se 4 (by rfl) ⟨896268, by rfl⟩ : syracuseStep 9560197 = 1792537) (by norm_num)
theorem B12746929 : Blo 2237435 12746929 := bstep (se 2 (by rfl) ⟨4780098, by rfl⟩ : syracuseStep 12746929 = 9560197) B9560197
theorem B16995905 : Blo 2237435 16995905 := bstep (se 2 (by rfl) ⟨6373464, by rfl⟩ : syracuseStep 16995905 = 12746929) B12746929
theorem B11330603 : Blo 2237435 11330603 := bstep (se 1 (by rfl) ⟨8497952, by rfl⟩ : syracuseStep 11330603 = 16995905) B16995905
theorem B7553735 : Blo 2237435 7553735 := bstep (se 1 (by rfl) ⟨5665301, by rfl⟩ : syracuseStep 7553735 = 11330603) B11330603
theorem B5035823 : Blo 2237435 5035823 := bstep (se 1 (by rfl) ⟨3776867, by rfl⟩ : syracuseStep 5035823 = 7553735) B7553735
theorem B3357215 : Blo 2237435 3357215 := bstep (se 1 (by rfl) ⟨2517911, by rfl⟩ : syracuseStep 3357215 = 5035823) B5035823
theorem B2238143 : Blo 2237435 2238143 := bstep (se 1 (by rfl) ⟨1678607, by rfl⟩ : syracuseStep 2238143 = 3357215) B3357215
theorem B3357221 : Blo 2237435 3357221 := bbase (se 4 (by rfl) ⟨314739, by rfl⟩ : syracuseStep 3357221 = 629479) (by norm_num)
theorem B2238147 : Blo 2237435 2238147 := bstep (se 1 (by rfl) ⟨1678610, by rfl⟩ : syracuseStep 2238147 = 3357221) B3357221
theorem B2832661 : Blo 2237435 2832661 := bbase (se 6 (by rfl) ⟨66390, by rfl⟩ : syracuseStep 2832661 = 132781) (by norm_num)
theorem B3776881 : Blo 2237435 3776881 := bstep (se 2 (by rfl) ⟨1416330, by rfl⟩ : syracuseStep 3776881 = 2832661) B2832661
theorem B5035841 : Blo 2237435 5035841 := bstep (se 2 (by rfl) ⟨1888440, by rfl⟩ : syracuseStep 5035841 = 3776881) B3776881
theorem B3357227 : Blo 2237435 3357227 := bstep (se 1 (by rfl) ⟨2517920, by rfl⟩ : syracuseStep 3357227 = 5035841) B5035841
theorem B2238151 : Blo 2237435 2238151 := bstep (se 1 (by rfl) ⟨1678613, by rfl⟩ : syracuseStep 2238151 = 3357227) B3357227
theorem B2517925 : Blo 2237435 2517925 := bbase (se 4 (by rfl) ⟨236055, by rfl⟩ : syracuseStep 2517925 = 472111) (by norm_num)
theorem B3357233 : Blo 2237435 3357233 := bstep (se 2 (by rfl) ⟨1258962, by rfl⟩ : syracuseStep 3357233 = 2517925) B2517925
theorem B2238155 : Blo 2237435 2238155 := bstep (se 1 (by rfl) ⟨1678616, by rfl⟩ : syracuseStep 2238155 = 3357233) B3357233
theorem B10755301 : Blo 2237435 10755301 := bbase (se 4 (by rfl) ⟨1008309, by rfl⟩ : syracuseStep 10755301 = 2016619) (by norm_num)
theorem B14340401 : Blo 2237435 14340401 := bstep (se 2 (by rfl) ⟨5377650, by rfl⟩ : syracuseStep 14340401 = 10755301) B10755301
theorem B9560267 : Blo 2237435 9560267 := bstep (se 1 (by rfl) ⟨7170200, by rfl⟩ : syracuseStep 9560267 = 14340401) B14340401
theorem B6373511 : Blo 2237435 6373511 := bstep (se 1 (by rfl) ⟨4780133, by rfl⟩ : syracuseStep 6373511 = 9560267) B9560267
theorem B4249007 : Blo 2237435 4249007 := bstep (se 1 (by rfl) ⟨3186755, by rfl⟩ : syracuseStep 4249007 = 6373511) B6373511
theorem B2832671 : Blo 2237435 2832671 := bstep (se 1 (by rfl) ⟨2124503, by rfl⟩ : syracuseStep 2832671 = 4249007) B4249007
theorem B7553789 : Blo 2237435 7553789 := bstep (se 3 (by rfl) ⟨1416335, by rfl⟩ : syracuseStep 7553789 = 2832671) B2832671
theorem B5035859 : Blo 2237435 5035859 := bstep (se 1 (by rfl) ⟨3776894, by rfl⟩ : syracuseStep 5035859 = 7553789) B7553789
theorem B3357239 : Blo 2237435 3357239 := bstep (se 1 (by rfl) ⟨2517929, by rfl⟩ : syracuseStep 3357239 = 5035859) B5035859
theorem B2238159 : Blo 2237435 2238159 := bstep (se 1 (by rfl) ⟨1678619, by rfl⟩ : syracuseStep 2238159 = 3357239) B3357239
theorem B3357245 : Blo 2237435 3357245 := bbase (se 3 (by rfl) ⟨629483, by rfl⟩ : syracuseStep 3357245 = 1258967) (by norm_num)
theorem B2238163 : Blo 2237435 2238163 := bstep (se 1 (by rfl) ⟨1678622, by rfl⟩ : syracuseStep 2238163 = 3357245) B3357245
theorem B5035877 : Blo 2237435 5035877 := bbase (se 4 (by rfl) ⟨472113, by rfl⟩ : syracuseStep 5035877 = 944227) (by norm_num)
theorem B3357251 : Blo 2237435 3357251 := bstep (se 1 (by rfl) ⟨2517938, by rfl⟩ : syracuseStep 3357251 = 5035877) B5035877
theorem B2238167 : Blo 2237435 2238167 := bstep (se 1 (by rfl) ⟨1678625, by rfl⟩ : syracuseStep 2238167 = 3357251) B3357251
theorem B5665373 : Blo 2237435 5665373 := bbase (se 3 (by rfl) ⟨1062257, by rfl⟩ : syracuseStep 5665373 = 2124515) (by norm_num)
theorem B3776915 : Blo 2237435 3776915 := bstep (se 1 (by rfl) ⟨2832686, by rfl⟩ : syracuseStep 3776915 = 5665373) B5665373
theorem B2517943 : Blo 2237435 2517943 := bstep (se 1 (by rfl) ⟨1888457, by rfl⟩ : syracuseStep 2517943 = 3776915) B3776915
theorem B3357257 : Blo 2237435 3357257 := bstep (se 2 (by rfl) ⟨1258971, by rfl⟩ : syracuseStep 3357257 = 2517943) B2517943
theorem B2238171 : Blo 2237435 2238171 := bstep (se 1 (by rfl) ⟨1678628, by rfl⟩ : syracuseStep 2238171 = 3357257) B3357257
theorem B4249037 : Blo 2237435 4249037 := bbase (se 3 (by rfl) ⟨796694, by rfl⟩ : syracuseStep 4249037 = 1593389) (by norm_num)
theorem B11330765 : Blo 2237435 11330765 := bstep (se 3 (by rfl) ⟨2124518, by rfl⟩ : syracuseStep 11330765 = 4249037) B4249037
theorem B7553843 : Blo 2237435 7553843 := bstep (se 1 (by rfl) ⟨5665382, by rfl⟩ : syracuseStep 7553843 = 11330765) B11330765
theorem B5035895 : Blo 2237435 5035895 := bstep (se 1 (by rfl) ⟨3776921, by rfl⟩ : syracuseStep 5035895 = 7553843) B7553843
theorem B3357263 : Blo 2237435 3357263 := bstep (se 1 (by rfl) ⟨2517947, by rfl⟩ : syracuseStep 3357263 = 5035895) B5035895
theorem B2238175 : Blo 2237435 2238175 := bstep (se 1 (by rfl) ⟨1678631, by rfl⟩ : syracuseStep 2238175 = 3357263) B3357263
theorem B3357269 : Blo 2237435 3357269 := bbase (se 8 (by rfl) ⟨19671, by rfl⟩ : syracuseStep 3357269 = 39343) (by norm_num)
theorem B2238179 : Blo 2237435 2238179 := bstep (se 1 (by rfl) ⟨1678634, by rfl⟩ : syracuseStep 2238179 = 3357269) B3357269
theorem B7170277 : Blo 2237435 7170277 := bbase (se 4 (by rfl) ⟨672213, by rfl⟩ : syracuseStep 7170277 = 1344427) (by norm_num)
theorem B9560369 : Blo 2237435 9560369 := bstep (se 2 (by rfl) ⟨3585138, by rfl⟩ : syracuseStep 9560369 = 7170277) B7170277
theorem B6373579 : Blo 2237435 6373579 := bstep (se 1 (by rfl) ⟨4780184, by rfl⟩ : syracuseStep 6373579 = 9560369) B9560369
theorem B8498105 : Blo 2237435 8498105 := bstep (se 2 (by rfl) ⟨3186789, by rfl⟩ : syracuseStep 8498105 = 6373579) B6373579
theorem B5665403 : Blo 2237435 5665403 := bstep (se 1 (by rfl) ⟨4249052, by rfl⟩ : syracuseStep 5665403 = 8498105) B8498105
theorem B3776935 : Blo 2237435 3776935 := bstep (se 1 (by rfl) ⟨2832701, by rfl⟩ : syracuseStep 3776935 = 5665403) B5665403
theorem B5035913 : Blo 2237435 5035913 := bstep (se 2 (by rfl) ⟨1888467, by rfl⟩ : syracuseStep 5035913 = 3776935) B3776935
theorem B3357275 : Blo 2237435 3357275 := bstep (se 1 (by rfl) ⟨2517956, by rfl⟩ : syracuseStep 3357275 = 5035913) B5035913
theorem B2238183 : Blo 2237435 2238183 := bstep (se 1 (by rfl) ⟨1678637, by rfl⟩ : syracuseStep 2238183 = 3357275) B3357275
theorem B2517961 : Blo 2237435 2517961 := bbase (se 2 (by rfl) ⟨944235, by rfl⟩ : syracuseStep 2517961 = 1888471) (by norm_num)
theorem B3357281 : Blo 2237435 3357281 := bstep (se 2 (by rfl) ⟨1258980, by rfl⟩ : syracuseStep 3357281 = 2517961) B2517961
theorem B2238187 : Blo 2237435 2238187 := bstep (se 1 (by rfl) ⟨1678640, by rfl⟩ : syracuseStep 2238187 = 3357281) B3357281
theorem B10902197 : Blo 2237435 10902197 := bbase (se 5 (by rfl) ⟨511040, by rfl⟩ : syracuseStep 10902197 = 1022081) (by norm_num)
theorem B7268131 : Blo 2237435 7268131 := bstep (se 1 (by rfl) ⟨5451098, by rfl⟩ : syracuseStep 7268131 = 10902197) B10902197
theorem B9690841 : Blo 2237435 9690841 := bstep (se 2 (by rfl) ⟨3634065, by rfl⟩ : syracuseStep 9690841 = 7268131) B7268131
theorem B12921121 : Blo 2237435 12921121 := bstep (se 2 (by rfl) ⟨4845420, by rfl⟩ : syracuseStep 12921121 = 9690841) B9690841
theorem B17228161 : Blo 2237435 17228161 := bstep (se 2 (by rfl) ⟨6460560, by rfl⟩ : syracuseStep 17228161 = 12921121) B12921121
theorem B22970881 : Blo 2237435 22970881 := bstep (se 2 (by rfl) ⟨8614080, by rfl⟩ : syracuseStep 22970881 = 17228161) B17228161
theorem B30627841 : Blo 2237435 30627841 := bstep (se 2 (by rfl) ⟨11485440, by rfl⟩ : syracuseStep 30627841 = 22970881) B22970881
theorem B40837121 : Blo 2237435 40837121 := bstep (se 2 (by rfl) ⟨15313920, by rfl⟩ : syracuseStep 40837121 = 30627841) B30627841
theorem B27224747 : Blo 2237435 27224747 := bstep (se 1 (by rfl) ⟨20418560, by rfl⟩ : syracuseStep 27224747 = 40837121) B40837121
theorem B18149831 : Blo 2237435 18149831 := bstep (se 1 (by rfl) ⟨13612373, by rfl⟩ : syracuseStep 18149831 = 27224747) B27224747
theorem B12099887 : Blo 2237435 12099887 := bstep (se 1 (by rfl) ⟨9074915, by rfl⟩ : syracuseStep 12099887 = 18149831) B18149831
theorem B8066591 : Blo 2237435 8066591 := bstep (se 1 (by rfl) ⟨6049943, by rfl⟩ : syracuseStep 8066591 = 12099887) B12099887
theorem B5377727 : Blo 2237435 5377727 := bstep (se 1 (by rfl) ⟨4033295, by rfl⟩ : syracuseStep 5377727 = 8066591) B8066591
theorem B3585151 : Blo 2237435 3585151 := bstep (se 1 (by rfl) ⟨2688863, by rfl⟩ : syracuseStep 3585151 = 5377727) B5377727
theorem B19120805 : Blo 2237435 19120805 := bstep (se 4 (by rfl) ⟨1792575, by rfl⟩ : syracuseStep 19120805 = 3585151) B3585151
theorem B12747203 : Blo 2237435 12747203 := bstep (se 1 (by rfl) ⟨9560402, by rfl⟩ : syracuseStep 12747203 = 19120805) B19120805
theorem B8498135 : Blo 2237435 8498135 := bstep (se 1 (by rfl) ⟨6373601, by rfl⟩ : syracuseStep 8498135 = 12747203) B12747203
theorem B5665423 : Blo 2237435 5665423 := bstep (se 1 (by rfl) ⟨4249067, by rfl⟩ : syracuseStep 5665423 = 8498135) B8498135
theorem B7553897 : Blo 2237435 7553897 := bstep (se 2 (by rfl) ⟨2832711, by rfl⟩ : syracuseStep 7553897 = 5665423) B5665423
theorem B5035931 : Blo 2237435 5035931 := bstep (se 1 (by rfl) ⟨3776948, by rfl⟩ : syracuseStep 5035931 = 7553897) B7553897
theorem B3357287 : Blo 2237435 3357287 := bstep (se 1 (by rfl) ⟨2517965, by rfl⟩ : syracuseStep 3357287 = 5035931) B5035931
theorem B2238191 : Blo 2237435 2238191 := bstep (se 1 (by rfl) ⟨1678643, by rfl⟩ : syracuseStep 2238191 = 3357287) B3357287
theorem B3357293 : Blo 2237435 3357293 := bbase (se 3 (by rfl) ⟨629492, by rfl⟩ : syracuseStep 3357293 = 1258985) (by norm_num)
theorem B2238195 : Blo 2237435 2238195 := bstep (se 1 (by rfl) ⟨1678646, by rfl⟩ : syracuseStep 2238195 = 3357293) B3357293
theorem B5035949 : Blo 2237435 5035949 := bbase (se 3 (by rfl) ⟨944240, by rfl⟩ : syracuseStep 5035949 = 1888481) (by norm_num)
theorem B3357299 : Blo 2237435 3357299 := bstep (se 1 (by rfl) ⟨2517974, by rfl⟩ : syracuseStep 3357299 = 5035949) B5035949
theorem B2238199 : Blo 2237435 2238199 := bstep (se 1 (by rfl) ⟨1678649, by rfl⟩ : syracuseStep 2238199 = 3357299) B3357299
theorem B6373637 : Blo 2237435 6373637 := bbase (se 4 (by rfl) ⟨597528, by rfl⟩ : syracuseStep 6373637 = 1195057) (by norm_num)
theorem B4249091 : Blo 2237435 4249091 := bstep (se 1 (by rfl) ⟨3186818, by rfl⟩ : syracuseStep 4249091 = 6373637) B6373637
theorem B2832727 : Blo 2237435 2832727 := bstep (se 1 (by rfl) ⟨2124545, by rfl⟩ : syracuseStep 2832727 = 4249091) B4249091
theorem B3776969 : Blo 2237435 3776969 := bstep (se 2 (by rfl) ⟨1416363, by rfl⟩ : syracuseStep 3776969 = 2832727) B2832727
theorem B2517979 : Blo 2237435 2517979 := bstep (se 1 (by rfl) ⟨1888484, by rfl⟩ : syracuseStep 2517979 = 3776969) B3776969
theorem B3357305 : Blo 2237435 3357305 := bstep (se 2 (by rfl) ⟨1258989, by rfl⟩ : syracuseStep 3357305 = 2517979) B2517979
theorem B2238203 : Blo 2237435 2238203 := bstep (se 1 (by rfl) ⟨1678652, by rfl⟩ : syracuseStep 2238203 = 3357305) B3357305
theorem B3403117 : Blo 2237435 3403117 := bbase (se 3 (by rfl) ⟨638084, by rfl⟩ : syracuseStep 3403117 = 1276169) (by norm_num)
theorem B18149957 : Blo 2237435 18149957 := bstep (se 4 (by rfl) ⟨1701558, by rfl⟩ : syracuseStep 18149957 = 3403117) B3403117
theorem B12099971 : Blo 2237435 12099971 := bstep (se 1 (by rfl) ⟨9074978, by rfl⟩ : syracuseStep 12099971 = 18149957) B18149957
theorem B8066647 : Blo 2237435 8066647 := bstep (se 1 (by rfl) ⟨6049985, by rfl⟩ : syracuseStep 8066647 = 12099971) B12099971
theorem B43022117 : Blo 2237435 43022117 := bstep (se 4 (by rfl) ⟨4033323, by rfl⟩ : syracuseStep 43022117 = 8066647) B8066647
theorem B28681411 : Blo 2237435 28681411 := bstep (se 1 (by rfl) ⟨21511058, by rfl⟩ : syracuseStep 28681411 = 43022117) B43022117
theorem B38241881 : Blo 2237435 38241881 := bstep (se 2 (by rfl) ⟨14340705, by rfl⟩ : syracuseStep 38241881 = 28681411) B28681411
theorem B25494587 : Blo 2237435 25494587 := bstep (se 1 (by rfl) ⟨19120940, by rfl⟩ : syracuseStep 25494587 = 38241881) B38241881
theorem B16996391 : Blo 2237435 16996391 := bstep (se 1 (by rfl) ⟨12747293, by rfl⟩ : syracuseStep 16996391 = 25494587) B25494587
theorem B11330927 : Blo 2237435 11330927 := bstep (se 1 (by rfl) ⟨8498195, by rfl⟩ : syracuseStep 11330927 = 16996391) B16996391
theorem B7553951 : Blo 2237435 7553951 := bstep (se 1 (by rfl) ⟨5665463, by rfl⟩ : syracuseStep 7553951 = 11330927) B11330927
theorem B5035967 : Blo 2237435 5035967 := bstep (se 1 (by rfl) ⟨3776975, by rfl⟩ : syracuseStep 5035967 = 7553951) B7553951
theorem B3357311 : Blo 2237435 3357311 := bstep (se 1 (by rfl) ⟨2517983, by rfl⟩ : syracuseStep 3357311 = 5035967) B5035967
theorem B2238207 : Blo 2237435 2238207 := bstep (se 1 (by rfl) ⟨1678655, by rfl⟩ : syracuseStep 2238207 = 3357311) B3357311
theorem B3357317 : Blo 2237435 3357317 := bbase (se 4 (by rfl) ⟨314748, by rfl⟩ : syracuseStep 3357317 = 629497) (by norm_num)
theorem B2238211 : Blo 2237435 2238211 := bstep (se 1 (by rfl) ⟨1678658, by rfl⟩ : syracuseStep 2238211 = 3357317) B3357317
theorem B3776989 : Blo 2237435 3776989 := bbase (se 3 (by rfl) ⟨708185, by rfl⟩ : syracuseStep 3776989 = 1416371) (by norm_num)
theorem B5035985 : Blo 2237435 5035985 := bstep (se 2 (by rfl) ⟨1888494, by rfl⟩ : syracuseStep 5035985 = 3776989) B3776989
theorem B3357323 : Blo 2237435 3357323 := bstep (se 1 (by rfl) ⟨2517992, by rfl⟩ : syracuseStep 3357323 = 5035985) B5035985
theorem B2238215 : Blo 2237435 2238215 := bstep (se 1 (by rfl) ⟨1678661, by rfl⟩ : syracuseStep 2238215 = 3357323) B3357323
theorem B2517997 : Blo 2237435 2517997 := bbase (se 3 (by rfl) ⟨472124, by rfl⟩ : syracuseStep 2517997 = 944249) (by norm_num)
theorem B3357329 : Blo 2237435 3357329 := bstep (se 2 (by rfl) ⟨1258998, by rfl⟩ : syracuseStep 3357329 = 2517997) B2517997
theorem B2238219 : Blo 2237435 2238219 := bstep (se 1 (by rfl) ⟨1678664, by rfl⟩ : syracuseStep 2238219 = 3357329) B3357329
theorem B7554005 : Blo 2237435 7554005 := bbase (se 7 (by rfl) ⟨88523, by rfl⟩ : syracuseStep 7554005 = 177047) (by norm_num)
theorem B5036003 : Blo 2237435 5036003 := bstep (se 1 (by rfl) ⟨3777002, by rfl⟩ : syracuseStep 5036003 = 7554005) B7554005
theorem B3357335 : Blo 2237435 3357335 := bstep (se 1 (by rfl) ⟨2518001, by rfl⟩ : syracuseStep 3357335 = 5036003) B5036003
theorem B2238223 : Blo 2237435 2238223 := bstep (se 1 (by rfl) ⟨1678667, by rfl⟩ : syracuseStep 2238223 = 3357335) B3357335
theorem B3357341 : Blo 2237435 3357341 := bbase (se 3 (by rfl) ⟨629501, by rfl⟩ : syracuseStep 3357341 = 1259003) (by norm_num)
theorem B2238227 : Blo 2237435 2238227 := bstep (se 1 (by rfl) ⟨1678670, by rfl⟩ : syracuseStep 2238227 = 3357341) B3357341
theorem B5036021 : Blo 2237435 5036021 := bbase (se 5 (by rfl) ⟨236063, by rfl⟩ : syracuseStep 5036021 = 472127) (by norm_num)
theorem B3357347 : Blo 2237435 3357347 := bstep (se 1 (by rfl) ⟨2518010, by rfl⟩ : syracuseStep 3357347 = 5036021) B5036021
theorem B2238231 : Blo 2237435 2238231 := bstep (se 1 (by rfl) ⟨1678673, by rfl⟩ : syracuseStep 2238231 = 3357347) B3357347
theorem B2910593 : Blo 2237435 2910593 := bbase (se 2 (by rfl) ⟨1091472, by rfl⟩ : syracuseStep 2910593 = 2182945) (by norm_num)
theorem B7761581 : Blo 2237435 7761581 := bstep (se 3 (by rfl) ⟨1455296, by rfl⟩ : syracuseStep 7761581 = 2910593) B2910593
theorem B5174387 : Blo 2237435 5174387 := bstep (se 1 (by rfl) ⟨3880790, by rfl⟩ : syracuseStep 5174387 = 7761581) B7761581
theorem B3449591 : Blo 2237435 3449591 := bstep (se 1 (by rfl) ⟨2587193, by rfl⟩ : syracuseStep 3449591 = 5174387) B5174387
theorem B2299727 : Blo 2237435 2299727 := bstep (se 1 (by rfl) ⟨1724795, by rfl⟩ : syracuseStep 2299727 = 3449591) B3449591
theorem B6132605 : Blo 2237435 6132605 := bstep (se 3 (by rfl) ⟨1149863, by rfl⟩ : syracuseStep 6132605 = 2299727) B2299727
theorem B16353613 : Blo 2237435 16353613 := bstep (se 3 (by rfl) ⟨3066302, by rfl⟩ : syracuseStep 16353613 = 6132605) B6132605
theorem B87219269 : Blo 2237435 87219269 := bstep (se 4 (by rfl) ⟨8176806, by rfl⟩ : syracuseStep 87219269 = 16353613) B16353613
theorem B58146179 : Blo 2237435 58146179 := bstep (se 1 (by rfl) ⟨43609634, by rfl⟩ : syracuseStep 58146179 = 87219269) B87219269
theorem B620225909 : Blo 2237435 620225909 := bstep (se 5 (by rfl) ⟨29073089, by rfl⟩ : syracuseStep 620225909 = 58146179) B58146179
theorem B413483939 : Blo 2237435 413483939 := bstep (se 1 (by rfl) ⟨310112954, by rfl⟩ : syracuseStep 413483939 = 620225909) B620225909
theorem B275655959 : Blo 2237435 275655959 := bstep (se 1 (by rfl) ⟨206741969, by rfl⟩ : syracuseStep 275655959 = 413483939) B413483939
theorem B183770639 : Blo 2237435 183770639 := bstep (se 1 (by rfl) ⟨137827979, by rfl⟩ : syracuseStep 183770639 = 275655959) B275655959
theorem B122513759 : Blo 2237435 122513759 := bstep (se 1 (by rfl) ⟨91885319, by rfl⟩ : syracuseStep 122513759 = 183770639) B183770639
theorem B81675839 : Blo 2237435 81675839 := bstep (se 1 (by rfl) ⟨61256879, by rfl⟩ : syracuseStep 81675839 = 122513759) B122513759
theorem B54450559 : Blo 2237435 54450559 := bstep (se 1 (by rfl) ⟨40837919, by rfl⟩ : syracuseStep 54450559 = 81675839) B81675839
theorem B72600745 : Blo 2237435 72600745 := bstep (se 2 (by rfl) ⟨27225279, by rfl⟩ : syracuseStep 72600745 = 54450559) B54450559
theorem B96800993 : Blo 2237435 96800993 := bstep (se 2 (by rfl) ⟨36300372, by rfl⟩ : syracuseStep 96800993 = 72600745) B72600745
theorem B64533995 : Blo 2237435 64533995 := bstep (se 1 (by rfl) ⟨48400496, by rfl⟩ : syracuseStep 64533995 = 96800993) B96800993
theorem B43022663 : Blo 2237435 43022663 := bstep (se 1 (by rfl) ⟨32266997, by rfl⟩ : syracuseStep 43022663 = 64533995) B64533995
theorem B28681775 : Blo 2237435 28681775 := bstep (se 1 (by rfl) ⟨21511331, by rfl⟩ : syracuseStep 28681775 = 43022663) B43022663
theorem B19121183 : Blo 2237435 19121183 := bstep (se 1 (by rfl) ⟨14340887, by rfl⟩ : syracuseStep 19121183 = 28681775) B28681775
theorem B12747455 : Blo 2237435 12747455 := bstep (se 1 (by rfl) ⟨9560591, by rfl⟩ : syracuseStep 12747455 = 19121183) B19121183
theorem B8498303 : Blo 2237435 8498303 := bstep (se 1 (by rfl) ⟨6373727, by rfl⟩ : syracuseStep 8498303 = 12747455) B12747455
theorem B5665535 : Blo 2237435 5665535 := bstep (se 1 (by rfl) ⟨4249151, by rfl⟩ : syracuseStep 5665535 = 8498303) B8498303
theorem B3777023 : Blo 2237435 3777023 := bstep (se 1 (by rfl) ⟨2832767, by rfl⟩ : syracuseStep 3777023 = 5665535) B5665535
theorem B2518015 : Blo 2237435 2518015 := bstep (se 1 (by rfl) ⟨1888511, by rfl⟩ : syracuseStep 2518015 = 3777023) B3777023
theorem B3357353 : Blo 2237435 3357353 := bstep (se 2 (by rfl) ⟨1259007, by rfl⟩ : syracuseStep 3357353 = 2518015) B2518015
theorem B2238235 : Blo 2237435 2238235 := bstep (se 1 (by rfl) ⟨1678676, by rfl⟩ : syracuseStep 2238235 = 3357353) B3357353
theorem B3186869 : Blo 2237435 3186869 := bbase (se 5 (by rfl) ⟨149384, by rfl⟩ : syracuseStep 3186869 = 298769) (by norm_num)
theorem B8498317 : Blo 2237435 8498317 := bstep (se 3 (by rfl) ⟨1593434, by rfl⟩ : syracuseStep 8498317 = 3186869) B3186869
theorem B11331089 : Blo 2237435 11331089 := bstep (se 2 (by rfl) ⟨4249158, by rfl⟩ : syracuseStep 11331089 = 8498317) B8498317
theorem B7554059 : Blo 2237435 7554059 := bstep (se 1 (by rfl) ⟨5665544, by rfl⟩ : syracuseStep 7554059 = 11331089) B11331089
theorem B5036039 : Blo 2237435 5036039 := bstep (se 1 (by rfl) ⟨3777029, by rfl⟩ : syracuseStep 5036039 = 7554059) B7554059
theorem B3357359 : Blo 2237435 3357359 := bstep (se 1 (by rfl) ⟨2518019, by rfl⟩ : syracuseStep 3357359 = 5036039) B5036039
theorem B2238239 : Blo 2237435 2238239 := bstep (se 1 (by rfl) ⟨1678679, by rfl⟩ : syracuseStep 2238239 = 3357359) B3357359
theorem B3357365 : Blo 2237435 3357365 := bbase (se 5 (by rfl) ⟨157376, by rfl⟩ : syracuseStep 3357365 = 314753) (by norm_num)
theorem B2238243 : Blo 2237435 2238243 := bstep (se 1 (by rfl) ⟨1678682, by rfl⟩ : syracuseStep 2238243 = 3357365) B3357365
theorem B5665565 : Blo 2237435 5665565 := bbase (se 3 (by rfl) ⟨1062293, by rfl⟩ : syracuseStep 5665565 = 2124587) (by norm_num)
theorem B3777043 : Blo 2237435 3777043 := bstep (se 1 (by rfl) ⟨2832782, by rfl⟩ : syracuseStep 3777043 = 5665565) B5665565
theorem B5036057 : Blo 2237435 5036057 := bstep (se 2 (by rfl) ⟨1888521, by rfl⟩ : syracuseStep 5036057 = 3777043) B3777043
theorem B3357371 : Blo 2237435 3357371 := bstep (se 1 (by rfl) ⟨2518028, by rfl⟩ : syracuseStep 3357371 = 5036057) B5036057
theorem B2238247 : Blo 2237435 2238247 := bstep (se 1 (by rfl) ⟨1678685, by rfl⟩ : syracuseStep 2238247 = 3357371) B3357371
theorem B2518033 : Blo 2237435 2518033 := bbase (se 2 (by rfl) ⟨944262, by rfl⟩ : syracuseStep 2518033 = 1888525) (by norm_num)
theorem B3357377 : Blo 2237435 3357377 := bstep (se 2 (by rfl) ⟨1259016, by rfl⟩ : syracuseStep 3357377 = 2518033) B2518033
theorem B2238251 : Blo 2237435 2238251 := bstep (se 1 (by rfl) ⟨1678688, by rfl⟩ : syracuseStep 2238251 = 3357377) B3357377
theorem B4249189 : Blo 2237435 4249189 := bbase (se 4 (by rfl) ⟨398361, by rfl⟩ : syracuseStep 4249189 = 796723) (by norm_num)
theorem B5665585 : Blo 2237435 5665585 := bstep (se 2 (by rfl) ⟨2124594, by rfl⟩ : syracuseStep 5665585 = 4249189) B4249189
theorem B7554113 : Blo 2237435 7554113 := bstep (se 2 (by rfl) ⟨2832792, by rfl⟩ : syracuseStep 7554113 = 5665585) B5665585
theorem B5036075 : Blo 2237435 5036075 := bstep (se 1 (by rfl) ⟨3777056, by rfl⟩ : syracuseStep 5036075 = 7554113) B7554113
theorem B3357383 : Blo 2237435 3357383 := bstep (se 1 (by rfl) ⟨2518037, by rfl⟩ : syracuseStep 3357383 = 5036075) B5036075
theorem B2238255 : Blo 2237435 2238255 := bstep (se 1 (by rfl) ⟨1678691, by rfl⟩ : syracuseStep 2238255 = 3357383) B3357383
theorem B3357389 : Blo 2237435 3357389 := bbase (se 3 (by rfl) ⟨629510, by rfl⟩ : syracuseStep 3357389 = 1259021) (by norm_num)
theorem B2238259 : Blo 2237435 2238259 := bstep (se 1 (by rfl) ⟨1678694, by rfl⟩ : syracuseStep 2238259 = 3357389) B3357389
theorem B5036093 : Blo 2237435 5036093 := bbase (se 3 (by rfl) ⟨944267, by rfl⟩ : syracuseStep 5036093 = 1888535) (by norm_num)
theorem B3357395 : Blo 2237435 3357395 := bstep (se 1 (by rfl) ⟨2518046, by rfl⟩ : syracuseStep 3357395 = 5036093) B5036093
theorem B2238263 : Blo 2237435 2238263 := bstep (se 1 (by rfl) ⟨1678697, by rfl⟩ : syracuseStep 2238263 = 3357395) B3357395
theorem B3777077 : Blo 2237435 3777077 := bbase (se 5 (by rfl) ⟨177050, by rfl⟩ : syracuseStep 3777077 = 354101) (by norm_num)
theorem B2518051 : Blo 2237435 2518051 := bstep (se 1 (by rfl) ⟨1888538, by rfl⟩ : syracuseStep 2518051 = 3777077) B3777077
theorem B3357401 : Blo 2237435 3357401 := bstep (se 2 (by rfl) ⟨1259025, by rfl⟩ : syracuseStep 3357401 = 2518051) B2518051
theorem B2238267 : Blo 2237435 2238267 := bstep (se 1 (by rfl) ⟨1678700, by rfl⟩ : syracuseStep 2238267 = 3357401) B3357401
theorem B6373829 : Blo 2237435 6373829 := bbase (se 4 (by rfl) ⟨597546, by rfl⟩ : syracuseStep 6373829 = 1195093) (by norm_num)
theorem B16996877 : Blo 2237435 16996877 := bstep (se 3 (by rfl) ⟨3186914, by rfl⟩ : syracuseStep 16996877 = 6373829) B6373829
theorem B11331251 : Blo 2237435 11331251 := bstep (se 1 (by rfl) ⟨8498438, by rfl⟩ : syracuseStep 11331251 = 16996877) B16996877
theorem B7554167 : Blo 2237435 7554167 := bstep (se 1 (by rfl) ⟨5665625, by rfl⟩ : syracuseStep 7554167 = 11331251) B11331251
theorem B5036111 : Blo 2237435 5036111 := bstep (se 1 (by rfl) ⟨3777083, by rfl⟩ : syracuseStep 5036111 = 7554167) B7554167
theorem B3357407 : Blo 2237435 3357407 := bstep (se 1 (by rfl) ⟨2518055, by rfl⟩ : syracuseStep 3357407 = 5036111) B5036111
theorem B2238271 : Blo 2237435 2238271 := bstep (se 1 (by rfl) ⟨1678703, by rfl⟩ : syracuseStep 2238271 = 3357407) B3357407
theorem B3357413 : Blo 2237435 3357413 := bbase (se 4 (by rfl) ⟨314757, by rfl⟩ : syracuseStep 3357413 = 629515) (by norm_num)
theorem B2238275 : Blo 2237435 2238275 := bstep (se 1 (by rfl) ⟨1678706, by rfl⟩ : syracuseStep 2238275 = 3357413) B3357413
theorem B3585293 : Blo 2237435 3585293 := bbase (se 3 (by rfl) ⟨672242, by rfl⟩ : syracuseStep 3585293 = 1344485) (by norm_num)
theorem B2390195 : Blo 2237435 2390195 := bstep (se 1 (by rfl) ⟨1792646, by rfl⟩ : syracuseStep 2390195 = 3585293) B3585293
theorem B6373853 : Blo 2237435 6373853 := bstep (se 3 (by rfl) ⟨1195097, by rfl⟩ : syracuseStep 6373853 = 2390195) B2390195
theorem B4249235 : Blo 2237435 4249235 := bstep (se 1 (by rfl) ⟨3186926, by rfl⟩ : syracuseStep 4249235 = 6373853) B6373853
theorem B2832823 : Blo 2237435 2832823 := bstep (se 1 (by rfl) ⟨2124617, by rfl⟩ : syracuseStep 2832823 = 4249235) B4249235
theorem B3777097 : Blo 2237435 3777097 := bstep (se 2 (by rfl) ⟨1416411, by rfl⟩ : syracuseStep 3777097 = 2832823) B2832823
theorem B5036129 : Blo 2237435 5036129 := bstep (se 2 (by rfl) ⟨1888548, by rfl⟩ : syracuseStep 5036129 = 3777097) B3777097
theorem B3357419 : Blo 2237435 3357419 := bstep (se 1 (by rfl) ⟨2518064, by rfl⟩ : syracuseStep 3357419 = 5036129) B5036129
theorem B2238279 : Blo 2237435 2238279 := bstep (se 1 (by rfl) ⟨1678709, by rfl⟩ : syracuseStep 2238279 = 3357419) B3357419
theorem B2518069 : Blo 2237435 2518069 := bbase (se 5 (by rfl) ⟨118034, by rfl⟩ : syracuseStep 2518069 = 236069) (by norm_num)
theorem B3357425 : Blo 2237435 3357425 := bstep (se 2 (by rfl) ⟨1259034, by rfl⟩ : syracuseStep 3357425 = 2518069) B2518069
theorem B2238283 : Blo 2237435 2238283 := bstep (se 1 (by rfl) ⟨1678712, by rfl⟩ : syracuseStep 2238283 = 3357425) B3357425
theorem B2832833 : Blo 2237435 2832833 := bbase (se 2 (by rfl) ⟨1062312, by rfl⟩ : syracuseStep 2832833 = 2124625) (by norm_num)
theorem B7554221 : Blo 2237435 7554221 := bstep (se 3 (by rfl) ⟨1416416, by rfl⟩ : syracuseStep 7554221 = 2832833) B2832833
theorem B5036147 : Blo 2237435 5036147 := bstep (se 1 (by rfl) ⟨3777110, by rfl⟩ : syracuseStep 5036147 = 7554221) B7554221
theorem B3357431 : Blo 2237435 3357431 := bstep (se 1 (by rfl) ⟨2518073, by rfl⟩ : syracuseStep 3357431 = 5036147) B5036147
theorem B2238287 : Blo 2237435 2238287 := bstep (se 1 (by rfl) ⟨1678715, by rfl⟩ : syracuseStep 2238287 = 3357431) B3357431
theorem B3357437 : Blo 2237435 3357437 := bbase (se 3 (by rfl) ⟨629519, by rfl⟩ : syracuseStep 3357437 = 1259039) (by norm_num)
theorem B2238291 : Blo 2237435 2238291 := bstep (se 1 (by rfl) ⟨1678718, by rfl⟩ : syracuseStep 2238291 = 3357437) B3357437
theorem B5036165 : Blo 2237435 5036165 := bbase (se 4 (by rfl) ⟨472140, by rfl⟩ : syracuseStep 5036165 = 944281) (by norm_num)
theorem B3357443 : Blo 2237435 3357443 := bstep (se 1 (by rfl) ⟨2518082, by rfl⟩ : syracuseStep 3357443 = 5036165) B5036165
theorem B2238295 : Blo 2237435 2238295 := bstep (se 1 (by rfl) ⟨1678721, by rfl⟩ : syracuseStep 2238295 = 3357443) B3357443
theorem B3585325 : Blo 2237435 3585325 := bbase (se 3 (by rfl) ⟨672248, by rfl⟩ : syracuseStep 3585325 = 1344497) (by norm_num)
theorem B4780433 : Blo 2237435 4780433 := bstep (se 2 (by rfl) ⟨1792662, by rfl⟩ : syracuseStep 4780433 = 3585325) B3585325
theorem B3186955 : Blo 2237435 3186955 := bstep (se 1 (by rfl) ⟨2390216, by rfl⟩ : syracuseStep 3186955 = 4780433) B4780433
theorem B4249273 : Blo 2237435 4249273 := bstep (se 2 (by rfl) ⟨1593477, by rfl⟩ : syracuseStep 4249273 = 3186955) B3186955
theorem B5665697 : Blo 2237435 5665697 := bstep (se 2 (by rfl) ⟨2124636, by rfl⟩ : syracuseStep 5665697 = 4249273) B4249273
theorem B3777131 : Blo 2237435 3777131 := bstep (se 1 (by rfl) ⟨2832848, by rfl⟩ : syracuseStep 3777131 = 5665697) B5665697
theorem B2518087 : Blo 2237435 2518087 := bstep (se 1 (by rfl) ⟨1888565, by rfl⟩ : syracuseStep 2518087 = 3777131) B3777131
theorem B3357449 : Blo 2237435 3357449 := bstep (se 2 (by rfl) ⟨1259043, by rfl⟩ : syracuseStep 3357449 = 2518087) B2518087
theorem B2238299 : Blo 2237435 2238299 := bstep (se 1 (by rfl) ⟨1678724, by rfl⟩ : syracuseStep 2238299 = 3357449) B3357449
theorem B11331413 : Blo 2237435 11331413 := bbase (se 9 (by rfl) ⟨33197, by rfl⟩ : syracuseStep 11331413 = 66395) (by norm_num)
theorem B7554275 : Blo 2237435 7554275 := bstep (se 1 (by rfl) ⟨5665706, by rfl⟩ : syracuseStep 7554275 = 11331413) B11331413
theorem B5036183 : Blo 2237435 5036183 := bstep (se 1 (by rfl) ⟨3777137, by rfl⟩ : syracuseStep 5036183 = 7554275) B7554275
theorem B3357455 : Blo 2237435 3357455 := bstep (se 1 (by rfl) ⟨2518091, by rfl⟩ : syracuseStep 3357455 = 5036183) B5036183
theorem B2238303 : Blo 2237435 2238303 := bstep (se 1 (by rfl) ⟨1678727, by rfl⟩ : syracuseStep 2238303 = 3357455) B3357455
theorem B3357461 : Blo 2237435 3357461 := bbase (se 6 (by rfl) ⟨78690, by rfl⟩ : syracuseStep 3357461 = 157381) (by norm_num)
theorem B2238307 : Blo 2237435 2238307 := bstep (se 1 (by rfl) ⟨1678730, by rfl⟩ : syracuseStep 2238307 = 3357461) B3357461
theorem B3828685 : Blo 2237435 3828685 := bbase (se 3 (by rfl) ⟨717878, by rfl⟩ : syracuseStep 3828685 = 1435757) (by norm_num)
theorem B5104913 : Blo 2237435 5104913 := bstep (se 2 (by rfl) ⟨1914342, by rfl⟩ : syracuseStep 5104913 = 3828685) B3828685
theorem B54452405 : Blo 2237435 54452405 := bstep (se 5 (by rfl) ⟨2552456, by rfl⟩ : syracuseStep 54452405 = 5104913) B5104913
theorem B36301603 : Blo 2237435 36301603 := bstep (se 1 (by rfl) ⟨27226202, by rfl⟩ : syracuseStep 36301603 = 54452405) B54452405
theorem B48402137 : Blo 2237435 48402137 := bstep (se 2 (by rfl) ⟨18150801, by rfl⟩ : syracuseStep 48402137 = 36301603) B36301603
theorem B32268091 : Blo 2237435 32268091 := bstep (se 1 (by rfl) ⟨24201068, by rfl⟩ : syracuseStep 32268091 = 48402137) B48402137
theorem B43024121 : Blo 2237435 43024121 := bstep (se 2 (by rfl) ⟨16134045, by rfl⟩ : syracuseStep 43024121 = 32268091) B32268091
theorem B28682747 : Blo 2237435 28682747 := bstep (se 1 (by rfl) ⟨21512060, by rfl⟩ : syracuseStep 28682747 = 43024121) B43024121
theorem B19121831 : Blo 2237435 19121831 := bstep (se 1 (by rfl) ⟨14341373, by rfl⟩ : syracuseStep 19121831 = 28682747) B28682747
theorem B12747887 : Blo 2237435 12747887 := bstep (se 1 (by rfl) ⟨9560915, by rfl⟩ : syracuseStep 12747887 = 19121831) B19121831
theorem B8498591 : Blo 2237435 8498591 := bstep (se 1 (by rfl) ⟨6373943, by rfl⟩ : syracuseStep 8498591 = 12747887) B12747887
theorem B5665727 : Blo 2237435 5665727 := bstep (se 1 (by rfl) ⟨4249295, by rfl⟩ : syracuseStep 5665727 = 8498591) B8498591
theorem B3777151 : Blo 2237435 3777151 := bstep (se 1 (by rfl) ⟨2832863, by rfl⟩ : syracuseStep 3777151 = 5665727) B5665727
theorem B5036201 : Blo 2237435 5036201 := bstep (se 2 (by rfl) ⟨1888575, by rfl⟩ : syracuseStep 5036201 = 3777151) B3777151
theorem B3357467 : Blo 2237435 3357467 := bstep (se 1 (by rfl) ⟨2518100, by rfl⟩ : syracuseStep 3357467 = 5036201) B5036201
theorem B2238311 : Blo 2237435 2238311 := bstep (se 1 (by rfl) ⟨1678733, by rfl⟩ : syracuseStep 2238311 = 3357467) B3357467
theorem B2518105 : Blo 2237435 2518105 := bbase (se 2 (by rfl) ⟨944289, by rfl⟩ : syracuseStep 2518105 = 1888579) (by norm_num)
theorem B3357473 : Blo 2237435 3357473 := bstep (se 2 (by rfl) ⟨1259052, by rfl⟩ : syracuseStep 3357473 = 2518105) B2518105
theorem B2238315 : Blo 2237435 2238315 := bstep (se 1 (by rfl) ⟨1678736, by rfl⟩ : syracuseStep 2238315 = 3357473) B3357473
theorem B3828701 : Blo 2237435 3828701 := bbase (se 3 (by rfl) ⟨717881, by rfl⟩ : syracuseStep 3828701 = 1435763) (by norm_num)
theorem B2552467 : Blo 2237435 2552467 := bstep (se 1 (by rfl) ⟨1914350, by rfl⟩ : syracuseStep 2552467 = 3828701) B3828701
theorem B3403289 : Blo 2237435 3403289 := bstep (se 2 (by rfl) ⟨1276233, by rfl⟩ : syracuseStep 3403289 = 2552467) B2552467
theorem B2268859 : Blo 2237435 2268859 := bstep (se 1 (by rfl) ⟨1701644, by rfl⟩ : syracuseStep 2268859 = 3403289) B3403289
theorem B3025145 : Blo 2237435 3025145 := bstep (se 2 (by rfl) ⟨1134429, by rfl⟩ : syracuseStep 3025145 = 2268859) B2268859
theorem B8067053 : Blo 2237435 8067053 := bstep (se 3 (by rfl) ⟨1512572, by rfl⟩ : syracuseStep 8067053 = 3025145) B3025145
theorem B5378035 : Blo 2237435 5378035 := bstep (se 1 (by rfl) ⟨4033526, by rfl⟩ : syracuseStep 5378035 = 8067053) B8067053
theorem B7170713 : Blo 2237435 7170713 := bstep (se 2 (by rfl) ⟨2689017, by rfl⟩ : syracuseStep 7170713 = 5378035) B5378035
theorem B4780475 : Blo 2237435 4780475 := bstep (se 1 (by rfl) ⟨3585356, by rfl⟩ : syracuseStep 4780475 = 7170713) B7170713
theorem B3186983 : Blo 2237435 3186983 := bstep (se 1 (by rfl) ⟨2390237, by rfl⟩ : syracuseStep 3186983 = 4780475) B4780475
theorem B8498621 : Blo 2237435 8498621 := bstep (se 3 (by rfl) ⟨1593491, by rfl⟩ : syracuseStep 8498621 = 3186983) B3186983
theorem B5665747 : Blo 2237435 5665747 := bstep (se 1 (by rfl) ⟨4249310, by rfl⟩ : syracuseStep 5665747 = 8498621) B8498621
theorem B7554329 : Blo 2237435 7554329 := bstep (se 2 (by rfl) ⟨2832873, by rfl⟩ : syracuseStep 7554329 = 5665747) B5665747
theorem B5036219 : Blo 2237435 5036219 := bstep (se 1 (by rfl) ⟨3777164, by rfl⟩ : syracuseStep 5036219 = 7554329) B7554329
theorem B3357479 : Blo 2237435 3357479 := bstep (se 1 (by rfl) ⟨2518109, by rfl⟩ : syracuseStep 3357479 = 5036219) B5036219
theorem B2238319 : Blo 2237435 2238319 := bstep (se 1 (by rfl) ⟨1678739, by rfl⟩ : syracuseStep 2238319 = 3357479) B3357479
theorem B3357485 : Blo 2237435 3357485 := bbase (se 3 (by rfl) ⟨629528, by rfl⟩ : syracuseStep 3357485 = 1259057) (by norm_num)
theorem B2238323 : Blo 2237435 2238323 := bstep (se 1 (by rfl) ⟨1678742, by rfl⟩ : syracuseStep 2238323 = 3357485) B3357485
theorem B5036237 : Blo 2237435 5036237 := bbase (se 3 (by rfl) ⟨944294, by rfl⟩ : syracuseStep 5036237 = 1888589) (by norm_num)
theorem B3357491 : Blo 2237435 3357491 := bstep (se 1 (by rfl) ⟨2518118, by rfl⟩ : syracuseStep 3357491 = 5036237) B5036237
theorem B2238327 : Blo 2237435 2238327 := bstep (se 1 (by rfl) ⟨1678745, by rfl⟩ : syracuseStep 2238327 = 3357491) B3357491
theorem B2832889 : Blo 2237435 2832889 := bbase (se 2 (by rfl) ⟨1062333, by rfl⟩ : syracuseStep 2832889 = 2124667) (by norm_num)
theorem B3777185 : Blo 2237435 3777185 := bstep (se 2 (by rfl) ⟨1416444, by rfl⟩ : syracuseStep 3777185 = 2832889) B2832889
theorem B2518123 : Blo 2237435 2518123 := bstep (se 1 (by rfl) ⟨1888592, by rfl⟩ : syracuseStep 2518123 = 3777185) B3777185
theorem B3357497 : Blo 2237435 3357497 := bstep (se 2 (by rfl) ⟨1259061, by rfl⟩ : syracuseStep 3357497 = 2518123) B2518123
theorem B2238331 : Blo 2237435 2238331 := bstep (se 1 (by rfl) ⟨1678748, by rfl⟩ : syracuseStep 2238331 = 3357497) B3357497
theorem B8067109 : Blo 2237435 8067109 := bbase (se 4 (by rfl) ⟨756291, by rfl⟩ : syracuseStep 8067109 = 1512583) (by norm_num)
theorem B10756145 : Blo 2237435 10756145 := bstep (se 2 (by rfl) ⟨4033554, by rfl⟩ : syracuseStep 10756145 = 8067109) B8067109
theorem B7170763 : Blo 2237435 7170763 := bstep (se 1 (by rfl) ⟨5378072, by rfl⟩ : syracuseStep 7170763 = 10756145) B10756145
theorem B9561017 : Blo 2237435 9561017 := bstep (se 2 (by rfl) ⟨3585381, by rfl⟩ : syracuseStep 9561017 = 7170763) B7170763
theorem B25496045 : Blo 2237435 25496045 := bstep (se 3 (by rfl) ⟨4780508, by rfl⟩ : syracuseStep 25496045 = 9561017) B9561017
theorem B16997363 : Blo 2237435 16997363 := bstep (se 1 (by rfl) ⟨12748022, by rfl⟩ : syracuseStep 16997363 = 25496045) B25496045
theorem B11331575 : Blo 2237435 11331575 := bstep (se 1 (by rfl) ⟨8498681, by rfl⟩ : syracuseStep 11331575 = 16997363) B16997363
theorem B7554383 : Blo 2237435 7554383 := bstep (se 1 (by rfl) ⟨5665787, by rfl⟩ : syracuseStep 7554383 = 11331575) B11331575
theorem B5036255 : Blo 2237435 5036255 := bstep (se 1 (by rfl) ⟨3777191, by rfl⟩ : syracuseStep 5036255 = 7554383) B7554383
theorem B3357503 : Blo 2237435 3357503 := bstep (se 1 (by rfl) ⟨2518127, by rfl⟩ : syracuseStep 3357503 = 5036255) B5036255
theorem B2238335 : Blo 2237435 2238335 := bstep (se 1 (by rfl) ⟨1678751, by rfl⟩ : syracuseStep 2238335 = 3357503) B3357503
theorem B3357509 : Blo 2237435 3357509 := bbase (se 4 (by rfl) ⟨314766, by rfl⟩ : syracuseStep 3357509 = 629533) (by norm_num)
theorem B2238339 : Blo 2237435 2238339 := bstep (se 1 (by rfl) ⟨1678754, by rfl⟩ : syracuseStep 2238339 = 3357509) B3357509
theorem B3777205 : Blo 2237435 3777205 := bbase (se 5 (by rfl) ⟨177056, by rfl⟩ : syracuseStep 3777205 = 354113) (by norm_num)
theorem B5036273 : Blo 2237435 5036273 := bstep (se 2 (by rfl) ⟨1888602, by rfl⟩ : syracuseStep 5036273 = 3777205) B3777205
theorem B3357515 : Blo 2237435 3357515 := bstep (se 1 (by rfl) ⟨2518136, by rfl⟩ : syracuseStep 3357515 = 5036273) B5036273
theorem B2238343 : Blo 2237435 2238343 := bstep (se 1 (by rfl) ⟨1678757, by rfl⟩ : syracuseStep 2238343 = 3357515) B3357515
theorem B2518141 : Blo 2237435 2518141 := bbase (se 3 (by rfl) ⟨472151, by rfl⟩ : syracuseStep 2518141 = 944303) (by norm_num)
theorem B3357521 : Blo 2237435 3357521 := bstep (se 2 (by rfl) ⟨1259070, by rfl⟩ : syracuseStep 3357521 = 2518141) B2518141
theorem B2238347 : Blo 2237435 2238347 := bstep (se 1 (by rfl) ⟨1678760, by rfl⟩ : syracuseStep 2238347 = 3357521) B3357521
theorem B7554437 : Blo 2237435 7554437 := bbase (se 4 (by rfl) ⟨708228, by rfl⟩ : syracuseStep 7554437 = 1416457) (by norm_num)
theorem B5036291 : Blo 2237435 5036291 := bstep (se 1 (by rfl) ⟨3777218, by rfl⟩ : syracuseStep 5036291 = 7554437) B7554437
theorem B3357527 : Blo 2237435 3357527 := bstep (se 1 (by rfl) ⟨2518145, by rfl⟩ : syracuseStep 3357527 = 5036291) B5036291
theorem B2238351 : Blo 2237435 2238351 := bstep (se 1 (by rfl) ⟨1678763, by rfl⟩ : syracuseStep 2238351 = 3357527) B3357527
theorem B3357533 : Blo 2237435 3357533 := bbase (se 3 (by rfl) ⟨629537, by rfl⟩ : syracuseStep 3357533 = 1259075) (by norm_num)
theorem B2238355 : Blo 2237435 2238355 := bstep (se 1 (by rfl) ⟨1678766, by rfl⟩ : syracuseStep 2238355 = 3357533) B3357533
theorem B5036309 : Blo 2237435 5036309 := bbase (se 6 (by rfl) ⟨118038, by rfl⟩ : syracuseStep 5036309 = 236077) (by norm_num)
theorem B3357539 : Blo 2237435 3357539 := bstep (se 1 (by rfl) ⟨2518154, by rfl⟩ : syracuseStep 3357539 = 5036309) B5036309
theorem B2238359 : Blo 2237435 2238359 := bstep (se 1 (by rfl) ⟨1678769, by rfl⟩ : syracuseStep 2238359 = 3357539) B3357539
theorem B8498789 : Blo 2237435 8498789 := bbase (se 4 (by rfl) ⟨796761, by rfl⟩ : syracuseStep 8498789 = 1593523) (by norm_num)
theorem B5665859 : Blo 2237435 5665859 := bstep (se 1 (by rfl) ⟨4249394, by rfl⟩ : syracuseStep 5665859 = 8498789) B8498789
theorem B3777239 : Blo 2237435 3777239 := bstep (se 1 (by rfl) ⟨2832929, by rfl⟩ : syracuseStep 3777239 = 5665859) B5665859
theorem B2518159 : Blo 2237435 2518159 := bstep (se 1 (by rfl) ⟨1888619, by rfl⟩ : syracuseStep 2518159 = 3777239) B3777239
theorem B3357545 : Blo 2237435 3357545 := bstep (se 2 (by rfl) ⟨1259079, by rfl⟩ : syracuseStep 3357545 = 2518159) B2518159
theorem B2238363 : Blo 2237435 2238363 := bstep (se 1 (by rfl) ⟨1678772, by rfl⟩ : syracuseStep 2238363 = 3357545) B3357545
theorem B4033613 : Blo 2237435 4033613 := bbase (se 3 (by rfl) ⟨756302, by rfl⟩ : syracuseStep 4033613 = 1512605) (by norm_num)
theorem B2689075 : Blo 2237435 2689075 := bstep (se 1 (by rfl) ⟨2016806, by rfl⟩ : syracuseStep 2689075 = 4033613) B4033613
theorem B3585433 : Blo 2237435 3585433 := bstep (se 2 (by rfl) ⟨1344537, by rfl⟩ : syracuseStep 3585433 = 2689075) B2689075
theorem B4780577 : Blo 2237435 4780577 := bstep (se 2 (by rfl) ⟨1792716, by rfl⟩ : syracuseStep 4780577 = 3585433) B3585433
theorem B12748205 : Blo 2237435 12748205 := bstep (se 3 (by rfl) ⟨2390288, by rfl⟩ : syracuseStep 12748205 = 4780577) B4780577
theorem B8498803 : Blo 2237435 8498803 := bstep (se 1 (by rfl) ⟨6374102, by rfl⟩ : syracuseStep 8498803 = 12748205) B12748205
theorem B11331737 : Blo 2237435 11331737 := bstep (se 2 (by rfl) ⟨4249401, by rfl⟩ : syracuseStep 11331737 = 8498803) B8498803
theorem B7554491 : Blo 2237435 7554491 := bstep (se 1 (by rfl) ⟨5665868, by rfl⟩ : syracuseStep 7554491 = 11331737) B11331737
theorem B5036327 : Blo 2237435 5036327 := bstep (se 1 (by rfl) ⟨3777245, by rfl⟩ : syracuseStep 5036327 = 7554491) B7554491
theorem B3357551 : Blo 2237435 3357551 := bstep (se 1 (by rfl) ⟨2518163, by rfl⟩ : syracuseStep 3357551 = 5036327) B5036327
theorem B2238367 : Blo 2237435 2238367 := bstep (se 1 (by rfl) ⟨1678775, by rfl⟩ : syracuseStep 2238367 = 3357551) B3357551
theorem B3357557 : Blo 2237435 3357557 := bbase (se 5 (by rfl) ⟨157385, by rfl⟩ : syracuseStep 3357557 = 314771) (by norm_num)
theorem B2238371 : Blo 2237435 2238371 := bstep (se 1 (by rfl) ⟨1678778, by rfl⟩ : syracuseStep 2238371 = 3357557) B3357557
theorem B2689085 : Blo 2237435 2689085 := bbase (se 3 (by rfl) ⟨504203, by rfl⟩ : syracuseStep 2689085 = 1008407) (by norm_num)
theorem B7170893 : Blo 2237435 7170893 := bstep (se 3 (by rfl) ⟨1344542, by rfl⟩ : syracuseStep 7170893 = 2689085) B2689085
theorem B4780595 : Blo 2237435 4780595 := bstep (se 1 (by rfl) ⟨3585446, by rfl⟩ : syracuseStep 4780595 = 7170893) B7170893
theorem B3187063 : Blo 2237435 3187063 := bstep (se 1 (by rfl) ⟨2390297, by rfl⟩ : syracuseStep 3187063 = 4780595) B4780595
theorem B4249417 : Blo 2237435 4249417 := bstep (se 2 (by rfl) ⟨1593531, by rfl⟩ : syracuseStep 4249417 = 3187063) B3187063
theorem B5665889 : Blo 2237435 5665889 := bstep (se 2 (by rfl) ⟨2124708, by rfl⟩ : syracuseStep 5665889 = 4249417) B4249417
theorem B3777259 : Blo 2237435 3777259 := bstep (se 1 (by rfl) ⟨2832944, by rfl⟩ : syracuseStep 3777259 = 5665889) B5665889
theorem B5036345 : Blo 2237435 5036345 := bstep (se 2 (by rfl) ⟨1888629, by rfl⟩ : syracuseStep 5036345 = 3777259) B3777259
theorem B3357563 : Blo 2237435 3357563 := bstep (se 1 (by rfl) ⟨2518172, by rfl⟩ : syracuseStep 3357563 = 5036345) B5036345
theorem B2238375 : Blo 2237435 2238375 := bstep (se 1 (by rfl) ⟨1678781, by rfl⟩ : syracuseStep 2238375 = 3357563) B3357563
theorem B2518177 : Blo 2237435 2518177 := bbase (se 2 (by rfl) ⟨944316, by rfl⟩ : syracuseStep 2518177 = 1888633) (by norm_num)
theorem B3357569 : Blo 2237435 3357569 := bstep (se 2 (by rfl) ⟨1259088, by rfl⟩ : syracuseStep 3357569 = 2518177) B2518177
theorem B2238379 : Blo 2237435 2238379 := bstep (se 1 (by rfl) ⟨1678784, by rfl⟩ : syracuseStep 2238379 = 3357569) B3357569
theorem B5665909 : Blo 2237435 5665909 := bbase (se 5 (by rfl) ⟨265589, by rfl⟩ : syracuseStep 5665909 = 531179) (by norm_num)
theorem B7554545 : Blo 2237435 7554545 := bstep (se 2 (by rfl) ⟨2832954, by rfl⟩ : syracuseStep 7554545 = 5665909) B5665909
theorem B5036363 : Blo 2237435 5036363 := bstep (se 1 (by rfl) ⟨3777272, by rfl⟩ : syracuseStep 5036363 = 7554545) B7554545
theorem B3357575 : Blo 2237435 3357575 := bstep (se 1 (by rfl) ⟨2518181, by rfl⟩ : syracuseStep 3357575 = 5036363) B5036363
theorem B2238383 : Blo 2237435 2238383 := bstep (se 1 (by rfl) ⟨1678787, by rfl⟩ : syracuseStep 2238383 = 3357575) B3357575
theorem B3357581 : Blo 2237435 3357581 := bbase (se 3 (by rfl) ⟨629546, by rfl⟩ : syracuseStep 3357581 = 1259093) (by norm_num)
theorem B2238387 : Blo 2237435 2238387 := bstep (se 1 (by rfl) ⟨1678790, by rfl⟩ : syracuseStep 2238387 = 3357581) B3357581
theorem B5036381 : Blo 2237435 5036381 := bbase (se 3 (by rfl) ⟨944321, by rfl⟩ : syracuseStep 5036381 = 1888643) (by norm_num)
theorem B3357587 : Blo 2237435 3357587 := bstep (se 1 (by rfl) ⟨2518190, by rfl⟩ : syracuseStep 3357587 = 5036381) B5036381
theorem B2238391 : Blo 2237435 2238391 := bstep (se 1 (by rfl) ⟨1678793, by rfl⟩ : syracuseStep 2238391 = 3357587) B3357587
theorem B3777293 : Blo 2237435 3777293 := bbase (se 3 (by rfl) ⟨708242, by rfl⟩ : syracuseStep 3777293 = 1416485) (by norm_num)
theorem B2518195 : Blo 2237435 2518195 := bstep (se 1 (by rfl) ⟨1888646, by rfl⟩ : syracuseStep 2518195 = 3777293) B3777293
theorem B3357593 : Blo 2237435 3357593 := bstep (se 2 (by rfl) ⟨1259097, by rfl⟩ : syracuseStep 3357593 = 2518195) B2518195
theorem B2238395 : Blo 2237435 2238395 := bstep (se 1 (by rfl) ⟨1678796, by rfl⟩ : syracuseStep 2238395 = 3357593) B3357593
theorem B19122581 : Blo 2237435 19122581 := bbase (se 6 (by rfl) ⟨448185, by rfl⟩ : syracuseStep 19122581 = 896371) (by norm_num)
theorem B12748387 : Blo 2237435 12748387 := bstep (se 1 (by rfl) ⟨9561290, by rfl⟩ : syracuseStep 12748387 = 19122581) B19122581
theorem B16997849 : Blo 2237435 16997849 := bstep (se 2 (by rfl) ⟨6374193, by rfl⟩ : syracuseStep 16997849 = 12748387) B12748387
theorem B11331899 : Blo 2237435 11331899 := bstep (se 1 (by rfl) ⟨8498924, by rfl⟩ : syracuseStep 11331899 = 16997849) B16997849
theorem B7554599 : Blo 2237435 7554599 := bstep (se 1 (by rfl) ⟨5665949, by rfl⟩ : syracuseStep 7554599 = 11331899) B11331899
theorem B5036399 : Blo 2237435 5036399 := bstep (se 1 (by rfl) ⟨3777299, by rfl⟩ : syracuseStep 5036399 = 7554599) B7554599
theorem B3357599 : Blo 2237435 3357599 := bstep (se 1 (by rfl) ⟨2518199, by rfl⟩ : syracuseStep 3357599 = 5036399) B5036399
theorem B2238399 : Blo 2237435 2238399 := bstep (se 1 (by rfl) ⟨1678799, by rfl⟩ : syracuseStep 2238399 = 3357599) B3357599
theorem B3357605 : Blo 2237435 3357605 := bbase (se 4 (by rfl) ⟨314775, by rfl⟩ : syracuseStep 3357605 = 629551) (by norm_num)
theorem B2238403 : Blo 2237435 2238403 := bstep (se 1 (by rfl) ⟨1678802, by rfl⟩ : syracuseStep 2238403 = 3357605) B3357605
theorem B2832985 : Blo 2237435 2832985 := bbase (se 2 (by rfl) ⟨1062369, by rfl⟩ : syracuseStep 2832985 = 2124739) (by norm_num)
theorem B3777313 : Blo 2237435 3777313 := bstep (se 2 (by rfl) ⟨1416492, by rfl⟩ : syracuseStep 3777313 = 2832985) B2832985
theorem B5036417 : Blo 2237435 5036417 := bstep (se 2 (by rfl) ⟨1888656, by rfl⟩ : syracuseStep 5036417 = 3777313) B3777313
theorem B3357611 : Blo 2237435 3357611 := bstep (se 1 (by rfl) ⟨2518208, by rfl⟩ : syracuseStep 3357611 = 5036417) B5036417
theorem B2238407 : Blo 2237435 2238407 := bstep (se 1 (by rfl) ⟨1678805, by rfl⟩ : syracuseStep 2238407 = 3357611) B3357611
theorem B2518213 : Blo 2237435 2518213 := bbase (se 4 (by rfl) ⟨236082, by rfl⟩ : syracuseStep 2518213 = 472165) (by norm_num)
theorem B3357617 : Blo 2237435 3357617 := bstep (se 2 (by rfl) ⟨1259106, by rfl⟩ : syracuseStep 3357617 = 2518213) B2518213
theorem B2238411 : Blo 2237435 2238411 := bstep (se 1 (by rfl) ⟨1678808, by rfl⟩ : syracuseStep 2238411 = 3357617) B3357617
theorem B4249493 : Blo 2237435 4249493 := bbase (se 6 (by rfl) ⟨99597, by rfl⟩ : syracuseStep 4249493 = 199195) (by norm_num)
theorem B2832995 : Blo 2237435 2832995 := bstep (se 1 (by rfl) ⟨2124746, by rfl⟩ : syracuseStep 2832995 = 4249493) B4249493
theorem B7554653 : Blo 2237435 7554653 := bstep (se 3 (by rfl) ⟨1416497, by rfl⟩ : syracuseStep 7554653 = 2832995) B2832995
theorem B5036435 : Blo 2237435 5036435 := bstep (se 1 (by rfl) ⟨3777326, by rfl⟩ : syracuseStep 5036435 = 7554653) B7554653
theorem B3357623 : Blo 2237435 3357623 := bstep (se 1 (by rfl) ⟨2518217, by rfl⟩ : syracuseStep 3357623 = 5036435) B5036435
theorem B2238415 : Blo 2237435 2238415 := bstep (se 1 (by rfl) ⟨1678811, by rfl⟩ : syracuseStep 2238415 = 3357623) B3357623
theorem B3357629 : Blo 2237435 3357629 := bbase (se 3 (by rfl) ⟨629555, by rfl⟩ : syracuseStep 3357629 = 1259111) (by norm_num)
theorem B2238419 : Blo 2237435 2238419 := bstep (se 1 (by rfl) ⟨1678814, by rfl⟩ : syracuseStep 2238419 = 3357629) B3357629
theorem B5036453 : Blo 2237435 5036453 := bbase (se 4 (by rfl) ⟨472167, by rfl⟩ : syracuseStep 5036453 = 944335) (by norm_num)
theorem B3357635 : Blo 2237435 3357635 := bstep (se 1 (by rfl) ⟨2518226, by rfl⟩ : syracuseStep 3357635 = 5036453) B5036453
theorem B2238423 : Blo 2237435 2238423 := bstep (se 1 (by rfl) ⟨1678817, by rfl⟩ : syracuseStep 2238423 = 3357635) B3357635
theorem B5666021 : Blo 2237435 5666021 := bbase (se 4 (by rfl) ⟨531189, by rfl⟩ : syracuseStep 5666021 = 1062379) (by norm_num)
theorem B3777347 : Blo 2237435 3777347 := bstep (se 1 (by rfl) ⟨2833010, by rfl⟩ : syracuseStep 3777347 = 5666021) B5666021
theorem B2518231 : Blo 2237435 2518231 := bstep (se 1 (by rfl) ⟨1888673, by rfl⟩ : syracuseStep 2518231 = 3777347) B3777347
theorem B3357641 : Blo 2237435 3357641 := bstep (se 2 (by rfl) ⟨1259115, by rfl⟩ : syracuseStep 3357641 = 2518231) B2518231
theorem B2238427 : Blo 2237435 2238427 := bstep (se 1 (by rfl) ⟨1678820, by rfl⟩ : syracuseStep 2238427 = 3357641) B3357641
theorem B2390357 : Blo 2237435 2390357 := bbase (se 10 (by rfl) ⟨3501, by rfl⟩ : syracuseStep 2390357 = 7003) (by norm_num)
theorem B6374285 : Blo 2237435 6374285 := bstep (se 3 (by rfl) ⟨1195178, by rfl⟩ : syracuseStep 6374285 = 2390357) B2390357
theorem B4249523 : Blo 2237435 4249523 := bstep (se 1 (by rfl) ⟨3187142, by rfl⟩ : syracuseStep 4249523 = 6374285) B6374285
theorem B11332061 : Blo 2237435 11332061 := bstep (se 3 (by rfl) ⟨2124761, by rfl⟩ : syracuseStep 11332061 = 4249523) B4249523
theorem B7554707 : Blo 2237435 7554707 := bstep (se 1 (by rfl) ⟨5666030, by rfl⟩ : syracuseStep 7554707 = 11332061) B11332061
theorem B5036471 : Blo 2237435 5036471 := bstep (se 1 (by rfl) ⟨3777353, by rfl⟩ : syracuseStep 5036471 = 7554707) B7554707
theorem B3357647 : Blo 2237435 3357647 := bstep (se 1 (by rfl) ⟨2518235, by rfl⟩ : syracuseStep 3357647 = 5036471) B5036471
theorem B2238431 : Blo 2237435 2238431 := bstep (se 1 (by rfl) ⟨1678823, by rfl⟩ : syracuseStep 2238431 = 3357647) B3357647
theorem B3357653 : Blo 2237435 3357653 := bbase (se 7 (by rfl) ⟨39347, by rfl⟩ : syracuseStep 3357653 = 78695) (by norm_num)
theorem B2238435 : Blo 2237435 2238435 := bstep (se 1 (by rfl) ⟨1678826, by rfl⟩ : syracuseStep 2238435 = 3357653) B3357653
theorem B8499077 : Blo 2237435 8499077 := bbase (se 4 (by rfl) ⟨796788, by rfl⟩ : syracuseStep 8499077 = 1593577) (by norm_num)
theorem B5666051 : Blo 2237435 5666051 := bstep (se 1 (by rfl) ⟨4249538, by rfl⟩ : syracuseStep 5666051 = 8499077) B8499077
theorem B3777367 : Blo 2237435 3777367 := bstep (se 1 (by rfl) ⟨2833025, by rfl⟩ : syracuseStep 3777367 = 5666051) B5666051
theorem B5036489 : Blo 2237435 5036489 := bstep (se 2 (by rfl) ⟨1888683, by rfl⟩ : syracuseStep 5036489 = 3777367) B3777367
theorem B3357659 : Blo 2237435 3357659 := bstep (se 1 (by rfl) ⟨2518244, by rfl⟩ : syracuseStep 3357659 = 5036489) B5036489
theorem B2238439 : Blo 2237435 2238439 := bstep (se 1 (by rfl) ⟨1678829, by rfl⟩ : syracuseStep 2238439 = 3357659) B3357659
theorem B2518249 : Blo 2237435 2518249 := bbase (se 2 (by rfl) ⟨944343, by rfl⟩ : syracuseStep 2518249 = 1888687) (by norm_num)
theorem B3357665 : Blo 2237435 3357665 := bstep (se 2 (by rfl) ⟨1259124, by rfl⟩ : syracuseStep 3357665 = 2518249) B2518249
theorem B2238443 : Blo 2237435 2238443 := bstep (se 1 (by rfl) ⟨1678832, by rfl⟩ : syracuseStep 2238443 = 3357665) B3357665
theorem B12748661 : Blo 2237435 12748661 := bbase (se 5 (by rfl) ⟨597593, by rfl⟩ : syracuseStep 12748661 = 1195187) (by norm_num)
theorem B8499107 : Blo 2237435 8499107 := bstep (se 1 (by rfl) ⟨6374330, by rfl⟩ : syracuseStep 8499107 = 12748661) B12748661
theorem B5666071 : Blo 2237435 5666071 := bstep (se 1 (by rfl) ⟨4249553, by rfl⟩ : syracuseStep 5666071 = 8499107) B8499107
theorem B7554761 : Blo 2237435 7554761 := bstep (se 2 (by rfl) ⟨2833035, by rfl⟩ : syracuseStep 7554761 = 5666071) B5666071
theorem B5036507 : Blo 2237435 5036507 := bstep (se 1 (by rfl) ⟨3777380, by rfl⟩ : syracuseStep 5036507 = 7554761) B7554761
theorem B3357671 : Blo 2237435 3357671 := bstep (se 1 (by rfl) ⟨2518253, by rfl⟩ : syracuseStep 3357671 = 5036507) B5036507
theorem B2238447 : Blo 2237435 2238447 := bstep (se 1 (by rfl) ⟨1678835, by rfl⟩ : syracuseStep 2238447 = 3357671) B3357671
theorem B3357677 : Blo 2237435 3357677 := bbase (se 3 (by rfl) ⟨629564, by rfl⟩ : syracuseStep 3357677 = 1259129) (by norm_num)
theorem B2238451 : Blo 2237435 2238451 := bstep (se 1 (by rfl) ⟨1678838, by rfl⟩ : syracuseStep 2238451 = 3357677) B3357677
theorem B5036525 : Blo 2237435 5036525 := bbase (se 3 (by rfl) ⟨944348, by rfl⟩ : syracuseStep 5036525 = 1888697) (by norm_num)
theorem B3357683 : Blo 2237435 3357683 := bstep (se 1 (by rfl) ⟨2518262, by rfl⟩ : syracuseStep 3357683 = 5036525) B5036525
theorem B2238455 : Blo 2237435 2238455 := bstep (se 1 (by rfl) ⟨1678841, by rfl⟩ : syracuseStep 2238455 = 3357683) B3357683
theorem B17230229 : Blo 2237435 17230229 := bbase (se 6 (by rfl) ⟨403833, by rfl⟩ : syracuseStep 17230229 = 807667) (by norm_num)
theorem B11486819 : Blo 2237435 11486819 := bstep (se 1 (by rfl) ⟨8615114, by rfl⟩ : syracuseStep 11486819 = 17230229) B17230229
theorem B30631517 : Blo 2237435 30631517 := bstep (se 3 (by rfl) ⟨5743409, by rfl⟩ : syracuseStep 30631517 = 11486819) B11486819
theorem B20421011 : Blo 2237435 20421011 := bstep (se 1 (by rfl) ⟨15315758, by rfl⟩ : syracuseStep 20421011 = 30631517) B30631517
theorem B13614007 : Blo 2237435 13614007 := bstep (se 1 (by rfl) ⟨10210505, by rfl⟩ : syracuseStep 13614007 = 20421011) B20421011
theorem B18152009 : Blo 2237435 18152009 := bstep (se 2 (by rfl) ⟨6807003, by rfl⟩ : syracuseStep 18152009 = 13614007) B13614007
theorem B12101339 : Blo 2237435 12101339 := bstep (se 1 (by rfl) ⟨9076004, by rfl⟩ : syracuseStep 12101339 = 18152009) B18152009
theorem B8067559 : Blo 2237435 8067559 := bstep (se 1 (by rfl) ⟨6050669, by rfl⟩ : syracuseStep 8067559 = 12101339) B12101339
theorem B10756745 : Blo 2237435 10756745 := bstep (se 2 (by rfl) ⟨4033779, by rfl⟩ : syracuseStep 10756745 = 8067559) B8067559
theorem B7171163 : Blo 2237435 7171163 := bstep (se 1 (by rfl) ⟨5378372, by rfl⟩ : syracuseStep 7171163 = 10756745) B10756745
theorem B4780775 : Blo 2237435 4780775 := bstep (se 1 (by rfl) ⟨3585581, by rfl⟩ : syracuseStep 4780775 = 7171163) B7171163
theorem B3187183 : Blo 2237435 3187183 := bstep (se 1 (by rfl) ⟨2390387, by rfl⟩ : syracuseStep 3187183 = 4780775) B4780775
theorem B4249577 : Blo 2237435 4249577 := bstep (se 2 (by rfl) ⟨1593591, by rfl⟩ : syracuseStep 4249577 = 3187183) B3187183
theorem B2833051 : Blo 2237435 2833051 := bstep (se 1 (by rfl) ⟨2124788, by rfl⟩ : syracuseStep 2833051 = 4249577) B4249577
theorem B3777401 : Blo 2237435 3777401 := bstep (se 2 (by rfl) ⟨1416525, by rfl⟩ : syracuseStep 3777401 = 2833051) B2833051
theorem B2518267 : Blo 2237435 2518267 := bstep (se 1 (by rfl) ⟨1888700, by rfl⟩ : syracuseStep 2518267 = 3777401) B3777401
theorem B3357689 : Blo 2237435 3357689 := bstep (se 2 (by rfl) ⟨1259133, by rfl⟩ : syracuseStep 3357689 = 2518267) B2518267
theorem B2238459 : Blo 2237435 2238459 := bstep (se 1 (by rfl) ⟨1678844, by rfl⟩ : syracuseStep 2238459 = 3357689) B3357689
theorem B7570613 : Blo 2237435 7570613 := bbase (se 5 (by rfl) ⟨354872, by rfl⟩ : syracuseStep 7570613 = 709745) (by norm_num)
theorem B5047075 : Blo 2237435 5047075 := bstep (se 1 (by rfl) ⟨3785306, by rfl⟩ : syracuseStep 5047075 = 7570613) B7570613
theorem B26917733 : Blo 2237435 26917733 := bstep (se 4 (by rfl) ⟨2523537, by rfl⟩ : syracuseStep 26917733 = 5047075) B5047075
theorem B17945155 : Blo 2237435 17945155 := bstep (se 1 (by rfl) ⟨13458866, by rfl⟩ : syracuseStep 17945155 = 26917733) B26917733
theorem B23926873 : Blo 2237435 23926873 := bstep (se 2 (by rfl) ⟨8972577, by rfl⟩ : syracuseStep 23926873 = 17945155) B17945155
theorem B31902497 : Blo 2237435 31902497 := bstep (se 2 (by rfl) ⟨11963436, by rfl⟩ : syracuseStep 31902497 = 23926873) B23926873
theorem B21268331 : Blo 2237435 21268331 := bstep (se 1 (by rfl) ⟨15951248, by rfl⟩ : syracuseStep 21268331 = 31902497) B31902497
theorem B14178887 : Blo 2237435 14178887 := bstep (se 1 (by rfl) ⟨10634165, by rfl⟩ : syracuseStep 14178887 = 21268331) B21268331
theorem B9452591 : Blo 2237435 9452591 := bstep (se 1 (by rfl) ⟨7089443, by rfl⟩ : syracuseStep 9452591 = 14178887) B14178887
theorem B6301727 : Blo 2237435 6301727 := bstep (se 1 (by rfl) ⟨4726295, by rfl⟩ : syracuseStep 6301727 = 9452591) B9452591
theorem B4201151 : Blo 2237435 4201151 := bstep (se 1 (by rfl) ⟨3150863, by rfl⟩ : syracuseStep 4201151 = 6301727) B6301727
theorem B11203069 : Blo 2237435 11203069 := bstep (se 3 (by rfl) ⟨2100575, by rfl⟩ : syracuseStep 11203069 = 4201151) B4201151
theorem B14937425 : Blo 2237435 14937425 := bstep (se 2 (by rfl) ⟨5601534, by rfl⟩ : syracuseStep 14937425 = 11203069) B11203069
theorem B9958283 : Blo 2237435 9958283 := bstep (se 1 (by rfl) ⟨7468712, by rfl⟩ : syracuseStep 9958283 = 14937425) B14937425
theorem B6638855 : Blo 2237435 6638855 := bstep (se 1 (by rfl) ⟨4979141, by rfl⟩ : syracuseStep 6638855 = 9958283) B9958283
theorem B17703613 : Blo 2237435 17703613 := bstep (se 3 (by rfl) ⟨3319427, by rfl⟩ : syracuseStep 17703613 = 6638855) B6638855
theorem B94419269 : Blo 2237435 94419269 := bstep (se 4 (by rfl) ⟨8851806, by rfl⟩ : syracuseStep 94419269 = 17703613) B17703613
theorem B62946179 : Blo 2237435 62946179 := bstep (se 1 (by rfl) ⟨47209634, by rfl⟩ : syracuseStep 62946179 = 94419269) B94419269
theorem B41964119 : Blo 2237435 41964119 := bstep (se 1 (by rfl) ⟨31473089, by rfl⟩ : syracuseStep 41964119 = 62946179) B62946179
theorem B27976079 : Blo 2237435 27976079 := bstep (se 1 (by rfl) ⟨20982059, by rfl⟩ : syracuseStep 27976079 = 41964119) B41964119
theorem B18650719 : Blo 2237435 18650719 := bstep (se 1 (by rfl) ⟨13988039, by rfl⟩ : syracuseStep 18650719 = 27976079) B27976079
theorem B99470501 : Blo 2237435 99470501 := bstep (se 4 (by rfl) ⟨9325359, by rfl⟩ : syracuseStep 99470501 = 18650719) B18650719
theorem B66313667 : Blo 2237435 66313667 := bstep (se 1 (by rfl) ⟨49735250, by rfl⟩ : syracuseStep 66313667 = 99470501) B99470501
theorem B44209111 : Blo 2237435 44209111 := bstep (se 1 (by rfl) ⟨33156833, by rfl⟩ : syracuseStep 44209111 = 66313667) B66313667
theorem B58945481 : Blo 2237435 58945481 := bstep (se 2 (by rfl) ⟨22104555, by rfl⟩ : syracuseStep 58945481 = 44209111) B44209111
theorem B39296987 : Blo 2237435 39296987 := bstep (se 1 (by rfl) ⟨29472740, by rfl⟩ : syracuseStep 39296987 = 58945481) B58945481
theorem B26197991 : Blo 2237435 26197991 := bstep (se 1 (by rfl) ⟨19648493, by rfl⟩ : syracuseStep 26197991 = 39296987) B39296987
theorem B17465327 : Blo 2237435 17465327 := bstep (se 1 (by rfl) ⟨13098995, by rfl⟩ : syracuseStep 17465327 = 26197991) B26197991
theorem B11643551 : Blo 2237435 11643551 := bstep (se 1 (by rfl) ⟨8732663, by rfl⟩ : syracuseStep 11643551 = 17465327) B17465327
theorem B124197877 : Blo 2237435 124197877 := bstep (se 5 (by rfl) ⟨5821775, by rfl⟩ : syracuseStep 124197877 = 11643551) B11643551
theorem B165597169 : Blo 2237435 165597169 := bstep (se 2 (by rfl) ⟨62098938, by rfl⟩ : syracuseStep 165597169 = 124197877) B124197877
theorem B220796225 : Blo 2237435 220796225 := bstep (se 2 (by rfl) ⟨82798584, by rfl⟩ : syracuseStep 220796225 = 165597169) B165597169
theorem B147197483 : Blo 2237435 147197483 := bstep (se 1 (by rfl) ⟨110398112, by rfl⟩ : syracuseStep 147197483 = 220796225) B220796225
theorem B98131655 : Blo 2237435 98131655 := bstep (se 1 (by rfl) ⟨73598741, by rfl⟩ : syracuseStep 98131655 = 147197483) B147197483
theorem B65421103 : Blo 2237435 65421103 := bstep (se 1 (by rfl) ⟨49065827, by rfl⟩ : syracuseStep 65421103 = 98131655) B98131655
theorem B87228137 : Blo 2237435 87228137 := bstep (se 2 (by rfl) ⟨32710551, by rfl⟩ : syracuseStep 87228137 = 65421103) B65421103
theorem B58152091 : Blo 2237435 58152091 := bstep (se 1 (by rfl) ⟨43614068, by rfl⟩ : syracuseStep 58152091 = 87228137) B87228137
theorem B77536121 : Blo 2237435 77536121 := bstep (se 2 (by rfl) ⟨29076045, by rfl⟩ : syracuseStep 77536121 = 58152091) B58152091
theorem B206762989 : Blo 2237435 206762989 := bstep (se 3 (by rfl) ⟨38768060, by rfl⟩ : syracuseStep 206762989 = 77536121) B77536121
theorem B275683985 : Blo 2237435 275683985 := bstep (se 2 (by rfl) ⟨103381494, by rfl⟩ : syracuseStep 275683985 = 206762989) B206762989
theorem B183789323 : Blo 2237435 183789323 := bstep (se 1 (by rfl) ⟨137841992, by rfl⟩ : syracuseStep 183789323 = 275683985) B275683985
theorem B122526215 : Blo 2237435 122526215 := bstep (se 1 (by rfl) ⟨91894661, by rfl⟩ : syracuseStep 122526215 = 183789323) B183789323
theorem B81684143 : Blo 2237435 81684143 := bstep (se 1 (by rfl) ⟨61263107, by rfl⟩ : syracuseStep 81684143 = 122526215) B122526215
theorem B54456095 : Blo 2237435 54456095 := bstep (se 1 (by rfl) ⟨40842071, by rfl⟩ : syracuseStep 54456095 = 81684143) B81684143
theorem B145216253 : Blo 2237435 145216253 := bstep (se 3 (by rfl) ⟨27228047, by rfl⟩ : syracuseStep 145216253 = 54456095) B54456095
theorem B96810835 : Blo 2237435 96810835 := bstep (se 1 (by rfl) ⟨72608126, by rfl⟩ : syracuseStep 96810835 = 145216253) B145216253
theorem B129081113 : Blo 2237435 129081113 := bstep (se 2 (by rfl) ⟨48405417, by rfl⟩ : syracuseStep 129081113 = 96810835) B96810835
theorem B86054075 : Blo 2237435 86054075 := bstep (se 1 (by rfl) ⟨64540556, by rfl⟩ : syracuseStep 86054075 = 129081113) B129081113
theorem B57369383 : Blo 2237435 57369383 := bstep (se 1 (by rfl) ⟨43027037, by rfl⟩ : syracuseStep 57369383 = 86054075) B86054075
theorem B38246255 : Blo 2237435 38246255 := bstep (se 1 (by rfl) ⟨28684691, by rfl⟩ : syracuseStep 38246255 = 57369383) B57369383
theorem B25497503 : Blo 2237435 25497503 := bstep (se 1 (by rfl) ⟨19123127, by rfl⟩ : syracuseStep 25497503 = 38246255) B38246255
theorem B16998335 : Blo 2237435 16998335 := bstep (se 1 (by rfl) ⟨12748751, by rfl⟩ : syracuseStep 16998335 = 25497503) B25497503
theorem B11332223 : Blo 2237435 11332223 := bstep (se 1 (by rfl) ⟨8499167, by rfl⟩ : syracuseStep 11332223 = 16998335) B16998335
theorem B7554815 : Blo 2237435 7554815 := bstep (se 1 (by rfl) ⟨5666111, by rfl⟩ : syracuseStep 7554815 = 11332223) B11332223
theorem B5036543 : Blo 2237435 5036543 := bstep (se 1 (by rfl) ⟨3777407, by rfl⟩ : syracuseStep 5036543 = 7554815) B7554815
theorem B3357695 : Blo 2237435 3357695 := bstep (se 1 (by rfl) ⟨2518271, by rfl⟩ : syracuseStep 3357695 = 5036543) B5036543
theorem B2238463 : Blo 2237435 2238463 := bstep (se 1 (by rfl) ⟨1678847, by rfl⟩ : syracuseStep 2238463 = 3357695) B3357695
theorem B3357701 : Blo 2237435 3357701 := bbase (se 4 (by rfl) ⟨314784, by rfl⟩ : syracuseStep 3357701 = 629569) (by norm_num)
theorem B2238467 : Blo 2237435 2238467 := bstep (se 1 (by rfl) ⟨1678850, by rfl⟩ : syracuseStep 2238467 = 3357701) B3357701
theorem B3777421 : Blo 2237435 3777421 := bbase (se 3 (by rfl) ⟨708266, by rfl⟩ : syracuseStep 3777421 = 1416533) (by norm_num)
theorem B5036561 : Blo 2237435 5036561 := bstep (se 2 (by rfl) ⟨1888710, by rfl⟩ : syracuseStep 5036561 = 3777421) B3777421
theorem B3357707 : Blo 2237435 3357707 := bstep (se 1 (by rfl) ⟨2518280, by rfl⟩ : syracuseStep 3357707 = 5036561) B5036561
theorem B2238471 : Blo 2237435 2238471 := bstep (se 1 (by rfl) ⟨1678853, by rfl⟩ : syracuseStep 2238471 = 3357707) B3357707
theorem B2518285 : Blo 2237435 2518285 := bbase (se 3 (by rfl) ⟨472178, by rfl⟩ : syracuseStep 2518285 = 944357) (by norm_num)
theorem B3357713 : Blo 2237435 3357713 := bstep (se 2 (by rfl) ⟨1259142, by rfl⟩ : syracuseStep 3357713 = 2518285) B2518285
theorem B2238475 : Blo 2237435 2238475 := bstep (se 1 (by rfl) ⟨1678856, by rfl⟩ : syracuseStep 2238475 = 3357713) B3357713
theorem B7554869 : Blo 2237435 7554869 := bbase (se 5 (by rfl) ⟨354134, by rfl⟩ : syracuseStep 7554869 = 708269) (by norm_num)
theorem B5036579 : Blo 2237435 5036579 := bstep (se 1 (by rfl) ⟨3777434, by rfl⟩ : syracuseStep 5036579 = 7554869) B7554869
theorem B3357719 : Blo 2237435 3357719 := bstep (se 1 (by rfl) ⟨2518289, by rfl⟩ : syracuseStep 3357719 = 5036579) B5036579
theorem B2238479 : Blo 2237435 2238479 := bstep (se 1 (by rfl) ⟨1678859, by rfl⟩ : syracuseStep 2238479 = 3357719) B3357719
theorem B3357725 : Blo 2237435 3357725 := bbase (se 3 (by rfl) ⟨629573, by rfl⟩ : syracuseStep 3357725 = 1259147) (by norm_num)
theorem B2238483 : Blo 2237435 2238483 := bstep (se 1 (by rfl) ⟨1678862, by rfl⟩ : syracuseStep 2238483 = 3357725) B3357725
theorem B5036597 : Blo 2237435 5036597 := bbase (se 5 (by rfl) ⟨236090, by rfl⟩ : syracuseStep 5036597 = 472181) (by norm_num)
theorem B3357731 : Blo 2237435 3357731 := bstep (se 1 (by rfl) ⟨2518298, by rfl⟩ : syracuseStep 3357731 = 5036597) B5036597
theorem B2238487 : Blo 2237435 2238487 := bstep (se 1 (by rfl) ⟨1678865, by rfl⟩ : syracuseStep 2238487 = 3357731) B3357731
theorem B9561685 : Blo 2237435 9561685 := bbase (se 8 (by rfl) ⟨56025, by rfl⟩ : syracuseStep 9561685 = 112051) (by norm_num)
theorem B12748913 : Blo 2237435 12748913 := bstep (se 2 (by rfl) ⟨4780842, by rfl⟩ : syracuseStep 12748913 = 9561685) B9561685
theorem B8499275 : Blo 2237435 8499275 := bstep (se 1 (by rfl) ⟨6374456, by rfl⟩ : syracuseStep 8499275 = 12748913) B12748913
theorem B5666183 : Blo 2237435 5666183 := bstep (se 1 (by rfl) ⟨4249637, by rfl⟩ : syracuseStep 5666183 = 8499275) B8499275
theorem B3777455 : Blo 2237435 3777455 := bstep (se 1 (by rfl) ⟨2833091, by rfl⟩ : syracuseStep 3777455 = 5666183) B5666183
theorem B2518303 : Blo 2237435 2518303 := bstep (se 1 (by rfl) ⟨1888727, by rfl⟩ : syracuseStep 2518303 = 3777455) B3777455
theorem B3357737 : Blo 2237435 3357737 := bstep (se 2 (by rfl) ⟨1259151, by rfl⟩ : syracuseStep 3357737 = 2518303) B2518303
theorem B2238491 : Blo 2237435 2238491 := bstep (se 1 (by rfl) ⟨1678868, by rfl⟩ : syracuseStep 2238491 = 3357737) B3357737
theorem B9561701 : Blo 2237435 9561701 := bbase (se 4 (by rfl) ⟨896409, by rfl⟩ : syracuseStep 9561701 = 1792819) (by norm_num)
theorem B6374467 : Blo 2237435 6374467 := bstep (se 1 (by rfl) ⟨4780850, by rfl⟩ : syracuseStep 6374467 = 9561701) B9561701
theorem B8499289 : Blo 2237435 8499289 := bstep (se 2 (by rfl) ⟨3187233, by rfl⟩ : syracuseStep 8499289 = 6374467) B6374467
theorem B11332385 : Blo 2237435 11332385 := bstep (se 2 (by rfl) ⟨4249644, by rfl⟩ : syracuseStep 11332385 = 8499289) B8499289
theorem B7554923 : Blo 2237435 7554923 := bstep (se 1 (by rfl) ⟨5666192, by rfl⟩ : syracuseStep 7554923 = 11332385) B11332385
theorem B5036615 : Blo 2237435 5036615 := bstep (se 1 (by rfl) ⟨3777461, by rfl⟩ : syracuseStep 5036615 = 7554923) B7554923
theorem B3357743 : Blo 2237435 3357743 := bstep (se 1 (by rfl) ⟨2518307, by rfl⟩ : syracuseStep 3357743 = 5036615) B5036615
theorem B2238495 : Blo 2237435 2238495 := bstep (se 1 (by rfl) ⟨1678871, by rfl⟩ : syracuseStep 2238495 = 3357743) B3357743
theorem B3357749 : Blo 2237435 3357749 := bbase (se 5 (by rfl) ⟨157394, by rfl⟩ : syracuseStep 3357749 = 314789) (by norm_num)
theorem B2238499 : Blo 2237435 2238499 := bstep (se 1 (by rfl) ⟨1678874, by rfl⟩ : syracuseStep 2238499 = 3357749) B3357749
theorem B5666213 : Blo 2237435 5666213 := bbase (se 4 (by rfl) ⟨531207, by rfl⟩ : syracuseStep 5666213 = 1062415) (by norm_num)
theorem B3777475 : Blo 2237435 3777475 := bstep (se 1 (by rfl) ⟨2833106, by rfl⟩ : syracuseStep 3777475 = 5666213) B5666213
theorem B5036633 : Blo 2237435 5036633 := bstep (se 2 (by rfl) ⟨1888737, by rfl⟩ : syracuseStep 5036633 = 3777475) B3777475
theorem B3357755 : Blo 2237435 3357755 := bstep (se 1 (by rfl) ⟨2518316, by rfl⟩ : syracuseStep 3357755 = 5036633) B5036633
theorem B2238503 : Blo 2237435 2238503 := bstep (se 1 (by rfl) ⟨1678877, by rfl⟩ : syracuseStep 2238503 = 3357755) B3357755
theorem B2518321 : Blo 2237435 2518321 := bbase (se 2 (by rfl) ⟨944370, by rfl⟩ : syracuseStep 2518321 = 1888741) (by norm_num)
theorem B3357761 : Blo 2237435 3357761 := bstep (se 2 (by rfl) ⟨1259160, by rfl⟩ : syracuseStep 3357761 = 2518321) B2518321
theorem B2238507 : Blo 2237435 2238507 := bstep (se 1 (by rfl) ⟨1678880, by rfl⟩ : syracuseStep 2238507 = 3357761) B3357761
theorem B4780885 : Blo 2237435 4780885 := bbase (se 9 (by rfl) ⟨14006, by rfl⟩ : syracuseStep 4780885 = 28013) (by norm_num)
theorem B6374513 : Blo 2237435 6374513 := bstep (se 2 (by rfl) ⟨2390442, by rfl⟩ : syracuseStep 6374513 = 4780885) B4780885
theorem B4249675 : Blo 2237435 4249675 := bstep (se 1 (by rfl) ⟨3187256, by rfl⟩ : syracuseStep 4249675 = 6374513) B6374513
theorem B5666233 : Blo 2237435 5666233 := bstep (se 2 (by rfl) ⟨2124837, by rfl⟩ : syracuseStep 5666233 = 4249675) B4249675
theorem B7554977 : Blo 2237435 7554977 := bstep (se 2 (by rfl) ⟨2833116, by rfl⟩ : syracuseStep 7554977 = 5666233) B5666233
theorem B5036651 : Blo 2237435 5036651 := bstep (se 1 (by rfl) ⟨3777488, by rfl⟩ : syracuseStep 5036651 = 7554977) B7554977
theorem B3357767 : Blo 2237435 3357767 := bstep (se 1 (by rfl) ⟨2518325, by rfl⟩ : syracuseStep 3357767 = 5036651) B5036651
theorem B2238511 : Blo 2237435 2238511 := bstep (se 1 (by rfl) ⟨1678883, by rfl⟩ : syracuseStep 2238511 = 3357767) B3357767
theorem B3357773 : Blo 2237435 3357773 := bbase (se 3 (by rfl) ⟨629582, by rfl⟩ : syracuseStep 3357773 = 1259165) (by norm_num)
theorem B2238515 : Blo 2237435 2238515 := bstep (se 1 (by rfl) ⟨1678886, by rfl⟩ : syracuseStep 2238515 = 3357773) B3357773
theorem B5036669 : Blo 2237435 5036669 := bbase (se 3 (by rfl) ⟨944375, by rfl⟩ : syracuseStep 5036669 = 1888751) (by norm_num)
theorem B3357779 : Blo 2237435 3357779 := bstep (se 1 (by rfl) ⟨2518334, by rfl⟩ : syracuseStep 3357779 = 5036669) B5036669
theorem B2238519 : Blo 2237435 2238519 := bstep (se 1 (by rfl) ⟨1678889, by rfl⟩ : syracuseStep 2238519 = 3357779) B3357779
theorem B3777509 : Blo 2237435 3777509 := bbase (se 4 (by rfl) ⟨354141, by rfl⟩ : syracuseStep 3777509 = 708283) (by norm_num)
theorem B2518339 : Blo 2237435 2518339 := bstep (se 1 (by rfl) ⟨1888754, by rfl⟩ : syracuseStep 2518339 = 3777509) B3777509
theorem B3357785 : Blo 2237435 3357785 := bstep (se 2 (by rfl) ⟨1259169, by rfl⟩ : syracuseStep 3357785 = 2518339) B2518339
theorem B2238523 : Blo 2237435 2238523 := bstep (se 1 (by rfl) ⟨1678892, by rfl⟩ : syracuseStep 2238523 = 3357785) B3357785
theorem B4033901 : Blo 2237435 4033901 := bbase (se 3 (by rfl) ⟨756356, by rfl⟩ : syracuseStep 4033901 = 1512713) (by norm_num)
theorem B10757069 : Blo 2237435 10757069 := bstep (se 3 (by rfl) ⟨2016950, by rfl⟩ : syracuseStep 10757069 = 4033901) B4033901
theorem B7171379 : Blo 2237435 7171379 := bstep (se 1 (by rfl) ⟨5378534, by rfl⟩ : syracuseStep 7171379 = 10757069) B10757069
theorem B4780919 : Blo 2237435 4780919 := bstep (se 1 (by rfl) ⟨3585689, by rfl⟩ : syracuseStep 4780919 = 7171379) B7171379
theorem B3187279 : Blo 2237435 3187279 := bstep (se 1 (by rfl) ⟨2390459, by rfl⟩ : syracuseStep 3187279 = 4780919) B4780919
theorem B16998821 : Blo 2237435 16998821 := bstep (se 4 (by rfl) ⟨1593639, by rfl⟩ : syracuseStep 16998821 = 3187279) B3187279
theorem B11332547 : Blo 2237435 11332547 := bstep (se 1 (by rfl) ⟨8499410, by rfl⟩ : syracuseStep 11332547 = 16998821) B16998821
theorem B7555031 : Blo 2237435 7555031 := bstep (se 1 (by rfl) ⟨5666273, by rfl⟩ : syracuseStep 7555031 = 11332547) B11332547
theorem B5036687 : Blo 2237435 5036687 := bstep (se 1 (by rfl) ⟨3777515, by rfl⟩ : syracuseStep 5036687 = 7555031) B7555031
theorem B3357791 : Blo 2237435 3357791 := bstep (se 1 (by rfl) ⟨2518343, by rfl⟩ : syracuseStep 3357791 = 5036687) B5036687
theorem B2238527 : Blo 2237435 2238527 := bstep (se 1 (by rfl) ⟨1678895, by rfl⟩ : syracuseStep 2238527 = 3357791) B3357791
theorem B3357797 : Blo 2237435 3357797 := bbase (se 4 (by rfl) ⟨314793, by rfl⟩ : syracuseStep 3357797 = 629587) (by norm_num)
theorem B2238531 : Blo 2237435 2238531 := bstep (se 1 (by rfl) ⟨1678898, by rfl⟩ : syracuseStep 2238531 = 3357797) B3357797
theorem B10210853 : Blo 2237435 10210853 := bbase (se 4 (by rfl) ⟨957267, by rfl⟩ : syracuseStep 10210853 = 1914535) (by norm_num)
theorem B6807235 : Blo 2237435 6807235 := bstep (se 1 (by rfl) ⟨5105426, by rfl⟩ : syracuseStep 6807235 = 10210853) B10210853
theorem B9076313 : Blo 2237435 9076313 := bstep (se 2 (by rfl) ⟨3403617, by rfl⟩ : syracuseStep 9076313 = 6807235) B6807235
theorem B6050875 : Blo 2237435 6050875 := bstep (se 1 (by rfl) ⟨4538156, by rfl⟩ : syracuseStep 6050875 = 9076313) B9076313
theorem B8067833 : Blo 2237435 8067833 := bstep (se 2 (by rfl) ⟨3025437, by rfl⟩ : syracuseStep 8067833 = 6050875) B6050875
theorem B5378555 : Blo 2237435 5378555 := bstep (se 1 (by rfl) ⟨4033916, by rfl⟩ : syracuseStep 5378555 = 8067833) B8067833
theorem B3585703 : Blo 2237435 3585703 := bstep (se 1 (by rfl) ⟨2689277, by rfl⟩ : syracuseStep 3585703 = 5378555) B5378555
theorem B4780937 : Blo 2237435 4780937 := bstep (se 2 (by rfl) ⟨1792851, by rfl⟩ : syracuseStep 4780937 = 3585703) B3585703
theorem B3187291 : Blo 2237435 3187291 := bstep (se 1 (by rfl) ⟨2390468, by rfl⟩ : syracuseStep 3187291 = 4780937) B4780937
theorem B4249721 : Blo 2237435 4249721 := bstep (se 2 (by rfl) ⟨1593645, by rfl⟩ : syracuseStep 4249721 = 3187291) B3187291
theorem B2833147 : Blo 2237435 2833147 := bstep (se 1 (by rfl) ⟨2124860, by rfl⟩ : syracuseStep 2833147 = 4249721) B4249721
theorem B3777529 : Blo 2237435 3777529 := bstep (se 2 (by rfl) ⟨1416573, by rfl⟩ : syracuseStep 3777529 = 2833147) B2833147
theorem B5036705 : Blo 2237435 5036705 := bstep (se 2 (by rfl) ⟨1888764, by rfl⟩ : syracuseStep 5036705 = 3777529) B3777529
theorem B3357803 : Blo 2237435 3357803 := bstep (se 1 (by rfl) ⟨2518352, by rfl⟩ : syracuseStep 3357803 = 5036705) B5036705
theorem B2238535 : Blo 2237435 2238535 := bstep (se 1 (by rfl) ⟨1678901, by rfl⟩ : syracuseStep 2238535 = 3357803) B3357803
theorem B2518357 : Blo 2237435 2518357 := bbase (se 11 (by rfl) ⟨1844, by rfl⟩ : syracuseStep 2518357 = 3689) (by norm_num)
theorem B3357809 : Blo 2237435 3357809 := bstep (se 2 (by rfl) ⟨1259178, by rfl⟩ : syracuseStep 3357809 = 2518357) B2518357
theorem B2238539 : Blo 2237435 2238539 := bstep (se 1 (by rfl) ⟨1678904, by rfl⟩ : syracuseStep 2238539 = 3357809) B3357809
theorem B2833157 : Blo 2237435 2833157 := bbase (se 4 (by rfl) ⟨265608, by rfl⟩ : syracuseStep 2833157 = 531217) (by norm_num)
theorem B7555085 : Blo 2237435 7555085 := bstep (se 3 (by rfl) ⟨1416578, by rfl⟩ : syracuseStep 7555085 = 2833157) B2833157
theorem B5036723 : Blo 2237435 5036723 := bstep (se 1 (by rfl) ⟨3777542, by rfl⟩ : syracuseStep 5036723 = 7555085) B7555085
theorem B3357815 : Blo 2237435 3357815 := bstep (se 1 (by rfl) ⟨2518361, by rfl⟩ : syracuseStep 3357815 = 5036723) B5036723
theorem B2238543 : Blo 2237435 2238543 := bstep (se 1 (by rfl) ⟨1678907, by rfl⟩ : syracuseStep 2238543 = 3357815) B3357815
theorem B3357821 : Blo 2237435 3357821 := bbase (se 3 (by rfl) ⟨629591, by rfl⟩ : syracuseStep 3357821 = 1259183) (by norm_num)
theorem B2238547 : Blo 2237435 2238547 := bstep (se 1 (by rfl) ⟨1678910, by rfl⟩ : syracuseStep 2238547 = 3357821) B3357821
theorem B5036741 : Blo 2237435 5036741 := bbase (se 4 (by rfl) ⟨472194, by rfl⟩ : syracuseStep 5036741 = 944389) (by norm_num)
theorem B3357827 : Blo 2237435 3357827 := bstep (se 1 (by rfl) ⟨2518370, by rfl⟩ : syracuseStep 3357827 = 5036741) B5036741
theorem B2238551 : Blo 2237435 2238551 := bstep (se 1 (by rfl) ⟨1678913, by rfl⟩ : syracuseStep 2238551 = 3357827) B3357827
theorem B11644037 : Blo 2237435 11644037 := bbase (se 4 (by rfl) ⟨1091628, by rfl⟩ : syracuseStep 11644037 = 2183257) (by norm_num)
theorem B7762691 : Blo 2237435 7762691 := bstep (se 1 (by rfl) ⟨5822018, by rfl⟩ : syracuseStep 7762691 = 11644037) B11644037
theorem B5175127 : Blo 2237435 5175127 := bstep (se 1 (by rfl) ⟨3881345, by rfl⟩ : syracuseStep 5175127 = 7762691) B7762691
theorem B6900169 : Blo 2237435 6900169 := bstep (se 2 (by rfl) ⟨2587563, by rfl⟩ : syracuseStep 6900169 = 5175127) B5175127
theorem B9200225 : Blo 2237435 9200225 := bstep (se 2 (by rfl) ⟨3450084, by rfl⟩ : syracuseStep 9200225 = 6900169) B6900169
theorem B6133483 : Blo 2237435 6133483 := bstep (se 1 (by rfl) ⟨4600112, by rfl⟩ : syracuseStep 6133483 = 9200225) B9200225
theorem B8177977 : Blo 2237435 8177977 := bstep (se 2 (by rfl) ⟨3066741, by rfl⟩ : syracuseStep 8177977 = 6133483) B6133483
theorem B10903969 : Blo 2237435 10903969 := bstep (se 2 (by rfl) ⟨4088988, by rfl⟩ : syracuseStep 10903969 = 8177977) B8177977
theorem B14538625 : Blo 2237435 14538625 := bstep (se 2 (by rfl) ⟨5451984, by rfl⟩ : syracuseStep 14538625 = 10903969) B10903969
theorem B310157333 : Blo 2237435 310157333 := bstep (se 6 (by rfl) ⟨7269312, by rfl⟩ : syracuseStep 310157333 = 14538625) B14538625
theorem B206771555 : Blo 2237435 206771555 := bstep (se 1 (by rfl) ⟨155078666, by rfl⟩ : syracuseStep 206771555 = 310157333) B310157333
theorem B137847703 : Blo 2237435 137847703 := bstep (se 1 (by rfl) ⟨103385777, by rfl⟩ : syracuseStep 137847703 = 206771555) B206771555
theorem B183796937 : Blo 2237435 183796937 := bstep (se 2 (by rfl) ⟨68923851, by rfl⟩ : syracuseStep 183796937 = 137847703) B137847703
theorem B122531291 : Blo 2237435 122531291 := bstep (se 1 (by rfl) ⟨91898468, by rfl⟩ : syracuseStep 122531291 = 183796937) B183796937
theorem B81687527 : Blo 2237435 81687527 := bstep (se 1 (by rfl) ⟨61265645, by rfl⟩ : syracuseStep 81687527 = 122531291) B122531291
theorem B54458351 : Blo 2237435 54458351 := bstep (se 1 (by rfl) ⟨40843763, by rfl⟩ : syracuseStep 54458351 = 81687527) B81687527
theorem B36305567 : Blo 2237435 36305567 := bstep (se 1 (by rfl) ⟨27229175, by rfl⟩ : syracuseStep 36305567 = 54458351) B54458351
theorem B24203711 : Blo 2237435 24203711 := bstep (se 1 (by rfl) ⟨18152783, by rfl⟩ : syracuseStep 24203711 = 36305567) B36305567
theorem B16135807 : Blo 2237435 16135807 := bstep (se 1 (by rfl) ⟨12101855, by rfl⟩ : syracuseStep 16135807 = 24203711) B24203711
theorem B21514409 : Blo 2237435 21514409 := bstep (se 2 (by rfl) ⟨8067903, by rfl⟩ : syracuseStep 21514409 = 16135807) B16135807
theorem B14342939 : Blo 2237435 14342939 := bstep (se 1 (by rfl) ⟨10757204, by rfl⟩ : syracuseStep 14342939 = 21514409) B21514409
theorem B9561959 : Blo 2237435 9561959 := bstep (se 1 (by rfl) ⟨7171469, by rfl⟩ : syracuseStep 9561959 = 14342939) B14342939
theorem B6374639 : Blo 2237435 6374639 := bstep (se 1 (by rfl) ⟨4780979, by rfl⟩ : syracuseStep 6374639 = 9561959) B9561959
theorem B4249759 : Blo 2237435 4249759 := bstep (se 1 (by rfl) ⟨3187319, by rfl⟩ : syracuseStep 4249759 = 6374639) B6374639
theorem B5666345 : Blo 2237435 5666345 := bstep (se 2 (by rfl) ⟨2124879, by rfl⟩ : syracuseStep 5666345 = 4249759) B4249759
theorem B3777563 : Blo 2237435 3777563 := bstep (se 1 (by rfl) ⟨2833172, by rfl⟩ : syracuseStep 3777563 = 5666345) B5666345
theorem B2518375 : Blo 2237435 2518375 := bstep (se 1 (by rfl) ⟨1888781, by rfl⟩ : syracuseStep 2518375 = 3777563) B3777563
theorem B3357833 : Blo 2237435 3357833 := bstep (se 2 (by rfl) ⟨1259187, by rfl⟩ : syracuseStep 3357833 = 2518375) B2518375
theorem B2238555 : Blo 2237435 2238555 := bstep (se 1 (by rfl) ⟨1678916, by rfl⟩ : syracuseStep 2238555 = 3357833) B3357833
theorem B11332709 : Blo 2237435 11332709 := bbase (se 4 (by rfl) ⟨1062441, by rfl⟩ : syracuseStep 11332709 = 2124883) (by norm_num)
theorem B7555139 : Blo 2237435 7555139 := bstep (se 1 (by rfl) ⟨5666354, by rfl⟩ : syracuseStep 7555139 = 11332709) B11332709
theorem B5036759 : Blo 2237435 5036759 := bstep (se 1 (by rfl) ⟨3777569, by rfl⟩ : syracuseStep 5036759 = 7555139) B7555139
theorem B3357839 : Blo 2237435 3357839 := bstep (se 1 (by rfl) ⟨2518379, by rfl⟩ : syracuseStep 3357839 = 5036759) B5036759
theorem B2238559 : Blo 2237435 2238559 := bstep (se 1 (by rfl) ⟨1678919, by rfl⟩ : syracuseStep 2238559 = 3357839) B3357839
theorem B3357845 : Blo 2237435 3357845 := bbase (se 6 (by rfl) ⟨78699, by rfl⟩ : syracuseStep 3357845 = 157399) (by norm_num)
theorem B2238563 : Blo 2237435 2238563 := bstep (se 1 (by rfl) ⟨1678922, by rfl⟩ : syracuseStep 2238563 = 3357845) B3357845
theorem B4033973 : Blo 2237435 4033973 := bbase (se 5 (by rfl) ⟨189092, by rfl⟩ : syracuseStep 4033973 = 378185) (by norm_num)
theorem B10757261 : Blo 2237435 10757261 := bstep (se 3 (by rfl) ⟨2016986, by rfl⟩ : syracuseStep 10757261 = 4033973) B4033973
theorem B7171507 : Blo 2237435 7171507 := bstep (se 1 (by rfl) ⟨5378630, by rfl⟩ : syracuseStep 7171507 = 10757261) B10757261
theorem B9562009 : Blo 2237435 9562009 := bstep (se 2 (by rfl) ⟨3585753, by rfl⟩ : syracuseStep 9562009 = 7171507) B7171507
theorem B12749345 : Blo 2237435 12749345 := bstep (se 2 (by rfl) ⟨4781004, by rfl⟩ : syracuseStep 12749345 = 9562009) B9562009
theorem B8499563 : Blo 2237435 8499563 := bstep (se 1 (by rfl) ⟨6374672, by rfl⟩ : syracuseStep 8499563 = 12749345) B12749345
theorem B5666375 : Blo 2237435 5666375 := bstep (se 1 (by rfl) ⟨4249781, by rfl⟩ : syracuseStep 5666375 = 8499563) B8499563
theorem B3777583 : Blo 2237435 3777583 := bstep (se 1 (by rfl) ⟨2833187, by rfl⟩ : syracuseStep 3777583 = 5666375) B5666375
theorem B5036777 : Blo 2237435 5036777 := bstep (se 2 (by rfl) ⟨1888791, by rfl⟩ : syracuseStep 5036777 = 3777583) B3777583
theorem B3357851 : Blo 2237435 3357851 := bstep (se 1 (by rfl) ⟨2518388, by rfl⟩ : syracuseStep 3357851 = 5036777) B5036777
theorem B2238567 : Blo 2237435 2238567 := bstep (se 1 (by rfl) ⟨1678925, by rfl⟩ : syracuseStep 2238567 = 3357851) B3357851
theorem B2518393 : Blo 2237435 2518393 := bbase (se 2 (by rfl) ⟨944397, by rfl⟩ : syracuseStep 2518393 = 1888795) (by norm_num)
theorem B3357857 : Blo 2237435 3357857 := bstep (se 2 (by rfl) ⟨1259196, by rfl⟩ : syracuseStep 3357857 = 2518393) B2518393
theorem B2238571 : Blo 2237435 2238571 := bstep (se 1 (by rfl) ⟨1678928, by rfl⟩ : syracuseStep 2238571 = 3357857) B3357857
theorem B6050981 : Blo 2237435 6050981 := bbase (se 4 (by rfl) ⟨567279, by rfl⟩ : syracuseStep 6050981 = 1134559) (by norm_num)
theorem B16135949 : Blo 2237435 16135949 := bstep (se 3 (by rfl) ⟨3025490, by rfl⟩ : syracuseStep 16135949 = 6050981) B6050981
theorem B10757299 : Blo 2237435 10757299 := bstep (se 1 (by rfl) ⟨8067974, by rfl⟩ : syracuseStep 10757299 = 16135949) B16135949
theorem B14343065 : Blo 2237435 14343065 := bstep (se 2 (by rfl) ⟨5378649, by rfl⟩ : syracuseStep 14343065 = 10757299) B10757299
theorem B9562043 : Blo 2237435 9562043 := bstep (se 1 (by rfl) ⟨7171532, by rfl⟩ : syracuseStep 9562043 = 14343065) B14343065
theorem B6374695 : Blo 2237435 6374695 := bstep (se 1 (by rfl) ⟨4781021, by rfl⟩ : syracuseStep 6374695 = 9562043) B9562043
theorem B8499593 : Blo 2237435 8499593 := bstep (se 2 (by rfl) ⟨3187347, by rfl⟩ : syracuseStep 8499593 = 6374695) B6374695
theorem B5666395 : Blo 2237435 5666395 := bstep (se 1 (by rfl) ⟨4249796, by rfl⟩ : syracuseStep 5666395 = 8499593) B8499593
theorem B7555193 : Blo 2237435 7555193 := bstep (se 2 (by rfl) ⟨2833197, by rfl⟩ : syracuseStep 7555193 = 5666395) B5666395
theorem B5036795 : Blo 2237435 5036795 := bstep (se 1 (by rfl) ⟨3777596, by rfl⟩ : syracuseStep 5036795 = 7555193) B7555193
theorem B3357863 : Blo 2237435 3357863 := bstep (se 1 (by rfl) ⟨2518397, by rfl⟩ : syracuseStep 3357863 = 5036795) B5036795
theorem B2238575 : Blo 2237435 2238575 := bstep (se 1 (by rfl) ⟨1678931, by rfl⟩ : syracuseStep 2238575 = 3357863) B3357863
theorem B3357869 : Blo 2237435 3357869 := bbase (se 3 (by rfl) ⟨629600, by rfl⟩ : syracuseStep 3357869 = 1259201) (by norm_num)
theorem B2238579 : Blo 2237435 2238579 := bstep (se 1 (by rfl) ⟨1678934, by rfl⟩ : syracuseStep 2238579 = 3357869) B3357869
theorem B5036813 : Blo 2237435 5036813 := bbase (se 3 (by rfl) ⟨944402, by rfl⟩ : syracuseStep 5036813 = 1888805) (by norm_num)
theorem B3357875 : Blo 2237435 3357875 := bstep (se 1 (by rfl) ⟨2518406, by rfl⟩ : syracuseStep 3357875 = 5036813) B5036813
theorem B2238583 : Blo 2237435 2238583 := bstep (se 1 (by rfl) ⟨1678937, by rfl⟩ : syracuseStep 2238583 = 3357875) B3357875
theorem B2833213 : Blo 2237435 2833213 := bbase (se 3 (by rfl) ⟨531227, by rfl⟩ : syracuseStep 2833213 = 1062455) (by norm_num)
theorem B3777617 : Blo 2237435 3777617 := bstep (se 2 (by rfl) ⟨1416606, by rfl⟩ : syracuseStep 3777617 = 2833213) B2833213
theorem B2518411 : Blo 2237435 2518411 := bstep (se 1 (by rfl) ⟨1888808, by rfl⟩ : syracuseStep 2518411 = 3777617) B3777617
theorem B3357881 : Blo 2237435 3357881 := bstep (se 2 (by rfl) ⟨1259205, by rfl⟩ : syracuseStep 3357881 = 2518411) B2518411
theorem B2238587 : Blo 2237435 2238587 := bstep (se 1 (by rfl) ⟨1678940, by rfl⟩ : syracuseStep 2238587 = 3357881) B3357881
theorem B19385141 : Blo 2237435 19385141 := bbase (se 5 (by rfl) ⟨908678, by rfl⟩ : syracuseStep 19385141 = 1817357) (by norm_num)
theorem B51693709 : Blo 2237435 51693709 := bstep (se 3 (by rfl) ⟨9692570, by rfl⟩ : syracuseStep 51693709 = 19385141) B19385141
theorem B68924945 : Blo 2237435 68924945 := bstep (se 2 (by rfl) ⟨25846854, by rfl⟩ : syracuseStep 68924945 = 51693709) B51693709
theorem B183799853 : Blo 2237435 183799853 := bstep (se 3 (by rfl) ⟨34462472, by rfl⟩ : syracuseStep 183799853 = 68924945) B68924945
theorem B122533235 : Blo 2237435 122533235 := bstep (se 1 (by rfl) ⟨91899926, by rfl⟩ : syracuseStep 122533235 = 183799853) B183799853
theorem B81688823 : Blo 2237435 81688823 := bstep (se 1 (by rfl) ⟨61266617, by rfl⟩ : syracuseStep 81688823 = 122533235) B122533235
theorem B54459215 : Blo 2237435 54459215 := bstep (se 1 (by rfl) ⟨40844411, by rfl⟩ : syracuseStep 54459215 = 81688823) B81688823
theorem B36306143 : Blo 2237435 36306143 := bstep (se 1 (by rfl) ⟨27229607, by rfl⟩ : syracuseStep 36306143 = 54459215) B54459215
theorem B24204095 : Blo 2237435 24204095 := bstep (se 1 (by rfl) ⟨18153071, by rfl⟩ : syracuseStep 24204095 = 36306143) B36306143
theorem B16136063 : Blo 2237435 16136063 := bstep (se 1 (by rfl) ⟨12102047, by rfl⟩ : syracuseStep 16136063 = 24204095) B24204095
theorem B10757375 : Blo 2237435 10757375 := bstep (se 1 (by rfl) ⟨8068031, by rfl⟩ : syracuseStep 10757375 = 16136063) B16136063
theorem B7171583 : Blo 2237435 7171583 := bstep (se 1 (by rfl) ⟨5378687, by rfl⟩ : syracuseStep 7171583 = 10757375) B10757375
theorem B19124221 : Blo 2237435 19124221 := bstep (se 3 (by rfl) ⟨3585791, by rfl⟩ : syracuseStep 19124221 = 7171583) B7171583
theorem B25498961 : Blo 2237435 25498961 := bstep (se 2 (by rfl) ⟨9562110, by rfl⟩ : syracuseStep 25498961 = 19124221) B19124221
theorem B16999307 : Blo 2237435 16999307 := bstep (se 1 (by rfl) ⟨12749480, by rfl⟩ : syracuseStep 16999307 = 25498961) B25498961
theorem B11332871 : Blo 2237435 11332871 := bstep (se 1 (by rfl) ⟨8499653, by rfl⟩ : syracuseStep 11332871 = 16999307) B16999307
theorem B7555247 : Blo 2237435 7555247 := bstep (se 1 (by rfl) ⟨5666435, by rfl⟩ : syracuseStep 7555247 = 11332871) B11332871
theorem B5036831 : Blo 2237435 5036831 := bstep (se 1 (by rfl) ⟨3777623, by rfl⟩ : syracuseStep 5036831 = 7555247) B7555247
theorem B3357887 : Blo 2237435 3357887 := bstep (se 1 (by rfl) ⟨2518415, by rfl⟩ : syracuseStep 3357887 = 5036831) B5036831
theorem B2238591 : Blo 2237435 2238591 := bstep (se 1 (by rfl) ⟨1678943, by rfl⟩ : syracuseStep 2238591 = 3357887) B3357887
theorem B3357893 : Blo 2237435 3357893 := bbase (se 4 (by rfl) ⟨314802, by rfl⟩ : syracuseStep 3357893 = 629605) (by norm_num)
theorem B2238595 : Blo 2237435 2238595 := bstep (se 1 (by rfl) ⟨1678946, by rfl⟩ : syracuseStep 2238595 = 3357893) B3357893
theorem B3777637 : Blo 2237435 3777637 := bbase (se 4 (by rfl) ⟨354153, by rfl⟩ : syracuseStep 3777637 = 708307) (by norm_num)
theorem B5036849 : Blo 2237435 5036849 := bstep (se 2 (by rfl) ⟨1888818, by rfl⟩ : syracuseStep 5036849 = 3777637) B3777637
theorem B3357899 : Blo 2237435 3357899 := bstep (se 1 (by rfl) ⟨2518424, by rfl⟩ : syracuseStep 3357899 = 5036849) B5036849
theorem B2238599 : Blo 2237435 2238599 := bstep (se 1 (by rfl) ⟨1678949, by rfl⟩ : syracuseStep 2238599 = 3357899) B3357899
theorem B2518429 : Blo 2237435 2518429 := bbase (se 3 (by rfl) ⟨472205, by rfl⟩ : syracuseStep 2518429 = 944411) (by norm_num)
theorem B3357905 : Blo 2237435 3357905 := bstep (se 2 (by rfl) ⟨1259214, by rfl⟩ : syracuseStep 3357905 = 2518429) B2518429
theorem B2238603 : Blo 2237435 2238603 := bstep (se 1 (by rfl) ⟨1678952, by rfl⟩ : syracuseStep 2238603 = 3357905) B3357905
theorem B7555301 : Blo 2237435 7555301 := bbase (se 4 (by rfl) ⟨708309, by rfl⟩ : syracuseStep 7555301 = 1416619) (by norm_num)
theorem B5036867 : Blo 2237435 5036867 := bstep (se 1 (by rfl) ⟨3777650, by rfl⟩ : syracuseStep 5036867 = 7555301) B7555301
theorem B3357911 : Blo 2237435 3357911 := bstep (se 1 (by rfl) ⟨2518433, by rfl⟩ : syracuseStep 3357911 = 5036867) B5036867
theorem B2238607 : Blo 2237435 2238607 := bstep (se 1 (by rfl) ⟨1678955, by rfl⟩ : syracuseStep 2238607 = 3357911) B3357911
theorem B3357917 : Blo 2237435 3357917 := bbase (se 3 (by rfl) ⟨629609, by rfl⟩ : syracuseStep 3357917 = 1259219) (by norm_num)
theorem B2238611 : Blo 2237435 2238611 := bstep (se 1 (by rfl) ⟨1678958, by rfl⟩ : syracuseStep 2238611 = 3357917) B3357917
theorem B5036885 : Blo 2237435 5036885 := bbase (se 9 (by rfl) ⟨14756, by rfl⟩ : syracuseStep 5036885 = 29513) (by norm_num)
theorem B3357923 : Blo 2237435 3357923 := bstep (se 1 (by rfl) ⟨2518442, by rfl⟩ : syracuseStep 3357923 = 5036885) B5036885
theorem B2238615 : Blo 2237435 2238615 := bstep (se 1 (by rfl) ⟨1678961, by rfl⟩ : syracuseStep 2238615 = 3357923) B3357923
theorem B6374821 : Blo 2237435 6374821 := bbase (se 4 (by rfl) ⟨597639, by rfl⟩ : syracuseStep 6374821 = 1195279) (by norm_num)
theorem B8499761 : Blo 2237435 8499761 := bstep (se 2 (by rfl) ⟨3187410, by rfl⟩ : syracuseStep 8499761 = 6374821) B6374821
theorem B5666507 : Blo 2237435 5666507 := bstep (se 1 (by rfl) ⟨4249880, by rfl⟩ : syracuseStep 5666507 = 8499761) B8499761
theorem B3777671 : Blo 2237435 3777671 := bstep (se 1 (by rfl) ⟨2833253, by rfl⟩ : syracuseStep 3777671 = 5666507) B5666507
theorem B2518447 : Blo 2237435 2518447 := bstep (se 1 (by rfl) ⟨1888835, by rfl⟩ : syracuseStep 2518447 = 3777671) B3777671
theorem B3357929 : Blo 2237435 3357929 := bstep (se 2 (by rfl) ⟨1259223, by rfl⟩ : syracuseStep 3357929 = 2518447) B2518447
theorem B2238619 : Blo 2237435 2238619 := bstep (se 1 (by rfl) ⟨1678964, by rfl⟩ : syracuseStep 2238619 = 3357929) B3357929
theorem B4538333 : Blo 2237435 4538333 := bbase (se 3 (by rfl) ⟨850937, by rfl⟩ : syracuseStep 4538333 = 1701875) (by norm_num)
theorem B3025555 : Blo 2237435 3025555 := bstep (se 1 (by rfl) ⟨2269166, by rfl⟩ : syracuseStep 3025555 = 4538333) B4538333
theorem B64545173 : Blo 2237435 64545173 := bstep (se 6 (by rfl) ⟨1512777, by rfl⟩ : syracuseStep 64545173 = 3025555) B3025555
theorem B43030115 : Blo 2237435 43030115 := bstep (se 1 (by rfl) ⟨32272586, by rfl⟩ : syracuseStep 43030115 = 64545173) B64545173
theorem B28686743 : Blo 2237435 28686743 := bstep (se 1 (by rfl) ⟨21515057, by rfl⟩ : syracuseStep 28686743 = 43030115) B43030115
theorem B19124495 : Blo 2237435 19124495 := bstep (se 1 (by rfl) ⟨14343371, by rfl⟩ : syracuseStep 19124495 = 28686743) B28686743
theorem B12749663 : Blo 2237435 12749663 := bstep (se 1 (by rfl) ⟨9562247, by rfl⟩ : syracuseStep 12749663 = 19124495) B19124495
theorem B8499775 : Blo 2237435 8499775 := bstep (se 1 (by rfl) ⟨6374831, by rfl⟩ : syracuseStep 8499775 = 12749663) B12749663
theorem B11333033 : Blo 2237435 11333033 := bstep (se 2 (by rfl) ⟨4249887, by rfl⟩ : syracuseStep 11333033 = 8499775) B8499775
theorem B7555355 : Blo 2237435 7555355 := bstep (se 1 (by rfl) ⟨5666516, by rfl⟩ : syracuseStep 7555355 = 11333033) B11333033
theorem B5036903 : Blo 2237435 5036903 := bstep (se 1 (by rfl) ⟨3777677, by rfl⟩ : syracuseStep 5036903 = 7555355) B7555355
theorem B3357935 : Blo 2237435 3357935 := bstep (se 1 (by rfl) ⟨2518451, by rfl⟩ : syracuseStep 3357935 = 5036903) B5036903
theorem B2238623 : Blo 2237435 2238623 := bstep (se 1 (by rfl) ⟨1678967, by rfl⟩ : syracuseStep 2238623 = 3357935) B3357935
theorem B3357941 : Blo 2237435 3357941 := bbase (se 5 (by rfl) ⟨157403, by rfl⟩ : syracuseStep 3357941 = 314807) (by norm_num)
theorem B2238627 : Blo 2237435 2238627 := bstep (se 1 (by rfl) ⟨1678970, by rfl⟩ : syracuseStep 2238627 = 3357941) B3357941
theorem B5105645 : Blo 2237435 5105645 := bbase (se 3 (by rfl) ⟨957308, by rfl⟩ : syracuseStep 5105645 = 1914617) (by norm_num)
theorem B3403763 : Blo 2237435 3403763 := bstep (se 1 (by rfl) ⟨2552822, by rfl⟩ : syracuseStep 3403763 = 5105645) B5105645
theorem B2269175 : Blo 2237435 2269175 := bstep (se 1 (by rfl) ⟨1701881, by rfl⟩ : syracuseStep 2269175 = 3403763) B3403763
theorem B6051133 : Blo 2237435 6051133 := bstep (se 3 (by rfl) ⟨1134587, by rfl⟩ : syracuseStep 6051133 = 2269175) B2269175
theorem B8068177 : Blo 2237435 8068177 := bstep (se 2 (by rfl) ⟨3025566, by rfl⟩ : syracuseStep 8068177 = 6051133) B6051133
theorem B10757569 : Blo 2237435 10757569 := bstep (se 2 (by rfl) ⟨4034088, by rfl⟩ : syracuseStep 10757569 = 8068177) B8068177
theorem B14343425 : Blo 2237435 14343425 := bstep (se 2 (by rfl) ⟨5378784, by rfl⟩ : syracuseStep 14343425 = 10757569) B10757569
theorem B9562283 : Blo 2237435 9562283 := bstep (se 1 (by rfl) ⟨7171712, by rfl⟩ : syracuseStep 9562283 = 14343425) B14343425
theorem B6374855 : Blo 2237435 6374855 := bstep (se 1 (by rfl) ⟨4781141, by rfl⟩ : syracuseStep 6374855 = 9562283) B9562283
theorem B4249903 : Blo 2237435 4249903 := bstep (se 1 (by rfl) ⟨3187427, by rfl⟩ : syracuseStep 4249903 = 6374855) B6374855
theorem B5666537 : Blo 2237435 5666537 := bstep (se 2 (by rfl) ⟨2124951, by rfl⟩ : syracuseStep 5666537 = 4249903) B4249903
theorem B3777691 : Blo 2237435 3777691 := bstep (se 1 (by rfl) ⟨2833268, by rfl⟩ : syracuseStep 3777691 = 5666537) B5666537
theorem B5036921 : Blo 2237435 5036921 := bstep (se 2 (by rfl) ⟨1888845, by rfl⟩ : syracuseStep 5036921 = 3777691) B3777691
theorem B3357947 : Blo 2237435 3357947 := bstep (se 1 (by rfl) ⟨2518460, by rfl⟩ : syracuseStep 3357947 = 5036921) B5036921
theorem B2238631 : Blo 2237435 2238631 := bstep (se 1 (by rfl) ⟨1678973, by rfl⟩ : syracuseStep 2238631 = 3357947) B3357947
theorem B2518465 : Blo 2237435 2518465 := bbase (se 2 (by rfl) ⟨944424, by rfl⟩ : syracuseStep 2518465 = 1888849) (by norm_num)
theorem B3357953 : Blo 2237435 3357953 := bstep (se 2 (by rfl) ⟨1259232, by rfl⟩ : syracuseStep 3357953 = 2518465) B2518465
theorem B2238635 : Blo 2237435 2238635 := bstep (se 1 (by rfl) ⟨1678976, by rfl⟩ : syracuseStep 2238635 = 3357953) B3357953
theorem B5666557 : Blo 2237435 5666557 := bbase (se 3 (by rfl) ⟨1062479, by rfl⟩ : syracuseStep 5666557 = 2124959) (by norm_num)
theorem B7555409 : Blo 2237435 7555409 := bstep (se 2 (by rfl) ⟨2833278, by rfl⟩ : syracuseStep 7555409 = 5666557) B5666557
theorem B5036939 : Blo 2237435 5036939 := bstep (se 1 (by rfl) ⟨3777704, by rfl⟩ : syracuseStep 5036939 = 7555409) B7555409
theorem B3357959 : Blo 2237435 3357959 := bstep (se 1 (by rfl) ⟨2518469, by rfl⟩ : syracuseStep 3357959 = 5036939) B5036939
theorem B2238639 : Blo 2237435 2238639 := bstep (se 1 (by rfl) ⟨1678979, by rfl⟩ : syracuseStep 2238639 = 3357959) B3357959
theorem B3357965 : Blo 2237435 3357965 := bbase (se 3 (by rfl) ⟨629618, by rfl⟩ : syracuseStep 3357965 = 1259237) (by norm_num)
theorem B2238643 : Blo 2237435 2238643 := bstep (se 1 (by rfl) ⟨1678982, by rfl⟩ : syracuseStep 2238643 = 3357965) B3357965
theorem B5036957 : Blo 2237435 5036957 := bbase (se 3 (by rfl) ⟨944429, by rfl⟩ : syracuseStep 5036957 = 1888859) (by norm_num)
theorem B3357971 : Blo 2237435 3357971 := bstep (se 1 (by rfl) ⟨2518478, by rfl⟩ : syracuseStep 3357971 = 5036957) B5036957
theorem B2238647 : Blo 2237435 2238647 := bstep (se 1 (by rfl) ⟨1678985, by rfl⟩ : syracuseStep 2238647 = 3357971) B3357971
theorem B3777725 : Blo 2237435 3777725 := bbase (se 3 (by rfl) ⟨708323, by rfl⟩ : syracuseStep 3777725 = 1416647) (by norm_num)
theorem B2518483 : Blo 2237435 2518483 := bstep (se 1 (by rfl) ⟨1888862, by rfl⟩ : syracuseStep 2518483 = 3777725) B3777725
theorem B3357977 : Blo 2237435 3357977 := bstep (se 2 (by rfl) ⟨1259241, by rfl⟩ : syracuseStep 3357977 = 2518483) B2518483
theorem B2238651 : Blo 2237435 2238651 := bstep (se 1 (by rfl) ⟨1678988, by rfl⟩ : syracuseStep 2238651 = 3357977) B3357977
theorem B12749845 : Blo 2237435 12749845 := bbase (se 6 (by rfl) ⟨298824, by rfl⟩ : syracuseStep 12749845 = 597649) (by norm_num)
theorem B16999793 : Blo 2237435 16999793 := bstep (se 2 (by rfl) ⟨6374922, by rfl⟩ : syracuseStep 16999793 = 12749845) B12749845
theorem B11333195 : Blo 2237435 11333195 := bstep (se 1 (by rfl) ⟨8499896, by rfl⟩ : syracuseStep 11333195 = 16999793) B16999793
theorem B7555463 : Blo 2237435 7555463 := bstep (se 1 (by rfl) ⟨5666597, by rfl⟩ : syracuseStep 7555463 = 11333195) B11333195
theorem B5036975 : Blo 2237435 5036975 := bstep (se 1 (by rfl) ⟨3777731, by rfl⟩ : syracuseStep 5036975 = 7555463) B7555463
theorem B3357983 : Blo 2237435 3357983 := bstep (se 1 (by rfl) ⟨2518487, by rfl⟩ : syracuseStep 3357983 = 5036975) B5036975
theorem B2238655 : Blo 2237435 2238655 := bstep (se 1 (by rfl) ⟨1678991, by rfl⟩ : syracuseStep 2238655 = 3357983) B3357983
theorem B3357989 : Blo 2237435 3357989 := bbase (se 4 (by rfl) ⟨314811, by rfl⟩ : syracuseStep 3357989 = 629623) (by norm_num)
theorem B2238659 : Blo 2237435 2238659 := bstep (se 1 (by rfl) ⟨1678994, by rfl⟩ : syracuseStep 2238659 = 3357989) B3357989
theorem B2833309 : Blo 2237435 2833309 := bbase (se 3 (by rfl) ⟨531245, by rfl⟩ : syracuseStep 2833309 = 1062491) (by norm_num)
theorem B3777745 : Blo 2237435 3777745 := bstep (se 2 (by rfl) ⟨1416654, by rfl⟩ : syracuseStep 3777745 = 2833309) B2833309
theorem B5036993 : Blo 2237435 5036993 := bstep (se 2 (by rfl) ⟨1888872, by rfl⟩ : syracuseStep 5036993 = 3777745) B3777745
theorem B3357995 : Blo 2237435 3357995 := bstep (se 1 (by rfl) ⟨2518496, by rfl⟩ : syracuseStep 3357995 = 5036993) B5036993
theorem B2238663 : Blo 2237435 2238663 := bstep (se 1 (by rfl) ⟨1678997, by rfl⟩ : syracuseStep 2238663 = 3357995) B3357995
theorem B2518501 : Blo 2237435 2518501 := bbase (se 4 (by rfl) ⟨236109, by rfl⟩ : syracuseStep 2518501 = 472219) (by norm_num)
theorem B3358001 : Blo 2237435 3358001 := bstep (se 2 (by rfl) ⟨1259250, by rfl⟩ : syracuseStep 3358001 = 2518501) B2518501
theorem B2238667 : Blo 2237435 2238667 := bstep (se 1 (by rfl) ⟨1679000, by rfl⟩ : syracuseStep 2238667 = 3358001) B3358001
theorem B3025621 : Blo 2237435 3025621 := bbase (se 7 (by rfl) ⟨35456, by rfl⟩ : syracuseStep 3025621 = 70913) (by norm_num)
theorem B4034161 : Blo 2237435 4034161 := bstep (se 2 (by rfl) ⟨1512810, by rfl⟩ : syracuseStep 4034161 = 3025621) B3025621
theorem B5378881 : Blo 2237435 5378881 := bstep (se 2 (by rfl) ⟨2017080, by rfl⟩ : syracuseStep 5378881 = 4034161) B4034161
theorem B7171841 : Blo 2237435 7171841 := bstep (se 2 (by rfl) ⟨2689440, by rfl⟩ : syracuseStep 7171841 = 5378881) B5378881
theorem B4781227 : Blo 2237435 4781227 := bstep (se 1 (by rfl) ⟨3585920, by rfl⟩ : syracuseStep 4781227 = 7171841) B7171841
theorem B6374969 : Blo 2237435 6374969 := bstep (se 2 (by rfl) ⟨2390613, by rfl⟩ : syracuseStep 6374969 = 4781227) B4781227
theorem B4249979 : Blo 2237435 4249979 := bstep (se 1 (by rfl) ⟨3187484, by rfl⟩ : syracuseStep 4249979 = 6374969) B6374969
theorem B2833319 : Blo 2237435 2833319 := bstep (se 1 (by rfl) ⟨2124989, by rfl⟩ : syracuseStep 2833319 = 4249979) B4249979
theorem B7555517 : Blo 2237435 7555517 := bstep (se 3 (by rfl) ⟨1416659, by rfl⟩ : syracuseStep 7555517 = 2833319) B2833319
theorem B5037011 : Blo 2237435 5037011 := bstep (se 1 (by rfl) ⟨3777758, by rfl⟩ : syracuseStep 5037011 = 7555517) B7555517
theorem B3358007 : Blo 2237435 3358007 := bstep (se 1 (by rfl) ⟨2518505, by rfl⟩ : syracuseStep 3358007 = 5037011) B5037011
theorem B2238671 : Blo 2237435 2238671 := bstep (se 1 (by rfl) ⟨1679003, by rfl⟩ : syracuseStep 2238671 = 3358007) B3358007
theorem B3358013 : Blo 2237435 3358013 := bbase (se 3 (by rfl) ⟨629627, by rfl⟩ : syracuseStep 3358013 = 1259255) (by norm_num)
theorem B2238675 : Blo 2237435 2238675 := bstep (se 1 (by rfl) ⟨1679006, by rfl⟩ : syracuseStep 2238675 = 3358013) B3358013
theorem B5037029 : Blo 2237435 5037029 := bbase (se 4 (by rfl) ⟨472221, by rfl⟩ : syracuseStep 5037029 = 944443) (by norm_num)
theorem B3358019 : Blo 2237435 3358019 := bstep (se 1 (by rfl) ⟨2518514, by rfl⟩ : syracuseStep 3358019 = 5037029) B5037029
theorem B2238679 : Blo 2237435 2238679 := bstep (se 1 (by rfl) ⟨1679009, by rfl⟩ : syracuseStep 2238679 = 3358019) B3358019
theorem B5666669 : Blo 2237435 5666669 := bbase (se 3 (by rfl) ⟨1062500, by rfl⟩ : syracuseStep 5666669 = 2125001) (by norm_num)
theorem B3777779 : Blo 2237435 3777779 := bstep (se 1 (by rfl) ⟨2833334, by rfl⟩ : syracuseStep 3777779 = 5666669) B5666669
theorem B2518519 : Blo 2237435 2518519 := bstep (se 1 (by rfl) ⟨1888889, by rfl⟩ : syracuseStep 2518519 = 3777779) B3777779
theorem B3358025 : Blo 2237435 3358025 := bstep (se 2 (by rfl) ⟨1259259, by rfl⟩ : syracuseStep 3358025 = 2518519) B2518519
theorem B2238683 : Blo 2237435 2238683 := bstep (se 1 (by rfl) ⟨1679012, by rfl⟩ : syracuseStep 2238683 = 3358025) B3358025
theorem B4781261 : Blo 2237435 4781261 := bbase (se 3 (by rfl) ⟨896486, by rfl⟩ : syracuseStep 4781261 = 1792973) (by norm_num)
theorem B3187507 : Blo 2237435 3187507 := bstep (se 1 (by rfl) ⟨2390630, by rfl⟩ : syracuseStep 3187507 = 4781261) B4781261
theorem B4250009 : Blo 2237435 4250009 := bstep (se 2 (by rfl) ⟨1593753, by rfl⟩ : syracuseStep 4250009 = 3187507) B3187507
theorem B11333357 : Blo 2237435 11333357 := bstep (se 3 (by rfl) ⟨2125004, by rfl⟩ : syracuseStep 11333357 = 4250009) B4250009
theorem B7555571 : Blo 2237435 7555571 := bstep (se 1 (by rfl) ⟨5666678, by rfl⟩ : syracuseStep 7555571 = 11333357) B11333357
theorem B5037047 : Blo 2237435 5037047 := bstep (se 1 (by rfl) ⟨3777785, by rfl⟩ : syracuseStep 5037047 = 7555571) B7555571
theorem B3358031 : Blo 2237435 3358031 := bstep (se 1 (by rfl) ⟨2518523, by rfl⟩ : syracuseStep 3358031 = 5037047) B5037047
theorem B2238687 : Blo 2237435 2238687 := bstep (se 1 (by rfl) ⟨1679015, by rfl⟩ : syracuseStep 2238687 = 3358031) B3358031
theorem B3358037 : Blo 2237435 3358037 := bbase (se 11 (by rfl) ⟨2459, by rfl⟩ : syracuseStep 3358037 = 4919) (by norm_num)
theorem B2238691 : Blo 2237435 2238691 := bstep (se 1 (by rfl) ⟨1679018, by rfl⟩ : syracuseStep 2238691 = 3358037) B3358037
theorem B13801205 : Blo 2237435 13801205 := bbase (se 5 (by rfl) ⟨646931, by rfl⟩ : syracuseStep 13801205 = 1293863) (by norm_num)
theorem B36803213 : Blo 2237435 36803213 := bstep (se 3 (by rfl) ⟨6900602, by rfl⟩ : syracuseStep 36803213 = 13801205) B13801205
theorem B24535475 : Blo 2237435 24535475 := bstep (se 1 (by rfl) ⟨18401606, by rfl⟩ : syracuseStep 24535475 = 36803213) B36803213
theorem B16356983 : Blo 2237435 16356983 := bstep (se 1 (by rfl) ⟨12267737, by rfl⟩ : syracuseStep 16356983 = 24535475) B24535475
theorem B43618621 : Blo 2237435 43618621 := bstep (se 3 (by rfl) ⟨8178491, by rfl⟩ : syracuseStep 43618621 = 16356983) B16356983
theorem B58158161 : Blo 2237435 58158161 := bstep (se 2 (by rfl) ⟨21809310, by rfl⟩ : syracuseStep 58158161 = 43618621) B43618621
theorem B38772107 : Blo 2237435 38772107 := bstep (se 1 (by rfl) ⟨29079080, by rfl⟩ : syracuseStep 38772107 = 58158161) B58158161
theorem B25848071 : Blo 2237435 25848071 := bstep (se 1 (by rfl) ⟨19386053, by rfl⟩ : syracuseStep 25848071 = 38772107) B38772107
theorem B17232047 : Blo 2237435 17232047 := bstep (se 1 (by rfl) ⟨12924035, by rfl⟩ : syracuseStep 17232047 = 25848071) B25848071
theorem B11488031 : Blo 2237435 11488031 := bstep (se 1 (by rfl) ⟨8616023, by rfl⟩ : syracuseStep 11488031 = 17232047) B17232047
theorem B7658687 : Blo 2237435 7658687 := bstep (se 1 (by rfl) ⟨5744015, by rfl⟩ : syracuseStep 7658687 = 11488031) B11488031
theorem B5105791 : Blo 2237435 5105791 := bstep (se 1 (by rfl) ⟨3829343, by rfl⟩ : syracuseStep 5105791 = 7658687) B7658687
theorem B6807721 : Blo 2237435 6807721 := bstep (se 2 (by rfl) ⟨2552895, by rfl⟩ : syracuseStep 6807721 = 5105791) B5105791
theorem B9076961 : Blo 2237435 9076961 := bstep (se 2 (by rfl) ⟨3403860, by rfl⟩ : syracuseStep 9076961 = 6807721) B6807721
theorem B6051307 : Blo 2237435 6051307 := bstep (se 1 (by rfl) ⟨4538480, by rfl⟩ : syracuseStep 6051307 = 9076961) B9076961
theorem B8068409 : Blo 2237435 8068409 := bstep (se 2 (by rfl) ⟨3025653, by rfl⟩ : syracuseStep 8068409 = 6051307) B6051307
theorem B5378939 : Blo 2237435 5378939 := bstep (se 1 (by rfl) ⟨4034204, by rfl⟩ : syracuseStep 5378939 = 8068409) B8068409
theorem B3585959 : Blo 2237435 3585959 := bstep (se 1 (by rfl) ⟨2689469, by rfl⟩ : syracuseStep 3585959 = 5378939) B5378939
theorem B2390639 : Blo 2237435 2390639 := bstep (se 1 (by rfl) ⟨1792979, by rfl⟩ : syracuseStep 2390639 = 3585959) B3585959
theorem B6375037 : Blo 2237435 6375037 := bstep (se 3 (by rfl) ⟨1195319, by rfl⟩ : syracuseStep 6375037 = 2390639) B2390639
theorem B8500049 : Blo 2237435 8500049 := bstep (se 2 (by rfl) ⟨3187518, by rfl⟩ : syracuseStep 8500049 = 6375037) B6375037
theorem B5666699 : Blo 2237435 5666699 := bstep (se 1 (by rfl) ⟨4250024, by rfl⟩ : syracuseStep 5666699 = 8500049) B8500049
theorem B3777799 : Blo 2237435 3777799 := bstep (se 1 (by rfl) ⟨2833349, by rfl⟩ : syracuseStep 3777799 = 5666699) B5666699
theorem B5037065 : Blo 2237435 5037065 := bstep (se 2 (by rfl) ⟨1888899, by rfl⟩ : syracuseStep 5037065 = 3777799) B3777799
theorem B3358043 : Blo 2237435 3358043 := bstep (se 1 (by rfl) ⟨2518532, by rfl⟩ : syracuseStep 3358043 = 5037065) B5037065
theorem B2238695 : Blo 2237435 2238695 := bstep (se 1 (by rfl) ⟨1679021, by rfl⟩ : syracuseStep 2238695 = 3358043) B3358043
theorem B2518537 : Blo 2237435 2518537 := bbase (se 2 (by rfl) ⟨944451, by rfl⟩ : syracuseStep 2518537 = 1888903) (by norm_num)
theorem B3358049 : Blo 2237435 3358049 := bstep (se 2 (by rfl) ⟨1259268, by rfl⟩ : syracuseStep 3358049 = 2518537) B2518537
theorem B2238699 : Blo 2237435 2238699 := bstep (se 1 (by rfl) ⟨1679024, by rfl⟩ : syracuseStep 2238699 = 3358049) B3358049
theorem B5822405 : Blo 2237435 5822405 := bbase (se 4 (by rfl) ⟨545850, by rfl⟩ : syracuseStep 5822405 = 1091701) (by norm_num)
theorem B3881603 : Blo 2237435 3881603 := bstep (se 1 (by rfl) ⟨2911202, by rfl⟩ : syracuseStep 3881603 = 5822405) B5822405
theorem B2587735 : Blo 2237435 2587735 := bstep (se 1 (by rfl) ⟨1940801, by rfl⟩ : syracuseStep 2587735 = 3881603) B3881603
theorem B3450313 : Blo 2237435 3450313 := bstep (se 2 (by rfl) ⟨1293867, by rfl⟩ : syracuseStep 3450313 = 2587735) B2587735
theorem B4600417 : Blo 2237435 4600417 := bstep (se 2 (by rfl) ⟨1725156, by rfl⟩ : syracuseStep 4600417 = 3450313) B3450313
theorem B6133889 : Blo 2237435 6133889 := bstep (se 2 (by rfl) ⟨2300208, by rfl⟩ : syracuseStep 6133889 = 4600417) B4600417
theorem B4089259 : Blo 2237435 4089259 := bstep (se 1 (by rfl) ⟨3066944, by rfl⟩ : syracuseStep 4089259 = 6133889) B6133889
theorem B5452345 : Blo 2237435 5452345 := bstep (se 2 (by rfl) ⟨2044629, by rfl⟩ : syracuseStep 5452345 = 4089259) B4089259
theorem B7269793 : Blo 2237435 7269793 := bstep (se 2 (by rfl) ⟨2726172, by rfl⟩ : syracuseStep 7269793 = 5452345) B5452345
theorem B38772229 : Blo 2237435 38772229 := bstep (se 4 (by rfl) ⟨3634896, by rfl⟩ : syracuseStep 38772229 = 7269793) B7269793
theorem B51696305 : Blo 2237435 51696305 := bstep (se 2 (by rfl) ⟨19386114, by rfl⟩ : syracuseStep 51696305 = 38772229) B38772229
theorem B34464203 : Blo 2237435 34464203 := bstep (se 1 (by rfl) ⟨25848152, by rfl⟩ : syracuseStep 34464203 = 51696305) B51696305
theorem B22976135 : Blo 2237435 22976135 := bstep (se 1 (by rfl) ⟨17232101, by rfl⟩ : syracuseStep 22976135 = 34464203) B34464203
theorem B15317423 : Blo 2237435 15317423 := bstep (se 1 (by rfl) ⟨11488067, by rfl⟩ : syracuseStep 15317423 = 22976135) B22976135
theorem B10211615 : Blo 2237435 10211615 := bstep (se 1 (by rfl) ⟨7658711, by rfl⟩ : syracuseStep 10211615 = 15317423) B15317423
theorem B6807743 : Blo 2237435 6807743 := bstep (se 1 (by rfl) ⟨5105807, by rfl⟩ : syracuseStep 6807743 = 10211615) B10211615
theorem B4538495 : Blo 2237435 4538495 := bstep (se 1 (by rfl) ⟨3403871, by rfl⟩ : syracuseStep 4538495 = 6807743) B6807743
theorem B12102653 : Blo 2237435 12102653 := bstep (se 3 (by rfl) ⟨2269247, by rfl⟩ : syracuseStep 12102653 = 4538495) B4538495
theorem B32273741 : Blo 2237435 32273741 := bstep (se 3 (by rfl) ⟨6051326, by rfl⟩ : syracuseStep 32273741 = 12102653) B12102653
theorem B21515827 : Blo 2237435 21515827 := bstep (se 1 (by rfl) ⟨16136870, by rfl⟩ : syracuseStep 21515827 = 32273741) B32273741
theorem B28687769 : Blo 2237435 28687769 := bstep (se 2 (by rfl) ⟨10757913, by rfl⟩ : syracuseStep 28687769 = 21515827) B21515827
theorem B19125179 : Blo 2237435 19125179 := bstep (se 1 (by rfl) ⟨14343884, by rfl⟩ : syracuseStep 19125179 = 28687769) B28687769
theorem B12750119 : Blo 2237435 12750119 := bstep (se 1 (by rfl) ⟨9562589, by rfl⟩ : syracuseStep 12750119 = 19125179) B19125179
theorem B8500079 : Blo 2237435 8500079 := bstep (se 1 (by rfl) ⟨6375059, by rfl⟩ : syracuseStep 8500079 = 12750119) B12750119
theorem B5666719 : Blo 2237435 5666719 := bstep (se 1 (by rfl) ⟨4250039, by rfl⟩ : syracuseStep 5666719 = 8500079) B8500079
theorem B7555625 : Blo 2237435 7555625 := bstep (se 2 (by rfl) ⟨2833359, by rfl⟩ : syracuseStep 7555625 = 5666719) B5666719
theorem B5037083 : Blo 2237435 5037083 := bstep (se 1 (by rfl) ⟨3777812, by rfl⟩ : syracuseStep 5037083 = 7555625) B7555625
theorem B3358055 : Blo 2237435 3358055 := bstep (se 1 (by rfl) ⟨2518541, by rfl⟩ : syracuseStep 3358055 = 5037083) B5037083
theorem B2238703 : Blo 2237435 2238703 := bstep (se 1 (by rfl) ⟨1679027, by rfl⟩ : syracuseStep 2238703 = 3358055) B3358055
theorem B3358061 : Blo 2237435 3358061 := bbase (se 3 (by rfl) ⟨629636, by rfl⟩ : syracuseStep 3358061 = 1259273) (by norm_num)
theorem B2238707 : Blo 2237435 2238707 := bstep (se 1 (by rfl) ⟨1679030, by rfl⟩ : syracuseStep 2238707 = 3358061) B3358061
theorem B5037101 : Blo 2237435 5037101 := bbase (se 3 (by rfl) ⟨944456, by rfl⟩ : syracuseStep 5037101 = 1888913) (by norm_num)
theorem B3358067 : Blo 2237435 3358067 := bstep (se 1 (by rfl) ⟨2518550, by rfl⟩ : syracuseStep 3358067 = 5037101) B5037101
theorem B2238711 : Blo 2237435 2238711 := bstep (se 1 (by rfl) ⟨1679033, by rfl⟩ : syracuseStep 2238711 = 3358067) B3358067
theorem B5105837 : Blo 2237435 5105837 := bbase (se 3 (by rfl) ⟨957344, by rfl⟩ : syracuseStep 5105837 = 1914689) (by norm_num)
theorem B3403891 : Blo 2237435 3403891 := bstep (se 1 (by rfl) ⟨2552918, by rfl⟩ : syracuseStep 3403891 = 5105837) B5105837
theorem B4538521 : Blo 2237435 4538521 := bstep (se 2 (by rfl) ⟨1701945, by rfl⟩ : syracuseStep 4538521 = 3403891) B3403891
theorem B6051361 : Blo 2237435 6051361 := bstep (se 2 (by rfl) ⟨2269260, by rfl⟩ : syracuseStep 6051361 = 4538521) B4538521
theorem B8068481 : Blo 2237435 8068481 := bstep (se 2 (by rfl) ⟨3025680, by rfl⟩ : syracuseStep 8068481 = 6051361) B6051361
theorem B5378987 : Blo 2237435 5378987 := bstep (se 1 (by rfl) ⟨4034240, by rfl⟩ : syracuseStep 5378987 = 8068481) B8068481
theorem B14343965 : Blo 2237435 14343965 := bstep (se 3 (by rfl) ⟨2689493, by rfl⟩ : syracuseStep 14343965 = 5378987) B5378987
theorem B9562643 : Blo 2237435 9562643 := bstep (se 1 (by rfl) ⟨7171982, by rfl⟩ : syracuseStep 9562643 = 14343965) B14343965
theorem B6375095 : Blo 2237435 6375095 := bstep (se 1 (by rfl) ⟨4781321, by rfl⟩ : syracuseStep 6375095 = 9562643) B9562643
theorem B4250063 : Blo 2237435 4250063 := bstep (se 1 (by rfl) ⟨3187547, by rfl⟩ : syracuseStep 4250063 = 6375095) B6375095
theorem B2833375 : Blo 2237435 2833375 := bstep (se 1 (by rfl) ⟨2125031, by rfl⟩ : syracuseStep 2833375 = 4250063) B4250063
theorem B3777833 : Blo 2237435 3777833 := bstep (se 2 (by rfl) ⟨1416687, by rfl⟩ : syracuseStep 3777833 = 2833375) B2833375
theorem B2518555 : Blo 2237435 2518555 := bstep (se 1 (by rfl) ⟨1888916, by rfl⟩ : syracuseStep 2518555 = 3777833) B3777833
theorem B3358073 : Blo 2237435 3358073 := bstep (se 2 (by rfl) ⟨1259277, by rfl⟩ : syracuseStep 3358073 = 2518555) B2518555
theorem B2238715 : Blo 2237435 2238715 := bstep (se 1 (by rfl) ⟨1679036, by rfl⟩ : syracuseStep 2238715 = 3358073) B3358073
theorem B3025685 : Blo 2237435 3025685 := bbase (se 6 (by rfl) ⟨70914, by rfl⟩ : syracuseStep 3025685 = 141829) (by norm_num)
theorem B8068493 : Blo 2237435 8068493 := bstep (se 3 (by rfl) ⟨1512842, by rfl⟩ : syracuseStep 8068493 = 3025685) B3025685
theorem B5378995 : Blo 2237435 5378995 := bstep (se 1 (by rfl) ⟨4034246, by rfl⟩ : syracuseStep 5378995 = 8068493) B8068493
theorem B7171993 : Blo 2237435 7171993 := bstep (se 2 (by rfl) ⟨2689497, by rfl⟩ : syracuseStep 7171993 = 5378995) B5378995
theorem B38250629 : Blo 2237435 38250629 := bstep (se 4 (by rfl) ⟨3585996, by rfl⟩ : syracuseStep 38250629 = 7171993) B7171993
theorem B25500419 : Blo 2237435 25500419 := bstep (se 1 (by rfl) ⟨19125314, by rfl⟩ : syracuseStep 25500419 = 38250629) B38250629
theorem B17000279 : Blo 2237435 17000279 := bstep (se 1 (by rfl) ⟨12750209, by rfl⟩ : syracuseStep 17000279 = 25500419) B25500419
theorem B11333519 : Blo 2237435 11333519 := bstep (se 1 (by rfl) ⟨8500139, by rfl⟩ : syracuseStep 11333519 = 17000279) B17000279
theorem B7555679 : Blo 2237435 7555679 := bstep (se 1 (by rfl) ⟨5666759, by rfl⟩ : syracuseStep 7555679 = 11333519) B11333519
theorem B5037119 : Blo 2237435 5037119 := bstep (se 1 (by rfl) ⟨3777839, by rfl⟩ : syracuseStep 5037119 = 7555679) B7555679
theorem B3358079 : Blo 2237435 3358079 := bstep (se 1 (by rfl) ⟨2518559, by rfl⟩ : syracuseStep 3358079 = 5037119) B5037119
theorem B2238719 : Blo 2237435 2238719 := bstep (se 1 (by rfl) ⟨1679039, by rfl⟩ : syracuseStep 2238719 = 3358079) B3358079
theorem B3358085 : Blo 2237435 3358085 := bbase (se 4 (by rfl) ⟨314820, by rfl⟩ : syracuseStep 3358085 = 629641) (by norm_num)
theorem B2238723 : Blo 2237435 2238723 := bstep (se 1 (by rfl) ⟨1679042, by rfl⟩ : syracuseStep 2238723 = 3358085) B3358085
theorem B3777853 : Blo 2237435 3777853 := bbase (se 3 (by rfl) ⟨708347, by rfl⟩ : syracuseStep 3777853 = 1416695) (by norm_num)
theorem B5037137 : Blo 2237435 5037137 := bstep (se 2 (by rfl) ⟨1888926, by rfl⟩ : syracuseStep 5037137 = 3777853) B3777853
theorem B3358091 : Blo 2237435 3358091 := bstep (se 1 (by rfl) ⟨2518568, by rfl⟩ : syracuseStep 3358091 = 5037137) B5037137
theorem B2238727 : Blo 2237435 2238727 := bstep (se 1 (by rfl) ⟨1679045, by rfl⟩ : syracuseStep 2238727 = 3358091) B3358091
theorem B2518573 : Blo 2237435 2518573 := bbase (se 3 (by rfl) ⟨472232, by rfl⟩ : syracuseStep 2518573 = 944465) (by norm_num)
theorem B3358097 : Blo 2237435 3358097 := bstep (se 2 (by rfl) ⟨1259286, by rfl⟩ : syracuseStep 3358097 = 2518573) B2518573
theorem B2238731 : Blo 2237435 2238731 := bstep (se 1 (by rfl) ⟨1679048, by rfl⟩ : syracuseStep 2238731 = 3358097) B3358097
theorem B7555733 : Blo 2237435 7555733 := bbase (se 6 (by rfl) ⟨177087, by rfl⟩ : syracuseStep 7555733 = 354175) (by norm_num)
theorem B5037155 : Blo 2237435 5037155 := bstep (se 1 (by rfl) ⟨3777866, by rfl⟩ : syracuseStep 5037155 = 7555733) B7555733
theorem B3358103 : Blo 2237435 3358103 := bstep (se 1 (by rfl) ⟨2518577, by rfl⟩ : syracuseStep 3358103 = 5037155) B5037155
theorem B2238735 : Blo 2237435 2238735 := bstep (se 1 (by rfl) ⟨1679051, by rfl⟩ : syracuseStep 2238735 = 3358103) B3358103
theorem B3358109 : Blo 2237435 3358109 := bbase (se 3 (by rfl) ⟨629645, by rfl⟩ : syracuseStep 3358109 = 1259291) (by norm_num)
theorem B2238739 : Blo 2237435 2238739 := bstep (se 1 (by rfl) ⟨1679054, by rfl⟩ : syracuseStep 2238739 = 3358109) B3358109
theorem B5037173 : Blo 2237435 5037173 := bbase (se 5 (by rfl) ⟨236117, by rfl⟩ : syracuseStep 5037173 = 472235) (by norm_num)
theorem B3358115 : Blo 2237435 3358115 := bstep (se 1 (by rfl) ⟨2518586, by rfl⟩ : syracuseStep 3358115 = 5037173) B5037173
theorem B2238743 : Blo 2237435 2238743 := bstep (se 1 (by rfl) ⟨1679057, by rfl⟩ : syracuseStep 2238743 = 3358115) B3358115
theorem B19125557 : Blo 2237435 19125557 := bbase (se 5 (by rfl) ⟨896510, by rfl⟩ : syracuseStep 19125557 = 1793021) (by norm_num)
theorem B12750371 : Blo 2237435 12750371 := bstep (se 1 (by rfl) ⟨9562778, by rfl⟩ : syracuseStep 12750371 = 19125557) B19125557
theorem B8500247 : Blo 2237435 8500247 := bstep (se 1 (by rfl) ⟨6375185, by rfl⟩ : syracuseStep 8500247 = 12750371) B12750371
theorem B5666831 : Blo 2237435 5666831 := bstep (se 1 (by rfl) ⟨4250123, by rfl⟩ : syracuseStep 5666831 = 8500247) B8500247
theorem B3777887 : Blo 2237435 3777887 := bstep (se 1 (by rfl) ⟨2833415, by rfl⟩ : syracuseStep 3777887 = 5666831) B5666831
theorem B2518591 : Blo 2237435 2518591 := bstep (se 1 (by rfl) ⟨1888943, by rfl⟩ : syracuseStep 2518591 = 3777887) B3777887
theorem B3358121 : Blo 2237435 3358121 := bstep (se 2 (by rfl) ⟨1259295, by rfl⟩ : syracuseStep 3358121 = 2518591) B2518591
theorem B2238747 : Blo 2237435 2238747 := bstep (se 1 (by rfl) ⟨1679060, by rfl⟩ : syracuseStep 2238747 = 3358121) B3358121
theorem B8500261 : Blo 2237435 8500261 := bbase (se 4 (by rfl) ⟨796899, by rfl⟩ : syracuseStep 8500261 = 1593799) (by norm_num)
theorem B11333681 : Blo 2237435 11333681 := bstep (se 2 (by rfl) ⟨4250130, by rfl⟩ : syracuseStep 11333681 = 8500261) B8500261
theorem B7555787 : Blo 2237435 7555787 := bstep (se 1 (by rfl) ⟨5666840, by rfl⟩ : syracuseStep 7555787 = 11333681) B11333681
theorem B5037191 : Blo 2237435 5037191 := bstep (se 1 (by rfl) ⟨3777893, by rfl⟩ : syracuseStep 5037191 = 7555787) B7555787
theorem B3358127 : Blo 2237435 3358127 := bstep (se 1 (by rfl) ⟨2518595, by rfl⟩ : syracuseStep 3358127 = 5037191) B5037191
theorem B2238751 : Blo 2237435 2238751 := bstep (se 1 (by rfl) ⟨1679063, by rfl⟩ : syracuseStep 2238751 = 3358127) B3358127
theorem B3358133 : Blo 2237435 3358133 := bbase (se 5 (by rfl) ⟨157412, by rfl⟩ : syracuseStep 3358133 = 314825) (by norm_num)
theorem B2238755 : Blo 2237435 2238755 := bstep (se 1 (by rfl) ⟨1679066, by rfl⟩ : syracuseStep 2238755 = 3358133) B3358133
theorem B5666861 : Blo 2237435 5666861 := bbase (se 3 (by rfl) ⟨1062536, by rfl⟩ : syracuseStep 5666861 = 2125073) (by norm_num)
theorem B3777907 : Blo 2237435 3777907 := bstep (se 1 (by rfl) ⟨2833430, by rfl⟩ : syracuseStep 3777907 = 5666861) B5666861
theorem B5037209 : Blo 2237435 5037209 := bstep (se 2 (by rfl) ⟨1888953, by rfl⟩ : syracuseStep 5037209 = 3777907) B3777907
theorem B3358139 : Blo 2237435 3358139 := bstep (se 1 (by rfl) ⟨2518604, by rfl⟩ : syracuseStep 3358139 = 5037209) B5037209
theorem B2238759 : Blo 2237435 2238759 := bstep (se 1 (by rfl) ⟨1679069, by rfl⟩ : syracuseStep 2238759 = 3358139) B3358139
theorem B2518609 : Blo 2237435 2518609 := bbase (se 2 (by rfl) ⟨944478, by rfl⟩ : syracuseStep 2518609 = 1888957) (by norm_num)
theorem B3358145 : Blo 2237435 3358145 := bstep (se 2 (by rfl) ⟨1259304, by rfl⟩ : syracuseStep 3358145 = 2518609) B2518609
theorem B2238763 : Blo 2237435 2238763 := bstep (se 1 (by rfl) ⟨1679072, by rfl⟩ : syracuseStep 2238763 = 3358145) B3358145
theorem B3187621 : Blo 2237435 3187621 := bbase (se 4 (by rfl) ⟨298839, by rfl⟩ : syracuseStep 3187621 = 597679) (by norm_num)
theorem B4250161 : Blo 2237435 4250161 := bstep (se 2 (by rfl) ⟨1593810, by rfl⟩ : syracuseStep 4250161 = 3187621) B3187621
theorem B5666881 : Blo 2237435 5666881 := bstep (se 2 (by rfl) ⟨2125080, by rfl⟩ : syracuseStep 5666881 = 4250161) B4250161
theorem B7555841 : Blo 2237435 7555841 := bstep (se 2 (by rfl) ⟨2833440, by rfl⟩ : syracuseStep 7555841 = 5666881) B5666881
theorem B5037227 : Blo 2237435 5037227 := bstep (se 1 (by rfl) ⟨3777920, by rfl⟩ : syracuseStep 5037227 = 7555841) B7555841
theorem B3358151 : Blo 2237435 3358151 := bstep (se 1 (by rfl) ⟨2518613, by rfl⟩ : syracuseStep 3358151 = 5037227) B5037227
theorem B2238767 : Blo 2237435 2238767 := bstep (se 1 (by rfl) ⟨1679075, by rfl⟩ : syracuseStep 2238767 = 3358151) B3358151
theorem B3358157 : Blo 2237435 3358157 := bbase (se 3 (by rfl) ⟨629654, by rfl⟩ : syracuseStep 3358157 = 1259309) (by norm_num)
theorem B2238771 : Blo 2237435 2238771 := bstep (se 1 (by rfl) ⟨1679078, by rfl⟩ : syracuseStep 2238771 = 3358157) B3358157
theorem B5037245 : Blo 2237435 5037245 := bbase (se 3 (by rfl) ⟨944483, by rfl⟩ : syracuseStep 5037245 = 1888967) (by norm_num)
theorem B3358163 : Blo 2237435 3358163 := bstep (se 1 (by rfl) ⟨2518622, by rfl⟩ : syracuseStep 3358163 = 5037245) B5037245
theorem B2238775 : Blo 2237435 2238775 := bstep (se 1 (by rfl) ⟨1679081, by rfl⟩ : syracuseStep 2238775 = 3358163) B3358163
theorem B3777941 : Blo 2237435 3777941 := bbase (se 6 (by rfl) ⟨88545, by rfl⟩ : syracuseStep 3777941 = 177091) (by norm_num)
theorem B2518627 : Blo 2237435 2518627 := bstep (se 1 (by rfl) ⟨1888970, by rfl⟩ : syracuseStep 2518627 = 3777941) B3777941
theorem B3358169 : Blo 2237435 3358169 := bstep (se 2 (by rfl) ⟨1259313, by rfl⟩ : syracuseStep 3358169 = 2518627) B2518627
theorem B2238779 : Blo 2237435 2238779 := bstep (se 1 (by rfl) ⟨1679084, by rfl⟩ : syracuseStep 2238779 = 3358169) B3358169
theorem B5379149 : Blo 2237435 5379149 := bbase (se 3 (by rfl) ⟨1008590, by rfl⟩ : syracuseStep 5379149 = 2017181) (by norm_num)
theorem B14344397 : Blo 2237435 14344397 := bstep (se 3 (by rfl) ⟨2689574, by rfl⟩ : syracuseStep 14344397 = 5379149) B5379149
theorem B9562931 : Blo 2237435 9562931 := bstep (se 1 (by rfl) ⟨7172198, by rfl⟩ : syracuseStep 9562931 = 14344397) B14344397
theorem B6375287 : Blo 2237435 6375287 := bstep (se 1 (by rfl) ⟨4781465, by rfl⟩ : syracuseStep 6375287 = 9562931) B9562931
theorem B17000765 : Blo 2237435 17000765 := bstep (se 3 (by rfl) ⟨3187643, by rfl⟩ : syracuseStep 17000765 = 6375287) B6375287
theorem B11333843 : Blo 2237435 11333843 := bstep (se 1 (by rfl) ⟨8500382, by rfl⟩ : syracuseStep 11333843 = 17000765) B17000765
theorem B7555895 : Blo 2237435 7555895 := bstep (se 1 (by rfl) ⟨5666921, by rfl⟩ : syracuseStep 7555895 = 11333843) B11333843
theorem B5037263 : Blo 2237435 5037263 := bstep (se 1 (by rfl) ⟨3777947, by rfl⟩ : syracuseStep 5037263 = 7555895) B7555895
theorem B3358175 : Blo 2237435 3358175 := bstep (se 1 (by rfl) ⟨2518631, by rfl⟩ : syracuseStep 3358175 = 5037263) B5037263
theorem B2238783 : Blo 2237435 2238783 := bstep (se 1 (by rfl) ⟨1679087, by rfl⟩ : syracuseStep 2238783 = 3358175) B3358175
theorem B3358181 : Blo 2237435 3358181 := bbase (se 4 (by rfl) ⟨314829, by rfl⟩ : syracuseStep 3358181 = 629659) (by norm_num)
theorem B2238787 : Blo 2237435 2238787 := bstep (se 1 (by rfl) ⟨1679090, by rfl⟩ : syracuseStep 2238787 = 3358181) B3358181
theorem B2553005 : Blo 2237435 2553005 := bbase (se 3 (by rfl) ⟨478688, by rfl⟩ : syracuseStep 2553005 = 957377) (by norm_num)
theorem B6808013 : Blo 2237435 6808013 := bstep (se 3 (by rfl) ⟨1276502, by rfl⟩ : syracuseStep 6808013 = 2553005) B2553005
theorem B4538675 : Blo 2237435 4538675 := bstep (se 1 (by rfl) ⟨3404006, by rfl⟩ : syracuseStep 4538675 = 6808013) B6808013
theorem B3025783 : Blo 2237435 3025783 := bstep (se 1 (by rfl) ⟨2269337, by rfl⟩ : syracuseStep 3025783 = 4538675) B4538675
theorem B4034377 : Blo 2237435 4034377 := bstep (se 2 (by rfl) ⟨1512891, by rfl⟩ : syracuseStep 4034377 = 3025783) B3025783
theorem B21516677 : Blo 2237435 21516677 := bstep (se 4 (by rfl) ⟨2017188, by rfl⟩ : syracuseStep 21516677 = 4034377) B4034377
theorem B14344451 : Blo 2237435 14344451 := bstep (se 1 (by rfl) ⟨10758338, by rfl⟩ : syracuseStep 14344451 = 21516677) B21516677
theorem B9562967 : Blo 2237435 9562967 := bstep (se 1 (by rfl) ⟨7172225, by rfl⟩ : syracuseStep 9562967 = 14344451) B14344451
theorem B6375311 : Blo 2237435 6375311 := bstep (se 1 (by rfl) ⟨4781483, by rfl⟩ : syracuseStep 6375311 = 9562967) B9562967
theorem B4250207 : Blo 2237435 4250207 := bstep (se 1 (by rfl) ⟨3187655, by rfl⟩ : syracuseStep 4250207 = 6375311) B6375311
theorem B2833471 : Blo 2237435 2833471 := bstep (se 1 (by rfl) ⟨2125103, by rfl⟩ : syracuseStep 2833471 = 4250207) B4250207
theorem B3777961 : Blo 2237435 3777961 := bstep (se 2 (by rfl) ⟨1416735, by rfl⟩ : syracuseStep 3777961 = 2833471) B2833471
theorem B5037281 : Blo 2237435 5037281 := bstep (se 2 (by rfl) ⟨1888980, by rfl⟩ : syracuseStep 5037281 = 3777961) B3777961
theorem B3358187 : Blo 2237435 3358187 := bstep (se 1 (by rfl) ⟨2518640, by rfl⟩ : syracuseStep 3358187 = 5037281) B5037281
theorem B2238791 : Blo 2237435 2238791 := bstep (se 1 (by rfl) ⟨1679093, by rfl⟩ : syracuseStep 2238791 = 3358187) B3358187
theorem B2518645 : Blo 2237435 2518645 := bbase (se 5 (by rfl) ⟨118061, by rfl⟩ : syracuseStep 2518645 = 236123) (by norm_num)
theorem B3358193 : Blo 2237435 3358193 := bstep (se 2 (by rfl) ⟨1259322, by rfl⟩ : syracuseStep 3358193 = 2518645) B2518645
theorem B2238795 : Blo 2237435 2238795 := bstep (se 1 (by rfl) ⟨1679096, by rfl⟩ : syracuseStep 2238795 = 3358193) B3358193
theorem B2833481 : Blo 2237435 2833481 := bbase (se 2 (by rfl) ⟨1062555, by rfl⟩ : syracuseStep 2833481 = 2125111) (by norm_num)
theorem B7555949 : Blo 2237435 7555949 := bstep (se 3 (by rfl) ⟨1416740, by rfl⟩ : syracuseStep 7555949 = 2833481) B2833481
theorem B5037299 : Blo 2237435 5037299 := bstep (se 1 (by rfl) ⟨3777974, by rfl⟩ : syracuseStep 5037299 = 7555949) B7555949
theorem B3358199 : Blo 2237435 3358199 := bstep (se 1 (by rfl) ⟨2518649, by rfl⟩ : syracuseStep 3358199 = 5037299) B5037299
theorem B2238799 : Blo 2237435 2238799 := bstep (se 1 (by rfl) ⟨1679099, by rfl⟩ : syracuseStep 2238799 = 3358199) B3358199
theorem B3358205 : Blo 2237435 3358205 := bbase (se 3 (by rfl) ⟨629663, by rfl⟩ : syracuseStep 3358205 = 1259327) (by norm_num)
theorem B2238803 : Blo 2237435 2238803 := bstep (se 1 (by rfl) ⟨1679102, by rfl⟩ : syracuseStep 2238803 = 3358205) B3358205
theorem B5037317 : Blo 2237435 5037317 := bbase (se 4 (by rfl) ⟨472248, by rfl⟩ : syracuseStep 5037317 = 944497) (by norm_num)
theorem B3358211 : Blo 2237435 3358211 := bstep (se 1 (by rfl) ⟨2518658, by rfl⟩ : syracuseStep 3358211 = 5037317) B5037317
theorem B2238807 : Blo 2237435 2238807 := bstep (se 1 (by rfl) ⟨1679105, by rfl⟩ : syracuseStep 2238807 = 3358211) B3358211
theorem B4250245 : Blo 2237435 4250245 := bbase (se 4 (by rfl) ⟨398460, by rfl⟩ : syracuseStep 4250245 = 796921) (by norm_num)
theorem B5666993 : Blo 2237435 5666993 := bstep (se 2 (by rfl) ⟨2125122, by rfl⟩ : syracuseStep 5666993 = 4250245) B4250245
theorem B3777995 : Blo 2237435 3777995 := bstep (se 1 (by rfl) ⟨2833496, by rfl⟩ : syracuseStep 3777995 = 5666993) B5666993
theorem B2518663 : Blo 2237435 2518663 := bstep (se 1 (by rfl) ⟨1888997, by rfl⟩ : syracuseStep 2518663 = 3777995) B3777995
theorem B3358217 : Blo 2237435 3358217 := bstep (se 2 (by rfl) ⟨1259331, by rfl⟩ : syracuseStep 3358217 = 2518663) B2518663
theorem B2238811 : Blo 2237435 2238811 := bstep (se 1 (by rfl) ⟨1679108, by rfl⟩ : syracuseStep 2238811 = 3358217) B3358217
theorem B11334005 : Blo 2237435 11334005 := bbase (se 5 (by rfl) ⟨531281, by rfl⟩ : syracuseStep 11334005 = 1062563) (by norm_num)
theorem B7556003 : Blo 2237435 7556003 := bstep (se 1 (by rfl) ⟨5667002, by rfl⟩ : syracuseStep 7556003 = 11334005) B11334005
theorem B5037335 : Blo 2237435 5037335 := bstep (se 1 (by rfl) ⟨3778001, by rfl⟩ : syracuseStep 5037335 = 7556003) B7556003
theorem B3358223 : Blo 2237435 3358223 := bstep (se 1 (by rfl) ⟨2518667, by rfl⟩ : syracuseStep 3358223 = 5037335) B5037335
theorem B2238815 : Blo 2237435 2238815 := bstep (se 1 (by rfl) ⟨1679111, by rfl⟩ : syracuseStep 2238815 = 3358223) B3358223
theorem B3358229 : Blo 2237435 3358229 := bbase (se 6 (by rfl) ⟨78708, by rfl⟩ : syracuseStep 3358229 = 157417) (by norm_num)
theorem B2238819 : Blo 2237435 2238819 := bstep (se 1 (by rfl) ⟨1679114, by rfl⟩ : syracuseStep 2238819 = 3358229) B3358229
theorem B3635093 : Blo 2237435 3635093 := bbase (se 6 (by rfl) ⟨85197, by rfl⟩ : syracuseStep 3635093 = 170395) (by norm_num)
theorem B2423395 : Blo 2237435 2423395 := bstep (se 1 (by rfl) ⟨1817546, by rfl⟩ : syracuseStep 2423395 = 3635093) B3635093
theorem B3231193 : Blo 2237435 3231193 := bstep (se 2 (by rfl) ⟨1211697, by rfl⟩ : syracuseStep 3231193 = 2423395) B2423395
theorem B4308257 : Blo 2237435 4308257 := bstep (se 2 (by rfl) ⟨1615596, by rfl⟩ : syracuseStep 4308257 = 3231193) B3231193
theorem B2872171 : Blo 2237435 2872171 := bstep (se 1 (by rfl) ⟨2154128, by rfl⟩ : syracuseStep 2872171 = 4308257) B4308257
theorem B3829561 : Blo 2237435 3829561 := bstep (se 2 (by rfl) ⟨1436085, by rfl⟩ : syracuseStep 3829561 = 2872171) B2872171
theorem B20424325 : Blo 2237435 20424325 := bstep (se 4 (by rfl) ⟨1914780, by rfl⟩ : syracuseStep 20424325 = 3829561) B3829561
theorem B27232433 : Blo 2237435 27232433 := bstep (se 2 (by rfl) ⟨10212162, by rfl⟩ : syracuseStep 27232433 = 20424325) B20424325
theorem B18154955 : Blo 2237435 18154955 := bstep (se 1 (by rfl) ⟨13616216, by rfl⟩ : syracuseStep 18154955 = 27232433) B27232433
theorem B12103303 : Blo 2237435 12103303 := bstep (se 1 (by rfl) ⟨9077477, by rfl⟩ : syracuseStep 12103303 = 18154955) B18154955
theorem B16137737 : Blo 2237435 16137737 := bstep (se 2 (by rfl) ⟨6051651, by rfl⟩ : syracuseStep 16137737 = 12103303) B12103303
theorem B10758491 : Blo 2237435 10758491 := bstep (se 1 (by rfl) ⟨8068868, by rfl⟩ : syracuseStep 10758491 = 16137737) B16137737
theorem B7172327 : Blo 2237435 7172327 := bstep (se 1 (by rfl) ⟨5379245, by rfl⟩ : syracuseStep 7172327 = 10758491) B10758491
theorem B19126205 : Blo 2237435 19126205 := bstep (se 3 (by rfl) ⟨3586163, by rfl⟩ : syracuseStep 19126205 = 7172327) B7172327
theorem B12750803 : Blo 2237435 12750803 := bstep (se 1 (by rfl) ⟨9563102, by rfl⟩ : syracuseStep 12750803 = 19126205) B19126205
theorem B8500535 : Blo 2237435 8500535 := bstep (se 1 (by rfl) ⟨6375401, by rfl⟩ : syracuseStep 8500535 = 12750803) B12750803
theorem B5667023 : Blo 2237435 5667023 := bstep (se 1 (by rfl) ⟨4250267, by rfl⟩ : syracuseStep 5667023 = 8500535) B8500535
theorem B3778015 : Blo 2237435 3778015 := bstep (se 1 (by rfl) ⟨2833511, by rfl⟩ : syracuseStep 3778015 = 5667023) B5667023
theorem B5037353 : Blo 2237435 5037353 := bstep (se 2 (by rfl) ⟨1889007, by rfl⟩ : syracuseStep 5037353 = 3778015) B3778015
theorem B3358235 : Blo 2237435 3358235 := bstep (se 1 (by rfl) ⟨2518676, by rfl⟩ : syracuseStep 3358235 = 5037353) B5037353
theorem B2238823 : Blo 2237435 2238823 := bstep (se 1 (by rfl) ⟨1679117, by rfl⟩ : syracuseStep 2238823 = 3358235) B3358235
theorem B2518681 : Blo 2237435 2518681 := bbase (se 2 (by rfl) ⟨944505, by rfl⟩ : syracuseStep 2518681 = 1889011) (by norm_num)
theorem B3358241 : Blo 2237435 3358241 := bstep (se 2 (by rfl) ⟨1259340, by rfl⟩ : syracuseStep 3358241 = 2518681) B2518681
theorem B2238827 : Blo 2237435 2238827 := bstep (se 1 (by rfl) ⟨1679120, by rfl⟩ : syracuseStep 2238827 = 3358241) B3358241
theorem B8500565 : Blo 2237435 8500565 := bbase (se 13 (by rfl) ⟨1556, by rfl⟩ : syracuseStep 8500565 = 3113) (by norm_num)
theorem B5667043 : Blo 2237435 5667043 := bstep (se 1 (by rfl) ⟨4250282, by rfl⟩ : syracuseStep 5667043 = 8500565) B8500565
theorem B7556057 : Blo 2237435 7556057 := bstep (se 2 (by rfl) ⟨2833521, by rfl⟩ : syracuseStep 7556057 = 5667043) B5667043
theorem B5037371 : Blo 2237435 5037371 := bstep (se 1 (by rfl) ⟨3778028, by rfl⟩ : syracuseStep 5037371 = 7556057) B7556057
theorem B3358247 : Blo 2237435 3358247 := bstep (se 1 (by rfl) ⟨2518685, by rfl⟩ : syracuseStep 3358247 = 5037371) B5037371
theorem B2238831 : Blo 2237435 2238831 := bstep (se 1 (by rfl) ⟨1679123, by rfl⟩ : syracuseStep 2238831 = 3358247) B3358247
theorem B3358253 : Blo 2237435 3358253 := bbase (se 3 (by rfl) ⟨629672, by rfl⟩ : syracuseStep 3358253 = 1259345) (by norm_num)
theorem B2238835 : Blo 2237435 2238835 := bstep (se 1 (by rfl) ⟨1679126, by rfl⟩ : syracuseStep 2238835 = 3358253) B3358253
theorem B5037389 : Blo 2237435 5037389 := bbase (se 3 (by rfl) ⟨944510, by rfl⟩ : syracuseStep 5037389 = 1889021) (by norm_num)
theorem B3358259 : Blo 2237435 3358259 := bstep (se 1 (by rfl) ⟨2518694, by rfl⟩ : syracuseStep 3358259 = 5037389) B5037389
theorem B2238839 : Blo 2237435 2238839 := bstep (se 1 (by rfl) ⟨1679129, by rfl⟩ : syracuseStep 2238839 = 3358259) B3358259
theorem B2833537 : Blo 2237435 2833537 := bbase (se 2 (by rfl) ⟨1062576, by rfl⟩ : syracuseStep 2833537 = 2125153) (by norm_num)
theorem B3778049 : Blo 2237435 3778049 := bstep (se 2 (by rfl) ⟨1416768, by rfl⟩ : syracuseStep 3778049 = 2833537) B2833537
theorem B2518699 : Blo 2237435 2518699 := bstep (se 1 (by rfl) ⟨1889024, by rfl⟩ : syracuseStep 2518699 = 3778049) B3778049
theorem B3358265 : Blo 2237435 3358265 := bstep (se 2 (by rfl) ⟨1259349, by rfl⟩ : syracuseStep 3358265 = 2518699) B2518699
theorem B2238843 : Blo 2237435 2238843 := bstep (se 1 (by rfl) ⟨1679132, by rfl⟩ : syracuseStep 2238843 = 3358265) B3358265
theorem B2390801 : Blo 2237435 2390801 := bbase (se 2 (by rfl) ⟨896550, by rfl⟩ : syracuseStep 2390801 = 1793101) (by norm_num)
theorem B25501877 : Blo 2237435 25501877 := bstep (se 5 (by rfl) ⟨1195400, by rfl⟩ : syracuseStep 25501877 = 2390801) B2390801
theorem B17001251 : Blo 2237435 17001251 := bstep (se 1 (by rfl) ⟨12750938, by rfl⟩ : syracuseStep 17001251 = 25501877) B25501877
theorem B11334167 : Blo 2237435 11334167 := bstep (se 1 (by rfl) ⟨8500625, by rfl⟩ : syracuseStep 11334167 = 17001251) B17001251
theorem B7556111 : Blo 2237435 7556111 := bstep (se 1 (by rfl) ⟨5667083, by rfl⟩ : syracuseStep 7556111 = 11334167) B11334167
theorem B5037407 : Blo 2237435 5037407 := bstep (se 1 (by rfl) ⟨3778055, by rfl⟩ : syracuseStep 5037407 = 7556111) B7556111
theorem B3358271 : Blo 2237435 3358271 := bstep (se 1 (by rfl) ⟨2518703, by rfl⟩ : syracuseStep 3358271 = 5037407) B5037407
theorem B2238847 : Blo 2237435 2238847 := bstep (se 1 (by rfl) ⟨1679135, by rfl⟩ : syracuseStep 2238847 = 3358271) B3358271
theorem B3358277 : Blo 2237435 3358277 := bbase (se 4 (by rfl) ⟨314838, by rfl⟩ : syracuseStep 3358277 = 629677) (by norm_num)
theorem B2238851 : Blo 2237435 2238851 := bstep (se 1 (by rfl) ⟨1679138, by rfl⟩ : syracuseStep 2238851 = 3358277) B3358277
theorem B3778069 : Blo 2237435 3778069 := bbase (se 6 (by rfl) ⟨88548, by rfl⟩ : syracuseStep 3778069 = 177097) (by norm_num)
theorem B5037425 : Blo 2237435 5037425 := bstep (se 2 (by rfl) ⟨1889034, by rfl⟩ : syracuseStep 5037425 = 3778069) B3778069
theorem B3358283 : Blo 2237435 3358283 := bstep (se 1 (by rfl) ⟨2518712, by rfl⟩ : syracuseStep 3358283 = 5037425) B5037425
theorem B2238855 : Blo 2237435 2238855 := bstep (se 1 (by rfl) ⟨1679141, by rfl⟩ : syracuseStep 2238855 = 3358283) B3358283
theorem B2518717 : Blo 2237435 2518717 := bbase (se 3 (by rfl) ⟨472259, by rfl⟩ : syracuseStep 2518717 = 944519) (by norm_num)
theorem B3358289 : Blo 2237435 3358289 := bstep (se 2 (by rfl) ⟨1259358, by rfl⟩ : syracuseStep 3358289 = 2518717) B2518717
theorem B2238859 : Blo 2237435 2238859 := bstep (se 1 (by rfl) ⟨1679144, by rfl⟩ : syracuseStep 2238859 = 3358289) B3358289
theorem B7556165 : Blo 2237435 7556165 := bbase (se 4 (by rfl) ⟨708390, by rfl⟩ : syracuseStep 7556165 = 1416781) (by norm_num)
theorem B5037443 : Blo 2237435 5037443 := bstep (se 1 (by rfl) ⟨3778082, by rfl⟩ : syracuseStep 5037443 = 7556165) B7556165
theorem B3358295 : Blo 2237435 3358295 := bstep (se 1 (by rfl) ⟨2518721, by rfl⟩ : syracuseStep 3358295 = 5037443) B5037443
theorem B2238863 : Blo 2237435 2238863 := bstep (se 1 (by rfl) ⟨1679147, by rfl⟩ : syracuseStep 2238863 = 3358295) B3358295
theorem B3358301 : Blo 2237435 3358301 := bbase (se 3 (by rfl) ⟨629681, by rfl⟩ : syracuseStep 3358301 = 1259363) (by norm_num)
theorem B2238867 : Blo 2237435 2238867 := bstep (se 1 (by rfl) ⟨1679150, by rfl⟩ : syracuseStep 2238867 = 3358301) B3358301
theorem B5037461 : Blo 2237435 5037461 := bbase (se 6 (by rfl) ⟨118065, by rfl⟩ : syracuseStep 5037461 = 236131) (by norm_num)
theorem B3358307 : Blo 2237435 3358307 := bstep (se 1 (by rfl) ⟨2518730, by rfl⟩ : syracuseStep 3358307 = 5037461) B5037461
theorem B2238871 : Blo 2237435 2238871 := bstep (se 1 (by rfl) ⟨1679153, by rfl⟩ : syracuseStep 2238871 = 3358307) B3358307
theorem B4538845 : Blo 2237435 4538845 := bbase (se 3 (by rfl) ⟨851033, by rfl⟩ : syracuseStep 4538845 = 1702067) (by norm_num)
theorem B24207173 : Blo 2237435 24207173 := bstep (se 4 (by rfl) ⟨2269422, by rfl⟩ : syracuseStep 24207173 = 4538845) B4538845
theorem B16138115 : Blo 2237435 16138115 := bstep (se 1 (by rfl) ⟨12103586, by rfl⟩ : syracuseStep 16138115 = 24207173) B24207173
theorem B10758743 : Blo 2237435 10758743 := bstep (se 1 (by rfl) ⟨8069057, by rfl⟩ : syracuseStep 10758743 = 16138115) B16138115
theorem B7172495 : Blo 2237435 7172495 := bstep (se 1 (by rfl) ⟨5379371, by rfl⟩ : syracuseStep 7172495 = 10758743) B10758743
theorem B4781663 : Blo 2237435 4781663 := bstep (se 1 (by rfl) ⟨3586247, by rfl⟩ : syracuseStep 4781663 = 7172495) B7172495
theorem B3187775 : Blo 2237435 3187775 := bstep (se 1 (by rfl) ⟨2390831, by rfl⟩ : syracuseStep 3187775 = 4781663) B4781663
theorem B8500733 : Blo 2237435 8500733 := bstep (se 3 (by rfl) ⟨1593887, by rfl⟩ : syracuseStep 8500733 = 3187775) B3187775
theorem B5667155 : Blo 2237435 5667155 := bstep (se 1 (by rfl) ⟨4250366, by rfl⟩ : syracuseStep 5667155 = 8500733) B8500733
theorem B3778103 : Blo 2237435 3778103 := bstep (se 1 (by rfl) ⟨2833577, by rfl⟩ : syracuseStep 3778103 = 5667155) B5667155
theorem B2518735 : Blo 2237435 2518735 := bstep (se 1 (by rfl) ⟨1889051, by rfl⟩ : syracuseStep 2518735 = 3778103) B3778103
theorem B3358313 : Blo 2237435 3358313 := bstep (se 2 (by rfl) ⟨1259367, by rfl⟩ : syracuseStep 3358313 = 2518735) B2518735
theorem B2238875 : Blo 2237435 2238875 := bstep (se 1 (by rfl) ⟨1679156, by rfl⟩ : syracuseStep 2238875 = 3358313) B3358313
theorem B3586253 : Blo 2237435 3586253 := bbase (se 3 (by rfl) ⟨672422, by rfl⟩ : syracuseStep 3586253 = 1344845) (by norm_num)
theorem B9563341 : Blo 2237435 9563341 := bstep (se 3 (by rfl) ⟨1793126, by rfl⟩ : syracuseStep 9563341 = 3586253) B3586253
theorem B12751121 : Blo 2237435 12751121 := bstep (se 2 (by rfl) ⟨4781670, by rfl⟩ : syracuseStep 12751121 = 9563341) B9563341
theorem B8500747 : Blo 2237435 8500747 := bstep (se 1 (by rfl) ⟨6375560, by rfl⟩ : syracuseStep 8500747 = 12751121) B12751121
theorem B11334329 : Blo 2237435 11334329 := bstep (se 2 (by rfl) ⟨4250373, by rfl⟩ : syracuseStep 11334329 = 8500747) B8500747
theorem B7556219 : Blo 2237435 7556219 := bstep (se 1 (by rfl) ⟨5667164, by rfl⟩ : syracuseStep 7556219 = 11334329) B11334329
theorem B5037479 : Blo 2237435 5037479 := bstep (se 1 (by rfl) ⟨3778109, by rfl⟩ : syracuseStep 5037479 = 7556219) B7556219
theorem B3358319 : Blo 2237435 3358319 := bstep (se 1 (by rfl) ⟨2518739, by rfl⟩ : syracuseStep 3358319 = 5037479) B5037479
theorem B2238879 : Blo 2237435 2238879 := bstep (se 1 (by rfl) ⟨1679159, by rfl⟩ : syracuseStep 2238879 = 3358319) B3358319
theorem B3358325 : Blo 2237435 3358325 := bbase (se 5 (by rfl) ⟨157421, by rfl⟩ : syracuseStep 3358325 = 314843) (by norm_num)
theorem B2238883 : Blo 2237435 2238883 := bstep (se 1 (by rfl) ⟨1679162, by rfl⟩ : syracuseStep 2238883 = 3358325) B3358325
theorem B4250389 : Blo 2237435 4250389 := bbase (se 6 (by rfl) ⟨99618, by rfl⟩ : syracuseStep 4250389 = 199237) (by norm_num)
theorem B5667185 : Blo 2237435 5667185 := bstep (se 2 (by rfl) ⟨2125194, by rfl⟩ : syracuseStep 5667185 = 4250389) B4250389
theorem B3778123 : Blo 2237435 3778123 := bstep (se 1 (by rfl) ⟨2833592, by rfl⟩ : syracuseStep 3778123 = 5667185) B5667185
theorem B5037497 : Blo 2237435 5037497 := bstep (se 2 (by rfl) ⟨1889061, by rfl⟩ : syracuseStep 5037497 = 3778123) B3778123
theorem B3358331 : Blo 2237435 3358331 := bstep (se 1 (by rfl) ⟨2518748, by rfl⟩ : syracuseStep 3358331 = 5037497) B5037497
theorem B2238887 : Blo 2237435 2238887 := bstep (se 1 (by rfl) ⟨1679165, by rfl⟩ : syracuseStep 2238887 = 3358331) B3358331
theorem B2518753 : Blo 2237435 2518753 := bbase (se 2 (by rfl) ⟨944532, by rfl⟩ : syracuseStep 2518753 = 1889065) (by norm_num)
theorem B3358337 : Blo 2237435 3358337 := bstep (se 2 (by rfl) ⟨1259376, by rfl⟩ : syracuseStep 3358337 = 2518753) B2518753
theorem B2238891 : Blo 2237435 2238891 := bstep (se 1 (by rfl) ⟨1679168, by rfl⟩ : syracuseStep 2238891 = 3358337) B3358337
theorem B5667205 : Blo 2237435 5667205 := bbase (se 4 (by rfl) ⟨531300, by rfl⟩ : syracuseStep 5667205 = 1062601) (by norm_num)
theorem B7556273 : Blo 2237435 7556273 := bstep (se 2 (by rfl) ⟨2833602, by rfl⟩ : syracuseStep 7556273 = 5667205) B5667205
theorem B5037515 : Blo 2237435 5037515 := bstep (se 1 (by rfl) ⟨3778136, by rfl⟩ : syracuseStep 5037515 = 7556273) B7556273
theorem B3358343 : Blo 2237435 3358343 := bstep (se 1 (by rfl) ⟨2518757, by rfl⟩ : syracuseStep 3358343 = 5037515) B5037515
theorem B2238895 : Blo 2237435 2238895 := bstep (se 1 (by rfl) ⟨1679171, by rfl⟩ : syracuseStep 2238895 = 3358343) B3358343
theorem B3358349 : Blo 2237435 3358349 := bbase (se 3 (by rfl) ⟨629690, by rfl⟩ : syracuseStep 3358349 = 1259381) (by norm_num)
theorem B2238899 : Blo 2237435 2238899 := bstep (se 1 (by rfl) ⟨1679174, by rfl⟩ : syracuseStep 2238899 = 3358349) B3358349
theorem B5037533 : Blo 2237435 5037533 := bbase (se 3 (by rfl) ⟨944537, by rfl⟩ : syracuseStep 5037533 = 1889075) (by norm_num)
theorem B3358355 : Blo 2237435 3358355 := bstep (se 1 (by rfl) ⟨2518766, by rfl⟩ : syracuseStep 3358355 = 5037533) B5037533
theorem B2238903 : Blo 2237435 2238903 := bstep (se 1 (by rfl) ⟨1679177, by rfl⟩ : syracuseStep 2238903 = 3358355) B3358355
theorem B3778157 : Blo 2237435 3778157 := bbase (se 3 (by rfl) ⟨708404, by rfl⟩ : syracuseStep 3778157 = 1416809) (by norm_num)
theorem B2518771 : Blo 2237435 2518771 := bstep (se 1 (by rfl) ⟨1889078, by rfl⟩ : syracuseStep 2518771 = 3778157) B3778157
theorem B3358361 : Blo 2237435 3358361 := bstep (se 2 (by rfl) ⟨1259385, by rfl⟩ : syracuseStep 3358361 = 2518771) B2518771
theorem B2238907 : Blo 2237435 2238907 := bstep (se 1 (by rfl) ⟨1679180, by rfl⟩ : syracuseStep 2238907 = 3358361) B3358361
theorem B7270469 : Blo 2237435 7270469 := bbase (se 4 (by rfl) ⟨681606, by rfl⟩ : syracuseStep 7270469 = 1363213) (by norm_num)
theorem B4846979 : Blo 2237435 4846979 := bstep (se 1 (by rfl) ⟨3635234, by rfl⟩ : syracuseStep 4846979 = 7270469) B7270469
theorem B12925277 : Blo 2237435 12925277 := bstep (se 3 (by rfl) ⟨2423489, by rfl⟩ : syracuseStep 12925277 = 4846979) B4846979
theorem B8616851 : Blo 2237435 8616851 := bstep (se 1 (by rfl) ⟨6462638, by rfl⟩ : syracuseStep 8616851 = 12925277) B12925277
theorem B5744567 : Blo 2237435 5744567 := bstep (se 1 (by rfl) ⟨4308425, by rfl⟩ : syracuseStep 5744567 = 8616851) B8616851
theorem B15318845 : Blo 2237435 15318845 := bstep (se 3 (by rfl) ⟨2872283, by rfl⟩ : syracuseStep 15318845 = 5744567) B5744567
theorem B10212563 : Blo 2237435 10212563 := bstep (se 1 (by rfl) ⟨7659422, by rfl⟩ : syracuseStep 10212563 = 15318845) B15318845
theorem B6808375 : Blo 2237435 6808375 := bstep (se 1 (by rfl) ⟨5106281, by rfl⟩ : syracuseStep 6808375 = 10212563) B10212563
theorem B9077833 : Blo 2237435 9077833 := bstep (se 2 (by rfl) ⟨3404187, by rfl⟩ : syracuseStep 9077833 = 6808375) B6808375
theorem B12103777 : Blo 2237435 12103777 := bstep (se 2 (by rfl) ⟨4538916, by rfl⟩ : syracuseStep 12103777 = 9077833) B9077833
theorem B16138369 : Blo 2237435 16138369 := bstep (se 2 (by rfl) ⟨6051888, by rfl⟩ : syracuseStep 16138369 = 12103777) B12103777
theorem B21517825 : Blo 2237435 21517825 := bstep (se 2 (by rfl) ⟨8069184, by rfl⟩ : syracuseStep 21517825 = 16138369) B16138369
theorem B28690433 : Blo 2237435 28690433 := bstep (se 2 (by rfl) ⟨10758912, by rfl⟩ : syracuseStep 28690433 = 21517825) B21517825
theorem B19126955 : Blo 2237435 19126955 := bstep (se 1 (by rfl) ⟨14345216, by rfl⟩ : syracuseStep 19126955 = 28690433) B28690433
theorem B12751303 : Blo 2237435 12751303 := bstep (se 1 (by rfl) ⟨9563477, by rfl⟩ : syracuseStep 12751303 = 19126955) B19126955
theorem B17001737 : Blo 2237435 17001737 := bstep (se 2 (by rfl) ⟨6375651, by rfl⟩ : syracuseStep 17001737 = 12751303) B12751303
theorem B11334491 : Blo 2237435 11334491 := bstep (se 1 (by rfl) ⟨8500868, by rfl⟩ : syracuseStep 11334491 = 17001737) B17001737
theorem B7556327 : Blo 2237435 7556327 := bstep (se 1 (by rfl) ⟨5667245, by rfl⟩ : syracuseStep 7556327 = 11334491) B11334491
theorem B5037551 : Blo 2237435 5037551 := bstep (se 1 (by rfl) ⟨3778163, by rfl⟩ : syracuseStep 5037551 = 7556327) B7556327
theorem B3358367 : Blo 2237435 3358367 := bstep (se 1 (by rfl) ⟨2518775, by rfl⟩ : syracuseStep 3358367 = 5037551) B5037551
theorem B2238911 : Blo 2237435 2238911 := bstep (se 1 (by rfl) ⟨1679183, by rfl⟩ : syracuseStep 2238911 = 3358367) B3358367
theorem B3358373 : Blo 2237435 3358373 := bbase (se 4 (by rfl) ⟨314847, by rfl⟩ : syracuseStep 3358373 = 629695) (by norm_num)
theorem B2238915 : Blo 2237435 2238915 := bstep (se 1 (by rfl) ⟨1679186, by rfl⟩ : syracuseStep 2238915 = 3358373) B3358373
theorem B2833633 : Blo 2237435 2833633 := bbase (se 2 (by rfl) ⟨1062612, by rfl⟩ : syracuseStep 2833633 = 2125225) (by norm_num)
theorem B3778177 : Blo 2237435 3778177 := bstep (se 2 (by rfl) ⟨1416816, by rfl⟩ : syracuseStep 3778177 = 2833633) B2833633
theorem B5037569 : Blo 2237435 5037569 := bstep (se 2 (by rfl) ⟨1889088, by rfl⟩ : syracuseStep 5037569 = 3778177) B3778177
theorem B3358379 : Blo 2237435 3358379 := bstep (se 1 (by rfl) ⟨2518784, by rfl⟩ : syracuseStep 3358379 = 5037569) B5037569
theorem B2238919 : Blo 2237435 2238919 := bstep (se 1 (by rfl) ⟨1679189, by rfl⟩ : syracuseStep 2238919 = 3358379) B3358379
theorem B2518789 : Blo 2237435 2518789 := bbase (se 4 (by rfl) ⟨236136, by rfl⟩ : syracuseStep 2518789 = 472273) (by norm_num)
theorem B3358385 : Blo 2237435 3358385 := bstep (se 2 (by rfl) ⟨1259394, by rfl⟩ : syracuseStep 3358385 = 2518789) B2518789
theorem B2238923 : Blo 2237435 2238923 := bstep (se 1 (by rfl) ⟨1679192, by rfl⟩ : syracuseStep 2238923 = 3358385) B3358385
theorem B8616917 : Blo 2237435 8616917 := bbase (se 7 (by rfl) ⟨100979, by rfl⟩ : syracuseStep 8616917 = 201959) (by norm_num)
theorem B5744611 : Blo 2237435 5744611 := bstep (se 1 (by rfl) ⟨4308458, by rfl⟩ : syracuseStep 5744611 = 8616917) B8616917
theorem B30637925 : Blo 2237435 30637925 := bstep (se 4 (by rfl) ⟨2872305, by rfl⟩ : syracuseStep 30637925 = 5744611) B5744611
theorem B20425283 : Blo 2237435 20425283 := bstep (se 1 (by rfl) ⟨15318962, by rfl⟩ : syracuseStep 20425283 = 30637925) B30637925
theorem B13616855 : Blo 2237435 13616855 := bstep (se 1 (by rfl) ⟨10212641, by rfl⟩ : syracuseStep 13616855 = 20425283) B20425283
theorem B9077903 : Blo 2237435 9077903 := bstep (se 1 (by rfl) ⟨6808427, by rfl⟩ : syracuseStep 9077903 = 13616855) B13616855
theorem B6051935 : Blo 2237435 6051935 := bstep (se 1 (by rfl) ⟨4538951, by rfl⟩ : syracuseStep 6051935 = 9077903) B9077903
theorem B4034623 : Blo 2237435 4034623 := bstep (se 1 (by rfl) ⟨3025967, by rfl⟩ : syracuseStep 4034623 = 6051935) B6051935
theorem B5379497 : Blo 2237435 5379497 := bstep (se 2 (by rfl) ⟨2017311, by rfl⟩ : syracuseStep 5379497 = 4034623) B4034623
theorem B3586331 : Blo 2237435 3586331 := bstep (se 1 (by rfl) ⟨2689748, by rfl⟩ : syracuseStep 3586331 = 5379497) B5379497
theorem B2390887 : Blo 2237435 2390887 := bstep (se 1 (by rfl) ⟨1793165, by rfl⟩ : syracuseStep 2390887 = 3586331) B3586331
theorem B3187849 : Blo 2237435 3187849 := bstep (se 2 (by rfl) ⟨1195443, by rfl⟩ : syracuseStep 3187849 = 2390887) B2390887
theorem B4250465 : Blo 2237435 4250465 := bstep (se 2 (by rfl) ⟨1593924, by rfl⟩ : syracuseStep 4250465 = 3187849) B3187849
theorem B2833643 : Blo 2237435 2833643 := bstep (se 1 (by rfl) ⟨2125232, by rfl⟩ : syracuseStep 2833643 = 4250465) B4250465
theorem B7556381 : Blo 2237435 7556381 := bstep (se 3 (by rfl) ⟨1416821, by rfl⟩ : syracuseStep 7556381 = 2833643) B2833643
theorem B5037587 : Blo 2237435 5037587 := bstep (se 1 (by rfl) ⟨3778190, by rfl⟩ : syracuseStep 5037587 = 7556381) B7556381
theorem B3358391 : Blo 2237435 3358391 := bstep (se 1 (by rfl) ⟨2518793, by rfl⟩ : syracuseStep 3358391 = 5037587) B5037587
theorem B2238927 : Blo 2237435 2238927 := bstep (se 1 (by rfl) ⟨1679195, by rfl⟩ : syracuseStep 2238927 = 3358391) B3358391
theorem B3358397 : Blo 2237435 3358397 := bbase (se 3 (by rfl) ⟨629699, by rfl⟩ : syracuseStep 3358397 = 1259399) (by norm_num)
theorem B2238931 : Blo 2237435 2238931 := bstep (se 1 (by rfl) ⟨1679198, by rfl⟩ : syracuseStep 2238931 = 3358397) B3358397
theorem B5037605 : Blo 2237435 5037605 := bbase (se 4 (by rfl) ⟨472275, by rfl⟩ : syracuseStep 5037605 = 944551) (by norm_num)
theorem B3358403 : Blo 2237435 3358403 := bstep (se 1 (by rfl) ⟨2518802, by rfl⟩ : syracuseStep 3358403 = 5037605) B5037605
theorem B2238935 : Blo 2237435 2238935 := bstep (se 1 (by rfl) ⟨1679201, by rfl⟩ : syracuseStep 2238935 = 3358403) B3358403
theorem B5667317 : Blo 2237435 5667317 := bbase (se 5 (by rfl) ⟨265655, by rfl⟩ : syracuseStep 5667317 = 531311) (by norm_num)
theorem B3778211 : Blo 2237435 3778211 := bstep (se 1 (by rfl) ⟨2833658, by rfl⟩ : syracuseStep 3778211 = 5667317) B5667317
theorem B2518807 : Blo 2237435 2518807 := bstep (se 1 (by rfl) ⟨1889105, by rfl⟩ : syracuseStep 2518807 = 3778211) B3778211
theorem B3358409 : Blo 2237435 3358409 := bstep (se 2 (by rfl) ⟨1259403, by rfl⟩ : syracuseStep 3358409 = 2518807) B2518807
theorem B2238939 : Blo 2237435 2238939 := bstep (se 1 (by rfl) ⟨1679204, by rfl⟩ : syracuseStep 2238939 = 3358409) B3358409
theorem B40850837 : Blo 2237435 40850837 := bbase (se 6 (by rfl) ⟨957441, by rfl⟩ : syracuseStep 40850837 = 1914883) (by norm_num)
theorem B27233891 : Blo 2237435 27233891 := bstep (se 1 (by rfl) ⟨20425418, by rfl⟩ : syracuseStep 27233891 = 40850837) B40850837
theorem B18155927 : Blo 2237435 18155927 := bstep (se 1 (by rfl) ⟨13616945, by rfl⟩ : syracuseStep 18155927 = 27233891) B27233891
theorem B48415805 : Blo 2237435 48415805 := bstep (se 3 (by rfl) ⟨9077963, by rfl⟩ : syracuseStep 48415805 = 18155927) B18155927
theorem B32277203 : Blo 2237435 32277203 := bstep (se 1 (by rfl) ⟨24207902, by rfl⟩ : syracuseStep 32277203 = 48415805) B48415805
theorem B21518135 : Blo 2237435 21518135 := bstep (se 1 (by rfl) ⟨16138601, by rfl⟩ : syracuseStep 21518135 = 32277203) B32277203
theorem B14345423 : Blo 2237435 14345423 := bstep (se 1 (by rfl) ⟨10759067, by rfl⟩ : syracuseStep 14345423 = 21518135) B21518135
theorem B9563615 : Blo 2237435 9563615 := bstep (se 1 (by rfl) ⟨7172711, by rfl⟩ : syracuseStep 9563615 = 14345423) B14345423
theorem B6375743 : Blo 2237435 6375743 := bstep (se 1 (by rfl) ⟨4781807, by rfl⟩ : syracuseStep 6375743 = 9563615) B9563615
theorem B4250495 : Blo 2237435 4250495 := bstep (se 1 (by rfl) ⟨3187871, by rfl⟩ : syracuseStep 4250495 = 6375743) B6375743
theorem B11334653 : Blo 2237435 11334653 := bstep (se 3 (by rfl) ⟨2125247, by rfl⟩ : syracuseStep 11334653 = 4250495) B4250495
theorem B7556435 : Blo 2237435 7556435 := bstep (se 1 (by rfl) ⟨5667326, by rfl⟩ : syracuseStep 7556435 = 11334653) B11334653
theorem B5037623 : Blo 2237435 5037623 := bstep (se 1 (by rfl) ⟨3778217, by rfl⟩ : syracuseStep 5037623 = 7556435) B7556435
theorem B3358415 : Blo 2237435 3358415 := bstep (se 1 (by rfl) ⟨2518811, by rfl⟩ : syracuseStep 3358415 = 5037623) B5037623
theorem B2238943 : Blo 2237435 2238943 := bstep (se 1 (by rfl) ⟨1679207, by rfl⟩ : syracuseStep 2238943 = 3358415) B3358415
theorem B3358421 : Blo 2237435 3358421 := bbase (se 7 (by rfl) ⟨39356, by rfl⟩ : syracuseStep 3358421 = 78713) (by norm_num)
theorem B2238947 : Blo 2237435 2238947 := bstep (se 1 (by rfl) ⟨1679210, by rfl⟩ : syracuseStep 2238947 = 3358421) B3358421
theorem B2689777 : Blo 2237435 2689777 := bbase (se 2 (by rfl) ⟨1008666, by rfl⟩ : syracuseStep 2689777 = 2017333) (by norm_num)
theorem B3586369 : Blo 2237435 3586369 := bstep (se 2 (by rfl) ⟨1344888, by rfl⟩ : syracuseStep 3586369 = 2689777) B2689777
theorem B4781825 : Blo 2237435 4781825 := bstep (se 2 (by rfl) ⟨1793184, by rfl⟩ : syracuseStep 4781825 = 3586369) B3586369
theorem B3187883 : Blo 2237435 3187883 := bstep (se 1 (by rfl) ⟨2390912, by rfl⟩ : syracuseStep 3187883 = 4781825) B4781825
theorem B8501021 : Blo 2237435 8501021 := bstep (se 3 (by rfl) ⟨1593941, by rfl⟩ : syracuseStep 8501021 = 3187883) B3187883
theorem B5667347 : Blo 2237435 5667347 := bstep (se 1 (by rfl) ⟨4250510, by rfl⟩ : syracuseStep 5667347 = 8501021) B8501021
theorem B3778231 : Blo 2237435 3778231 := bstep (se 1 (by rfl) ⟨2833673, by rfl⟩ : syracuseStep 3778231 = 5667347) B5667347
theorem B5037641 : Blo 2237435 5037641 := bstep (se 2 (by rfl) ⟨1889115, by rfl⟩ : syracuseStep 5037641 = 3778231) B3778231
theorem B3358427 : Blo 2237435 3358427 := bstep (se 1 (by rfl) ⟨2518820, by rfl⟩ : syracuseStep 3358427 = 5037641) B5037641
theorem B2238951 : Blo 2237435 2238951 := bstep (se 1 (by rfl) ⟨1679213, by rfl⟩ : syracuseStep 2238951 = 3358427) B3358427
theorem B2518825 : Blo 2237435 2518825 := bbase (se 2 (by rfl) ⟨944559, by rfl⟩ : syracuseStep 2518825 = 1889119) (by norm_num)
theorem B3358433 : Blo 2237435 3358433 := bstep (se 2 (by rfl) ⟨1259412, by rfl⟩ : syracuseStep 3358433 = 2518825) B2518825
theorem B2238955 : Blo 2237435 2238955 := bstep (se 1 (by rfl) ⟨1679216, by rfl⟩ : syracuseStep 2238955 = 3358433) B3358433
theorem B14345525 : Blo 2237435 14345525 := bbase (se 5 (by rfl) ⟨672446, by rfl⟩ : syracuseStep 14345525 = 1344893) (by norm_num)
theorem B9563683 : Blo 2237435 9563683 := bstep (se 1 (by rfl) ⟨7172762, by rfl⟩ : syracuseStep 9563683 = 14345525) B14345525
theorem B12751577 : Blo 2237435 12751577 := bstep (se 2 (by rfl) ⟨4781841, by rfl⟩ : syracuseStep 12751577 = 9563683) B9563683
theorem B8501051 : Blo 2237435 8501051 := bstep (se 1 (by rfl) ⟨6375788, by rfl⟩ : syracuseStep 8501051 = 12751577) B12751577
theorem B5667367 : Blo 2237435 5667367 := bstep (se 1 (by rfl) ⟨4250525, by rfl⟩ : syracuseStep 5667367 = 8501051) B8501051
theorem B7556489 : Blo 2237435 7556489 := bstep (se 2 (by rfl) ⟨2833683, by rfl⟩ : syracuseStep 7556489 = 5667367) B5667367
theorem B5037659 : Blo 2237435 5037659 := bstep (se 1 (by rfl) ⟨3778244, by rfl⟩ : syracuseStep 5037659 = 7556489) B7556489
theorem B3358439 : Blo 2237435 3358439 := bstep (se 1 (by rfl) ⟨2518829, by rfl⟩ : syracuseStep 3358439 = 5037659) B5037659
theorem B2238959 : Blo 2237435 2238959 := bstep (se 1 (by rfl) ⟨1679219, by rfl⟩ : syracuseStep 2238959 = 3358439) B3358439
theorem B3358445 : Blo 2237435 3358445 := bbase (se 3 (by rfl) ⟨629708, by rfl⟩ : syracuseStep 3358445 = 1259417) (by norm_num)
theorem B2238963 : Blo 2237435 2238963 := bstep (se 1 (by rfl) ⟨1679222, by rfl⟩ : syracuseStep 2238963 = 3358445) B3358445
theorem B5037677 : Blo 2237435 5037677 := bbase (se 3 (by rfl) ⟨944564, by rfl⟩ : syracuseStep 5037677 = 1889129) (by norm_num)
theorem B3358451 : Blo 2237435 3358451 := bstep (se 1 (by rfl) ⟨2518838, by rfl⟩ : syracuseStep 3358451 = 5037677) B5037677
theorem B2238967 : Blo 2237435 2238967 := bstep (se 1 (by rfl) ⟨1679225, by rfl⟩ : syracuseStep 2238967 = 3358451) B3358451
theorem B4250549 : Blo 2237435 4250549 := bbase (se 5 (by rfl) ⟨199244, by rfl⟩ : syracuseStep 4250549 = 398489) (by norm_num)
theorem B2833699 : Blo 2237435 2833699 := bstep (se 1 (by rfl) ⟨2125274, by rfl⟩ : syracuseStep 2833699 = 4250549) B4250549
theorem B3778265 : Blo 2237435 3778265 := bstep (se 2 (by rfl) ⟨1416849, by rfl⟩ : syracuseStep 3778265 = 2833699) B2833699
theorem B2518843 : Blo 2237435 2518843 := bstep (se 1 (by rfl) ⟨1889132, by rfl⟩ : syracuseStep 2518843 = 3778265) B3778265
theorem B3358457 : Blo 2237435 3358457 := bstep (se 2 (by rfl) ⟨1259421, by rfl⟩ : syracuseStep 3358457 = 2518843) B2518843
theorem B2238971 : Blo 2237435 2238971 := bstep (se 1 (by rfl) ⟨1679228, by rfl⟩ : syracuseStep 2238971 = 3358457) B3358457
theorem B6995621 : Blo 2237435 6995621 := bbase (se 4 (by rfl) ⟨655839, by rfl⟩ : syracuseStep 6995621 = 1311679) (by norm_num)
theorem B4663747 : Blo 2237435 4663747 := bstep (se 1 (by rfl) ⟨3497810, by rfl⟩ : syracuseStep 4663747 = 6995621) B6995621
theorem B24873317 : Blo 2237435 24873317 := bstep (se 4 (by rfl) ⟨2331873, by rfl⟩ : syracuseStep 24873317 = 4663747) B4663747
theorem B16582211 : Blo 2237435 16582211 := bstep (se 1 (by rfl) ⟨12436658, by rfl⟩ : syracuseStep 16582211 = 24873317) B24873317
theorem B11054807 : Blo 2237435 11054807 := bstep (se 1 (by rfl) ⟨8291105, by rfl⟩ : syracuseStep 11054807 = 16582211) B16582211
theorem B7369871 : Blo 2237435 7369871 := bstep (se 1 (by rfl) ⟨5527403, by rfl⟩ : syracuseStep 7369871 = 11054807) B11054807
theorem B78611957 : Blo 2237435 78611957 := bstep (se 5 (by rfl) ⟨3684935, by rfl⟩ : syracuseStep 78611957 = 7369871) B7369871
theorem B52407971 : Blo 2237435 52407971 := bstep (se 1 (by rfl) ⟨39305978, by rfl⟩ : syracuseStep 52407971 = 78611957) B78611957
theorem B34938647 : Blo 2237435 34938647 := bstep (se 1 (by rfl) ⟨26203985, by rfl⟩ : syracuseStep 34938647 = 52407971) B52407971
theorem B23292431 : Blo 2237435 23292431 := bstep (se 1 (by rfl) ⟨17469323, by rfl⟩ : syracuseStep 23292431 = 34938647) B34938647
theorem B15528287 : Blo 2237435 15528287 := bstep (se 1 (by rfl) ⟨11646215, by rfl⟩ : syracuseStep 15528287 = 23292431) B23292431
theorem B41408765 : Blo 2237435 41408765 := bstep (se 3 (by rfl) ⟨7764143, by rfl⟩ : syracuseStep 41408765 = 15528287) B15528287
theorem B27605843 : Blo 2237435 27605843 := bstep (se 1 (by rfl) ⟨20704382, by rfl⟩ : syracuseStep 27605843 = 41408765) B41408765
theorem B18403895 : Blo 2237435 18403895 := bstep (se 1 (by rfl) ⟨13802921, by rfl⟩ : syracuseStep 18403895 = 27605843) B27605843
theorem B12269263 : Blo 2237435 12269263 := bstep (se 1 (by rfl) ⟨9201947, by rfl⟩ : syracuseStep 12269263 = 18403895) B18403895
theorem B16359017 : Blo 2237435 16359017 := bstep (se 2 (by rfl) ⟨6134631, by rfl⟩ : syracuseStep 16359017 = 12269263) B12269263
theorem B43624045 : Blo 2237435 43624045 := bstep (se 3 (by rfl) ⟨8179508, by rfl⟩ : syracuseStep 43624045 = 16359017) B16359017
theorem B58165393 : Blo 2237435 58165393 := bstep (se 2 (by rfl) ⟨21812022, by rfl⟩ : syracuseStep 58165393 = 43624045) B43624045
theorem B77553857 : Blo 2237435 77553857 := bstep (se 2 (by rfl) ⟨29082696, by rfl⟩ : syracuseStep 77553857 = 58165393) B58165393
theorem B51702571 : Blo 2237435 51702571 := bstep (se 1 (by rfl) ⟨38776928, by rfl⟩ : syracuseStep 51702571 = 77553857) B77553857
theorem B68936761 : Blo 2237435 68936761 := bstep (se 2 (by rfl) ⟨25851285, by rfl⟩ : syracuseStep 68936761 = 51702571) B51702571
theorem B91915681 : Blo 2237435 91915681 := bstep (se 2 (by rfl) ⟨34468380, by rfl⟩ : syracuseStep 91915681 = 68936761) B68936761
theorem B122554241 : Blo 2237435 122554241 := bstep (se 2 (by rfl) ⟨45957840, by rfl⟩ : syracuseStep 122554241 = 91915681) B91915681
theorem B81702827 : Blo 2237435 81702827 := bstep (se 1 (by rfl) ⟨61277120, by rfl⟩ : syracuseStep 81702827 = 122554241) B122554241
theorem B54468551 : Blo 2237435 54468551 := bstep (se 1 (by rfl) ⟨40851413, by rfl⟩ : syracuseStep 54468551 = 81702827) B81702827
theorem B145249469 : Blo 2237435 145249469 := bstep (se 3 (by rfl) ⟨27234275, by rfl⟩ : syracuseStep 145249469 = 54468551) B54468551
theorem B96832979 : Blo 2237435 96832979 := bstep (se 1 (by rfl) ⟨72624734, by rfl⟩ : syracuseStep 96832979 = 145249469) B145249469
theorem B64555319 : Blo 2237435 64555319 := bstep (se 1 (by rfl) ⟨48416489, by rfl⟩ : syracuseStep 64555319 = 96832979) B96832979
theorem B43036879 : Blo 2237435 43036879 := bstep (se 1 (by rfl) ⟨32277659, by rfl⟩ : syracuseStep 43036879 = 64555319) B64555319
theorem B57382505 : Blo 2237435 57382505 := bstep (se 2 (by rfl) ⟨21518439, by rfl⟩ : syracuseStep 57382505 = 43036879) B43036879
theorem B38255003 : Blo 2237435 38255003 := bstep (se 1 (by rfl) ⟨28691252, by rfl⟩ : syracuseStep 38255003 = 57382505) B57382505
theorem B25503335 : Blo 2237435 25503335 := bstep (se 1 (by rfl) ⟨19127501, by rfl⟩ : syracuseStep 25503335 = 38255003) B38255003
theorem B17002223 : Blo 2237435 17002223 := bstep (se 1 (by rfl) ⟨12751667, by rfl⟩ : syracuseStep 17002223 = 25503335) B25503335
theorem B11334815 : Blo 2237435 11334815 := bstep (se 1 (by rfl) ⟨8501111, by rfl⟩ : syracuseStep 11334815 = 17002223) B17002223
theorem B7556543 : Blo 2237435 7556543 := bstep (se 1 (by rfl) ⟨5667407, by rfl⟩ : syracuseStep 7556543 = 11334815) B11334815
theorem B5037695 : Blo 2237435 5037695 := bstep (se 1 (by rfl) ⟨3778271, by rfl⟩ : syracuseStep 5037695 = 7556543) B7556543
theorem B3358463 : Blo 2237435 3358463 := bstep (se 1 (by rfl) ⟨2518847, by rfl⟩ : syracuseStep 3358463 = 5037695) B5037695
theorem B2238975 : Blo 2237435 2238975 := bstep (se 1 (by rfl) ⟨1679231, by rfl⟩ : syracuseStep 2238975 = 3358463) B3358463
theorem B3358469 : Blo 2237435 3358469 := bbase (se 4 (by rfl) ⟨314856, by rfl⟩ : syracuseStep 3358469 = 629713) (by norm_num)
theorem B2238979 : Blo 2237435 2238979 := bstep (se 1 (by rfl) ⟨1679234, by rfl⟩ : syracuseStep 2238979 = 3358469) B3358469
theorem B3778285 : Blo 2237435 3778285 := bbase (se 3 (by rfl) ⟨708428, by rfl⟩ : syracuseStep 3778285 = 1416857) (by norm_num)
theorem B5037713 : Blo 2237435 5037713 := bstep (se 2 (by rfl) ⟨1889142, by rfl⟩ : syracuseStep 5037713 = 3778285) B3778285
theorem B3358475 : Blo 2237435 3358475 := bstep (se 1 (by rfl) ⟨2518856, by rfl⟩ : syracuseStep 3358475 = 5037713) B5037713
theorem B2238983 : Blo 2237435 2238983 := bstep (se 1 (by rfl) ⟨1679237, by rfl⟩ : syracuseStep 2238983 = 3358475) B3358475
theorem B2518861 : Blo 2237435 2518861 := bbase (se 3 (by rfl) ⟨472286, by rfl⟩ : syracuseStep 2518861 = 944573) (by norm_num)
theorem B3358481 : Blo 2237435 3358481 := bstep (se 2 (by rfl) ⟨1259430, by rfl⟩ : syracuseStep 3358481 = 2518861) B2518861
theorem B2238987 : Blo 2237435 2238987 := bstep (se 1 (by rfl) ⟨1679240, by rfl⟩ : syracuseStep 2238987 = 3358481) B3358481
theorem B7556597 : Blo 2237435 7556597 := bbase (se 5 (by rfl) ⟨354215, by rfl⟩ : syracuseStep 7556597 = 708431) (by norm_num)
theorem B5037731 : Blo 2237435 5037731 := bstep (se 1 (by rfl) ⟨3778298, by rfl⟩ : syracuseStep 5037731 = 7556597) B7556597
theorem B3358487 : Blo 2237435 3358487 := bstep (se 1 (by rfl) ⟨2518865, by rfl⟩ : syracuseStep 3358487 = 5037731) B5037731
theorem B2238991 : Blo 2237435 2238991 := bstep (se 1 (by rfl) ⟨1679243, by rfl⟩ : syracuseStep 2238991 = 3358487) B3358487
theorem B3358493 : Blo 2237435 3358493 := bbase (se 3 (by rfl) ⟨629717, by rfl⟩ : syracuseStep 3358493 = 1259435) (by norm_num)
theorem B2238995 : Blo 2237435 2238995 := bstep (se 1 (by rfl) ⟨1679246, by rfl⟩ : syracuseStep 2238995 = 3358493) B3358493
theorem B5037749 : Blo 2237435 5037749 := bbase (se 5 (by rfl) ⟨236144, by rfl⟩ : syracuseStep 5037749 = 472289) (by norm_num)
theorem B3358499 : Blo 2237435 3358499 := bstep (se 1 (by rfl) ⟨2518874, by rfl⟩ : syracuseStep 3358499 = 5037749) B5037749
theorem B2238999 : Blo 2237435 2238999 := bstep (se 1 (by rfl) ⟨1679249, by rfl⟩ : syracuseStep 2238999 = 3358499) B3358499
theorem B12751829 : Blo 2237435 12751829 := bbase (se 7 (by rfl) ⟨149435, by rfl⟩ : syracuseStep 12751829 = 298871) (by norm_num)
theorem B8501219 : Blo 2237435 8501219 := bstep (se 1 (by rfl) ⟨6375914, by rfl⟩ : syracuseStep 8501219 = 12751829) B12751829
theorem B5667479 : Blo 2237435 5667479 := bstep (se 1 (by rfl) ⟨4250609, by rfl⟩ : syracuseStep 5667479 = 8501219) B8501219
theorem B3778319 : Blo 2237435 3778319 := bstep (se 1 (by rfl) ⟨2833739, by rfl⟩ : syracuseStep 3778319 = 5667479) B5667479
theorem B2518879 : Blo 2237435 2518879 := bstep (se 1 (by rfl) ⟨1889159, by rfl⟩ : syracuseStep 2518879 = 3778319) B3778319
theorem B3358505 : Blo 2237435 3358505 := bstep (se 2 (by rfl) ⟨1259439, by rfl⟩ : syracuseStep 3358505 = 2518879) B2518879
theorem B2239003 : Blo 2237435 2239003 := bstep (se 1 (by rfl) ⟨1679252, by rfl⟩ : syracuseStep 2239003 = 3358505) B3358505
theorem B6375925 : Blo 2237435 6375925 := bbase (se 5 (by rfl) ⟨298871, by rfl⟩ : syracuseStep 6375925 = 597743) (by norm_num)
theorem B8501233 : Blo 2237435 8501233 := bstep (se 2 (by rfl) ⟨3187962, by rfl⟩ : syracuseStep 8501233 = 6375925) B6375925
theorem B11334977 : Blo 2237435 11334977 := bstep (se 2 (by rfl) ⟨4250616, by rfl⟩ : syracuseStep 11334977 = 8501233) B8501233
theorem B7556651 : Blo 2237435 7556651 := bstep (se 1 (by rfl) ⟨5667488, by rfl⟩ : syracuseStep 7556651 = 11334977) B11334977
theorem B5037767 : Blo 2237435 5037767 := bstep (se 1 (by rfl) ⟨3778325, by rfl⟩ : syracuseStep 5037767 = 7556651) B7556651
theorem B3358511 : Blo 2237435 3358511 := bstep (se 1 (by rfl) ⟨2518883, by rfl⟩ : syracuseStep 3358511 = 5037767) B5037767
theorem B2239007 : Blo 2237435 2239007 := bstep (se 1 (by rfl) ⟨1679255, by rfl⟩ : syracuseStep 2239007 = 3358511) B3358511
theorem B3358517 : Blo 2237435 3358517 := bbase (se 5 (by rfl) ⟨157430, by rfl⟩ : syracuseStep 3358517 = 314861) (by norm_num)
theorem B2239011 : Blo 2237435 2239011 := bstep (se 1 (by rfl) ⟨1679258, by rfl⟩ : syracuseStep 2239011 = 3358517) B3358517
theorem B5667509 : Blo 2237435 5667509 := bbase (se 5 (by rfl) ⟨265664, by rfl⟩ : syracuseStep 5667509 = 531329) (by norm_num)
theorem B3778339 : Blo 2237435 3778339 := bstep (se 1 (by rfl) ⟨2833754, by rfl⟩ : syracuseStep 3778339 = 5667509) B5667509
theorem B5037785 : Blo 2237435 5037785 := bstep (se 2 (by rfl) ⟨1889169, by rfl⟩ : syracuseStep 5037785 = 3778339) B3778339
theorem B3358523 : Blo 2237435 3358523 := bstep (se 1 (by rfl) ⟨2518892, by rfl⟩ : syracuseStep 3358523 = 5037785) B5037785
theorem B2239015 : Blo 2237435 2239015 := bstep (se 1 (by rfl) ⟨1679261, by rfl⟩ : syracuseStep 2239015 = 3358523) B3358523
theorem B2518897 : Blo 2237435 2518897 := bbase (se 2 (by rfl) ⟨944586, by rfl⟩ : syracuseStep 2518897 = 1889173) (by norm_num)
theorem B3358529 : Blo 2237435 3358529 := bstep (se 2 (by rfl) ⟨1259448, by rfl⟩ : syracuseStep 3358529 = 2518897) B2518897
theorem B2239019 : Blo 2237435 2239019 := bstep (se 1 (by rfl) ⟨1679264, by rfl⟩ : syracuseStep 2239019 = 3358529) B3358529
theorem B9563957 : Blo 2237435 9563957 := bbase (se 5 (by rfl) ⟨448310, by rfl⟩ : syracuseStep 9563957 = 896621) (by norm_num)
theorem B6375971 : Blo 2237435 6375971 := bstep (se 1 (by rfl) ⟨4781978, by rfl⟩ : syracuseStep 6375971 = 9563957) B9563957
theorem B4250647 : Blo 2237435 4250647 := bstep (se 1 (by rfl) ⟨3187985, by rfl⟩ : syracuseStep 4250647 = 6375971) B6375971
theorem B5667529 : Blo 2237435 5667529 := bstep (se 2 (by rfl) ⟨2125323, by rfl⟩ : syracuseStep 5667529 = 4250647) B4250647
theorem B7556705 : Blo 2237435 7556705 := bstep (se 2 (by rfl) ⟨2833764, by rfl⟩ : syracuseStep 7556705 = 5667529) B5667529
theorem B5037803 : Blo 2237435 5037803 := bstep (se 1 (by rfl) ⟨3778352, by rfl⟩ : syracuseStep 5037803 = 7556705) B7556705
theorem B3358535 : Blo 2237435 3358535 := bstep (se 1 (by rfl) ⟨2518901, by rfl⟩ : syracuseStep 3358535 = 5037803) B5037803
theorem B2239023 : Blo 2237435 2239023 := bstep (se 1 (by rfl) ⟨1679267, by rfl⟩ : syracuseStep 2239023 = 3358535) B3358535
theorem B3358541 : Blo 2237435 3358541 := bbase (se 3 (by rfl) ⟨629726, by rfl⟩ : syracuseStep 3358541 = 1259453) (by norm_num)
theorem B2239027 : Blo 2237435 2239027 := bstep (se 1 (by rfl) ⟨1679270, by rfl⟩ : syracuseStep 2239027 = 3358541) B3358541
theorem B5037821 : Blo 2237435 5037821 := bbase (se 3 (by rfl) ⟨944591, by rfl⟩ : syracuseStep 5037821 = 1889183) (by norm_num)
theorem B3358547 : Blo 2237435 3358547 := bstep (se 1 (by rfl) ⟨2518910, by rfl⟩ : syracuseStep 3358547 = 5037821) B5037821
theorem B2239031 : Blo 2237435 2239031 := bstep (se 1 (by rfl) ⟨1679273, by rfl⟩ : syracuseStep 2239031 = 3358547) B3358547
theorem B3778373 : Blo 2237435 3778373 := bbase (se 4 (by rfl) ⟨354222, by rfl⟩ : syracuseStep 3778373 = 708445) (by norm_num)
theorem B2518915 : Blo 2237435 2518915 := bstep (se 1 (by rfl) ⟨1889186, by rfl⟩ : syracuseStep 2518915 = 3778373) B3778373
theorem B3358553 : Blo 2237435 3358553 := bstep (se 2 (by rfl) ⟨1259457, by rfl⟩ : syracuseStep 3358553 = 2518915) B2518915
theorem B2239035 : Blo 2237435 2239035 := bstep (se 1 (by rfl) ⟨1679276, by rfl⟩ : syracuseStep 2239035 = 3358553) B3358553
theorem B17002709 : Blo 2237435 17002709 := bbase (se 7 (by rfl) ⟨199250, by rfl⟩ : syracuseStep 17002709 = 398501) (by norm_num)
theorem B11335139 : Blo 2237435 11335139 := bstep (se 1 (by rfl) ⟨8501354, by rfl⟩ : syracuseStep 11335139 = 17002709) B17002709
theorem B7556759 : Blo 2237435 7556759 := bstep (se 1 (by rfl) ⟨5667569, by rfl⟩ : syracuseStep 7556759 = 11335139) B11335139
theorem B5037839 : Blo 2237435 5037839 := bstep (se 1 (by rfl) ⟨3778379, by rfl⟩ : syracuseStep 5037839 = 7556759) B7556759
theorem B3358559 : Blo 2237435 3358559 := bstep (se 1 (by rfl) ⟨2518919, by rfl⟩ : syracuseStep 3358559 = 5037839) B5037839
theorem B2239039 : Blo 2237435 2239039 := bstep (se 1 (by rfl) ⟨1679279, by rfl⟩ : syracuseStep 2239039 = 3358559) B3358559
theorem B3358565 : Blo 2237435 3358565 := bbase (se 4 (by rfl) ⟨314865, by rfl⟩ : syracuseStep 3358565 = 629731) (by norm_num)
theorem B2239043 : Blo 2237435 2239043 := bstep (se 1 (by rfl) ⟨1679282, by rfl⟩ : syracuseStep 2239043 = 3358565) B3358565
theorem B4250693 : Blo 2237435 4250693 := bbase (se 4 (by rfl) ⟨398502, by rfl⟩ : syracuseStep 4250693 = 797005) (by norm_num)
theorem B2833795 : Blo 2237435 2833795 := bstep (se 1 (by rfl) ⟨2125346, by rfl⟩ : syracuseStep 2833795 = 4250693) B4250693
theorem B3778393 : Blo 2237435 3778393 := bstep (se 2 (by rfl) ⟨1416897, by rfl⟩ : syracuseStep 3778393 = 2833795) B2833795
theorem B5037857 : Blo 2237435 5037857 := bstep (se 2 (by rfl) ⟨1889196, by rfl⟩ : syracuseStep 5037857 = 3778393) B3778393
theorem B3358571 : Blo 2237435 3358571 := bstep (se 1 (by rfl) ⟨2518928, by rfl⟩ : syracuseStep 3358571 = 5037857) B5037857
theorem B2239047 : Blo 2237435 2239047 := bstep (se 1 (by rfl) ⟨1679285, by rfl⟩ : syracuseStep 2239047 = 3358571) B3358571
theorem B2518933 : Blo 2237435 2518933 := bbase (se 6 (by rfl) ⟨59037, by rfl⟩ : syracuseStep 2518933 = 118075) (by norm_num)
theorem B3358577 : Blo 2237435 3358577 := bstep (se 2 (by rfl) ⟨1259466, by rfl⟩ : syracuseStep 3358577 = 2518933) B2518933
theorem B2239051 : Blo 2237435 2239051 := bstep (se 1 (by rfl) ⟨1679288, by rfl⟩ : syracuseStep 2239051 = 3358577) B3358577
theorem B2833805 : Blo 2237435 2833805 := bbase (se 3 (by rfl) ⟨531338, by rfl⟩ : syracuseStep 2833805 = 1062677) (by norm_num)
theorem B7556813 : Blo 2237435 7556813 := bstep (se 3 (by rfl) ⟨1416902, by rfl⟩ : syracuseStep 7556813 = 2833805) B2833805
theorem B5037875 : Blo 2237435 5037875 := bstep (se 1 (by rfl) ⟨3778406, by rfl⟩ : syracuseStep 5037875 = 7556813) B7556813
theorem B3358583 : Blo 2237435 3358583 := bstep (se 1 (by rfl) ⟨2518937, by rfl⟩ : syracuseStep 3358583 = 5037875) B5037875
theorem B2239055 : Blo 2237435 2239055 := bstep (se 1 (by rfl) ⟨1679291, by rfl⟩ : syracuseStep 2239055 = 3358583) B3358583
theorem B3358589 : Blo 2237435 3358589 := bbase (se 3 (by rfl) ⟨629735, by rfl⟩ : syracuseStep 3358589 = 1259471) (by norm_num)
theorem B2239059 : Blo 2237435 2239059 := bstep (se 1 (by rfl) ⟨1679294, by rfl⟩ : syracuseStep 2239059 = 3358589) B3358589
theorem B5037893 : Blo 2237435 5037893 := bbase (se 4 (by rfl) ⟨472302, by rfl⟩ : syracuseStep 5037893 = 944605) (by norm_num)
theorem B3358595 : Blo 2237435 3358595 := bstep (se 1 (by rfl) ⟨2518946, by rfl⟩ : syracuseStep 3358595 = 5037893) B5037893
theorem B2239063 : Blo 2237435 2239063 := bstep (se 1 (by rfl) ⟨1679297, by rfl⟩ : syracuseStep 2239063 = 3358595) B3358595
theorem B6808853 : Blo 2237435 6808853 := bbase (se 6 (by rfl) ⟨159582, by rfl⟩ : syracuseStep 6808853 = 319165) (by norm_num)
theorem B4539235 : Blo 2237435 4539235 := bstep (se 1 (by rfl) ⟨3404426, by rfl⟩ : syracuseStep 4539235 = 6808853) B6808853
theorem B6052313 : Blo 2237435 6052313 := bstep (se 2 (by rfl) ⟨2269617, by rfl⟩ : syracuseStep 6052313 = 4539235) B4539235
theorem B4034875 : Blo 2237435 4034875 := bstep (se 1 (by rfl) ⟨3026156, by rfl⟩ : syracuseStep 4034875 = 6052313) B6052313
theorem B5379833 : Blo 2237435 5379833 := bstep (se 2 (by rfl) ⟨2017437, by rfl⟩ : syracuseStep 5379833 = 4034875) B4034875
theorem B3586555 : Blo 2237435 3586555 := bstep (se 1 (by rfl) ⟨2689916, by rfl⟩ : syracuseStep 3586555 = 5379833) B5379833
theorem B4782073 : Blo 2237435 4782073 := bstep (se 2 (by rfl) ⟨1793277, by rfl⟩ : syracuseStep 4782073 = 3586555) B3586555
theorem B6376097 : Blo 2237435 6376097 := bstep (se 2 (by rfl) ⟨2391036, by rfl⟩ : syracuseStep 6376097 = 4782073) B4782073
theorem B4250731 : Blo 2237435 4250731 := bstep (se 1 (by rfl) ⟨3188048, by rfl⟩ : syracuseStep 4250731 = 6376097) B6376097
theorem B5667641 : Blo 2237435 5667641 := bstep (se 2 (by rfl) ⟨2125365, by rfl⟩ : syracuseStep 5667641 = 4250731) B4250731
theorem B3778427 : Blo 2237435 3778427 := bstep (se 1 (by rfl) ⟨2833820, by rfl⟩ : syracuseStep 3778427 = 5667641) B5667641
theorem B2518951 : Blo 2237435 2518951 := bstep (se 1 (by rfl) ⟨1889213, by rfl⟩ : syracuseStep 2518951 = 3778427) B3778427
theorem B3358601 : Blo 2237435 3358601 := bstep (se 2 (by rfl) ⟨1259475, by rfl⟩ : syracuseStep 3358601 = 2518951) B2518951
theorem B2239067 : Blo 2237435 2239067 := bstep (se 1 (by rfl) ⟨1679300, by rfl⟩ : syracuseStep 2239067 = 3358601) B3358601
theorem B11335301 : Blo 2237435 11335301 := bbase (se 4 (by rfl) ⟨1062684, by rfl⟩ : syracuseStep 11335301 = 2125369) (by norm_num)
theorem B7556867 : Blo 2237435 7556867 := bstep (se 1 (by rfl) ⟨5667650, by rfl⟩ : syracuseStep 7556867 = 11335301) B11335301
theorem B5037911 : Blo 2237435 5037911 := bstep (se 1 (by rfl) ⟨3778433, by rfl⟩ : syracuseStep 5037911 = 7556867) B7556867
theorem B3358607 : Blo 2237435 3358607 := bstep (se 1 (by rfl) ⟨2518955, by rfl⟩ : syracuseStep 3358607 = 5037911) B5037911
theorem B2239071 : Blo 2237435 2239071 := bstep (se 1 (by rfl) ⟨1679303, by rfl⟩ : syracuseStep 2239071 = 3358607) B3358607
theorem B3358613 : Blo 2237435 3358613 := bbase (se 6 (by rfl) ⟨78717, by rfl⟩ : syracuseStep 3358613 = 157435) (by norm_num)
theorem B2239075 : Blo 2237435 2239075 := bstep (se 1 (by rfl) ⟨1679306, by rfl⟩ : syracuseStep 2239075 = 3358613) B3358613
theorem B2391049 : Blo 2237435 2391049 := bbase (se 2 (by rfl) ⟨896643, by rfl⟩ : syracuseStep 2391049 = 1793287) (by norm_num)
theorem B12752261 : Blo 2237435 12752261 := bstep (se 4 (by rfl) ⟨1195524, by rfl⟩ : syracuseStep 12752261 = 2391049) B2391049
theorem B8501507 : Blo 2237435 8501507 := bstep (se 1 (by rfl) ⟨6376130, by rfl⟩ : syracuseStep 8501507 = 12752261) B12752261
theorem B5667671 : Blo 2237435 5667671 := bstep (se 1 (by rfl) ⟨4250753, by rfl⟩ : syracuseStep 5667671 = 8501507) B8501507
theorem B3778447 : Blo 2237435 3778447 := bstep (se 1 (by rfl) ⟨2833835, by rfl⟩ : syracuseStep 3778447 = 5667671) B5667671
theorem B5037929 : Blo 2237435 5037929 := bstep (se 2 (by rfl) ⟨1889223, by rfl⟩ : syracuseStep 5037929 = 3778447) B3778447
theorem B3358619 : Blo 2237435 3358619 := bstep (se 1 (by rfl) ⟨2518964, by rfl⟩ : syracuseStep 3358619 = 5037929) B5037929
theorem B2239079 : Blo 2237435 2239079 := bstep (se 1 (by rfl) ⟨1679309, by rfl⟩ : syracuseStep 2239079 = 3358619) B3358619
theorem B2518969 : Blo 2237435 2518969 := bbase (se 2 (by rfl) ⟨944613, by rfl⟩ : syracuseStep 2518969 = 1889227) (by norm_num)
theorem B3358625 : Blo 2237435 3358625 := bstep (se 2 (by rfl) ⟨1259484, by rfl⟩ : syracuseStep 3358625 = 2518969) B2518969
theorem B2239083 : Blo 2237435 2239083 := bstep (se 1 (by rfl) ⟨1679312, by rfl⟩ : syracuseStep 2239083 = 3358625) B3358625
theorem B7173173 : Blo 2237435 7173173 := bbase (se 5 (by rfl) ⟨336242, by rfl⟩ : syracuseStep 7173173 = 672485) (by norm_num)
theorem B4782115 : Blo 2237435 4782115 := bstep (se 1 (by rfl) ⟨3586586, by rfl⟩ : syracuseStep 4782115 = 7173173) B7173173
theorem B6376153 : Blo 2237435 6376153 := bstep (se 2 (by rfl) ⟨2391057, by rfl⟩ : syracuseStep 6376153 = 4782115) B4782115
theorem B8501537 : Blo 2237435 8501537 := bstep (se 2 (by rfl) ⟨3188076, by rfl⟩ : syracuseStep 8501537 = 6376153) B6376153
theorem B5667691 : Blo 2237435 5667691 := bstep (se 1 (by rfl) ⟨4250768, by rfl⟩ : syracuseStep 5667691 = 8501537) B8501537
theorem B7556921 : Blo 2237435 7556921 := bstep (se 2 (by rfl) ⟨2833845, by rfl⟩ : syracuseStep 7556921 = 5667691) B5667691
theorem B5037947 : Blo 2237435 5037947 := bstep (se 1 (by rfl) ⟨3778460, by rfl⟩ : syracuseStep 5037947 = 7556921) B7556921
theorem B3358631 : Blo 2237435 3358631 := bstep (se 1 (by rfl) ⟨2518973, by rfl⟩ : syracuseStep 3358631 = 5037947) B5037947
theorem B2239087 : Blo 2237435 2239087 := bstep (se 1 (by rfl) ⟨1679315, by rfl⟩ : syracuseStep 2239087 = 3358631) B3358631
theorem B3358637 : Blo 2237435 3358637 := bbase (se 3 (by rfl) ⟨629744, by rfl⟩ : syracuseStep 3358637 = 1259489) (by norm_num)
theorem B2239091 : Blo 2237435 2239091 := bstep (se 1 (by rfl) ⟨1679318, by rfl⟩ : syracuseStep 2239091 = 3358637) B3358637
theorem B5037965 : Blo 2237435 5037965 := bbase (se 3 (by rfl) ⟨944618, by rfl⟩ : syracuseStep 5037965 = 1889237) (by norm_num)
theorem B3358643 : Blo 2237435 3358643 := bstep (se 1 (by rfl) ⟨2518982, by rfl⟩ : syracuseStep 3358643 = 5037965) B5037965
theorem B2239095 : Blo 2237435 2239095 := bstep (se 1 (by rfl) ⟨1679321, by rfl⟩ : syracuseStep 2239095 = 3358643) B3358643
theorem B2833861 : Blo 2237435 2833861 := bbase (se 4 (by rfl) ⟨265674, by rfl⟩ : syracuseStep 2833861 = 531349) (by norm_num)
theorem B3778481 : Blo 2237435 3778481 := bstep (se 2 (by rfl) ⟨1416930, by rfl⟩ : syracuseStep 3778481 = 2833861) B2833861
theorem B2518987 : Blo 2237435 2518987 := bstep (se 1 (by rfl) ⟨1889240, by rfl⟩ : syracuseStep 2518987 = 3778481) B3778481
theorem B3358649 : Blo 2237435 3358649 := bstep (se 2 (by rfl) ⟨1259493, by rfl⟩ : syracuseStep 3358649 = 2518987) B2518987
theorem B2239099 : Blo 2237435 2239099 := bstep (se 1 (by rfl) ⟨1679324, by rfl⟩ : syracuseStep 2239099 = 3358649) B3358649
theorem B2911721 : Blo 2237435 2911721 := bbase (se 2 (by rfl) ⟨1091895, by rfl⟩ : syracuseStep 2911721 = 2183791) (by norm_num)
theorem B7764589 : Blo 2237435 7764589 := bstep (se 3 (by rfl) ⟨1455860, by rfl⟩ : syracuseStep 7764589 = 2911721) B2911721
theorem B10352785 : Blo 2237435 10352785 := bstep (se 2 (by rfl) ⟨3882294, by rfl⟩ : syracuseStep 10352785 = 7764589) B7764589
theorem B13803713 : Blo 2237435 13803713 := bstep (se 2 (by rfl) ⟨5176392, by rfl⟩ : syracuseStep 13803713 = 10352785) B10352785
theorem B9202475 : Blo 2237435 9202475 := bstep (se 1 (by rfl) ⟨6901856, by rfl⟩ : syracuseStep 9202475 = 13803713) B13803713
theorem B6134983 : Blo 2237435 6134983 := bstep (se 1 (by rfl) ⟨4601237, by rfl⟩ : syracuseStep 6134983 = 9202475) B9202475
theorem B32719909 : Blo 2237435 32719909 := bstep (se 4 (by rfl) ⟨3067491, by rfl⟩ : syracuseStep 32719909 = 6134983) B6134983
theorem B43626545 : Blo 2237435 43626545 := bstep (se 2 (by rfl) ⟨16359954, by rfl⟩ : syracuseStep 43626545 = 32719909) B32719909
theorem B29084363 : Blo 2237435 29084363 := bstep (se 1 (by rfl) ⟨21813272, by rfl⟩ : syracuseStep 29084363 = 43626545) B43626545
theorem B19389575 : Blo 2237435 19389575 := bstep (se 1 (by rfl) ⟨14542181, by rfl⟩ : syracuseStep 19389575 = 29084363) B29084363
theorem B51705533 : Blo 2237435 51705533 := bstep (se 3 (by rfl) ⟨9694787, by rfl⟩ : syracuseStep 51705533 = 19389575) B19389575
theorem B34470355 : Blo 2237435 34470355 := bstep (se 1 (by rfl) ⟨25852766, by rfl⟩ : syracuseStep 34470355 = 51705533) B51705533
theorem B45960473 : Blo 2237435 45960473 := bstep (se 2 (by rfl) ⟨17235177, by rfl⟩ : syracuseStep 45960473 = 34470355) B34470355
theorem B30640315 : Blo 2237435 30640315 := bstep (se 1 (by rfl) ⟨22980236, by rfl⟩ : syracuseStep 30640315 = 45960473) B45960473
theorem B40853753 : Blo 2237435 40853753 := bstep (se 2 (by rfl) ⟨15320157, by rfl⟩ : syracuseStep 40853753 = 30640315) B30640315
theorem B27235835 : Blo 2237435 27235835 := bstep (se 1 (by rfl) ⟨20426876, by rfl⟩ : syracuseStep 27235835 = 40853753) B40853753
theorem B18157223 : Blo 2237435 18157223 := bstep (se 1 (by rfl) ⟨13617917, by rfl⟩ : syracuseStep 18157223 = 27235835) B27235835
theorem B12104815 : Blo 2237435 12104815 := bstep (se 1 (by rfl) ⟨9078611, by rfl⟩ : syracuseStep 12104815 = 18157223) B18157223
theorem B16139753 : Blo 2237435 16139753 := bstep (se 2 (by rfl) ⟨6052407, by rfl⟩ : syracuseStep 16139753 = 12104815) B12104815
theorem B10759835 : Blo 2237435 10759835 := bstep (se 1 (by rfl) ⟨8069876, by rfl⟩ : syracuseStep 10759835 = 16139753) B16139753
theorem B28692893 : Blo 2237435 28692893 := bstep (se 3 (by rfl) ⟨5379917, by rfl⟩ : syracuseStep 28692893 = 10759835) B10759835
theorem B19128595 : Blo 2237435 19128595 := bstep (se 1 (by rfl) ⟨14346446, by rfl⟩ : syracuseStep 19128595 = 28692893) B28692893
theorem B25504793 : Blo 2237435 25504793 := bstep (se 2 (by rfl) ⟨9564297, by rfl⟩ : syracuseStep 25504793 = 19128595) B19128595
theorem B17003195 : Blo 2237435 17003195 := bstep (se 1 (by rfl) ⟨12752396, by rfl⟩ : syracuseStep 17003195 = 25504793) B25504793
theorem B11335463 : Blo 2237435 11335463 := bstep (se 1 (by rfl) ⟨8501597, by rfl⟩ : syracuseStep 11335463 = 17003195) B17003195
theorem B7556975 : Blo 2237435 7556975 := bstep (se 1 (by rfl) ⟨5667731, by rfl⟩ : syracuseStep 7556975 = 11335463) B11335463
theorem B5037983 : Blo 2237435 5037983 := bstep (se 1 (by rfl) ⟨3778487, by rfl⟩ : syracuseStep 5037983 = 7556975) B7556975
theorem B3358655 : Blo 2237435 3358655 := bstep (se 1 (by rfl) ⟨2518991, by rfl⟩ : syracuseStep 3358655 = 5037983) B5037983
theorem B2239103 : Blo 2237435 2239103 := bstep (se 1 (by rfl) ⟨1679327, by rfl⟩ : syracuseStep 2239103 = 3358655) B3358655
theorem B3358661 : Blo 2237435 3358661 := bbase (se 4 (by rfl) ⟨314874, by rfl⟩ : syracuseStep 3358661 = 629749) (by norm_num)
theorem B2239107 : Blo 2237435 2239107 := bstep (se 1 (by rfl) ⟨1679330, by rfl⟩ : syracuseStep 2239107 = 3358661) B3358661
theorem B3778501 : Blo 2237435 3778501 := bbase (se 4 (by rfl) ⟨354234, by rfl⟩ : syracuseStep 3778501 = 708469) (by norm_num)
theorem B5038001 : Blo 2237435 5038001 := bstep (se 2 (by rfl) ⟨1889250, by rfl⟩ : syracuseStep 5038001 = 3778501) B3778501
theorem B3358667 : Blo 2237435 3358667 := bstep (se 1 (by rfl) ⟨2519000, by rfl⟩ : syracuseStep 3358667 = 5038001) B5038001
theorem B2239111 : Blo 2237435 2239111 := bstep (se 1 (by rfl) ⟨1679333, by rfl⟩ : syracuseStep 2239111 = 3358667) B3358667
theorem B2519005 : Blo 2237435 2519005 := bbase (se 3 (by rfl) ⟨472313, by rfl⟩ : syracuseStep 2519005 = 944627) (by norm_num)
theorem B3358673 : Blo 2237435 3358673 := bstep (se 2 (by rfl) ⟨1259502, by rfl⟩ : syracuseStep 3358673 = 2519005) B2519005
theorem B2239115 : Blo 2237435 2239115 := bstep (se 1 (by rfl) ⟨1679336, by rfl⟩ : syracuseStep 2239115 = 3358673) B3358673
theorem B7557029 : Blo 2237435 7557029 := bbase (se 4 (by rfl) ⟨708471, by rfl⟩ : syracuseStep 7557029 = 1416943) (by norm_num)
theorem B5038019 : Blo 2237435 5038019 := bstep (se 1 (by rfl) ⟨3778514, by rfl⟩ : syracuseStep 5038019 = 7557029) B7557029
theorem B3358679 : Blo 2237435 3358679 := bstep (se 1 (by rfl) ⟨2519009, by rfl⟩ : syracuseStep 3358679 = 5038019) B5038019
theorem B2239119 : Blo 2237435 2239119 := bstep (se 1 (by rfl) ⟨1679339, by rfl⟩ : syracuseStep 2239119 = 3358679) B3358679
theorem B3358685 : Blo 2237435 3358685 := bbase (se 3 (by rfl) ⟨629753, by rfl⟩ : syracuseStep 3358685 = 1259507) (by norm_num)
theorem B2239123 : Blo 2237435 2239123 := bstep (se 1 (by rfl) ⟨1679342, by rfl⟩ : syracuseStep 2239123 = 3358685) B3358685
theorem B5038037 : Blo 2237435 5038037 := bbase (se 7 (by rfl) ⟨59039, by rfl⟩ : syracuseStep 5038037 = 118079) (by norm_num)
theorem B3358691 : Blo 2237435 3358691 := bstep (se 1 (by rfl) ⟨2519018, by rfl⟩ : syracuseStep 3358691 = 5038037) B5038037
theorem B2239127 : Blo 2237435 2239127 := bstep (se 1 (by rfl) ⟨1679345, by rfl⟩ : syracuseStep 2239127 = 3358691) B3358691
theorem B2689993 : Blo 2237435 2689993 := bbase (se 2 (by rfl) ⟨1008747, by rfl⟩ : syracuseStep 2689993 = 2017495) (by norm_num)
theorem B14346629 : Blo 2237435 14346629 := bstep (se 4 (by rfl) ⟨1344996, by rfl⟩ : syracuseStep 14346629 = 2689993) B2689993
theorem B9564419 : Blo 2237435 9564419 := bstep (se 1 (by rfl) ⟨7173314, by rfl⟩ : syracuseStep 9564419 = 14346629) B14346629
theorem B6376279 : Blo 2237435 6376279 := bstep (se 1 (by rfl) ⟨4782209, by rfl⟩ : syracuseStep 6376279 = 9564419) B9564419
theorem B8501705 : Blo 2237435 8501705 := bstep (se 2 (by rfl) ⟨3188139, by rfl⟩ : syracuseStep 8501705 = 6376279) B6376279
theorem B5667803 : Blo 2237435 5667803 := bstep (se 1 (by rfl) ⟨4250852, by rfl⟩ : syracuseStep 5667803 = 8501705) B8501705
theorem B3778535 : Blo 2237435 3778535 := bstep (se 1 (by rfl) ⟨2833901, by rfl⟩ : syracuseStep 3778535 = 5667803) B5667803
theorem B2519023 : Blo 2237435 2519023 := bstep (se 1 (by rfl) ⟨1889267, by rfl⟩ : syracuseStep 2519023 = 3778535) B3778535
theorem B3358697 : Blo 2237435 3358697 := bstep (se 2 (by rfl) ⟨1259511, by rfl⟩ : syracuseStep 3358697 = 2519023) B2519023
theorem B2239131 : Blo 2237435 2239131 := bstep (se 1 (by rfl) ⟨1679348, by rfl⟩ : syracuseStep 2239131 = 3358697) B3358697
theorem B2300653 : Blo 2237435 2300653 := bbase (se 3 (by rfl) ⟨431372, by rfl⟩ : syracuseStep 2300653 = 862745) (by norm_num)
theorem B12270149 : Blo 2237435 12270149 := bstep (se 4 (by rfl) ⟨1150326, by rfl⟩ : syracuseStep 12270149 = 2300653) B2300653
theorem B8180099 : Blo 2237435 8180099 := bstep (se 1 (by rfl) ⟨6135074, by rfl⟩ : syracuseStep 8180099 = 12270149) B12270149
theorem B5453399 : Blo 2237435 5453399 := bstep (se 1 (by rfl) ⟨4090049, by rfl⟩ : syracuseStep 5453399 = 8180099) B8180099
theorem B3635599 : Blo 2237435 3635599 := bstep (se 1 (by rfl) ⟨2726699, by rfl⟩ : syracuseStep 3635599 = 5453399) B5453399
theorem B4847465 : Blo 2237435 4847465 := bstep (se 2 (by rfl) ⟨1817799, by rfl⟩ : syracuseStep 4847465 = 3635599) B3635599
theorem B12926573 : Blo 2237435 12926573 := bstep (se 3 (by rfl) ⟨2423732, by rfl⟩ : syracuseStep 12926573 = 4847465) B4847465
theorem B8617715 : Blo 2237435 8617715 := bstep (se 1 (by rfl) ⟨6463286, by rfl⟩ : syracuseStep 8617715 = 12926573) B12926573
theorem B5745143 : Blo 2237435 5745143 := bstep (se 1 (by rfl) ⟨4308857, by rfl⟩ : syracuseStep 5745143 = 8617715) B8617715
theorem B3830095 : Blo 2237435 3830095 := bstep (se 1 (by rfl) ⟨2872571, by rfl⟩ : syracuseStep 3830095 = 5745143) B5745143
theorem B20427173 : Blo 2237435 20427173 := bstep (se 4 (by rfl) ⟨1915047, by rfl⟩ : syracuseStep 20427173 = 3830095) B3830095
theorem B13618115 : Blo 2237435 13618115 := bstep (se 1 (by rfl) ⟨10213586, by rfl⟩ : syracuseStep 13618115 = 20427173) B20427173
theorem B9078743 : Blo 2237435 9078743 := bstep (se 1 (by rfl) ⟨6809057, by rfl⟩ : syracuseStep 9078743 = 13618115) B13618115
theorem B6052495 : Blo 2237435 6052495 := bstep (se 1 (by rfl) ⟨4539371, by rfl⟩ : syracuseStep 6052495 = 9078743) B9078743
theorem B8069993 : Blo 2237435 8069993 := bstep (se 2 (by rfl) ⟨3026247, by rfl⟩ : syracuseStep 8069993 = 6052495) B6052495
theorem B5379995 : Blo 2237435 5379995 := bstep (se 1 (by rfl) ⟨4034996, by rfl⟩ : syracuseStep 5379995 = 8069993) B8069993
theorem B3586663 : Blo 2237435 3586663 := bstep (se 1 (by rfl) ⟨2689997, by rfl⟩ : syracuseStep 3586663 = 5379995) B5379995
theorem B19128869 : Blo 2237435 19128869 := bstep (se 4 (by rfl) ⟨1793331, by rfl⟩ : syracuseStep 19128869 = 3586663) B3586663
theorem B12752579 : Blo 2237435 12752579 := bstep (se 1 (by rfl) ⟨9564434, by rfl⟩ : syracuseStep 12752579 = 19128869) B19128869
theorem B8501719 : Blo 2237435 8501719 := bstep (se 1 (by rfl) ⟨6376289, by rfl⟩ : syracuseStep 8501719 = 12752579) B12752579
theorem B11335625 : Blo 2237435 11335625 := bstep (se 2 (by rfl) ⟨4250859, by rfl⟩ : syracuseStep 11335625 = 8501719) B8501719
theorem B7557083 : Blo 2237435 7557083 := bstep (se 1 (by rfl) ⟨5667812, by rfl⟩ : syracuseStep 7557083 = 11335625) B11335625
theorem B5038055 : Blo 2237435 5038055 := bstep (se 1 (by rfl) ⟨3778541, by rfl⟩ : syracuseStep 5038055 = 7557083) B7557083
theorem B3358703 : Blo 2237435 3358703 := bstep (se 1 (by rfl) ⟨2519027, by rfl⟩ : syracuseStep 3358703 = 5038055) B5038055
theorem B2239135 : Blo 2237435 2239135 := bstep (se 1 (by rfl) ⟨1679351, by rfl⟩ : syracuseStep 2239135 = 3358703) B3358703
theorem B3358709 : Blo 2237435 3358709 := bbase (se 5 (by rfl) ⟨157439, by rfl⟩ : syracuseStep 3358709 = 314879) (by norm_num)
theorem B2239139 : Blo 2237435 2239139 := bstep (se 1 (by rfl) ⟨1679354, by rfl⟩ : syracuseStep 2239139 = 3358709) B3358709
theorem B13618165 : Blo 2237435 13618165 := bbase (se 5 (by rfl) ⟨638351, by rfl⟩ : syracuseStep 13618165 = 1276703) (by norm_num)
theorem B18157553 : Blo 2237435 18157553 := bstep (se 2 (by rfl) ⟨6809082, by rfl⟩ : syracuseStep 18157553 = 13618165) B13618165
theorem B12105035 : Blo 2237435 12105035 := bstep (se 1 (by rfl) ⟨9078776, by rfl⟩ : syracuseStep 12105035 = 18157553) B18157553
theorem B8070023 : Blo 2237435 8070023 := bstep (se 1 (by rfl) ⟨6052517, by rfl⟩ : syracuseStep 8070023 = 12105035) B12105035
theorem B5380015 : Blo 2237435 5380015 := bstep (se 1 (by rfl) ⟨4035011, by rfl⟩ : syracuseStep 5380015 = 8070023) B8070023
theorem B7173353 : Blo 2237435 7173353 := bstep (se 2 (by rfl) ⟨2690007, by rfl⟩ : syracuseStep 7173353 = 5380015) B5380015
theorem B4782235 : Blo 2237435 4782235 := bstep (se 1 (by rfl) ⟨3586676, by rfl⟩ : syracuseStep 4782235 = 7173353) B7173353
theorem B6376313 : Blo 2237435 6376313 := bstep (se 2 (by rfl) ⟨2391117, by rfl⟩ : syracuseStep 6376313 = 4782235) B4782235
theorem B4250875 : Blo 2237435 4250875 := bstep (se 1 (by rfl) ⟨3188156, by rfl⟩ : syracuseStep 4250875 = 6376313) B6376313
theorem B5667833 : Blo 2237435 5667833 := bstep (se 2 (by rfl) ⟨2125437, by rfl⟩ : syracuseStep 5667833 = 4250875) B4250875
theorem B3778555 : Blo 2237435 3778555 := bstep (se 1 (by rfl) ⟨2833916, by rfl⟩ : syracuseStep 3778555 = 5667833) B5667833
theorem B5038073 : Blo 2237435 5038073 := bstep (se 2 (by rfl) ⟨1889277, by rfl⟩ : syracuseStep 5038073 = 3778555) B3778555
theorem B3358715 : Blo 2237435 3358715 := bstep (se 1 (by rfl) ⟨2519036, by rfl⟩ : syracuseStep 3358715 = 5038073) B5038073
theorem B2239143 : Blo 2237435 2239143 := bstep (se 1 (by rfl) ⟨1679357, by rfl⟩ : syracuseStep 2239143 = 3358715) B3358715
theorem B2519041 : Blo 2237435 2519041 := bbase (se 2 (by rfl) ⟨944640, by rfl⟩ : syracuseStep 2519041 = 1889281) (by norm_num)
theorem B3358721 : Blo 2237435 3358721 := bstep (se 2 (by rfl) ⟨1259520, by rfl⟩ : syracuseStep 3358721 = 2519041) B2519041
theorem B2239147 : Blo 2237435 2239147 := bstep (se 1 (by rfl) ⟨1679360, by rfl⟩ : syracuseStep 2239147 = 3358721) B3358721
theorem B5667853 : Blo 2237435 5667853 := bbase (se 3 (by rfl) ⟨1062722, by rfl⟩ : syracuseStep 5667853 = 2125445) (by norm_num)
theorem B7557137 : Blo 2237435 7557137 := bstep (se 2 (by rfl) ⟨2833926, by rfl⟩ : syracuseStep 7557137 = 5667853) B5667853
theorem B5038091 : Blo 2237435 5038091 := bstep (se 1 (by rfl) ⟨3778568, by rfl⟩ : syracuseStep 5038091 = 7557137) B7557137
theorem B3358727 : Blo 2237435 3358727 := bstep (se 1 (by rfl) ⟨2519045, by rfl⟩ : syracuseStep 3358727 = 5038091) B5038091
theorem B2239151 : Blo 2237435 2239151 := bstep (se 1 (by rfl) ⟨1679363, by rfl⟩ : syracuseStep 2239151 = 3358727) B3358727
theorem B3358733 : Blo 2237435 3358733 := bbase (se 3 (by rfl) ⟨629762, by rfl⟩ : syracuseStep 3358733 = 1259525) (by norm_num)
theorem B2239155 : Blo 2237435 2239155 := bstep (se 1 (by rfl) ⟨1679366, by rfl⟩ : syracuseStep 2239155 = 3358733) B3358733
theorem B5038109 : Blo 2237435 5038109 := bbase (se 3 (by rfl) ⟨944645, by rfl⟩ : syracuseStep 5038109 = 1889291) (by norm_num)
theorem B3358739 : Blo 2237435 3358739 := bstep (se 1 (by rfl) ⟨2519054, by rfl⟩ : syracuseStep 3358739 = 5038109) B5038109
theorem B2239159 : Blo 2237435 2239159 := bstep (se 1 (by rfl) ⟨1679369, by rfl⟩ : syracuseStep 2239159 = 3358739) B3358739
theorem B3778589 : Blo 2237435 3778589 := bbase (se 3 (by rfl) ⟨708485, by rfl⟩ : syracuseStep 3778589 = 1416971) (by norm_num)
theorem B2519059 : Blo 2237435 2519059 := bstep (se 1 (by rfl) ⟨1889294, by rfl⟩ : syracuseStep 2519059 = 3778589) B3778589
theorem B3358745 : Blo 2237435 3358745 := bstep (se 2 (by rfl) ⟨1259529, by rfl⟩ : syracuseStep 3358745 = 2519059) B2519059
theorem B2239163 : Blo 2237435 2239163 := bstep (se 1 (by rfl) ⟨1679372, by rfl⟩ : syracuseStep 2239163 = 3358745) B3358745
theorem B3830149 : Blo 2237435 3830149 := bbase (se 4 (by rfl) ⟨359076, by rfl⟩ : syracuseStep 3830149 = 718153) (by norm_num)
theorem B20427461 : Blo 2237435 20427461 := bstep (se 4 (by rfl) ⟨1915074, by rfl⟩ : syracuseStep 20427461 = 3830149) B3830149
theorem B13618307 : Blo 2237435 13618307 := bstep (se 1 (by rfl) ⟨10213730, by rfl⟩ : syracuseStep 13618307 = 20427461) B20427461
theorem B36315485 : Blo 2237435 36315485 := bstep (se 3 (by rfl) ⟨6809153, by rfl⟩ : syracuseStep 36315485 = 13618307) B13618307
theorem B24210323 : Blo 2237435 24210323 := bstep (se 1 (by rfl) ⟨18157742, by rfl⟩ : syracuseStep 24210323 = 36315485) B36315485
theorem B16140215 : Blo 2237435 16140215 := bstep (se 1 (by rfl) ⟨12105161, by rfl⟩ : syracuseStep 16140215 = 24210323) B24210323
theorem B10760143 : Blo 2237435 10760143 := bstep (se 1 (by rfl) ⟨8070107, by rfl⟩ : syracuseStep 10760143 = 16140215) B16140215
theorem B14346857 : Blo 2237435 14346857 := bstep (se 2 (by rfl) ⟨5380071, by rfl⟩ : syracuseStep 14346857 = 10760143) B10760143
theorem B9564571 : Blo 2237435 9564571 := bstep (se 1 (by rfl) ⟨7173428, by rfl⟩ : syracuseStep 9564571 = 14346857) B14346857
theorem B12752761 : Blo 2237435 12752761 := bstep (se 2 (by rfl) ⟨4782285, by rfl⟩ : syracuseStep 12752761 = 9564571) B9564571
theorem B17003681 : Blo 2237435 17003681 := bstep (se 2 (by rfl) ⟨6376380, by rfl⟩ : syracuseStep 17003681 = 12752761) B12752761
theorem B11335787 : Blo 2237435 11335787 := bstep (se 1 (by rfl) ⟨8501840, by rfl⟩ : syracuseStep 11335787 = 17003681) B17003681
theorem B7557191 : Blo 2237435 7557191 := bstep (se 1 (by rfl) ⟨5667893, by rfl⟩ : syracuseStep 7557191 = 11335787) B11335787
theorem B5038127 : Blo 2237435 5038127 := bstep (se 1 (by rfl) ⟨3778595, by rfl⟩ : syracuseStep 5038127 = 7557191) B7557191
theorem B3358751 : Blo 2237435 3358751 := bstep (se 1 (by rfl) ⟨2519063, by rfl⟩ : syracuseStep 3358751 = 5038127) B5038127
theorem B2239167 : Blo 2237435 2239167 := bstep (se 1 (by rfl) ⟨1679375, by rfl⟩ : syracuseStep 2239167 = 3358751) B3358751
theorem B3358757 : Blo 2237435 3358757 := bbase (se 4 (by rfl) ⟨314883, by rfl⟩ : syracuseStep 3358757 = 629767) (by norm_num)
theorem B2239171 : Blo 2237435 2239171 := bstep (se 1 (by rfl) ⟨1679378, by rfl⟩ : syracuseStep 2239171 = 3358757) B3358757
theorem B2833957 : Blo 2237435 2833957 := bbase (se 4 (by rfl) ⟨265683, by rfl⟩ : syracuseStep 2833957 = 531367) (by norm_num)
theorem B3778609 : Blo 2237435 3778609 := bstep (se 2 (by rfl) ⟨1416978, by rfl⟩ : syracuseStep 3778609 = 2833957) B2833957
theorem B5038145 : Blo 2237435 5038145 := bstep (se 2 (by rfl) ⟨1889304, by rfl⟩ : syracuseStep 5038145 = 3778609) B3778609
theorem B3358763 : Blo 2237435 3358763 := bstep (se 1 (by rfl) ⟨2519072, by rfl⟩ : syracuseStep 3358763 = 5038145) B5038145
theorem B2239175 : Blo 2237435 2239175 := bstep (se 1 (by rfl) ⟨1679381, by rfl⟩ : syracuseStep 2239175 = 3358763) B3358763
theorem B2519077 : Blo 2237435 2519077 := bbase (se 4 (by rfl) ⟨236163, by rfl⟩ : syracuseStep 2519077 = 472327) (by norm_num)
theorem B3358769 : Blo 2237435 3358769 := bstep (se 2 (by rfl) ⟨1259538, by rfl⟩ : syracuseStep 3358769 = 2519077) B2519077
theorem B2239179 : Blo 2237435 2239179 := bstep (se 1 (by rfl) ⟨1679384, by rfl⟩ : syracuseStep 2239179 = 3358769) B3358769
theorem B18157877 : Blo 2237435 18157877 := bbase (se 5 (by rfl) ⟨851150, by rfl⟩ : syracuseStep 18157877 = 1702301) (by norm_num)
theorem B12105251 : Blo 2237435 12105251 := bstep (se 1 (by rfl) ⟨9078938, by rfl⟩ : syracuseStep 12105251 = 18157877) B18157877
theorem B8070167 : Blo 2237435 8070167 := bstep (se 1 (by rfl) ⟨6052625, by rfl⟩ : syracuseStep 8070167 = 12105251) B12105251
theorem B5380111 : Blo 2237435 5380111 := bstep (se 1 (by rfl) ⟨4035083, by rfl⟩ : syracuseStep 5380111 = 8070167) B8070167
theorem B7173481 : Blo 2237435 7173481 := bstep (se 2 (by rfl) ⟨2690055, by rfl⟩ : syracuseStep 7173481 = 5380111) B5380111
theorem B9564641 : Blo 2237435 9564641 := bstep (se 2 (by rfl) ⟨3586740, by rfl⟩ : syracuseStep 9564641 = 7173481) B7173481
theorem B6376427 : Blo 2237435 6376427 := bstep (se 1 (by rfl) ⟨4782320, by rfl⟩ : syracuseStep 6376427 = 9564641) B9564641
theorem B4250951 : Blo 2237435 4250951 := bstep (se 1 (by rfl) ⟨3188213, by rfl⟩ : syracuseStep 4250951 = 6376427) B6376427
theorem B2833967 : Blo 2237435 2833967 := bstep (se 1 (by rfl) ⟨2125475, by rfl⟩ : syracuseStep 2833967 = 4250951) B4250951
theorem B7557245 : Blo 2237435 7557245 := bstep (se 3 (by rfl) ⟨1416983, by rfl⟩ : syracuseStep 7557245 = 2833967) B2833967
theorem B5038163 : Blo 2237435 5038163 := bstep (se 1 (by rfl) ⟨3778622, by rfl⟩ : syracuseStep 5038163 = 7557245) B7557245
theorem B3358775 : Blo 2237435 3358775 := bstep (se 1 (by rfl) ⟨2519081, by rfl⟩ : syracuseStep 3358775 = 5038163) B5038163
theorem B2239183 : Blo 2237435 2239183 := bstep (se 1 (by rfl) ⟨1679387, by rfl⟩ : syracuseStep 2239183 = 3358775) B3358775
theorem B3358781 : Blo 2237435 3358781 := bbase (se 3 (by rfl) ⟨629771, by rfl⟩ : syracuseStep 3358781 = 1259543) (by norm_num)
theorem B2239187 : Blo 2237435 2239187 := bstep (se 1 (by rfl) ⟨1679390, by rfl⟩ : syracuseStep 2239187 = 3358781) B3358781
theorem B5038181 : Blo 2237435 5038181 := bbase (se 4 (by rfl) ⟨472329, by rfl⟩ : syracuseStep 5038181 = 944659) (by norm_num)
theorem B3358787 : Blo 2237435 3358787 := bstep (se 1 (by rfl) ⟨2519090, by rfl⟩ : syracuseStep 3358787 = 5038181) B5038181
theorem B2239191 : Blo 2237435 2239191 := bstep (se 1 (by rfl) ⟨1679393, by rfl⟩ : syracuseStep 2239191 = 3358787) B3358787
theorem B5667965 : Blo 2237435 5667965 := bbase (se 3 (by rfl) ⟨1062743, by rfl⟩ : syracuseStep 5667965 = 2125487) (by norm_num)
theorem B3778643 : Blo 2237435 3778643 := bstep (se 1 (by rfl) ⟨2833982, by rfl⟩ : syracuseStep 3778643 = 5667965) B5667965
theorem B2519095 : Blo 2237435 2519095 := bstep (se 1 (by rfl) ⟨1889321, by rfl⟩ : syracuseStep 2519095 = 3778643) B3778643
theorem B3358793 : Blo 2237435 3358793 := bstep (se 2 (by rfl) ⟨1259547, by rfl⟩ : syracuseStep 3358793 = 2519095) B2519095
theorem B2239195 : Blo 2237435 2239195 := bstep (se 1 (by rfl) ⟨1679396, by rfl⟩ : syracuseStep 2239195 = 3358793) B3358793
theorem B4250981 : Blo 2237435 4250981 := bbase (se 4 (by rfl) ⟨398529, by rfl⟩ : syracuseStep 4250981 = 797059) (by norm_num)
theorem B11335949 : Blo 2237435 11335949 := bstep (se 3 (by rfl) ⟨2125490, by rfl⟩ : syracuseStep 11335949 = 4250981) B4250981
theorem B7557299 : Blo 2237435 7557299 := bstep (se 1 (by rfl) ⟨5667974, by rfl⟩ : syracuseStep 7557299 = 11335949) B11335949
theorem B5038199 : Blo 2237435 5038199 := bstep (se 1 (by rfl) ⟨3778649, by rfl⟩ : syracuseStep 5038199 = 7557299) B7557299
theorem B3358799 : Blo 2237435 3358799 := bstep (se 1 (by rfl) ⟨2519099, by rfl⟩ : syracuseStep 3358799 = 5038199) B5038199
theorem B2239199 : Blo 2237435 2239199 := bstep (se 1 (by rfl) ⟨1679399, by rfl⟩ : syracuseStep 2239199 = 3358799) B3358799
theorem B3358805 : Blo 2237435 3358805 := bbase (se 8 (by rfl) ⟨19680, by rfl⟩ : syracuseStep 3358805 = 39361) (by norm_num)
theorem B2239203 : Blo 2237435 2239203 := bstep (se 1 (by rfl) ⟨1679402, by rfl⟩ : syracuseStep 2239203 = 3358805) B3358805
theorem B18158069 : Blo 2237435 18158069 := bbase (se 5 (by rfl) ⟨851159, by rfl⟩ : syracuseStep 18158069 = 1702319) (by norm_num)
theorem B12105379 : Blo 2237435 12105379 := bstep (se 1 (by rfl) ⟨9079034, by rfl⟩ : syracuseStep 12105379 = 18158069) B18158069
theorem B16140505 : Blo 2237435 16140505 := bstep (se 2 (by rfl) ⟨6052689, by rfl⟩ : syracuseStep 16140505 = 12105379) B12105379
theorem B21520673 : Blo 2237435 21520673 := bstep (se 2 (by rfl) ⟨8070252, by rfl⟩ : syracuseStep 21520673 = 16140505) B16140505
theorem B14347115 : Blo 2237435 14347115 := bstep (se 1 (by rfl) ⟨10760336, by rfl⟩ : syracuseStep 14347115 = 21520673) B21520673
theorem B9564743 : Blo 2237435 9564743 := bstep (se 1 (by rfl) ⟨7173557, by rfl⟩ : syracuseStep 9564743 = 14347115) B14347115
theorem B6376495 : Blo 2237435 6376495 := bstep (se 1 (by rfl) ⟨4782371, by rfl⟩ : syracuseStep 6376495 = 9564743) B9564743
theorem B8501993 : Blo 2237435 8501993 := bstep (se 2 (by rfl) ⟨3188247, by rfl⟩ : syracuseStep 8501993 = 6376495) B6376495
theorem B5667995 : Blo 2237435 5667995 := bstep (se 1 (by rfl) ⟨4250996, by rfl⟩ : syracuseStep 5667995 = 8501993) B8501993
theorem B3778663 : Blo 2237435 3778663 := bstep (se 1 (by rfl) ⟨2833997, by rfl⟩ : syracuseStep 3778663 = 5667995) B5667995
theorem B5038217 : Blo 2237435 5038217 := bstep (se 2 (by rfl) ⟨1889331, by rfl⟩ : syracuseStep 5038217 = 3778663) B3778663
theorem B3358811 : Blo 2237435 3358811 := bstep (se 1 (by rfl) ⟨2519108, by rfl⟩ : syracuseStep 3358811 = 5038217) B5038217
theorem B2239207 : Blo 2237435 2239207 := bstep (se 1 (by rfl) ⟨1679405, by rfl⟩ : syracuseStep 2239207 = 3358811) B3358811
theorem B2519113 : Blo 2237435 2519113 := bbase (se 2 (by rfl) ⟨944667, by rfl⟩ : syracuseStep 2519113 = 1889335) (by norm_num)
theorem B3358817 : Blo 2237435 3358817 := bstep (se 2 (by rfl) ⟨1259556, by rfl⟩ : syracuseStep 3358817 = 2519113) B2519113
theorem B2239211 : Blo 2237435 2239211 := bstep (se 1 (by rfl) ⟨1679408, by rfl⟩ : syracuseStep 2239211 = 3358817) B3358817
theorem B77562197 : Blo 2237435 77562197 := bbase (se 10 (by rfl) ⟨113616, by rfl⟩ : syracuseStep 77562197 = 227233) (by norm_num)
theorem B51708131 : Blo 2237435 51708131 := bstep (se 1 (by rfl) ⟨38781098, by rfl⟩ : syracuseStep 51708131 = 77562197) B77562197
theorem B34472087 : Blo 2237435 34472087 := bstep (se 1 (by rfl) ⟨25854065, by rfl⟩ : syracuseStep 34472087 = 51708131) B51708131
theorem B22981391 : Blo 2237435 22981391 := bstep (se 1 (by rfl) ⟨17236043, by rfl⟩ : syracuseStep 22981391 = 34472087) B34472087
theorem B15320927 : Blo 2237435 15320927 := bstep (se 1 (by rfl) ⟨11490695, by rfl⟩ : syracuseStep 15320927 = 22981391) B22981391
theorem B10213951 : Blo 2237435 10213951 := bstep (se 1 (by rfl) ⟨7660463, by rfl⟩ : syracuseStep 10213951 = 15320927) B15320927
theorem B13618601 : Blo 2237435 13618601 := bstep (se 2 (by rfl) ⟨5106975, by rfl⟩ : syracuseStep 13618601 = 10213951) B10213951
theorem B9079067 : Blo 2237435 9079067 := bstep (se 1 (by rfl) ⟨6809300, by rfl⟩ : syracuseStep 9079067 = 13618601) B13618601
theorem B6052711 : Blo 2237435 6052711 := bstep (se 1 (by rfl) ⟨4539533, by rfl⟩ : syracuseStep 6052711 = 9079067) B9079067
theorem B8070281 : Blo 2237435 8070281 := bstep (se 2 (by rfl) ⟨3026355, by rfl⟩ : syracuseStep 8070281 = 6052711) B6052711
theorem B5380187 : Blo 2237435 5380187 := bstep (se 1 (by rfl) ⟨4035140, by rfl⟩ : syracuseStep 5380187 = 8070281) B8070281
theorem B14347165 : Blo 2237435 14347165 := bstep (se 3 (by rfl) ⟨2690093, by rfl⟩ : syracuseStep 14347165 = 5380187) B5380187
theorem B19129553 : Blo 2237435 19129553 := bstep (se 2 (by rfl) ⟨7173582, by rfl⟩ : syracuseStep 19129553 = 14347165) B14347165
theorem B12753035 : Blo 2237435 12753035 := bstep (se 1 (by rfl) ⟨9564776, by rfl⟩ : syracuseStep 12753035 = 19129553) B19129553
theorem B8502023 : Blo 2237435 8502023 := bstep (se 1 (by rfl) ⟨6376517, by rfl⟩ : syracuseStep 8502023 = 12753035) B12753035
theorem B5668015 : Blo 2237435 5668015 := bstep (se 1 (by rfl) ⟨4251011, by rfl⟩ : syracuseStep 5668015 = 8502023) B8502023
theorem B7557353 : Blo 2237435 7557353 := bstep (se 2 (by rfl) ⟨2834007, by rfl⟩ : syracuseStep 7557353 = 5668015) B5668015
theorem B5038235 : Blo 2237435 5038235 := bstep (se 1 (by rfl) ⟨3778676, by rfl⟩ : syracuseStep 5038235 = 7557353) B7557353
theorem B3358823 : Blo 2237435 3358823 := bstep (se 1 (by rfl) ⟨2519117, by rfl⟩ : syracuseStep 3358823 = 5038235) B5038235
theorem B2239215 : Blo 2237435 2239215 := bstep (se 1 (by rfl) ⟨1679411, by rfl⟩ : syracuseStep 2239215 = 3358823) B3358823
theorem B3358829 : Blo 2237435 3358829 := bbase (se 3 (by rfl) ⟨629780, by rfl⟩ : syracuseStep 3358829 = 1259561) (by norm_num)
theorem B2239219 : Blo 2237435 2239219 := bstep (se 1 (by rfl) ⟨1679414, by rfl⟩ : syracuseStep 2239219 = 3358829) B3358829
theorem B5038253 : Blo 2237435 5038253 := bbase (se 3 (by rfl) ⟨944672, by rfl⟩ : syracuseStep 5038253 = 1889345) (by norm_num)
theorem B3358835 : Blo 2237435 3358835 := bstep (se 1 (by rfl) ⟨2519126, by rfl⟩ : syracuseStep 3358835 = 5038253) B5038253
theorem B2239223 : Blo 2237435 2239223 := bstep (se 1 (by rfl) ⟨1679417, by rfl⟩ : syracuseStep 2239223 = 3358835) B3358835
theorem B3635749 : Blo 2237435 3635749 := bbase (se 4 (by rfl) ⟨340851, by rfl⟩ : syracuseStep 3635749 = 681703) (by norm_num)
theorem B19390661 : Blo 2237435 19390661 := bstep (se 4 (by rfl) ⟨1817874, by rfl⟩ : syracuseStep 19390661 = 3635749) B3635749
theorem B12927107 : Blo 2237435 12927107 := bstep (se 1 (by rfl) ⟨9695330, by rfl⟩ : syracuseStep 12927107 = 19390661) B19390661
theorem B8618071 : Blo 2237435 8618071 := bstep (se 1 (by rfl) ⟨6463553, by rfl⟩ : syracuseStep 8618071 = 12927107) B12927107
theorem B11490761 : Blo 2237435 11490761 := bstep (se 2 (by rfl) ⟨4309035, by rfl⟩ : syracuseStep 11490761 = 8618071) B8618071
theorem B7660507 : Blo 2237435 7660507 := bstep (se 1 (by rfl) ⟨5745380, by rfl⟩ : syracuseStep 7660507 = 11490761) B11490761
theorem B10214009 : Blo 2237435 10214009 := bstep (se 2 (by rfl) ⟨3830253, by rfl⟩ : syracuseStep 10214009 = 7660507) B7660507
theorem B6809339 : Blo 2237435 6809339 := bstep (se 1 (by rfl) ⟨5107004, by rfl⟩ : syracuseStep 6809339 = 10214009) B10214009
theorem B4539559 : Blo 2237435 4539559 := bstep (se 1 (by rfl) ⟨3404669, by rfl⟩ : syracuseStep 4539559 = 6809339) B6809339
theorem B6052745 : Blo 2237435 6052745 := bstep (se 2 (by rfl) ⟨2269779, by rfl⟩ : syracuseStep 6052745 = 4539559) B4539559
theorem B16140653 : Blo 2237435 16140653 := bstep (se 3 (by rfl) ⟨3026372, by rfl⟩ : syracuseStep 16140653 = 6052745) B6052745
theorem B10760435 : Blo 2237435 10760435 := bstep (se 1 (by rfl) ⟨8070326, by rfl⟩ : syracuseStep 10760435 = 16140653) B16140653
theorem B7173623 : Blo 2237435 7173623 := bstep (se 1 (by rfl) ⟨5380217, by rfl⟩ : syracuseStep 7173623 = 10760435) B10760435
theorem B4782415 : Blo 2237435 4782415 := bstep (se 1 (by rfl) ⟨3586811, by rfl⟩ : syracuseStep 4782415 = 7173623) B7173623
theorem B6376553 : Blo 2237435 6376553 := bstep (se 2 (by rfl) ⟨2391207, by rfl⟩ : syracuseStep 6376553 = 4782415) B4782415
theorem B4251035 : Blo 2237435 4251035 := bstep (se 1 (by rfl) ⟨3188276, by rfl⟩ : syracuseStep 4251035 = 6376553) B6376553
theorem B2834023 : Blo 2237435 2834023 := bstep (se 1 (by rfl) ⟨2125517, by rfl⟩ : syracuseStep 2834023 = 4251035) B4251035
theorem B3778697 : Blo 2237435 3778697 := bstep (se 2 (by rfl) ⟨1417011, by rfl⟩ : syracuseStep 3778697 = 2834023) B2834023
theorem B2519131 : Blo 2237435 2519131 := bstep (se 1 (by rfl) ⟨1889348, by rfl⟩ : syracuseStep 2519131 = 3778697) B3778697
theorem B3358841 : Blo 2237435 3358841 := bstep (se 2 (by rfl) ⟨1259565, by rfl⟩ : syracuseStep 3358841 = 2519131) B2519131
theorem B2239227 : Blo 2237435 2239227 := bstep (se 1 (by rfl) ⟨1679420, by rfl⟩ : syracuseStep 2239227 = 3358841) B3358841
theorem B5107013 : Blo 2237435 5107013 := bbase (se 4 (by rfl) ⟨478782, by rfl⟩ : syracuseStep 5107013 = 957565) (by norm_num)
theorem B3404675 : Blo 2237435 3404675 := bstep (se 1 (by rfl) ⟨2553506, by rfl⟩ : syracuseStep 3404675 = 5107013) B5107013
theorem B2269783 : Blo 2237435 2269783 := bstep (se 1 (by rfl) ⟨1702337, by rfl⟩ : syracuseStep 2269783 = 3404675) B3404675
theorem B3026377 : Blo 2237435 3026377 := bstep (se 2 (by rfl) ⟨1134891, by rfl⟩ : syracuseStep 3026377 = 2269783) B2269783
theorem B4035169 : Blo 2237435 4035169 := bstep (se 2 (by rfl) ⟨1513188, by rfl⟩ : syracuseStep 4035169 = 3026377) B3026377
theorem B5380225 : Blo 2237435 5380225 := bstep (se 2 (by rfl) ⟨2017584, by rfl⟩ : syracuseStep 5380225 = 4035169) B4035169
theorem B28694533 : Blo 2237435 28694533 := bstep (se 4 (by rfl) ⟨2690112, by rfl⟩ : syracuseStep 28694533 = 5380225) B5380225
theorem B38259377 : Blo 2237435 38259377 := bstep (se 2 (by rfl) ⟨14347266, by rfl⟩ : syracuseStep 38259377 = 28694533) B28694533
theorem B25506251 : Blo 2237435 25506251 := bstep (se 1 (by rfl) ⟨19129688, by rfl⟩ : syracuseStep 25506251 = 38259377) B38259377
theorem B17004167 : Blo 2237435 17004167 := bstep (se 1 (by rfl) ⟨12753125, by rfl⟩ : syracuseStep 17004167 = 25506251) B25506251
theorem B11336111 : Blo 2237435 11336111 := bstep (se 1 (by rfl) ⟨8502083, by rfl⟩ : syracuseStep 11336111 = 17004167) B17004167
theorem B7557407 : Blo 2237435 7557407 := bstep (se 1 (by rfl) ⟨5668055, by rfl⟩ : syracuseStep 7557407 = 11336111) B11336111
theorem B5038271 : Blo 2237435 5038271 := bstep (se 1 (by rfl) ⟨3778703, by rfl⟩ : syracuseStep 5038271 = 7557407) B7557407
theorem B3358847 : Blo 2237435 3358847 := bstep (se 1 (by rfl) ⟨2519135, by rfl⟩ : syracuseStep 3358847 = 5038271) B5038271
theorem B2239231 : Blo 2237435 2239231 := bstep (se 1 (by rfl) ⟨1679423, by rfl⟩ : syracuseStep 2239231 = 3358847) B3358847
theorem B3358853 : Blo 2237435 3358853 := bbase (se 4 (by rfl) ⟨314892, by rfl⟩ : syracuseStep 3358853 = 629785) (by norm_num)
theorem B2239235 : Blo 2237435 2239235 := bstep (se 1 (by rfl) ⟨1679426, by rfl⟩ : syracuseStep 2239235 = 3358853) B3358853
theorem B3778717 : Blo 2237435 3778717 := bbase (se 3 (by rfl) ⟨708509, by rfl⟩ : syracuseStep 3778717 = 1417019) (by norm_num)
theorem B5038289 : Blo 2237435 5038289 := bstep (se 2 (by rfl) ⟨1889358, by rfl⟩ : syracuseStep 5038289 = 3778717) B3778717
theorem B3358859 : Blo 2237435 3358859 := bstep (se 1 (by rfl) ⟨2519144, by rfl⟩ : syracuseStep 3358859 = 5038289) B5038289
theorem B2239239 : Blo 2237435 2239239 := bstep (se 1 (by rfl) ⟨1679429, by rfl⟩ : syracuseStep 2239239 = 3358859) B3358859
theorem B2519149 : Blo 2237435 2519149 := bbase (se 3 (by rfl) ⟨472340, by rfl⟩ : syracuseStep 2519149 = 944681) (by norm_num)
theorem B3358865 : Blo 2237435 3358865 := bstep (se 2 (by rfl) ⟨1259574, by rfl⟩ : syracuseStep 3358865 = 2519149) B2519149
theorem B2239243 : Blo 2237435 2239243 := bstep (se 1 (by rfl) ⟨1679432, by rfl⟩ : syracuseStep 2239243 = 3358865) B3358865
theorem B7557461 : Blo 2237435 7557461 := bbase (se 10 (by rfl) ⟨11070, by rfl⟩ : syracuseStep 7557461 = 22141) (by norm_num)
theorem B5038307 : Blo 2237435 5038307 := bstep (se 1 (by rfl) ⟨3778730, by rfl⟩ : syracuseStep 5038307 = 7557461) B7557461
theorem B3358871 : Blo 2237435 3358871 := bstep (se 1 (by rfl) ⟨2519153, by rfl⟩ : syracuseStep 3358871 = 5038307) B5038307
theorem B2239247 : Blo 2237435 2239247 := bstep (se 1 (by rfl) ⟨1679435, by rfl⟩ : syracuseStep 2239247 = 3358871) B3358871
theorem B3358877 : Blo 2237435 3358877 := bbase (se 3 (by rfl) ⟨629789, by rfl⟩ : syracuseStep 3358877 = 1259579) (by norm_num)
theorem B2239251 : Blo 2237435 2239251 := bstep (se 1 (by rfl) ⟨1679438, by rfl⟩ : syracuseStep 2239251 = 3358877) B3358877
theorem B5038325 : Blo 2237435 5038325 := bbase (se 5 (by rfl) ⟨236171, by rfl⟩ : syracuseStep 5038325 = 472343) (by norm_num)
theorem B3358883 : Blo 2237435 3358883 := bstep (se 1 (by rfl) ⟨2519162, by rfl⟩ : syracuseStep 3358883 = 5038325) B5038325
theorem B2239255 : Blo 2237435 2239255 := bstep (se 1 (by rfl) ⟨1679441, by rfl⟩ : syracuseStep 2239255 = 3358883) B3358883
theorem B21521173 : Blo 2237435 21521173 := bbase (se 6 (by rfl) ⟨504402, by rfl⟩ : syracuseStep 21521173 = 1008805) (by norm_num)
theorem B28694897 : Blo 2237435 28694897 := bstep (se 2 (by rfl) ⟨10760586, by rfl⟩ : syracuseStep 28694897 = 21521173) B21521173
theorem B19129931 : Blo 2237435 19129931 := bstep (se 1 (by rfl) ⟨14347448, by rfl⟩ : syracuseStep 19129931 = 28694897) B28694897
theorem B12753287 : Blo 2237435 12753287 := bstep (se 1 (by rfl) ⟨9564965, by rfl⟩ : syracuseStep 12753287 = 19129931) B19129931
theorem B8502191 : Blo 2237435 8502191 := bstep (se 1 (by rfl) ⟨6376643, by rfl⟩ : syracuseStep 8502191 = 12753287) B12753287
theorem B5668127 : Blo 2237435 5668127 := bstep (se 1 (by rfl) ⟨4251095, by rfl⟩ : syracuseStep 5668127 = 8502191) B8502191
theorem B3778751 : Blo 2237435 3778751 := bstep (se 1 (by rfl) ⟨2834063, by rfl⟩ : syracuseStep 3778751 = 5668127) B5668127
theorem B2519167 : Blo 2237435 2519167 := bstep (se 1 (by rfl) ⟨1889375, by rfl⟩ : syracuseStep 2519167 = 3778751) B3778751
theorem B3358889 : Blo 2237435 3358889 := bstep (se 2 (by rfl) ⟨1259583, by rfl⟩ : syracuseStep 3358889 = 2519167) B2519167
theorem B2239259 : Blo 2237435 2239259 := bstep (se 1 (by rfl) ⟨1679444, by rfl⟩ : syracuseStep 2239259 = 3358889) B3358889
theorem B5528117 : Blo 2237435 5528117 := bbase (se 5 (by rfl) ⟨259130, by rfl⟩ : syracuseStep 5528117 = 518261) (by norm_num)
theorem B3685411 : Blo 2237435 3685411 := bstep (se 1 (by rfl) ⟨2764058, by rfl⟩ : syracuseStep 3685411 = 5528117) B5528117
theorem B19655525 : Blo 2237435 19655525 := bstep (se 4 (by rfl) ⟨1842705, by rfl⟩ : syracuseStep 19655525 = 3685411) B3685411
theorem B13103683 : Blo 2237435 13103683 := bstep (se 1 (by rfl) ⟨9827762, by rfl⟩ : syracuseStep 13103683 = 19655525) B19655525
theorem B69886309 : Blo 2237435 69886309 := bstep (se 4 (by rfl) ⟨6551841, by rfl⟩ : syracuseStep 69886309 = 13103683) B13103683
theorem B93181745 : Blo 2237435 93181745 := bstep (se 2 (by rfl) ⟨34943154, by rfl⟩ : syracuseStep 93181745 = 69886309) B69886309
theorem B62121163 : Blo 2237435 62121163 := bstep (se 1 (by rfl) ⟨46590872, by rfl⟩ : syracuseStep 62121163 = 93181745) B93181745
theorem B82828217 : Blo 2237435 82828217 := bstep (se 2 (by rfl) ⟨31060581, by rfl⟩ : syracuseStep 82828217 = 62121163) B62121163
theorem B220875245 : Blo 2237435 220875245 := bstep (se 3 (by rfl) ⟨41414108, by rfl⟩ : syracuseStep 220875245 = 82828217) B82828217
theorem B147250163 : Blo 2237435 147250163 := bstep (se 1 (by rfl) ⟨110437622, by rfl⟩ : syracuseStep 147250163 = 220875245) B220875245
theorem B98166775 : Blo 2237435 98166775 := bstep (se 1 (by rfl) ⟨73625081, by rfl⟩ : syracuseStep 98166775 = 147250163) B147250163
theorem B130889033 : Blo 2237435 130889033 := bstep (se 2 (by rfl) ⟨49083387, by rfl⟩ : syracuseStep 130889033 = 98166775) B98166775
theorem B87259355 : Blo 2237435 87259355 := bstep (se 1 (by rfl) ⟨65444516, by rfl⟩ : syracuseStep 87259355 = 130889033) B130889033
theorem B58172903 : Blo 2237435 58172903 := bstep (se 1 (by rfl) ⟨43629677, by rfl⟩ : syracuseStep 58172903 = 87259355) B87259355
theorem B38781935 : Blo 2237435 38781935 := bstep (se 1 (by rfl) ⟨29086451, by rfl⟩ : syracuseStep 38781935 = 58172903) B58172903
theorem B25854623 : Blo 2237435 25854623 := bstep (se 1 (by rfl) ⟨19390967, by rfl⟩ : syracuseStep 25854623 = 38781935) B38781935
theorem B17236415 : Blo 2237435 17236415 := bstep (se 1 (by rfl) ⟨12927311, by rfl⟩ : syracuseStep 17236415 = 25854623) B25854623
theorem B11490943 : Blo 2237435 11490943 := bstep (se 1 (by rfl) ⟨8618207, by rfl⟩ : syracuseStep 11490943 = 17236415) B17236415
theorem B15321257 : Blo 2237435 15321257 := bstep (se 2 (by rfl) ⟨5745471, by rfl⟩ : syracuseStep 15321257 = 11490943) B11490943
theorem B10214171 : Blo 2237435 10214171 := bstep (se 1 (by rfl) ⟨7660628, by rfl⟩ : syracuseStep 10214171 = 15321257) B15321257
theorem B6809447 : Blo 2237435 6809447 := bstep (se 1 (by rfl) ⟨5107085, by rfl⟩ : syracuseStep 6809447 = 10214171) B10214171
theorem B18158525 : Blo 2237435 18158525 := bstep (se 3 (by rfl) ⟨3404723, by rfl⟩ : syracuseStep 18158525 = 6809447) B6809447
theorem B12105683 : Blo 2237435 12105683 := bstep (se 1 (by rfl) ⟨9079262, by rfl⟩ : syracuseStep 12105683 = 18158525) B18158525
theorem B8070455 : Blo 2237435 8070455 := bstep (se 1 (by rfl) ⟨6052841, by rfl⟩ : syracuseStep 8070455 = 12105683) B12105683
theorem B5380303 : Blo 2237435 5380303 := bstep (se 1 (by rfl) ⟨4035227, by rfl⟩ : syracuseStep 5380303 = 8070455) B8070455
theorem B7173737 : Blo 2237435 7173737 := bstep (se 2 (by rfl) ⟨2690151, by rfl⟩ : syracuseStep 7173737 = 5380303) B5380303
theorem B4782491 : Blo 2237435 4782491 := bstep (se 1 (by rfl) ⟨3586868, by rfl⟩ : syracuseStep 4782491 = 7173737) B7173737
theorem B3188327 : Blo 2237435 3188327 := bstep (se 1 (by rfl) ⟨2391245, by rfl⟩ : syracuseStep 3188327 = 4782491) B4782491
theorem B8502205 : Blo 2237435 8502205 := bstep (se 3 (by rfl) ⟨1594163, by rfl⟩ : syracuseStep 8502205 = 3188327) B3188327
theorem B11336273 : Blo 2237435 11336273 := bstep (se 2 (by rfl) ⟨4251102, by rfl⟩ : syracuseStep 11336273 = 8502205) B8502205
theorem B7557515 : Blo 2237435 7557515 := bstep (se 1 (by rfl) ⟨5668136, by rfl⟩ : syracuseStep 7557515 = 11336273) B11336273
theorem B5038343 : Blo 2237435 5038343 := bstep (se 1 (by rfl) ⟨3778757, by rfl⟩ : syracuseStep 5038343 = 7557515) B7557515
theorem B3358895 : Blo 2237435 3358895 := bstep (se 1 (by rfl) ⟨2519171, by rfl⟩ : syracuseStep 3358895 = 5038343) B5038343
theorem B2239263 : Blo 2237435 2239263 := bstep (se 1 (by rfl) ⟨1679447, by rfl⟩ : syracuseStep 2239263 = 3358895) B3358895
theorem B3358901 : Blo 2237435 3358901 := bbase (se 5 (by rfl) ⟨157448, by rfl⟩ : syracuseStep 3358901 = 314897) (by norm_num)
theorem B2239267 : Blo 2237435 2239267 := bstep (se 1 (by rfl) ⟨1679450, by rfl⟩ : syracuseStep 2239267 = 3358901) B3358901
theorem B5668157 : Blo 2237435 5668157 := bbase (se 3 (by rfl) ⟨1062779, by rfl⟩ : syracuseStep 5668157 = 2125559) (by norm_num)
theorem B3778771 : Blo 2237435 3778771 := bstep (se 1 (by rfl) ⟨2834078, by rfl⟩ : syracuseStep 3778771 = 5668157) B5668157
theorem B5038361 : Blo 2237435 5038361 := bstep (se 2 (by rfl) ⟨1889385, by rfl⟩ : syracuseStep 5038361 = 3778771) B3778771
theorem B3358907 : Blo 2237435 3358907 := bstep (se 1 (by rfl) ⟨2519180, by rfl⟩ : syracuseStep 3358907 = 5038361) B5038361
theorem B2239271 : Blo 2237435 2239271 := bstep (se 1 (by rfl) ⟨1679453, by rfl⟩ : syracuseStep 2239271 = 3358907) B3358907
theorem B2519185 : Blo 2237435 2519185 := bbase (se 2 (by rfl) ⟨944694, by rfl⟩ : syracuseStep 2519185 = 1889389) (by norm_num)
theorem B3358913 : Blo 2237435 3358913 := bstep (se 2 (by rfl) ⟨1259592, by rfl⟩ : syracuseStep 3358913 = 2519185) B2519185
theorem B2239275 : Blo 2237435 2239275 := bstep (se 1 (by rfl) ⟨1679456, by rfl⟩ : syracuseStep 2239275 = 3358913) B3358913
theorem B4251133 : Blo 2237435 4251133 := bbase (se 3 (by rfl) ⟨797087, by rfl⟩ : syracuseStep 4251133 = 1594175) (by norm_num)
theorem B5668177 : Blo 2237435 5668177 := bstep (se 2 (by rfl) ⟨2125566, by rfl⟩ : syracuseStep 5668177 = 4251133) B4251133
theorem B7557569 : Blo 2237435 7557569 := bstep (se 2 (by rfl) ⟨2834088, by rfl⟩ : syracuseStep 7557569 = 5668177) B5668177
theorem B5038379 : Blo 2237435 5038379 := bstep (se 1 (by rfl) ⟨3778784, by rfl⟩ : syracuseStep 5038379 = 7557569) B7557569
theorem B3358919 : Blo 2237435 3358919 := bstep (se 1 (by rfl) ⟨2519189, by rfl⟩ : syracuseStep 3358919 = 5038379) B5038379
theorem B2239279 : Blo 2237435 2239279 := bstep (se 1 (by rfl) ⟨1679459, by rfl⟩ : syracuseStep 2239279 = 3358919) B3358919
theorem B3358925 : Blo 2237435 3358925 := bbase (se 3 (by rfl) ⟨629798, by rfl⟩ : syracuseStep 3358925 = 1259597) (by norm_num)
theorem B2239283 : Blo 2237435 2239283 := bstep (se 1 (by rfl) ⟨1679462, by rfl⟩ : syracuseStep 2239283 = 3358925) B3358925
theorem B5038397 : Blo 2237435 5038397 := bbase (se 3 (by rfl) ⟨944699, by rfl⟩ : syracuseStep 5038397 = 1889399) (by norm_num)
theorem B3358931 : Blo 2237435 3358931 := bstep (se 1 (by rfl) ⟨2519198, by rfl⟩ : syracuseStep 3358931 = 5038397) B5038397
theorem B2239287 : Blo 2237435 2239287 := bstep (se 1 (by rfl) ⟨1679465, by rfl⟩ : syracuseStep 2239287 = 3358931) B3358931
theorem B3778805 : Blo 2237435 3778805 := bbase (se 5 (by rfl) ⟨177131, by rfl⟩ : syracuseStep 3778805 = 354263) (by norm_num)
theorem B2519203 : Blo 2237435 2519203 := bstep (se 1 (by rfl) ⟨1889402, by rfl⟩ : syracuseStep 2519203 = 3778805) B3778805
theorem B3358937 : Blo 2237435 3358937 := bstep (se 2 (by rfl) ⟨1259601, by rfl⟩ : syracuseStep 3358937 = 2519203) B2519203
theorem B2239291 : Blo 2237435 2239291 := bstep (se 1 (by rfl) ⟨1679468, by rfl⟩ : syracuseStep 2239291 = 3358937) B3358937
theorem B9695621 : Blo 2237435 9695621 := bbase (se 4 (by rfl) ⟨908964, by rfl⟩ : syracuseStep 9695621 = 1817929) (by norm_num)
theorem B6463747 : Blo 2237435 6463747 := bstep (se 1 (by rfl) ⟨4847810, by rfl⟩ : syracuseStep 6463747 = 9695621) B9695621
theorem B8618329 : Blo 2237435 8618329 := bstep (se 2 (by rfl) ⟨3231873, by rfl⟩ : syracuseStep 8618329 = 6463747) B6463747
theorem B45964421 : Blo 2237435 45964421 := bstep (se 4 (by rfl) ⟨4309164, by rfl⟩ : syracuseStep 45964421 = 8618329) B8618329
theorem B30642947 : Blo 2237435 30642947 := bstep (se 1 (by rfl) ⟨22982210, by rfl⟩ : syracuseStep 30642947 = 45964421) B45964421
theorem B20428631 : Blo 2237435 20428631 := bstep (se 1 (by rfl) ⟨15321473, by rfl⟩ : syracuseStep 20428631 = 30642947) B30642947
theorem B13619087 : Blo 2237435 13619087 := bstep (se 1 (by rfl) ⟨10214315, by rfl⟩ : syracuseStep 13619087 = 20428631) B20428631
theorem B9079391 : Blo 2237435 9079391 := bstep (se 1 (by rfl) ⟨6809543, by rfl⟩ : syracuseStep 9079391 = 13619087) B13619087
theorem B24211709 : Blo 2237435 24211709 := bstep (se 3 (by rfl) ⟨4539695, by rfl⟩ : syracuseStep 24211709 = 9079391) B9079391
theorem B16141139 : Blo 2237435 16141139 := bstep (se 1 (by rfl) ⟨12105854, by rfl⟩ : syracuseStep 16141139 = 24211709) B24211709
theorem B10760759 : Blo 2237435 10760759 := bstep (se 1 (by rfl) ⟨8070569, by rfl⟩ : syracuseStep 10760759 = 16141139) B16141139
theorem B7173839 : Blo 2237435 7173839 := bstep (se 1 (by rfl) ⟨5380379, by rfl⟩ : syracuseStep 7173839 = 10760759) B10760759
theorem B4782559 : Blo 2237435 4782559 := bstep (se 1 (by rfl) ⟨3586919, by rfl⟩ : syracuseStep 4782559 = 7173839) B7173839
theorem B6376745 : Blo 2237435 6376745 := bstep (se 2 (by rfl) ⟨2391279, by rfl⟩ : syracuseStep 6376745 = 4782559) B4782559
theorem B17004653 : Blo 2237435 17004653 := bstep (se 3 (by rfl) ⟨3188372, by rfl⟩ : syracuseStep 17004653 = 6376745) B6376745
theorem B11336435 : Blo 2237435 11336435 := bstep (se 1 (by rfl) ⟨8502326, by rfl⟩ : syracuseStep 11336435 = 17004653) B17004653
theorem B7557623 : Blo 2237435 7557623 := bstep (se 1 (by rfl) ⟨5668217, by rfl⟩ : syracuseStep 7557623 = 11336435) B11336435
theorem B5038415 : Blo 2237435 5038415 := bstep (se 1 (by rfl) ⟨3778811, by rfl⟩ : syracuseStep 5038415 = 7557623) B7557623
theorem B3358943 : Blo 2237435 3358943 := bstep (se 1 (by rfl) ⟨2519207, by rfl⟩ : syracuseStep 3358943 = 5038415) B5038415
theorem B2239295 : Blo 2237435 2239295 := bstep (se 1 (by rfl) ⟨1679471, by rfl⟩ : syracuseStep 2239295 = 3358943) B3358943
theorem B3358949 : Blo 2237435 3358949 := bbase (se 4 (by rfl) ⟨314901, by rfl⟩ : syracuseStep 3358949 = 629803) (by norm_num)
theorem B2239299 : Blo 2237435 2239299 := bstep (se 1 (by rfl) ⟨1679474, by rfl⟩ : syracuseStep 2239299 = 3358949) B3358949
theorem B3586933 : Blo 2237435 3586933 := bbase (se 5 (by rfl) ⟨168137, by rfl⟩ : syracuseStep 3586933 = 336275) (by norm_num)
theorem B4782577 : Blo 2237435 4782577 := bstep (se 2 (by rfl) ⟨1793466, by rfl⟩ : syracuseStep 4782577 = 3586933) B3586933
theorem B6376769 : Blo 2237435 6376769 := bstep (se 2 (by rfl) ⟨2391288, by rfl⟩ : syracuseStep 6376769 = 4782577) B4782577
theorem B4251179 : Blo 2237435 4251179 := bstep (se 1 (by rfl) ⟨3188384, by rfl⟩ : syracuseStep 4251179 = 6376769) B6376769
theorem B2834119 : Blo 2237435 2834119 := bstep (se 1 (by rfl) ⟨2125589, by rfl⟩ : syracuseStep 2834119 = 4251179) B4251179
theorem B3778825 : Blo 2237435 3778825 := bstep (se 2 (by rfl) ⟨1417059, by rfl⟩ : syracuseStep 3778825 = 2834119) B2834119
theorem B5038433 : Blo 2237435 5038433 := bstep (se 2 (by rfl) ⟨1889412, by rfl⟩ : syracuseStep 5038433 = 3778825) B3778825
theorem B3358955 : Blo 2237435 3358955 := bstep (se 1 (by rfl) ⟨2519216, by rfl⟩ : syracuseStep 3358955 = 5038433) B5038433
theorem B2239303 : Blo 2237435 2239303 := bstep (se 1 (by rfl) ⟨1679477, by rfl⟩ : syracuseStep 2239303 = 3358955) B3358955
theorem B2519221 : Blo 2237435 2519221 := bbase (se 5 (by rfl) ⟨118088, by rfl⟩ : syracuseStep 2519221 = 236177) (by norm_num)
theorem B3358961 : Blo 2237435 3358961 := bstep (se 2 (by rfl) ⟨1259610, by rfl⟩ : syracuseStep 3358961 = 2519221) B2519221
theorem B2239307 : Blo 2237435 2239307 := bstep (se 1 (by rfl) ⟨1679480, by rfl⟩ : syracuseStep 2239307 = 3358961) B3358961
theorem B2834129 : Blo 2237435 2834129 := bbase (se 2 (by rfl) ⟨1062798, by rfl⟩ : syracuseStep 2834129 = 2125597) (by norm_num)
theorem B7557677 : Blo 2237435 7557677 := bstep (se 3 (by rfl) ⟨1417064, by rfl⟩ : syracuseStep 7557677 = 2834129) B2834129
theorem B5038451 : Blo 2237435 5038451 := bstep (se 1 (by rfl) ⟨3778838, by rfl⟩ : syracuseStep 5038451 = 7557677) B7557677
theorem B3358967 : Blo 2237435 3358967 := bstep (se 1 (by rfl) ⟨2519225, by rfl⟩ : syracuseStep 3358967 = 5038451) B5038451
theorem B2239311 : Blo 2237435 2239311 := bstep (se 1 (by rfl) ⟨1679483, by rfl⟩ : syracuseStep 2239311 = 3358967) B3358967
theorem B3358973 : Blo 2237435 3358973 := bbase (se 3 (by rfl) ⟨629807, by rfl⟩ : syracuseStep 3358973 = 1259615) (by norm_num)
theorem B2239315 : Blo 2237435 2239315 := bstep (se 1 (by rfl) ⟨1679486, by rfl⟩ : syracuseStep 2239315 = 3358973) B3358973
theorem B5038469 : Blo 2237435 5038469 := bbase (se 4 (by rfl) ⟨472356, by rfl⟩ : syracuseStep 5038469 = 944713) (by norm_num)
theorem B3358979 : Blo 2237435 3358979 := bstep (se 1 (by rfl) ⟨2519234, by rfl⟩ : syracuseStep 3358979 = 5038469) B5038469
theorem B2239319 : Blo 2237435 2239319 := bstep (se 1 (by rfl) ⟨1679489, by rfl⟩ : syracuseStep 2239319 = 3358979) B3358979
theorem B3188413 : Blo 2237435 3188413 := bbase (se 3 (by rfl) ⟨597827, by rfl⟩ : syracuseStep 3188413 = 1195655) (by norm_num)
theorem B4251217 : Blo 2237435 4251217 := bstep (se 2 (by rfl) ⟨1594206, by rfl⟩ : syracuseStep 4251217 = 3188413) B3188413
theorem B5668289 : Blo 2237435 5668289 := bstep (se 2 (by rfl) ⟨2125608, by rfl⟩ : syracuseStep 5668289 = 4251217) B4251217
theorem B3778859 : Blo 2237435 3778859 := bstep (se 1 (by rfl) ⟨2834144, by rfl⟩ : syracuseStep 3778859 = 5668289) B5668289
theorem B2519239 : Blo 2237435 2519239 := bstep (se 1 (by rfl) ⟨1889429, by rfl⟩ : syracuseStep 2519239 = 3778859) B3778859
theorem B3358985 : Blo 2237435 3358985 := bstep (se 2 (by rfl) ⟨1259619, by rfl⟩ : syracuseStep 3358985 = 2519239) B2519239
theorem B2239323 : Blo 2237435 2239323 := bstep (se 1 (by rfl) ⟨1679492, by rfl⟩ : syracuseStep 2239323 = 3358985) B3358985
theorem B11336597 : Blo 2237435 11336597 := bbase (se 6 (by rfl) ⟨265701, by rfl⟩ : syracuseStep 11336597 = 531403) (by norm_num)
theorem B7557731 : Blo 2237435 7557731 := bstep (se 1 (by rfl) ⟨5668298, by rfl⟩ : syracuseStep 7557731 = 11336597) B11336597
theorem B5038487 : Blo 2237435 5038487 := bstep (se 1 (by rfl) ⟨3778865, by rfl⟩ : syracuseStep 5038487 = 7557731) B7557731
theorem B3358991 : Blo 2237435 3358991 := bstep (se 1 (by rfl) ⟨2519243, by rfl⟩ : syracuseStep 3358991 = 5038487) B5038487
theorem B2239327 : Blo 2237435 2239327 := bstep (se 1 (by rfl) ⟨1679495, by rfl⟩ : syracuseStep 2239327 = 3358991) B3358991
theorem B3358997 : Blo 2237435 3358997 := bbase (se 6 (by rfl) ⟨78726, by rfl⟩ : syracuseStep 3358997 = 157453) (by norm_num)
theorem B2239331 : Blo 2237435 2239331 := bstep (se 1 (by rfl) ⟨1679498, by rfl⟩ : syracuseStep 2239331 = 3358997) B3358997
theorem B3830437 : Blo 2237435 3830437 := bbase (se 4 (by rfl) ⟨359103, by rfl⟩ : syracuseStep 3830437 = 718207) (by norm_num)
theorem B5107249 : Blo 2237435 5107249 := bstep (se 2 (by rfl) ⟨1915218, by rfl⟩ : syracuseStep 5107249 = 3830437) B3830437
theorem B6809665 : Blo 2237435 6809665 := bstep (se 2 (by rfl) ⟨2553624, by rfl⟩ : syracuseStep 6809665 = 5107249) B5107249
theorem B9079553 : Blo 2237435 9079553 := bstep (se 2 (by rfl) ⟨3404832, by rfl⟩ : syracuseStep 9079553 = 6809665) B6809665
theorem B24212141 : Blo 2237435 24212141 := bstep (se 3 (by rfl) ⟨4539776, by rfl⟩ : syracuseStep 24212141 = 9079553) B9079553
theorem B16141427 : Blo 2237435 16141427 := bstep (se 1 (by rfl) ⟨12106070, by rfl⟩ : syracuseStep 16141427 = 24212141) B24212141
theorem B10760951 : Blo 2237435 10760951 := bstep (se 1 (by rfl) ⟨8070713, by rfl⟩ : syracuseStep 10760951 = 16141427) B16141427
theorem B28695869 : Blo 2237435 28695869 := bstep (se 3 (by rfl) ⟨5380475, by rfl⟩ : syracuseStep 28695869 = 10760951) B10760951
theorem B19130579 : Blo 2237435 19130579 := bstep (se 1 (by rfl) ⟨14347934, by rfl⟩ : syracuseStep 19130579 = 28695869) B28695869
theorem B12753719 : Blo 2237435 12753719 := bstep (se 1 (by rfl) ⟨9565289, by rfl⟩ : syracuseStep 12753719 = 19130579) B19130579
theorem B8502479 : Blo 2237435 8502479 := bstep (se 1 (by rfl) ⟨6376859, by rfl⟩ : syracuseStep 8502479 = 12753719) B12753719
theorem B5668319 : Blo 2237435 5668319 := bstep (se 1 (by rfl) ⟨4251239, by rfl⟩ : syracuseStep 5668319 = 8502479) B8502479
theorem B3778879 : Blo 2237435 3778879 := bstep (se 1 (by rfl) ⟨2834159, by rfl⟩ : syracuseStep 3778879 = 5668319) B5668319
theorem B5038505 : Blo 2237435 5038505 := bstep (se 2 (by rfl) ⟨1889439, by rfl⟩ : syracuseStep 5038505 = 3778879) B3778879
theorem B3359003 : Blo 2237435 3359003 := bstep (se 1 (by rfl) ⟨2519252, by rfl⟩ : syracuseStep 3359003 = 5038505) B5038505
theorem B2239335 : Blo 2237435 2239335 := bstep (se 1 (by rfl) ⟨1679501, by rfl⟩ : syracuseStep 2239335 = 3359003) B3359003
theorem B2519257 : Blo 2237435 2519257 := bbase (se 2 (by rfl) ⟨944721, by rfl⟩ : syracuseStep 2519257 = 1889443) (by norm_num)
theorem B3359009 : Blo 2237435 3359009 := bstep (se 2 (by rfl) ⟨1259628, by rfl⟩ : syracuseStep 3359009 = 2519257) B2519257
theorem B2239339 : Blo 2237435 2239339 := bstep (se 1 (by rfl) ⟨1679504, by rfl⟩ : syracuseStep 2239339 = 3359009) B3359009
theorem B3586997 : Blo 2237435 3586997 := bbase (se 5 (by rfl) ⟨168140, by rfl⟩ : syracuseStep 3586997 = 336281) (by norm_num)
theorem B2391331 : Blo 2237435 2391331 := bstep (se 1 (by rfl) ⟨1793498, by rfl⟩ : syracuseStep 2391331 = 3586997) B3586997
theorem B3188441 : Blo 2237435 3188441 := bstep (se 2 (by rfl) ⟨1195665, by rfl⟩ : syracuseStep 3188441 = 2391331) B2391331
theorem B8502509 : Blo 2237435 8502509 := bstep (se 3 (by rfl) ⟨1594220, by rfl⟩ : syracuseStep 8502509 = 3188441) B3188441
theorem B5668339 : Blo 2237435 5668339 := bstep (se 1 (by rfl) ⟨4251254, by rfl⟩ : syracuseStep 5668339 = 8502509) B8502509
theorem B7557785 : Blo 2237435 7557785 := bstep (se 2 (by rfl) ⟨2834169, by rfl⟩ : syracuseStep 7557785 = 5668339) B5668339
theorem B5038523 : Blo 2237435 5038523 := bstep (se 1 (by rfl) ⟨3778892, by rfl⟩ : syracuseStep 5038523 = 7557785) B7557785
theorem B3359015 : Blo 2237435 3359015 := bstep (se 1 (by rfl) ⟨2519261, by rfl⟩ : syracuseStep 3359015 = 5038523) B5038523
theorem B2239343 : Blo 2237435 2239343 := bstep (se 1 (by rfl) ⟨1679507, by rfl⟩ : syracuseStep 2239343 = 3359015) B3359015
theorem B3359021 : Blo 2237435 3359021 := bbase (se 3 (by rfl) ⟨629816, by rfl⟩ : syracuseStep 3359021 = 1259633) (by norm_num)
theorem B2239347 : Blo 2237435 2239347 := bstep (se 1 (by rfl) ⟨1679510, by rfl⟩ : syracuseStep 2239347 = 3359021) B3359021
theorem B5038541 : Blo 2237435 5038541 := bbase (se 3 (by rfl) ⟨944726, by rfl⟩ : syracuseStep 5038541 = 1889453) (by norm_num)
theorem B3359027 : Blo 2237435 3359027 := bstep (se 1 (by rfl) ⟨2519270, by rfl⟩ : syracuseStep 3359027 = 5038541) B5038541
theorem B2239351 : Blo 2237435 2239351 := bstep (se 1 (by rfl) ⟨1679513, by rfl⟩ : syracuseStep 2239351 = 3359027) B3359027
theorem B2834185 : Blo 2237435 2834185 := bbase (se 2 (by rfl) ⟨1062819, by rfl⟩ : syracuseStep 2834185 = 2125639) (by norm_num)
theorem B3778913 : Blo 2237435 3778913 := bstep (se 2 (by rfl) ⟨1417092, by rfl⟩ : syracuseStep 3778913 = 2834185) B2834185
theorem B2519275 : Blo 2237435 2519275 := bstep (se 1 (by rfl) ⟨1889456, by rfl⟩ : syracuseStep 2519275 = 3778913) B3778913
theorem B3359033 : Blo 2237435 3359033 := bstep (se 2 (by rfl) ⟨1259637, by rfl⟩ : syracuseStep 3359033 = 2519275) B2519275
theorem B2239355 : Blo 2237435 2239355 := bstep (se 1 (by rfl) ⟨1679516, by rfl⟩ : syracuseStep 2239355 = 3359033) B3359033
theorem B4601765 : Blo 2237435 4601765 := bbase (se 4 (by rfl) ⟨431415, by rfl⟩ : syracuseStep 4601765 = 862831) (by norm_num)
theorem B3067843 : Blo 2237435 3067843 := bstep (se 1 (by rfl) ⟨2300882, by rfl⟩ : syracuseStep 3067843 = 4601765) B4601765
theorem B4090457 : Blo 2237435 4090457 := bstep (se 2 (by rfl) ⟨1533921, by rfl⟩ : syracuseStep 4090457 = 3067843) B3067843
theorem B10907885 : Blo 2237435 10907885 := bstep (se 3 (by rfl) ⟨2045228, by rfl⟩ : syracuseStep 10907885 = 4090457) B4090457
theorem B29087693 : Blo 2237435 29087693 := bstep (se 3 (by rfl) ⟨5453942, by rfl⟩ : syracuseStep 29087693 = 10907885) B10907885
theorem B19391795 : Blo 2237435 19391795 := bstep (se 1 (by rfl) ⟨14543846, by rfl⟩ : syracuseStep 19391795 = 29087693) B29087693
theorem B12927863 : Blo 2237435 12927863 := bstep (se 1 (by rfl) ⟨9695897, by rfl⟩ : syracuseStep 12927863 = 19391795) B19391795
theorem B8618575 : Blo 2237435 8618575 := bstep (se 1 (by rfl) ⟨6463931, by rfl⟩ : syracuseStep 8618575 = 12927863) B12927863
theorem B11491433 : Blo 2237435 11491433 := bstep (se 2 (by rfl) ⟨4309287, by rfl⟩ : syracuseStep 11491433 = 8618575) B8618575
theorem B7660955 : Blo 2237435 7660955 := bstep (se 1 (by rfl) ⟨5745716, by rfl⟩ : syracuseStep 7660955 = 11491433) B11491433
theorem B5107303 : Blo 2237435 5107303 := bstep (se 1 (by rfl) ⟨3830477, by rfl⟩ : syracuseStep 5107303 = 7660955) B7660955
theorem B27238949 : Blo 2237435 27238949 := bstep (se 4 (by rfl) ⟨2553651, by rfl⟩ : syracuseStep 27238949 = 5107303) B5107303
theorem B18159299 : Blo 2237435 18159299 := bstep (se 1 (by rfl) ⟨13619474, by rfl⟩ : syracuseStep 18159299 = 27238949) B27238949
theorem B12106199 : Blo 2237435 12106199 := bstep (se 1 (by rfl) ⟨9079649, by rfl⟩ : syracuseStep 12106199 = 18159299) B18159299
theorem B32283197 : Blo 2237435 32283197 := bstep (se 3 (by rfl) ⟨6053099, by rfl⟩ : syracuseStep 32283197 = 12106199) B12106199
theorem B21522131 : Blo 2237435 21522131 := bstep (se 1 (by rfl) ⟨16141598, by rfl⟩ : syracuseStep 21522131 = 32283197) B32283197
theorem B14348087 : Blo 2237435 14348087 := bstep (se 1 (by rfl) ⟨10761065, by rfl⟩ : syracuseStep 14348087 = 21522131) B21522131
theorem B9565391 : Blo 2237435 9565391 := bstep (se 1 (by rfl) ⟨7174043, by rfl⟩ : syracuseStep 9565391 = 14348087) B14348087
theorem B25507709 : Blo 2237435 25507709 := bstep (se 3 (by rfl) ⟨4782695, by rfl⟩ : syracuseStep 25507709 = 9565391) B9565391
theorem B17005139 : Blo 2237435 17005139 := bstep (se 1 (by rfl) ⟨12753854, by rfl⟩ : syracuseStep 17005139 = 25507709) B25507709
theorem B11336759 : Blo 2237435 11336759 := bstep (se 1 (by rfl) ⟨8502569, by rfl⟩ : syracuseStep 11336759 = 17005139) B17005139
theorem B7557839 : Blo 2237435 7557839 := bstep (se 1 (by rfl) ⟨5668379, by rfl⟩ : syracuseStep 7557839 = 11336759) B11336759
theorem B5038559 : Blo 2237435 5038559 := bstep (se 1 (by rfl) ⟨3778919, by rfl⟩ : syracuseStep 5038559 = 7557839) B7557839
theorem B3359039 : Blo 2237435 3359039 := bstep (se 1 (by rfl) ⟨2519279, by rfl⟩ : syracuseStep 3359039 = 5038559) B5038559
theorem B2239359 : Blo 2237435 2239359 := bstep (se 1 (by rfl) ⟨1679519, by rfl⟩ : syracuseStep 2239359 = 3359039) B3359039
theorem B3359045 : Blo 2237435 3359045 := bbase (se 4 (by rfl) ⟨314910, by rfl⟩ : syracuseStep 3359045 = 629821) (by norm_num)
theorem B2239363 : Blo 2237435 2239363 := bstep (se 1 (by rfl) ⟨1679522, by rfl⟩ : syracuseStep 2239363 = 3359045) B3359045
theorem B3778933 : Blo 2237435 3778933 := bbase (se 5 (by rfl) ⟨177137, by rfl⟩ : syracuseStep 3778933 = 354275) (by norm_num)
theorem B5038577 : Blo 2237435 5038577 := bstep (se 2 (by rfl) ⟨1889466, by rfl⟩ : syracuseStep 5038577 = 3778933) B3778933
theorem B3359051 : Blo 2237435 3359051 := bstep (se 1 (by rfl) ⟨2519288, by rfl⟩ : syracuseStep 3359051 = 5038577) B5038577
theorem B2239367 : Blo 2237435 2239367 := bstep (se 1 (by rfl) ⟨1679525, by rfl⟩ : syracuseStep 2239367 = 3359051) B3359051
theorem B2519293 : Blo 2237435 2519293 := bbase (se 3 (by rfl) ⟨472367, by rfl⟩ : syracuseStep 2519293 = 944735) (by norm_num)
theorem B3359057 : Blo 2237435 3359057 := bstep (se 2 (by rfl) ⟨1259646, by rfl⟩ : syracuseStep 3359057 = 2519293) B2519293
theorem B2239371 : Blo 2237435 2239371 := bstep (se 1 (by rfl) ⟨1679528, by rfl⟩ : syracuseStep 2239371 = 3359057) B3359057
theorem B7557893 : Blo 2237435 7557893 := bbase (se 4 (by rfl) ⟨708552, by rfl⟩ : syracuseStep 7557893 = 1417105) (by norm_num)
theorem B5038595 : Blo 2237435 5038595 := bstep (se 1 (by rfl) ⟨3778946, by rfl⟩ : syracuseStep 5038595 = 7557893) B7557893
theorem B3359063 : Blo 2237435 3359063 := bstep (se 1 (by rfl) ⟨2519297, by rfl⟩ : syracuseStep 3359063 = 5038595) B5038595
theorem B2239375 : Blo 2237435 2239375 := bstep (se 1 (by rfl) ⟨1679531, by rfl⟩ : syracuseStep 2239375 = 3359063) B3359063
theorem B3359069 : Blo 2237435 3359069 := bbase (se 3 (by rfl) ⟨629825, by rfl⟩ : syracuseStep 3359069 = 1259651) (by norm_num)
theorem B2239379 : Blo 2237435 2239379 := bstep (se 1 (by rfl) ⟨1679534, by rfl⟩ : syracuseStep 2239379 = 3359069) B3359069
theorem B5038613 : Blo 2237435 5038613 := bbase (se 6 (by rfl) ⟨118092, by rfl⟩ : syracuseStep 5038613 = 236185) (by norm_num)
theorem B3359075 : Blo 2237435 3359075 := bstep (se 1 (by rfl) ⟨2519306, by rfl⟩ : syracuseStep 3359075 = 5038613) B5038613
theorem B2239383 : Blo 2237435 2239383 := bstep (se 1 (by rfl) ⟨1679537, by rfl⟩ : syracuseStep 2239383 = 3359075) B3359075
theorem B8502677 : Blo 2237435 8502677 := bbase (se 6 (by rfl) ⟨199281, by rfl⟩ : syracuseStep 8502677 = 398563) (by norm_num)
theorem B5668451 : Blo 2237435 5668451 := bstep (se 1 (by rfl) ⟨4251338, by rfl⟩ : syracuseStep 5668451 = 8502677) B8502677
theorem B3778967 : Blo 2237435 3778967 := bstep (se 1 (by rfl) ⟨2834225, by rfl⟩ : syracuseStep 3778967 = 5668451) B5668451
theorem B2519311 : Blo 2237435 2519311 := bstep (se 1 (by rfl) ⟨1889483, by rfl⟩ : syracuseStep 2519311 = 3778967) B3778967
theorem B3359081 : Blo 2237435 3359081 := bstep (se 2 (by rfl) ⟨1259655, by rfl⟩ : syracuseStep 3359081 = 2519311) B2519311
theorem B2239387 : Blo 2237435 2239387 := bstep (se 1 (by rfl) ⟨1679540, by rfl⟩ : syracuseStep 2239387 = 3359081) B3359081
theorem B12754037 : Blo 2237435 12754037 := bbase (se 5 (by rfl) ⟨597845, by rfl⟩ : syracuseStep 12754037 = 1195691) (by norm_num)
theorem B8502691 : Blo 2237435 8502691 := bstep (se 1 (by rfl) ⟨6377018, by rfl⟩ : syracuseStep 8502691 = 12754037) B12754037
theorem B11336921 : Blo 2237435 11336921 := bstep (se 2 (by rfl) ⟨4251345, by rfl⟩ : syracuseStep 11336921 = 8502691) B8502691
theorem B7557947 : Blo 2237435 7557947 := bstep (se 1 (by rfl) ⟨5668460, by rfl⟩ : syracuseStep 7557947 = 11336921) B11336921
theorem B5038631 : Blo 2237435 5038631 := bstep (se 1 (by rfl) ⟨3778973, by rfl⟩ : syracuseStep 5038631 = 7557947) B7557947
theorem B3359087 : Blo 2237435 3359087 := bstep (se 1 (by rfl) ⟨2519315, by rfl⟩ : syracuseStep 3359087 = 5038631) B5038631
theorem B2239391 : Blo 2237435 2239391 := bstep (se 1 (by rfl) ⟨1679543, by rfl⟩ : syracuseStep 2239391 = 3359087) B3359087
theorem B3359093 : Blo 2237435 3359093 := bbase (se 5 (by rfl) ⟨157457, by rfl⟩ : syracuseStep 3359093 = 314915) (by norm_num)
theorem B2239395 : Blo 2237435 2239395 := bstep (se 1 (by rfl) ⟨1679546, by rfl⟩ : syracuseStep 2239395 = 3359093) B3359093
theorem B12106421 : Blo 2237435 12106421 := bbase (se 5 (by rfl) ⟨567488, by rfl⟩ : syracuseStep 12106421 = 1134977) (by norm_num)
theorem B8070947 : Blo 2237435 8070947 := bstep (se 1 (by rfl) ⟨6053210, by rfl⟩ : syracuseStep 8070947 = 12106421) B12106421
theorem B5380631 : Blo 2237435 5380631 := bstep (se 1 (by rfl) ⟨4035473, by rfl⟩ : syracuseStep 5380631 = 8070947) B8070947
theorem B3587087 : Blo 2237435 3587087 := bstep (se 1 (by rfl) ⟨2690315, by rfl⟩ : syracuseStep 3587087 = 5380631) B5380631
theorem B2391391 : Blo 2237435 2391391 := bstep (se 1 (by rfl) ⟨1793543, by rfl⟩ : syracuseStep 2391391 = 3587087) B3587087
theorem B3188521 : Blo 2237435 3188521 := bstep (se 2 (by rfl) ⟨1195695, by rfl⟩ : syracuseStep 3188521 = 2391391) B2391391
theorem B4251361 : Blo 2237435 4251361 := bstep (se 2 (by rfl) ⟨1594260, by rfl⟩ : syracuseStep 4251361 = 3188521) B3188521
theorem B5668481 : Blo 2237435 5668481 := bstep (se 2 (by rfl) ⟨2125680, by rfl⟩ : syracuseStep 5668481 = 4251361) B4251361
theorem B3778987 : Blo 2237435 3778987 := bstep (se 1 (by rfl) ⟨2834240, by rfl⟩ : syracuseStep 3778987 = 5668481) B5668481
theorem B5038649 : Blo 2237435 5038649 := bstep (se 2 (by rfl) ⟨1889493, by rfl⟩ : syracuseStep 5038649 = 3778987) B3778987
theorem B3359099 : Blo 2237435 3359099 := bstep (se 1 (by rfl) ⟨2519324, by rfl⟩ : syracuseStep 3359099 = 5038649) B5038649
theorem B2239399 : Blo 2237435 2239399 := bstep (se 1 (by rfl) ⟨1679549, by rfl⟩ : syracuseStep 2239399 = 3359099) B3359099
theorem B2519329 : Blo 2237435 2519329 := bbase (se 2 (by rfl) ⟨944748, by rfl⟩ : syracuseStep 2519329 = 1889497) (by norm_num)
theorem B3359105 : Blo 2237435 3359105 := bstep (se 2 (by rfl) ⟨1259664, by rfl⟩ : syracuseStep 3359105 = 2519329) B2519329
theorem B2239403 : Blo 2237435 2239403 := bstep (se 1 (by rfl) ⟨1679552, by rfl⟩ : syracuseStep 2239403 = 3359105) B3359105
theorem B5668501 : Blo 2237435 5668501 := bbase (se 6 (by rfl) ⟨132855, by rfl⟩ : syracuseStep 5668501 = 265711) (by norm_num)
theorem B7558001 : Blo 2237435 7558001 := bstep (se 2 (by rfl) ⟨2834250, by rfl⟩ : syracuseStep 7558001 = 5668501) B5668501
theorem B5038667 : Blo 2237435 5038667 := bstep (se 1 (by rfl) ⟨3779000, by rfl⟩ : syracuseStep 5038667 = 7558001) B7558001
theorem B3359111 : Blo 2237435 3359111 := bstep (se 1 (by rfl) ⟨2519333, by rfl⟩ : syracuseStep 3359111 = 5038667) B5038667
theorem B2239407 : Blo 2237435 2239407 := bstep (se 1 (by rfl) ⟨1679555, by rfl⟩ : syracuseStep 2239407 = 3359111) B3359111
theorem B3359117 : Blo 2237435 3359117 := bbase (se 3 (by rfl) ⟨629834, by rfl⟩ : syracuseStep 3359117 = 1259669) (by norm_num)
theorem B2239411 : Blo 2237435 2239411 := bstep (se 1 (by rfl) ⟨1679558, by rfl⟩ : syracuseStep 2239411 = 3359117) B3359117
theorem B5038685 : Blo 2237435 5038685 := bbase (se 3 (by rfl) ⟨944753, by rfl⟩ : syracuseStep 5038685 = 1889507) (by norm_num)
theorem B3359123 : Blo 2237435 3359123 := bstep (se 1 (by rfl) ⟨2519342, by rfl⟩ : syracuseStep 3359123 = 5038685) B5038685
theorem B2239415 : Blo 2237435 2239415 := bstep (se 1 (by rfl) ⟨1679561, by rfl⟩ : syracuseStep 2239415 = 3359123) B3359123
theorem B3779021 : Blo 2237435 3779021 := bbase (se 3 (by rfl) ⟨708566, by rfl⟩ : syracuseStep 3779021 = 1417133) (by norm_num)
theorem B2519347 : Blo 2237435 2519347 := bstep (se 1 (by rfl) ⟨1889510, by rfl⟩ : syracuseStep 2519347 = 3779021) B3779021
theorem B3359129 : Blo 2237435 3359129 := bstep (se 2 (by rfl) ⟨1259673, by rfl⟩ : syracuseStep 3359129 = 2519347) B2519347
theorem B2239419 : Blo 2237435 2239419 := bstep (se 1 (by rfl) ⟨1679564, by rfl⟩ : syracuseStep 2239419 = 3359129) B3359129
theorem B2553725 : Blo 2237435 2553725 := bbase (se 3 (by rfl) ⟨478823, by rfl⟩ : syracuseStep 2553725 = 957647) (by norm_num)
theorem B6809933 : Blo 2237435 6809933 := bstep (se 3 (by rfl) ⟨1276862, by rfl⟩ : syracuseStep 6809933 = 2553725) B2553725
theorem B4539955 : Blo 2237435 4539955 := bstep (se 1 (by rfl) ⟨3404966, by rfl⟩ : syracuseStep 4539955 = 6809933) B6809933
theorem B6053273 : Blo 2237435 6053273 := bstep (se 2 (by rfl) ⟨2269977, by rfl⟩ : syracuseStep 6053273 = 4539955) B4539955
theorem B4035515 : Blo 2237435 4035515 := bstep (se 1 (by rfl) ⟨3026636, by rfl⟩ : syracuseStep 4035515 = 6053273) B6053273
theorem B10761373 : Blo 2237435 10761373 := bstep (se 3 (by rfl) ⟨2017757, by rfl⟩ : syracuseStep 10761373 = 4035515) B4035515
theorem B14348497 : Blo 2237435 14348497 := bstep (se 2 (by rfl) ⟨5380686, by rfl⟩ : syracuseStep 14348497 = 10761373) B10761373
theorem B19131329 : Blo 2237435 19131329 := bstep (se 2 (by rfl) ⟨7174248, by rfl⟩ : syracuseStep 19131329 = 14348497) B14348497
theorem B12754219 : Blo 2237435 12754219 := bstep (se 1 (by rfl) ⟨9565664, by rfl⟩ : syracuseStep 12754219 = 19131329) B19131329
theorem B17005625 : Blo 2237435 17005625 := bstep (se 2 (by rfl) ⟨6377109, by rfl⟩ : syracuseStep 17005625 = 12754219) B12754219
theorem B11337083 : Blo 2237435 11337083 := bstep (se 1 (by rfl) ⟨8502812, by rfl⟩ : syracuseStep 11337083 = 17005625) B17005625
theorem B7558055 : Blo 2237435 7558055 := bstep (se 1 (by rfl) ⟨5668541, by rfl⟩ : syracuseStep 7558055 = 11337083) B11337083
theorem B5038703 : Blo 2237435 5038703 := bstep (se 1 (by rfl) ⟨3779027, by rfl⟩ : syracuseStep 5038703 = 7558055) B7558055
theorem B3359135 : Blo 2237435 3359135 := bstep (se 1 (by rfl) ⟨2519351, by rfl⟩ : syracuseStep 3359135 = 5038703) B5038703
theorem B2239423 : Blo 2237435 2239423 := bstep (se 1 (by rfl) ⟨1679567, by rfl⟩ : syracuseStep 2239423 = 3359135) B3359135
theorem B3359141 : Blo 2237435 3359141 := bbase (se 4 (by rfl) ⟨314919, by rfl⟩ : syracuseStep 3359141 = 629839) (by norm_num)
theorem B2239427 : Blo 2237435 2239427 := bstep (se 1 (by rfl) ⟨1679570, by rfl⟩ : syracuseStep 2239427 = 3359141) B3359141
theorem B2834281 : Blo 2237435 2834281 := bbase (se 2 (by rfl) ⟨1062855, by rfl⟩ : syracuseStep 2834281 = 2125711) (by norm_num)
theorem B3779041 : Blo 2237435 3779041 := bstep (se 2 (by rfl) ⟨1417140, by rfl⟩ : syracuseStep 3779041 = 2834281) B2834281
theorem B5038721 : Blo 2237435 5038721 := bstep (se 2 (by rfl) ⟨1889520, by rfl⟩ : syracuseStep 5038721 = 3779041) B3779041
theorem B3359147 : Blo 2237435 3359147 := bstep (se 1 (by rfl) ⟨2519360, by rfl⟩ : syracuseStep 3359147 = 5038721) B5038721
theorem B2239431 : Blo 2237435 2239431 := bstep (se 1 (by rfl) ⟨1679573, by rfl⟩ : syracuseStep 2239431 = 3359147) B3359147
theorem B2519365 : Blo 2237435 2519365 := bbase (se 4 (by rfl) ⟨236190, by rfl⟩ : syracuseStep 2519365 = 472381) (by norm_num)
theorem B3359153 : Blo 2237435 3359153 := bstep (se 2 (by rfl) ⟨1259682, by rfl⟩ : syracuseStep 3359153 = 2519365) B2519365
theorem B2239435 : Blo 2237435 2239435 := bstep (se 1 (by rfl) ⟨1679576, by rfl⟩ : syracuseStep 2239435 = 3359153) B3359153
theorem C0 (j : ℕ) (h1 : 559358 ≤ j) (h2 : j ≤ 559858) : Blo 2237435 (4 * j + 3) := by
  interval_cases j
  · exact B2237435
  · exact B2237439
  · exact B2237443
  · exact B2237447
  · exact B2237451
  · exact B2237455
  · exact B2237459
  · exact B2237463
  · exact B2237467
  · exact B2237471
  · exact B2237475
  · exact B2237479
  · exact B2237483
  · exact B2237487
  · exact B2237491
  · exact B2237495
  · exact B2237499
  · exact B2237503
  · exact B2237507
  · exact B2237511
  · exact B2237515
  · exact B2237519
  · exact B2237523
  · exact B2237527
  · exact B2237531
  · exact B2237535
  · exact B2237539
  · exact B2237543
  · exact B2237547
  · exact B2237551
  · exact B2237555
  · exact B2237559
  · exact B2237563
  · exact B2237567
  · exact B2237571
  · exact B2237575
  · exact B2237579
  · exact B2237583
  · exact B2237587
  · exact B2237591
  · exact B2237595
  · exact B2237599
  · exact B2237603
  · exact B2237607
  · exact B2237611
  · exact B2237615
  · exact B2237619
  · exact B2237623
  · exact B2237627
  · exact B2237631
  · exact B2237635
  · exact B2237639
  · exact B2237643
  · exact B2237647
  · exact B2237651
  · exact B2237655
  · exact B2237659
  · exact B2237663
  · exact B2237667
  · exact B2237671
  · exact B2237675
  · exact B2237679
  · exact B2237683
  · exact B2237687
  · exact B2237691
  · exact B2237695
  · exact B2237699
  · exact B2237703
  · exact B2237707
  · exact B2237711
  · exact B2237715
  · exact B2237719
  · exact B2237723
  · exact B2237727
  · exact B2237731
  · exact B2237735
  · exact B2237739
  · exact B2237743
  · exact B2237747
  · exact B2237751
  · exact B2237755
  · exact B2237759
  · exact B2237763
  · exact B2237767
  · exact B2237771
  · exact B2237775
  · exact B2237779
  · exact B2237783
  · exact B2237787
  · exact B2237791
  · exact B2237795
  · exact B2237799
  · exact B2237803
  · exact B2237807
  · exact B2237811
  · exact B2237815
  · exact B2237819
  · exact B2237823
  · exact B2237827
  · exact B2237831
  · exact B2237835
  · exact B2237839
  · exact B2237843
  · exact B2237847
  · exact B2237851
  · exact B2237855
  · exact B2237859
  · exact B2237863
  · exact B2237867
  · exact B2237871
  · exact B2237875
  · exact B2237879
  · exact B2237883
  · exact B2237887
  · exact B2237891
  · exact B2237895
  · exact B2237899
  · exact B2237903
  · exact B2237907
  · exact B2237911
  · exact B2237915
  · exact B2237919
  · exact B2237923
  · exact B2237927
  · exact B2237931
  · exact B2237935
  · exact B2237939
  · exact B2237943
  · exact B2237947
  · exact B2237951
  · exact B2237955
  · exact B2237959
  · exact B2237963
  · exact B2237967
  · exact B2237971
  · exact B2237975
  · exact B2237979
  · exact B2237983
  · exact B2237987
  · exact B2237991
  · exact B2237995
  · exact B2237999
  · exact B2238003
  · exact B2238007
  · exact B2238011
  · exact B2238015
  · exact B2238019
  · exact B2238023
  · exact B2238027
  · exact B2238031
  · exact B2238035
  · exact B2238039
  · exact B2238043
  · exact B2238047
  · exact B2238051
  · exact B2238055
  · exact B2238059
  · exact B2238063
  · exact B2238067
  · exact B2238071
  · exact B2238075
  · exact B2238079
  · exact B2238083
  · exact B2238087
  · exact B2238091
  · exact B2238095
  · exact B2238099
  · exact B2238103
  · exact B2238107
  · exact B2238111
  · exact B2238115
  · exact B2238119
  · exact B2238123
  · exact B2238127
  · exact B2238131
  · exact B2238135
  · exact B2238139
  · exact B2238143
  · exact B2238147
  · exact B2238151
  · exact B2238155
  · exact B2238159
  · exact B2238163
  · exact B2238167
  · exact B2238171
  · exact B2238175
  · exact B2238179
  · exact B2238183
  · exact B2238187
  · exact B2238191
  · exact B2238195
  · exact B2238199
  · exact B2238203
  · exact B2238207
  · exact B2238211
  · exact B2238215
  · exact B2238219
  · exact B2238223
  · exact B2238227
  · exact B2238231
  · exact B2238235
  · exact B2238239
  · exact B2238243
  · exact B2238247
  · exact B2238251
  · exact B2238255
  · exact B2238259
  · exact B2238263
  · exact B2238267
  · exact B2238271
  · exact B2238275
  · exact B2238279
  · exact B2238283
  · exact B2238287
  · exact B2238291
  · exact B2238295
  · exact B2238299
  · exact B2238303
  · exact B2238307
  · exact B2238311
  · exact B2238315
  · exact B2238319
  · exact B2238323
  · exact B2238327
  · exact B2238331
  · exact B2238335
  · exact B2238339
  · exact B2238343
  · exact B2238347
  · exact B2238351
  · exact B2238355
  · exact B2238359
  · exact B2238363
  · exact B2238367
  · exact B2238371
  · exact B2238375
  · exact B2238379
  · exact B2238383
  · exact B2238387
  · exact B2238391
  · exact B2238395
  · exact B2238399
  · exact B2238403
  · exact B2238407
  · exact B2238411
  · exact B2238415
  · exact B2238419
  · exact B2238423
  · exact B2238427
  · exact B2238431
  · exact B2238435
  · exact B2238439
  · exact B2238443
  · exact B2238447
  · exact B2238451
  · exact B2238455
  · exact B2238459
  · exact B2238463
  · exact B2238467
  · exact B2238471
  · exact B2238475
  · exact B2238479
  · exact B2238483
  · exact B2238487
  · exact B2238491
  · exact B2238495
  · exact B2238499
  · exact B2238503
  · exact B2238507
  · exact B2238511
  · exact B2238515
  · exact B2238519
  · exact B2238523
  · exact B2238527
  · exact B2238531
  · exact B2238535
  · exact B2238539
  · exact B2238543
  · exact B2238547
  · exact B2238551
  · exact B2238555
  · exact B2238559
  · exact B2238563
  · exact B2238567
  · exact B2238571
  · exact B2238575
  · exact B2238579
  · exact B2238583
  · exact B2238587
  · exact B2238591
  · exact B2238595
  · exact B2238599
  · exact B2238603
  · exact B2238607
  · exact B2238611
  · exact B2238615
  · exact B2238619
  · exact B2238623
  · exact B2238627
  · exact B2238631
  · exact B2238635
  · exact B2238639
  · exact B2238643
  · exact B2238647
  · exact B2238651
  · exact B2238655
  · exact B2238659
  · exact B2238663
  · exact B2238667
  · exact B2238671
  · exact B2238675
  · exact B2238679
  · exact B2238683
  · exact B2238687
  · exact B2238691
  · exact B2238695
  · exact B2238699
  · exact B2238703
  · exact B2238707
  · exact B2238711
  · exact B2238715
  · exact B2238719
  · exact B2238723
  · exact B2238727
  · exact B2238731
  · exact B2238735
  · exact B2238739
  · exact B2238743
  · exact B2238747
  · exact B2238751
  · exact B2238755
  · exact B2238759
  · exact B2238763
  · exact B2238767
  · exact B2238771
  · exact B2238775
  · exact B2238779
  · exact B2238783
  · exact B2238787
  · exact B2238791
  · exact B2238795
  · exact B2238799
  · exact B2238803
  · exact B2238807
  · exact B2238811
  · exact B2238815
  · exact B2238819
  · exact B2238823
  · exact B2238827
  · exact B2238831
  · exact B2238835
  · exact B2238839
  · exact B2238843
  · exact B2238847
  · exact B2238851
  · exact B2238855
  · exact B2238859
  · exact B2238863
  · exact B2238867
  · exact B2238871
  · exact B2238875
  · exact B2238879
  · exact B2238883
  · exact B2238887
  · exact B2238891
  · exact B2238895
  · exact B2238899
  · exact B2238903
  · exact B2238907
  · exact B2238911
  · exact B2238915
  · exact B2238919
  · exact B2238923
  · exact B2238927
  · exact B2238931
  · exact B2238935
  · exact B2238939
  · exact B2238943
  · exact B2238947
  · exact B2238951
  · exact B2238955
  · exact B2238959
  · exact B2238963
  · exact B2238967
  · exact B2238971
  · exact B2238975
  · exact B2238979
  · exact B2238983
  · exact B2238987
  · exact B2238991
  · exact B2238995
  · exact B2238999
  · exact B2239003
  · exact B2239007
  · exact B2239011
  · exact B2239015
  · exact B2239019
  · exact B2239023
  · exact B2239027
  · exact B2239031
  · exact B2239035
  · exact B2239039
  · exact B2239043
  · exact B2239047
  · exact B2239051
  · exact B2239055
  · exact B2239059
  · exact B2239063
  · exact B2239067
  · exact B2239071
  · exact B2239075
  · exact B2239079
  · exact B2239083
  · exact B2239087
  · exact B2239091
  · exact B2239095
  · exact B2239099
  · exact B2239103
  · exact B2239107
  · exact B2239111
  · exact B2239115
  · exact B2239119
  · exact B2239123
  · exact B2239127
  · exact B2239131
  · exact B2239135
  · exact B2239139
  · exact B2239143
  · exact B2239147
  · exact B2239151
  · exact B2239155
  · exact B2239159
  · exact B2239163
  · exact B2239167
  · exact B2239171
  · exact B2239175
  · exact B2239179
  · exact B2239183
  · exact B2239187
  · exact B2239191
  · exact B2239195
  · exact B2239199
  · exact B2239203
  · exact B2239207
  · exact B2239211
  · exact B2239215
  · exact B2239219
  · exact B2239223
  · exact B2239227
  · exact B2239231
  · exact B2239235
  · exact B2239239
  · exact B2239243
  · exact B2239247
  · exact B2239251
  · exact B2239255
  · exact B2239259
  · exact B2239263
  · exact B2239267
  · exact B2239271
  · exact B2239275
  · exact B2239279
  · exact B2239283
  · exact B2239287
  · exact B2239291
  · exact B2239295
  · exact B2239299
  · exact B2239303
  · exact B2239307
  · exact B2239311
  · exact B2239315
  · exact B2239319
  · exact B2239323
  · exact B2239327
  · exact B2239331
  · exact B2239335
  · exact B2239339
  · exact B2239343
  · exact B2239347
  · exact B2239351
  · exact B2239355
  · exact B2239359
  · exact B2239363
  · exact B2239367
  · exact B2239371
  · exact B2239375
  · exact B2239379
  · exact B2239383
  · exact B2239387
  · exact B2239391
  · exact B2239395
  · exact B2239399
  · exact B2239403
  · exact B2239407
  · exact B2239411
  · exact B2239415
  · exact B2239419
  · exact B2239423
  · exact B2239427
  · exact B2239431
  · exact B2239435
theorem solution (m : ℕ) (hlo : 2237435 ≤ m) (hhi : m ≤ 2239435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 559358 ≤ j := by omega
    have hj2 : j ≤ 559858 := by omega
    have hb : Blo 2237435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
