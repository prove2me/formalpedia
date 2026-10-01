-- Prove2me | solution 1 for syracuse_descends_range_2227435_2229435
-- status  : ACCEPTED   (prove)
-- author  : @chstdu
-- created : 2026-09-23T17:18:46.237977+00:00
-- url     : https://prove2.me/submissions/4ceeaef8-a3b4-4b2a-963c-e6447f93bc5d

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

theorem B2505865 : Blo 2227435 2505865 := bbase (se 2 (by rfl) ⟨939699, by rfl⟩ : syracuseStep 2505865 = 1879399) (by norm_num)
theorem B3341153 : Blo 2227435 3341153 := bstep (se 2 (by rfl) ⟨1252932, by rfl⟩ : syracuseStep 3341153 = 2505865) B2505865
theorem B2227435 : Blo 2227435 2227435 := bstep (se 1 (by rfl) ⟨1670576, by rfl⟩ : syracuseStep 2227435 = 3341153) B3341153
theorem B5160197 : Blo 2227435 5160197 := bbase (se 4 (by rfl) ⟨483768, by rfl⟩ : syracuseStep 5160197 = 967537) (by norm_num)
theorem B13760525 : Blo 2227435 13760525 := bstep (se 3 (by rfl) ⟨2580098, by rfl⟩ : syracuseStep 13760525 = 5160197) B5160197
theorem B9173683 : Blo 2227435 9173683 := bstep (se 1 (by rfl) ⟨6880262, by rfl⟩ : syracuseStep 9173683 = 13760525) B13760525
theorem B12231577 : Blo 2227435 12231577 := bstep (se 2 (by rfl) ⟨4586841, by rfl⟩ : syracuseStep 12231577 = 9173683) B9173683
theorem B16308769 : Blo 2227435 16308769 := bstep (se 2 (by rfl) ⟨6115788, by rfl⟩ : syracuseStep 16308769 = 12231577) B12231577
theorem B21745025 : Blo 2227435 21745025 := bstep (se 2 (by rfl) ⟨8154384, by rfl⟩ : syracuseStep 21745025 = 16308769) B16308769
theorem B14496683 : Blo 2227435 14496683 := bstep (se 1 (by rfl) ⟨10872512, by rfl⟩ : syracuseStep 14496683 = 21745025) B21745025
theorem B38657821 : Blo 2227435 38657821 := bstep (se 3 (by rfl) ⟨7248341, by rfl⟩ : syracuseStep 38657821 = 14496683) B14496683
theorem B51543761 : Blo 2227435 51543761 := bstep (se 2 (by rfl) ⟨19328910, by rfl⟩ : syracuseStep 51543761 = 38657821) B38657821
theorem B137450029 : Blo 2227435 137450029 := bstep (se 3 (by rfl) ⟨25771880, by rfl⟩ : syracuseStep 137450029 = 51543761) B51543761
theorem B183266705 : Blo 2227435 183266705 := bstep (se 2 (by rfl) ⟨68725014, by rfl⟩ : syracuseStep 183266705 = 137450029) B137450029
theorem B122177803 : Blo 2227435 122177803 := bstep (se 1 (by rfl) ⟨91633352, by rfl⟩ : syracuseStep 122177803 = 183266705) B183266705
theorem B162903737 : Blo 2227435 162903737 := bstep (se 2 (by rfl) ⟨61088901, by rfl⟩ : syracuseStep 162903737 = 122177803) B122177803
theorem B108602491 : Blo 2227435 108602491 := bstep (se 1 (by rfl) ⟨81451868, by rfl⟩ : syracuseStep 108602491 = 162903737) B162903737
theorem B144803321 : Blo 2227435 144803321 := bstep (se 2 (by rfl) ⟨54301245, by rfl⟩ : syracuseStep 144803321 = 108602491) B108602491
theorem B96535547 : Blo 2227435 96535547 := bstep (se 1 (by rfl) ⟨72401660, by rfl⟩ : syracuseStep 96535547 = 144803321) B144803321
theorem B64357031 : Blo 2227435 64357031 := bstep (se 1 (by rfl) ⟨48267773, by rfl⟩ : syracuseStep 64357031 = 96535547) B96535547
theorem B42904687 : Blo 2227435 42904687 := bstep (se 1 (by rfl) ⟨32178515, by rfl⟩ : syracuseStep 42904687 = 64357031) B64357031
theorem B57206249 : Blo 2227435 57206249 := bstep (se 2 (by rfl) ⟨21452343, by rfl⟩ : syracuseStep 57206249 = 42904687) B42904687
theorem B38137499 : Blo 2227435 38137499 := bstep (se 1 (by rfl) ⟨28603124, by rfl⟩ : syracuseStep 38137499 = 57206249) B57206249
theorem B25424999 : Blo 2227435 25424999 := bstep (se 1 (by rfl) ⟨19068749, by rfl⟩ : syracuseStep 25424999 = 38137499) B38137499
theorem B16949999 : Blo 2227435 16949999 := bstep (se 1 (by rfl) ⟨12712499, by rfl⟩ : syracuseStep 16949999 = 25424999) B25424999
theorem B11299999 : Blo 2227435 11299999 := bstep (se 1 (by rfl) ⟨8474999, by rfl⟩ : syracuseStep 11299999 = 16949999) B16949999
theorem B15066665 : Blo 2227435 15066665 := bstep (se 2 (by rfl) ⟨5649999, by rfl⟩ : syracuseStep 15066665 = 11299999) B11299999
theorem B10044443 : Blo 2227435 10044443 := bstep (se 1 (by rfl) ⟨7533332, by rfl⟩ : syracuseStep 10044443 = 15066665) B15066665
theorem B26785181 : Blo 2227435 26785181 := bstep (se 3 (by rfl) ⟨5022221, by rfl⟩ : syracuseStep 26785181 = 10044443) B10044443
theorem B17856787 : Blo 2227435 17856787 := bstep (se 1 (by rfl) ⟨13392590, by rfl⟩ : syracuseStep 17856787 = 26785181) B26785181
theorem B23809049 : Blo 2227435 23809049 := bstep (se 2 (by rfl) ⟨8928393, by rfl⟩ : syracuseStep 23809049 = 17856787) B17856787
theorem B15872699 : Blo 2227435 15872699 := bstep (se 1 (by rfl) ⟨11904524, by rfl⟩ : syracuseStep 15872699 = 23809049) B23809049
theorem B42327197 : Blo 2227435 42327197 := bstep (se 3 (by rfl) ⟨7936349, by rfl⟩ : syracuseStep 42327197 = 15872699) B15872699
theorem B28218131 : Blo 2227435 28218131 := bstep (se 1 (by rfl) ⟨21163598, by rfl⟩ : syracuseStep 28218131 = 42327197) B42327197
theorem B18812087 : Blo 2227435 18812087 := bstep (se 1 (by rfl) ⟨14109065, by rfl⟩ : syracuseStep 18812087 = 28218131) B28218131
theorem B12541391 : Blo 2227435 12541391 := bstep (se 1 (by rfl) ⟨9406043, by rfl⟩ : syracuseStep 12541391 = 18812087) B18812087
theorem B8360927 : Blo 2227435 8360927 := bstep (se 1 (by rfl) ⟨6270695, by rfl⟩ : syracuseStep 8360927 = 12541391) B12541391
theorem B5573951 : Blo 2227435 5573951 := bstep (se 1 (by rfl) ⟨4180463, by rfl⟩ : syracuseStep 5573951 = 8360927) B8360927
theorem B3715967 : Blo 2227435 3715967 := bstep (se 1 (by rfl) ⟨2786975, by rfl⟩ : syracuseStep 3715967 = 5573951) B5573951
theorem B2477311 : Blo 2227435 2477311 := bstep (se 1 (by rfl) ⟨1857983, by rfl⟩ : syracuseStep 2477311 = 3715967) B3715967
theorem B13212325 : Blo 2227435 13212325 := bstep (se 4 (by rfl) ⟨1238655, by rfl⟩ : syracuseStep 13212325 = 2477311) B2477311
theorem B70465733 : Blo 2227435 70465733 := bstep (se 4 (by rfl) ⟨6606162, by rfl⟩ : syracuseStep 70465733 = 13212325) B13212325
theorem B46977155 : Blo 2227435 46977155 := bstep (se 1 (by rfl) ⟨35232866, by rfl⟩ : syracuseStep 46977155 = 70465733) B70465733
theorem B31318103 : Blo 2227435 31318103 := bstep (se 1 (by rfl) ⟨23488577, by rfl⟩ : syracuseStep 31318103 = 46977155) B46977155
theorem B20878735 : Blo 2227435 20878735 := bstep (se 1 (by rfl) ⟨15659051, by rfl⟩ : syracuseStep 20878735 = 31318103) B31318103
theorem B27838313 : Blo 2227435 27838313 := bstep (se 2 (by rfl) ⟨10439367, by rfl⟩ : syracuseStep 27838313 = 20878735) B20878735
theorem B18558875 : Blo 2227435 18558875 := bstep (se 1 (by rfl) ⟨13919156, by rfl⟩ : syracuseStep 18558875 = 27838313) B27838313
theorem B12372583 : Blo 2227435 12372583 := bstep (se 1 (by rfl) ⟨9279437, by rfl⟩ : syracuseStep 12372583 = 18558875) B18558875
theorem B16496777 : Blo 2227435 16496777 := bstep (se 2 (by rfl) ⟨6186291, by rfl⟩ : syracuseStep 16496777 = 12372583) B12372583
theorem B10997851 : Blo 2227435 10997851 := bstep (se 1 (by rfl) ⟨8248388, by rfl⟩ : syracuseStep 10997851 = 16496777) B16496777
theorem B14663801 : Blo 2227435 14663801 := bstep (se 2 (by rfl) ⟨5498925, by rfl⟩ : syracuseStep 14663801 = 10997851) B10997851
theorem B39103469 : Blo 2227435 39103469 := bstep (se 3 (by rfl) ⟨7331900, by rfl⟩ : syracuseStep 39103469 = 14663801) B14663801
theorem B26068979 : Blo 2227435 26068979 := bstep (se 1 (by rfl) ⟨19551734, by rfl⟩ : syracuseStep 26068979 = 39103469) B39103469
theorem B17379319 : Blo 2227435 17379319 := bstep (se 1 (by rfl) ⟨13034489, by rfl⟩ : syracuseStep 17379319 = 26068979) B26068979
theorem B23172425 : Blo 2227435 23172425 := bstep (se 2 (by rfl) ⟨8689659, by rfl⟩ : syracuseStep 23172425 = 17379319) B17379319
theorem B15448283 : Blo 2227435 15448283 := bstep (se 1 (by rfl) ⟨11586212, by rfl⟩ : syracuseStep 15448283 = 23172425) B23172425
theorem B10298855 : Blo 2227435 10298855 := bstep (se 1 (by rfl) ⟨7724141, by rfl⟩ : syracuseStep 10298855 = 15448283) B15448283
theorem B6865903 : Blo 2227435 6865903 := bstep (se 1 (by rfl) ⟨5149427, by rfl⟩ : syracuseStep 6865903 = 10298855) B10298855
theorem B36618149 : Blo 2227435 36618149 := bstep (se 4 (by rfl) ⟨3432951, by rfl⟩ : syracuseStep 36618149 = 6865903) B6865903
theorem B24412099 : Blo 2227435 24412099 := bstep (se 1 (by rfl) ⟨18309074, by rfl⟩ : syracuseStep 24412099 = 36618149) B36618149
theorem B32549465 : Blo 2227435 32549465 := bstep (se 2 (by rfl) ⟨12206049, by rfl⟩ : syracuseStep 32549465 = 24412099) B24412099
theorem B86798573 : Blo 2227435 86798573 := bstep (se 3 (by rfl) ⟨16274732, by rfl⟩ : syracuseStep 86798573 = 32549465) B32549465
theorem B57865715 : Blo 2227435 57865715 := bstep (se 1 (by rfl) ⟨43399286, by rfl⟩ : syracuseStep 57865715 = 86798573) B86798573
theorem B38577143 : Blo 2227435 38577143 := bstep (se 1 (by rfl) ⟨28932857, by rfl⟩ : syracuseStep 38577143 = 57865715) B57865715
theorem B25718095 : Blo 2227435 25718095 := bstep (se 1 (by rfl) ⟨19288571, by rfl⟩ : syracuseStep 25718095 = 38577143) B38577143
theorem B34290793 : Blo 2227435 34290793 := bstep (se 2 (by rfl) ⟨12859047, by rfl⟩ : syracuseStep 34290793 = 25718095) B25718095
theorem B45721057 : Blo 2227435 45721057 := bstep (se 2 (by rfl) ⟨17145396, by rfl⟩ : syracuseStep 45721057 = 34290793) B34290793
theorem B60961409 : Blo 2227435 60961409 := bstep (se 2 (by rfl) ⟨22860528, by rfl⟩ : syracuseStep 60961409 = 45721057) B45721057
theorem B40640939 : Blo 2227435 40640939 := bstep (se 1 (by rfl) ⟨30480704, by rfl⟩ : syracuseStep 40640939 = 60961409) B60961409
theorem B27093959 : Blo 2227435 27093959 := bstep (se 1 (by rfl) ⟨20320469, by rfl⟩ : syracuseStep 27093959 = 40640939) B40640939
theorem B18062639 : Blo 2227435 18062639 := bstep (se 1 (by rfl) ⟨13546979, by rfl⟩ : syracuseStep 18062639 = 27093959) B27093959
theorem B12041759 : Blo 2227435 12041759 := bstep (se 1 (by rfl) ⟨9031319, by rfl⟩ : syracuseStep 12041759 = 18062639) B18062639
theorem B8027839 : Blo 2227435 8027839 := bstep (se 1 (by rfl) ⟨6020879, by rfl⟩ : syracuseStep 8027839 = 12041759) B12041759
theorem B42815141 : Blo 2227435 42815141 := bstep (se 4 (by rfl) ⟨4013919, by rfl⟩ : syracuseStep 42815141 = 8027839) B8027839
theorem B28543427 : Blo 2227435 28543427 := bstep (se 1 (by rfl) ⟨21407570, by rfl⟩ : syracuseStep 28543427 = 42815141) B42815141
theorem B19028951 : Blo 2227435 19028951 := bstep (se 1 (by rfl) ⟨14271713, by rfl⟩ : syracuseStep 19028951 = 28543427) B28543427
theorem B12685967 : Blo 2227435 12685967 := bstep (se 1 (by rfl) ⟨9514475, by rfl⟩ : syracuseStep 12685967 = 19028951) B19028951
theorem B8457311 : Blo 2227435 8457311 := bstep (se 1 (by rfl) ⟨6342983, by rfl⟩ : syracuseStep 8457311 = 12685967) B12685967
theorem B5638207 : Blo 2227435 5638207 := bstep (se 1 (by rfl) ⟨4228655, by rfl⟩ : syracuseStep 5638207 = 8457311) B8457311
theorem B7517609 : Blo 2227435 7517609 := bstep (se 2 (by rfl) ⟨2819103, by rfl⟩ : syracuseStep 7517609 = 5638207) B5638207
theorem B5011739 : Blo 2227435 5011739 := bstep (se 1 (by rfl) ⟨3758804, by rfl⟩ : syracuseStep 5011739 = 7517609) B7517609
theorem B3341159 : Blo 2227435 3341159 := bstep (se 1 (by rfl) ⟨2505869, by rfl⟩ : syracuseStep 3341159 = 5011739) B5011739
theorem B2227439 : Blo 2227435 2227439 := bstep (se 1 (by rfl) ⟨1670579, by rfl⟩ : syracuseStep 2227439 = 3341159) B3341159
theorem B3341165 : Blo 2227435 3341165 := bbase (se 3 (by rfl) ⟨626468, by rfl⟩ : syracuseStep 3341165 = 1252937) (by norm_num)
theorem B2227443 : Blo 2227435 2227443 := bstep (se 1 (by rfl) ⟨1670582, by rfl⟩ : syracuseStep 2227443 = 3341165) B3341165
theorem B5011757 : Blo 2227435 5011757 := bbase (se 3 (by rfl) ⟨939704, by rfl⟩ : syracuseStep 5011757 = 1879409) (by norm_num)
theorem B3341171 : Blo 2227435 3341171 := bstep (se 1 (by rfl) ⟨2505878, by rfl⟩ : syracuseStep 3341171 = 5011757) B5011757
theorem B2227447 : Blo 2227435 2227447 := bstep (se 1 (by rfl) ⟨1670585, by rfl⟩ : syracuseStep 2227447 = 3341171) B3341171
theorem B3386765 : Blo 2227435 3386765 := bbase (se 3 (by rfl) ⟨635018, by rfl⟩ : syracuseStep 3386765 = 1270037) (by norm_num)
theorem B2257843 : Blo 2227435 2257843 := bstep (se 1 (by rfl) ⟨1693382, by rfl⟩ : syracuseStep 2257843 = 3386765) B3386765
theorem B3010457 : Blo 2227435 3010457 := bstep (se 2 (by rfl) ⟨1128921, by rfl⟩ : syracuseStep 3010457 = 2257843) B2257843
theorem B8027885 : Blo 2227435 8027885 := bstep (se 3 (by rfl) ⟨1505228, by rfl⟩ : syracuseStep 8027885 = 3010457) B3010457
theorem B5351923 : Blo 2227435 5351923 := bstep (se 1 (by rfl) ⟨4013942, by rfl⟩ : syracuseStep 5351923 = 8027885) B8027885
theorem B7135897 : Blo 2227435 7135897 := bstep (se 2 (by rfl) ⟨2675961, by rfl⟩ : syracuseStep 7135897 = 5351923) B5351923
theorem B9514529 : Blo 2227435 9514529 := bstep (se 2 (by rfl) ⟨3567948, by rfl⟩ : syracuseStep 9514529 = 7135897) B7135897
theorem B6343019 : Blo 2227435 6343019 := bstep (se 1 (by rfl) ⟨4757264, by rfl⟩ : syracuseStep 6343019 = 9514529) B9514529
theorem B4228679 : Blo 2227435 4228679 := bstep (se 1 (by rfl) ⟨3171509, by rfl⟩ : syracuseStep 4228679 = 6343019) B6343019
theorem B2819119 : Blo 2227435 2819119 := bstep (se 1 (by rfl) ⟨2114339, by rfl⟩ : syracuseStep 2819119 = 4228679) B4228679
theorem B3758825 : Blo 2227435 3758825 := bstep (se 2 (by rfl) ⟨1409559, by rfl⟩ : syracuseStep 3758825 = 2819119) B2819119
theorem B2505883 : Blo 2227435 2505883 := bstep (se 1 (by rfl) ⟨1879412, by rfl⟩ : syracuseStep 2505883 = 3758825) B3758825
theorem B3341177 : Blo 2227435 3341177 := bstep (se 2 (by rfl) ⟨1252941, by rfl⟩ : syracuseStep 3341177 = 2505883) B2505883
theorem B2227451 : Blo 2227435 2227451 := bstep (se 1 (by rfl) ⟨1670588, by rfl⟩ : syracuseStep 2227451 = 3341177) B3341177
theorem B10298933 : Blo 2227435 10298933 := bbase (se 5 (by rfl) ⟨482762, by rfl⟩ : syracuseStep 10298933 = 965525) (by norm_num)
theorem B6865955 : Blo 2227435 6865955 := bstep (se 1 (by rfl) ⟨5149466, by rfl⟩ : syracuseStep 6865955 = 10298933) B10298933
theorem B4577303 : Blo 2227435 4577303 := bstep (se 1 (by rfl) ⟨3432977, by rfl⟩ : syracuseStep 4577303 = 6865955) B6865955
theorem B3051535 : Blo 2227435 3051535 := bstep (se 1 (by rfl) ⟨2288651, by rfl⟩ : syracuseStep 3051535 = 4577303) B4577303
theorem B4068713 : Blo 2227435 4068713 := bstep (se 2 (by rfl) ⟨1525767, by rfl⟩ : syracuseStep 4068713 = 3051535) B3051535
theorem B2712475 : Blo 2227435 2712475 := bstep (se 1 (by rfl) ⟨2034356, by rfl⟩ : syracuseStep 2712475 = 4068713) B4068713
theorem B3616633 : Blo 2227435 3616633 := bstep (se 2 (by rfl) ⟨1356237, by rfl⟩ : syracuseStep 3616633 = 2712475) B2712475
theorem B19288709 : Blo 2227435 19288709 := bstep (se 4 (by rfl) ⟨1808316, by rfl⟩ : syracuseStep 19288709 = 3616633) B3616633
theorem B12859139 : Blo 2227435 12859139 := bstep (se 1 (by rfl) ⟨9644354, by rfl⟩ : syracuseStep 12859139 = 19288709) B19288709
theorem B8572759 : Blo 2227435 8572759 := bstep (se 1 (by rfl) ⟨6429569, by rfl⟩ : syracuseStep 8572759 = 12859139) B12859139
theorem B45721381 : Blo 2227435 45721381 := bstep (se 4 (by rfl) ⟨4286379, by rfl⟩ : syracuseStep 45721381 = 8572759) B8572759
theorem B60961841 : Blo 2227435 60961841 := bstep (se 2 (by rfl) ⟨22860690, by rfl⟩ : syracuseStep 60961841 = 45721381) B45721381
theorem B40641227 : Blo 2227435 40641227 := bstep (se 1 (by rfl) ⟨30480920, by rfl⟩ : syracuseStep 40641227 = 60961841) B60961841
theorem B27094151 : Blo 2227435 27094151 := bstep (se 1 (by rfl) ⟨20320613, by rfl⟩ : syracuseStep 27094151 = 40641227) B40641227
theorem B18062767 : Blo 2227435 18062767 := bstep (se 1 (by rfl) ⟨13547075, by rfl⟩ : syracuseStep 18062767 = 27094151) B27094151
theorem B24083689 : Blo 2227435 24083689 := bstep (se 2 (by rfl) ⟨9031383, by rfl⟩ : syracuseStep 24083689 = 18062767) B18062767
theorem B32111585 : Blo 2227435 32111585 := bstep (se 2 (by rfl) ⟨12041844, by rfl⟩ : syracuseStep 32111585 = 24083689) B24083689
theorem B21407723 : Blo 2227435 21407723 := bstep (se 1 (by rfl) ⟨16055792, by rfl⟩ : syracuseStep 21407723 = 32111585) B32111585
theorem B14271815 : Blo 2227435 14271815 := bstep (se 1 (by rfl) ⟨10703861, by rfl⟩ : syracuseStep 14271815 = 21407723) B21407723
theorem B38058173 : Blo 2227435 38058173 := bstep (se 3 (by rfl) ⟨7135907, by rfl⟩ : syracuseStep 38058173 = 14271815) B14271815
theorem B25372115 : Blo 2227435 25372115 := bstep (se 1 (by rfl) ⟨19029086, by rfl⟩ : syracuseStep 25372115 = 38058173) B38058173
theorem B16914743 : Blo 2227435 16914743 := bstep (se 1 (by rfl) ⟨12686057, by rfl⟩ : syracuseStep 16914743 = 25372115) B25372115
theorem B11276495 : Blo 2227435 11276495 := bstep (se 1 (by rfl) ⟨8457371, by rfl⟩ : syracuseStep 11276495 = 16914743) B16914743
theorem B7517663 : Blo 2227435 7517663 := bstep (se 1 (by rfl) ⟨5638247, by rfl⟩ : syracuseStep 7517663 = 11276495) B11276495
theorem B5011775 : Blo 2227435 5011775 := bstep (se 1 (by rfl) ⟨3758831, by rfl⟩ : syracuseStep 5011775 = 7517663) B7517663
theorem B3341183 : Blo 2227435 3341183 := bstep (se 1 (by rfl) ⟨2505887, by rfl⟩ : syracuseStep 3341183 = 5011775) B5011775
theorem B2227455 : Blo 2227435 2227455 := bstep (se 1 (by rfl) ⟨1670591, by rfl⟩ : syracuseStep 2227455 = 3341183) B3341183
theorem B3341189 : Blo 2227435 3341189 := bbase (se 4 (by rfl) ⟨313236, by rfl⟩ : syracuseStep 3341189 = 626473) (by norm_num)
theorem B2227459 : Blo 2227435 2227459 := bstep (se 1 (by rfl) ⟨1670594, by rfl⟩ : syracuseStep 2227459 = 3341189) B3341189
theorem B3758845 : Blo 2227435 3758845 := bbase (se 3 (by rfl) ⟨704783, by rfl⟩ : syracuseStep 3758845 = 1409567) (by norm_num)
theorem B5011793 : Blo 2227435 5011793 := bstep (se 2 (by rfl) ⟨1879422, by rfl⟩ : syracuseStep 5011793 = 3758845) B3758845
theorem B3341195 : Blo 2227435 3341195 := bstep (se 1 (by rfl) ⟨2505896, by rfl⟩ : syracuseStep 3341195 = 5011793) B5011793
theorem B2227463 : Blo 2227435 2227463 := bstep (se 1 (by rfl) ⟨1670597, by rfl⟩ : syracuseStep 2227463 = 3341195) B3341195
theorem B2505901 : Blo 2227435 2505901 := bbase (se 3 (by rfl) ⟨469856, by rfl⟩ : syracuseStep 2505901 = 939713) (by norm_num)
theorem B3341201 : Blo 2227435 3341201 := bstep (se 2 (by rfl) ⟨1252950, by rfl⟩ : syracuseStep 3341201 = 2505901) B2505901
theorem B2227467 : Blo 2227435 2227467 := bstep (se 1 (by rfl) ⟨1670600, by rfl⟩ : syracuseStep 2227467 = 3341201) B3341201
theorem B7517717 : Blo 2227435 7517717 := bbase (se 6 (by rfl) ⟨176196, by rfl⟩ : syracuseStep 7517717 = 352393) (by norm_num)
theorem B5011811 : Blo 2227435 5011811 := bstep (se 1 (by rfl) ⟨3758858, by rfl⟩ : syracuseStep 5011811 = 7517717) B7517717
theorem B3341207 : Blo 2227435 3341207 := bstep (se 1 (by rfl) ⟨2505905, by rfl⟩ : syracuseStep 3341207 = 5011811) B5011811
theorem B2227471 : Blo 2227435 2227471 := bstep (se 1 (by rfl) ⟨1670603, by rfl⟩ : syracuseStep 2227471 = 3341207) B3341207
theorem B3341213 : Blo 2227435 3341213 := bbase (se 3 (by rfl) ⟨626477, by rfl⟩ : syracuseStep 3341213 = 1252955) (by norm_num)
theorem B2227475 : Blo 2227435 2227475 := bstep (se 1 (by rfl) ⟨1670606, by rfl⟩ : syracuseStep 2227475 = 3341213) B3341213
theorem B5011829 : Blo 2227435 5011829 := bbase (se 5 (by rfl) ⟨234929, by rfl⟩ : syracuseStep 5011829 = 469859) (by norm_num)
theorem B3341219 : Blo 2227435 3341219 := bstep (se 1 (by rfl) ⟨2505914, by rfl⟩ : syracuseStep 3341219 = 5011829) B5011829
theorem B2227479 : Blo 2227435 2227479 := bstep (se 1 (by rfl) ⟨1670609, by rfl⟩ : syracuseStep 2227479 = 3341219) B3341219
theorem B40641749 : Blo 2227435 40641749 := bbase (se 7 (by rfl) ⟨476270, by rfl⟩ : syracuseStep 40641749 = 952541) (by norm_num)
theorem B27094499 : Blo 2227435 27094499 := bstep (se 1 (by rfl) ⟨20320874, by rfl⟩ : syracuseStep 27094499 = 40641749) B40641749
theorem B18062999 : Blo 2227435 18062999 := bstep (se 1 (by rfl) ⟨13547249, by rfl⟩ : syracuseStep 18062999 = 27094499) B27094499
theorem B12041999 : Blo 2227435 12041999 := bstep (se 1 (by rfl) ⟨9031499, by rfl⟩ : syracuseStep 12041999 = 18062999) B18062999
theorem B8027999 : Blo 2227435 8027999 := bstep (se 1 (by rfl) ⟨6020999, by rfl⟩ : syracuseStep 8027999 = 12041999) B12041999
theorem B5351999 : Blo 2227435 5351999 := bstep (se 1 (by rfl) ⟨4013999, by rfl⟩ : syracuseStep 5351999 = 8027999) B8027999
theorem B14271997 : Blo 2227435 14271997 := bstep (se 3 (by rfl) ⟨2675999, by rfl⟩ : syracuseStep 14271997 = 5351999) B5351999
theorem B19029329 : Blo 2227435 19029329 := bstep (se 2 (by rfl) ⟨7135998, by rfl⟩ : syracuseStep 19029329 = 14271997) B14271997
theorem B12686219 : Blo 2227435 12686219 := bstep (se 1 (by rfl) ⟨9514664, by rfl⟩ : syracuseStep 12686219 = 19029329) B19029329
theorem B8457479 : Blo 2227435 8457479 := bstep (se 1 (by rfl) ⟨6343109, by rfl⟩ : syracuseStep 8457479 = 12686219) B12686219
theorem B5638319 : Blo 2227435 5638319 := bstep (se 1 (by rfl) ⟨4228739, by rfl⟩ : syracuseStep 5638319 = 8457479) B8457479
theorem B3758879 : Blo 2227435 3758879 := bstep (se 1 (by rfl) ⟨2819159, by rfl⟩ : syracuseStep 3758879 = 5638319) B5638319
theorem B2505919 : Blo 2227435 2505919 := bstep (se 1 (by rfl) ⟨1879439, by rfl⟩ : syracuseStep 2505919 = 3758879) B3758879
theorem B3341225 : Blo 2227435 3341225 := bstep (se 2 (by rfl) ⟨1252959, by rfl⟩ : syracuseStep 3341225 = 2505919) B2505919
theorem B2227483 : Blo 2227435 2227483 := bstep (se 1 (by rfl) ⟨1670612, by rfl⟩ : syracuseStep 2227483 = 3341225) B3341225
theorem B8457493 : Blo 2227435 8457493 := bbase (se 6 (by rfl) ⟨198222, by rfl⟩ : syracuseStep 8457493 = 396445) (by norm_num)
theorem B11276657 : Blo 2227435 11276657 := bstep (se 2 (by rfl) ⟨4228746, by rfl⟩ : syracuseStep 11276657 = 8457493) B8457493
theorem B7517771 : Blo 2227435 7517771 := bstep (se 1 (by rfl) ⟨5638328, by rfl⟩ : syracuseStep 7517771 = 11276657) B11276657
theorem B5011847 : Blo 2227435 5011847 := bstep (se 1 (by rfl) ⟨3758885, by rfl⟩ : syracuseStep 5011847 = 7517771) B7517771
theorem B3341231 : Blo 2227435 3341231 := bstep (se 1 (by rfl) ⟨2505923, by rfl⟩ : syracuseStep 3341231 = 5011847) B5011847
theorem B2227487 : Blo 2227435 2227487 := bstep (se 1 (by rfl) ⟨1670615, by rfl⟩ : syracuseStep 2227487 = 3341231) B3341231
theorem B3341237 : Blo 2227435 3341237 := bbase (se 5 (by rfl) ⟨156620, by rfl⟩ : syracuseStep 3341237 = 313241) (by norm_num)
theorem B2227491 : Blo 2227435 2227491 := bstep (se 1 (by rfl) ⟨1670618, by rfl⟩ : syracuseStep 2227491 = 3341237) B3341237
theorem B5638349 : Blo 2227435 5638349 := bbase (se 3 (by rfl) ⟨1057190, by rfl⟩ : syracuseStep 5638349 = 2114381) (by norm_num)
theorem B3758899 : Blo 2227435 3758899 := bstep (se 1 (by rfl) ⟨2819174, by rfl⟩ : syracuseStep 3758899 = 5638349) B5638349
theorem B5011865 : Blo 2227435 5011865 := bstep (se 2 (by rfl) ⟨1879449, by rfl⟩ : syracuseStep 5011865 = 3758899) B3758899
theorem B3341243 : Blo 2227435 3341243 := bstep (se 1 (by rfl) ⟨2505932, by rfl⟩ : syracuseStep 3341243 = 5011865) B5011865
theorem B2227495 : Blo 2227435 2227495 := bstep (se 1 (by rfl) ⟨1670621, by rfl⟩ : syracuseStep 2227495 = 3341243) B3341243
theorem B2505937 : Blo 2227435 2505937 := bbase (se 2 (by rfl) ⟨939726, by rfl⟩ : syracuseStep 2505937 = 1879453) (by norm_num)
theorem B3341249 : Blo 2227435 3341249 := bstep (se 2 (by rfl) ⟨1252968, by rfl⟩ : syracuseStep 3341249 = 2505937) B2505937
theorem B2227499 : Blo 2227435 2227499 := bstep (se 1 (by rfl) ⟨1670624, by rfl⟩ : syracuseStep 2227499 = 3341249) B3341249
theorem B5425069 : Blo 2227435 5425069 := bbase (se 3 (by rfl) ⟨1017200, by rfl⟩ : syracuseStep 5425069 = 2034401) (by norm_num)
theorem B7233425 : Blo 2227435 7233425 := bstep (se 2 (by rfl) ⟨2712534, by rfl⟩ : syracuseStep 7233425 = 5425069) B5425069
theorem B4822283 : Blo 2227435 4822283 := bstep (se 1 (by rfl) ⟨3616712, by rfl⟩ : syracuseStep 4822283 = 7233425) B7233425
theorem B3214855 : Blo 2227435 3214855 := bstep (se 1 (by rfl) ⟨2411141, by rfl⟩ : syracuseStep 3214855 = 4822283) B4822283
theorem B17145893 : Blo 2227435 17145893 := bstep (se 4 (by rfl) ⟨1607427, by rfl⟩ : syracuseStep 17145893 = 3214855) B3214855
theorem B11430595 : Blo 2227435 11430595 := bstep (se 1 (by rfl) ⟨8572946, by rfl⟩ : syracuseStep 11430595 = 17145893) B17145893
theorem B15240793 : Blo 2227435 15240793 := bstep (se 2 (by rfl) ⟨5715297, by rfl⟩ : syracuseStep 15240793 = 11430595) B11430595
theorem B20321057 : Blo 2227435 20321057 := bstep (se 2 (by rfl) ⟨7620396, by rfl⟩ : syracuseStep 20321057 = 15240793) B15240793
theorem B54189485 : Blo 2227435 54189485 := bstep (se 3 (by rfl) ⟨10160528, by rfl⟩ : syracuseStep 54189485 = 20321057) B20321057
theorem B36126323 : Blo 2227435 36126323 := bstep (se 1 (by rfl) ⟨27094742, by rfl⟩ : syracuseStep 36126323 = 54189485) B54189485
theorem B24084215 : Blo 2227435 24084215 := bstep (se 1 (by rfl) ⟨18063161, by rfl⟩ : syracuseStep 24084215 = 36126323) B36126323
theorem B16056143 : Blo 2227435 16056143 := bstep (se 1 (by rfl) ⟨12042107, by rfl⟩ : syracuseStep 16056143 = 24084215) B24084215
theorem B10704095 : Blo 2227435 10704095 := bstep (se 1 (by rfl) ⟨8028071, by rfl⟩ : syracuseStep 10704095 = 16056143) B16056143
theorem B7136063 : Blo 2227435 7136063 := bstep (se 1 (by rfl) ⟨5352047, by rfl⟩ : syracuseStep 7136063 = 10704095) B10704095
theorem B4757375 : Blo 2227435 4757375 := bstep (se 1 (by rfl) ⟨3568031, by rfl⟩ : syracuseStep 4757375 = 7136063) B7136063
theorem B3171583 : Blo 2227435 3171583 := bstep (se 1 (by rfl) ⟨2378687, by rfl⟩ : syracuseStep 3171583 = 4757375) B4757375
theorem B4228777 : Blo 2227435 4228777 := bstep (se 2 (by rfl) ⟨1585791, by rfl⟩ : syracuseStep 4228777 = 3171583) B3171583
theorem B5638369 : Blo 2227435 5638369 := bstep (se 2 (by rfl) ⟨2114388, by rfl⟩ : syracuseStep 5638369 = 4228777) B4228777
theorem B7517825 : Blo 2227435 7517825 := bstep (se 2 (by rfl) ⟨2819184, by rfl⟩ : syracuseStep 7517825 = 5638369) B5638369
theorem B5011883 : Blo 2227435 5011883 := bstep (se 1 (by rfl) ⟨3758912, by rfl⟩ : syracuseStep 5011883 = 7517825) B7517825
theorem B3341255 : Blo 2227435 3341255 := bstep (se 1 (by rfl) ⟨2505941, by rfl⟩ : syracuseStep 3341255 = 5011883) B5011883
theorem B2227503 : Blo 2227435 2227503 := bstep (se 1 (by rfl) ⟨1670627, by rfl⟩ : syracuseStep 2227503 = 3341255) B3341255
theorem B3341261 : Blo 2227435 3341261 := bbase (se 3 (by rfl) ⟨626486, by rfl⟩ : syracuseStep 3341261 = 1252973) (by norm_num)
theorem B2227507 : Blo 2227435 2227507 := bstep (se 1 (by rfl) ⟨1670630, by rfl⟩ : syracuseStep 2227507 = 3341261) B3341261
theorem B5011901 : Blo 2227435 5011901 := bbase (se 3 (by rfl) ⟨939731, by rfl⟩ : syracuseStep 5011901 = 1879463) (by norm_num)
theorem B3341267 : Blo 2227435 3341267 := bstep (se 1 (by rfl) ⟨2505950, by rfl⟩ : syracuseStep 3341267 = 5011901) B5011901
theorem B2227511 : Blo 2227435 2227511 := bstep (se 1 (by rfl) ⟨1670633, by rfl⟩ : syracuseStep 2227511 = 3341267) B3341267
theorem B3758933 : Blo 2227435 3758933 := bbase (se 9 (by rfl) ⟨11012, by rfl⟩ : syracuseStep 3758933 = 22025) (by norm_num)
theorem B2505955 : Blo 2227435 2505955 := bstep (se 1 (by rfl) ⟨1879466, by rfl⟩ : syracuseStep 2505955 = 3758933) B3758933
theorem B3341273 : Blo 2227435 3341273 := bstep (se 2 (by rfl) ⟨1252977, by rfl⟩ : syracuseStep 3341273 = 2505955) B2505955
theorem B2227515 : Blo 2227435 2227515 := bstep (se 1 (by rfl) ⟨1670636, by rfl⟩ : syracuseStep 2227515 = 3341273) B3341273
theorem B5352085 : Blo 2227435 5352085 := bbase (se 6 (by rfl) ⟨125439, by rfl⟩ : syracuseStep 5352085 = 250879) (by norm_num)
theorem B7136113 : Blo 2227435 7136113 := bstep (se 2 (by rfl) ⟨2676042, by rfl⟩ : syracuseStep 7136113 = 5352085) B5352085
theorem B9514817 : Blo 2227435 9514817 := bstep (se 2 (by rfl) ⟨3568056, by rfl⟩ : syracuseStep 9514817 = 7136113) B7136113
theorem B6343211 : Blo 2227435 6343211 := bstep (se 1 (by rfl) ⟨4757408, by rfl⟩ : syracuseStep 6343211 = 9514817) B9514817
theorem B16915229 : Blo 2227435 16915229 := bstep (se 3 (by rfl) ⟨3171605, by rfl⟩ : syracuseStep 16915229 = 6343211) B6343211
theorem B11276819 : Blo 2227435 11276819 := bstep (se 1 (by rfl) ⟨8457614, by rfl⟩ : syracuseStep 11276819 = 16915229) B16915229
theorem B7517879 : Blo 2227435 7517879 := bstep (se 1 (by rfl) ⟨5638409, by rfl⟩ : syracuseStep 7517879 = 11276819) B11276819
theorem B5011919 : Blo 2227435 5011919 := bstep (se 1 (by rfl) ⟨3758939, by rfl⟩ : syracuseStep 5011919 = 7517879) B7517879
theorem B3341279 : Blo 2227435 3341279 := bstep (se 1 (by rfl) ⟨2505959, by rfl⟩ : syracuseStep 3341279 = 5011919) B5011919
theorem B2227519 : Blo 2227435 2227519 := bstep (se 1 (by rfl) ⟨1670639, by rfl⟩ : syracuseStep 2227519 = 3341279) B3341279
theorem B3341285 : Blo 2227435 3341285 := bbase (se 4 (by rfl) ⟨313245, by rfl⟩ : syracuseStep 3341285 = 626491) (by norm_num)
theorem B2227523 : Blo 2227435 2227523 := bstep (se 1 (by rfl) ⟨1670642, by rfl⟩ : syracuseStep 2227523 = 3341285) B3341285
theorem B9514853 : Blo 2227435 9514853 := bbase (se 4 (by rfl) ⟨892017, by rfl⟩ : syracuseStep 9514853 = 1784035) (by norm_num)
theorem B6343235 : Blo 2227435 6343235 := bstep (se 1 (by rfl) ⟨4757426, by rfl⟩ : syracuseStep 6343235 = 9514853) B9514853
theorem B4228823 : Blo 2227435 4228823 := bstep (se 1 (by rfl) ⟨3171617, by rfl⟩ : syracuseStep 4228823 = 6343235) B6343235
theorem B2819215 : Blo 2227435 2819215 := bstep (se 1 (by rfl) ⟨2114411, by rfl⟩ : syracuseStep 2819215 = 4228823) B4228823
theorem B3758953 : Blo 2227435 3758953 := bstep (se 2 (by rfl) ⟨1409607, by rfl⟩ : syracuseStep 3758953 = 2819215) B2819215
theorem B5011937 : Blo 2227435 5011937 := bstep (se 2 (by rfl) ⟨1879476, by rfl⟩ : syracuseStep 5011937 = 3758953) B3758953
theorem B3341291 : Blo 2227435 3341291 := bstep (se 1 (by rfl) ⟨2505968, by rfl⟩ : syracuseStep 3341291 = 5011937) B5011937
theorem B2227527 : Blo 2227435 2227527 := bstep (se 1 (by rfl) ⟨1670645, by rfl⟩ : syracuseStep 2227527 = 3341291) B3341291
theorem B2505973 : Blo 2227435 2505973 := bbase (se 5 (by rfl) ⟨117467, by rfl⟩ : syracuseStep 2505973 = 234935) (by norm_num)
theorem B3341297 : Blo 2227435 3341297 := bstep (se 2 (by rfl) ⟨1252986, by rfl⟩ : syracuseStep 3341297 = 2505973) B2505973
theorem B2227531 : Blo 2227435 2227531 := bstep (se 1 (by rfl) ⟨1670648, by rfl⟩ : syracuseStep 2227531 = 3341297) B3341297
theorem B2819225 : Blo 2227435 2819225 := bbase (se 2 (by rfl) ⟨1057209, by rfl⟩ : syracuseStep 2819225 = 2114419) (by norm_num)
theorem B7517933 : Blo 2227435 7517933 := bstep (se 3 (by rfl) ⟨1409612, by rfl⟩ : syracuseStep 7517933 = 2819225) B2819225
theorem B5011955 : Blo 2227435 5011955 := bstep (se 1 (by rfl) ⟨3758966, by rfl⟩ : syracuseStep 5011955 = 7517933) B7517933
theorem B3341303 : Blo 2227435 3341303 := bstep (se 1 (by rfl) ⟨2505977, by rfl⟩ : syracuseStep 3341303 = 5011955) B5011955
theorem B2227535 : Blo 2227435 2227535 := bstep (se 1 (by rfl) ⟨1670651, by rfl⟩ : syracuseStep 2227535 = 3341303) B3341303
theorem B3341309 : Blo 2227435 3341309 := bbase (se 3 (by rfl) ⟨626495, by rfl⟩ : syracuseStep 3341309 = 1252991) (by norm_num)
theorem B2227539 : Blo 2227435 2227539 := bstep (se 1 (by rfl) ⟨1670654, by rfl⟩ : syracuseStep 2227539 = 3341309) B3341309
theorem B5011973 : Blo 2227435 5011973 := bbase (se 4 (by rfl) ⟨469872, by rfl⟩ : syracuseStep 5011973 = 939745) (by norm_num)
theorem B3341315 : Blo 2227435 3341315 := bstep (se 1 (by rfl) ⟨2505986, by rfl⟩ : syracuseStep 3341315 = 5011973) B5011973
theorem B2227543 : Blo 2227435 2227543 := bstep (se 1 (by rfl) ⟨1670657, by rfl⟩ : syracuseStep 2227543 = 3341315) B3341315
theorem B4228861 : Blo 2227435 4228861 := bbase (se 3 (by rfl) ⟨792911, by rfl⟩ : syracuseStep 4228861 = 1585823) (by norm_num)
theorem B5638481 : Blo 2227435 5638481 := bstep (se 2 (by rfl) ⟨2114430, by rfl⟩ : syracuseStep 5638481 = 4228861) B4228861
theorem B3758987 : Blo 2227435 3758987 := bstep (se 1 (by rfl) ⟨2819240, by rfl⟩ : syracuseStep 3758987 = 5638481) B5638481
theorem B2505991 : Blo 2227435 2505991 := bstep (se 1 (by rfl) ⟨1879493, by rfl⟩ : syracuseStep 2505991 = 3758987) B3758987
theorem B3341321 : Blo 2227435 3341321 := bstep (se 2 (by rfl) ⟨1252995, by rfl⟩ : syracuseStep 3341321 = 2505991) B2505991
theorem B2227547 : Blo 2227435 2227547 := bstep (se 1 (by rfl) ⟨1670660, by rfl⟩ : syracuseStep 2227547 = 3341321) B3341321
theorem B11276981 : Blo 2227435 11276981 := bbase (se 5 (by rfl) ⟨528608, by rfl⟩ : syracuseStep 11276981 = 1057217) (by norm_num)
theorem B7517987 : Blo 2227435 7517987 := bstep (se 1 (by rfl) ⟨5638490, by rfl⟩ : syracuseStep 7517987 = 11276981) B11276981
theorem B5011991 : Blo 2227435 5011991 := bstep (se 1 (by rfl) ⟨3758993, by rfl⟩ : syracuseStep 5011991 = 7517987) B7517987
theorem B3341327 : Blo 2227435 3341327 := bstep (se 1 (by rfl) ⟨2505995, by rfl⟩ : syracuseStep 3341327 = 5011991) B5011991
theorem B2227551 : Blo 2227435 2227551 := bstep (se 1 (by rfl) ⟨1670663, by rfl⟩ : syracuseStep 2227551 = 3341327) B3341327
theorem B3341333 : Blo 2227435 3341333 := bbase (se 6 (by rfl) ⟨78312, by rfl⟩ : syracuseStep 3341333 = 156625) (by norm_num)
theorem B2227555 : Blo 2227435 2227555 := bstep (se 1 (by rfl) ⟨1670666, by rfl⟩ : syracuseStep 2227555 = 3341333) B3341333
theorem B21408725 : Blo 2227435 21408725 := bbase (se 7 (by rfl) ⟨250883, by rfl⟩ : syracuseStep 21408725 = 501767) (by norm_num)
theorem B14272483 : Blo 2227435 14272483 := bstep (se 1 (by rfl) ⟨10704362, by rfl⟩ : syracuseStep 14272483 = 21408725) B21408725
theorem B19029977 : Blo 2227435 19029977 := bstep (se 2 (by rfl) ⟨7136241, by rfl⟩ : syracuseStep 19029977 = 14272483) B14272483
theorem B12686651 : Blo 2227435 12686651 := bstep (se 1 (by rfl) ⟨9514988, by rfl⟩ : syracuseStep 12686651 = 19029977) B19029977
theorem B8457767 : Blo 2227435 8457767 := bstep (se 1 (by rfl) ⟨6343325, by rfl⟩ : syracuseStep 8457767 = 12686651) B12686651
theorem B5638511 : Blo 2227435 5638511 := bstep (se 1 (by rfl) ⟨4228883, by rfl⟩ : syracuseStep 5638511 = 8457767) B8457767
theorem B3759007 : Blo 2227435 3759007 := bstep (se 1 (by rfl) ⟨2819255, by rfl⟩ : syracuseStep 3759007 = 5638511) B5638511
theorem B5012009 : Blo 2227435 5012009 := bstep (se 2 (by rfl) ⟨1879503, by rfl⟩ : syracuseStep 5012009 = 3759007) B3759007
theorem B3341339 : Blo 2227435 3341339 := bstep (se 1 (by rfl) ⟨2506004, by rfl⟩ : syracuseStep 3341339 = 5012009) B5012009
theorem B2227559 : Blo 2227435 2227559 := bstep (se 1 (by rfl) ⟨1670669, by rfl⟩ : syracuseStep 2227559 = 3341339) B3341339
theorem B2506009 : Blo 2227435 2506009 := bbase (se 2 (by rfl) ⟨939753, by rfl⟩ : syracuseStep 2506009 = 1879507) (by norm_num)
theorem B3341345 : Blo 2227435 3341345 := bstep (se 2 (by rfl) ⟨1253004, by rfl⟩ : syracuseStep 3341345 = 2506009) B2506009
theorem B2227563 : Blo 2227435 2227563 := bstep (se 1 (by rfl) ⟨1670672, by rfl⟩ : syracuseStep 2227563 = 3341345) B3341345
theorem B8457797 : Blo 2227435 8457797 := bbase (se 4 (by rfl) ⟨792918, by rfl⟩ : syracuseStep 8457797 = 1585837) (by norm_num)
theorem B5638531 : Blo 2227435 5638531 := bstep (se 1 (by rfl) ⟨4228898, by rfl⟩ : syracuseStep 5638531 = 8457797) B8457797
theorem B7518041 : Blo 2227435 7518041 := bstep (se 2 (by rfl) ⟨2819265, by rfl⟩ : syracuseStep 7518041 = 5638531) B5638531
theorem B5012027 : Blo 2227435 5012027 := bstep (se 1 (by rfl) ⟨3759020, by rfl⟩ : syracuseStep 5012027 = 7518041) B7518041
theorem B3341351 : Blo 2227435 3341351 := bstep (se 1 (by rfl) ⟨2506013, by rfl⟩ : syracuseStep 3341351 = 5012027) B5012027
theorem B2227567 : Blo 2227435 2227567 := bstep (se 1 (by rfl) ⟨1670675, by rfl⟩ : syracuseStep 2227567 = 3341351) B3341351
theorem B3341357 : Blo 2227435 3341357 := bbase (se 3 (by rfl) ⟨626504, by rfl⟩ : syracuseStep 3341357 = 1253009) (by norm_num)
theorem B2227571 : Blo 2227435 2227571 := bstep (se 1 (by rfl) ⟨1670678, by rfl⟩ : syracuseStep 2227571 = 3341357) B3341357
theorem B5012045 : Blo 2227435 5012045 := bbase (se 3 (by rfl) ⟨939758, by rfl⟩ : syracuseStep 5012045 = 1879517) (by norm_num)
theorem B3341363 : Blo 2227435 3341363 := bstep (se 1 (by rfl) ⟨2506022, by rfl⟩ : syracuseStep 3341363 = 5012045) B5012045
theorem B2227575 : Blo 2227435 2227575 := bstep (se 1 (by rfl) ⟨1670681, by rfl⟩ : syracuseStep 2227575 = 3341363) B3341363
theorem B2819281 : Blo 2227435 2819281 := bbase (se 2 (by rfl) ⟨1057230, by rfl⟩ : syracuseStep 2819281 = 2114461) (by norm_num)
theorem B3759041 : Blo 2227435 3759041 := bstep (se 2 (by rfl) ⟨1409640, by rfl⟩ : syracuseStep 3759041 = 2819281) B2819281
theorem B2506027 : Blo 2227435 2506027 := bstep (se 1 (by rfl) ⟨1879520, by rfl⟩ : syracuseStep 2506027 = 3759041) B3759041
theorem B3341369 : Blo 2227435 3341369 := bstep (se 2 (by rfl) ⟨1253013, by rfl⟩ : syracuseStep 3341369 = 2506027) B2506027
theorem B2227579 : Blo 2227435 2227579 := bstep (se 1 (by rfl) ⟨1670684, by rfl⟩ : syracuseStep 2227579 = 3341369) B3341369
theorem B4640021 : Blo 2227435 4640021 := bbase (se 6 (by rfl) ⟨108750, by rfl⟩ : syracuseStep 4640021 = 217501) (by norm_num)
theorem B3093347 : Blo 2227435 3093347 := bstep (se 1 (by rfl) ⟨2320010, by rfl⟩ : syracuseStep 3093347 = 4640021) B4640021
theorem B8248925 : Blo 2227435 8248925 := bstep (se 3 (by rfl) ⟨1546673, by rfl⟩ : syracuseStep 8248925 = 3093347) B3093347
theorem B5499283 : Blo 2227435 5499283 := bstep (se 1 (by rfl) ⟨4124462, by rfl⟩ : syracuseStep 5499283 = 8248925) B8248925
theorem B7332377 : Blo 2227435 7332377 := bstep (se 2 (by rfl) ⟨2749641, by rfl⟩ : syracuseStep 7332377 = 5499283) B5499283
theorem B19553005 : Blo 2227435 19553005 := bstep (se 3 (by rfl) ⟨3666188, by rfl⟩ : syracuseStep 19553005 = 7332377) B7332377
theorem B26070673 : Blo 2227435 26070673 := bstep (se 2 (by rfl) ⟨9776502, by rfl⟩ : syracuseStep 26070673 = 19553005) B19553005
theorem B34760897 : Blo 2227435 34760897 := bstep (se 2 (by rfl) ⟨13035336, by rfl⟩ : syracuseStep 34760897 = 26070673) B26070673
theorem B23173931 : Blo 2227435 23173931 := bstep (se 1 (by rfl) ⟨17380448, by rfl⟩ : syracuseStep 23173931 = 34760897) B34760897
theorem B15449287 : Blo 2227435 15449287 := bstep (se 1 (by rfl) ⟨11586965, by rfl⟩ : syracuseStep 15449287 = 23173931) B23173931
theorem B20599049 : Blo 2227435 20599049 := bstep (se 2 (by rfl) ⟨7724643, by rfl⟩ : syracuseStep 20599049 = 15449287) B15449287
theorem B54930797 : Blo 2227435 54930797 := bstep (se 3 (by rfl) ⟨10299524, by rfl⟩ : syracuseStep 54930797 = 20599049) B20599049
theorem B36620531 : Blo 2227435 36620531 := bstep (se 1 (by rfl) ⟨27465398, by rfl⟩ : syracuseStep 36620531 = 54930797) B54930797
theorem B24413687 : Blo 2227435 24413687 := bstep (se 1 (by rfl) ⟨18310265, by rfl⟩ : syracuseStep 24413687 = 36620531) B36620531
theorem B16275791 : Blo 2227435 16275791 := bstep (se 1 (by rfl) ⟨12206843, by rfl⟩ : syracuseStep 16275791 = 24413687) B24413687
theorem B10850527 : Blo 2227435 10850527 := bstep (se 1 (by rfl) ⟨8137895, by rfl⟩ : syracuseStep 10850527 = 16275791) B16275791
theorem B14467369 : Blo 2227435 14467369 := bstep (se 2 (by rfl) ⟨5425263, by rfl⟩ : syracuseStep 14467369 = 10850527) B10850527
theorem B19289825 : Blo 2227435 19289825 := bstep (se 2 (by rfl) ⟨7233684, by rfl⟩ : syracuseStep 19289825 = 14467369) B14467369
theorem B12859883 : Blo 2227435 12859883 := bstep (se 1 (by rfl) ⟨9644912, by rfl⟩ : syracuseStep 12859883 = 19289825) B19289825
theorem B8573255 : Blo 2227435 8573255 := bstep (se 1 (by rfl) ⟨6429941, by rfl⟩ : syracuseStep 8573255 = 12859883) B12859883
theorem B5715503 : Blo 2227435 5715503 := bstep (se 1 (by rfl) ⟨4286627, by rfl⟩ : syracuseStep 5715503 = 8573255) B8573255
theorem B3810335 : Blo 2227435 3810335 := bstep (se 1 (by rfl) ⟨2857751, by rfl⟩ : syracuseStep 3810335 = 5715503) B5715503
theorem B10160893 : Blo 2227435 10160893 := bstep (se 3 (by rfl) ⟨1905167, by rfl⟩ : syracuseStep 10160893 = 3810335) B3810335
theorem B13547857 : Blo 2227435 13547857 := bstep (se 2 (by rfl) ⟨5080446, by rfl⟩ : syracuseStep 13547857 = 10160893) B10160893
theorem B18063809 : Blo 2227435 18063809 := bstep (se 2 (by rfl) ⟨6773928, by rfl⟩ : syracuseStep 18063809 = 13547857) B13547857
theorem B12042539 : Blo 2227435 12042539 := bstep (se 1 (by rfl) ⟨9031904, by rfl⟩ : syracuseStep 12042539 = 18063809) B18063809
theorem B8028359 : Blo 2227435 8028359 := bstep (se 1 (by rfl) ⟨6021269, by rfl⟩ : syracuseStep 8028359 = 12042539) B12042539
theorem B5352239 : Blo 2227435 5352239 := bstep (se 1 (by rfl) ⟨4014179, by rfl⟩ : syracuseStep 5352239 = 8028359) B8028359
theorem B3568159 : Blo 2227435 3568159 := bstep (se 1 (by rfl) ⟨2676119, by rfl⟩ : syracuseStep 3568159 = 5352239) B5352239
theorem B4757545 : Blo 2227435 4757545 := bstep (se 2 (by rfl) ⟨1784079, by rfl⟩ : syracuseStep 4757545 = 3568159) B3568159
theorem B25373573 : Blo 2227435 25373573 := bstep (se 4 (by rfl) ⟨2378772, by rfl⟩ : syracuseStep 25373573 = 4757545) B4757545
theorem B16915715 : Blo 2227435 16915715 := bstep (se 1 (by rfl) ⟨12686786, by rfl⟩ : syracuseStep 16915715 = 25373573) B25373573
theorem B11277143 : Blo 2227435 11277143 := bstep (se 1 (by rfl) ⟨8457857, by rfl⟩ : syracuseStep 11277143 = 16915715) B16915715
theorem B7518095 : Blo 2227435 7518095 := bstep (se 1 (by rfl) ⟨5638571, by rfl⟩ : syracuseStep 7518095 = 11277143) B11277143
theorem B5012063 : Blo 2227435 5012063 := bstep (se 1 (by rfl) ⟨3759047, by rfl⟩ : syracuseStep 5012063 = 7518095) B7518095
theorem B3341375 : Blo 2227435 3341375 := bstep (se 1 (by rfl) ⟨2506031, by rfl⟩ : syracuseStep 3341375 = 5012063) B5012063
theorem B2227583 : Blo 2227435 2227583 := bstep (se 1 (by rfl) ⟨1670687, by rfl⟩ : syracuseStep 2227583 = 3341375) B3341375
theorem B3341381 : Blo 2227435 3341381 := bbase (se 4 (by rfl) ⟨313254, by rfl⟩ : syracuseStep 3341381 = 626509) (by norm_num)
theorem B2227587 : Blo 2227435 2227587 := bstep (se 1 (by rfl) ⟨1670690, by rfl⟩ : syracuseStep 2227587 = 3341381) B3341381
theorem B3759061 : Blo 2227435 3759061 := bbase (se 7 (by rfl) ⟨44051, by rfl⟩ : syracuseStep 3759061 = 88103) (by norm_num)
theorem B5012081 : Blo 2227435 5012081 := bstep (se 2 (by rfl) ⟨1879530, by rfl⟩ : syracuseStep 5012081 = 3759061) B3759061
theorem B3341387 : Blo 2227435 3341387 := bstep (se 1 (by rfl) ⟨2506040, by rfl⟩ : syracuseStep 3341387 = 5012081) B5012081
theorem B2227591 : Blo 2227435 2227591 := bstep (se 1 (by rfl) ⟨1670693, by rfl⟩ : syracuseStep 2227591 = 3341387) B3341387
theorem B2506045 : Blo 2227435 2506045 := bbase (se 3 (by rfl) ⟨469883, by rfl⟩ : syracuseStep 2506045 = 939767) (by norm_num)
theorem B3341393 : Blo 2227435 3341393 := bstep (se 2 (by rfl) ⟨1253022, by rfl⟩ : syracuseStep 3341393 = 2506045) B2506045
theorem B2227595 : Blo 2227435 2227595 := bstep (se 1 (by rfl) ⟨1670696, by rfl⟩ : syracuseStep 2227595 = 3341393) B3341393
theorem B7518149 : Blo 2227435 7518149 := bbase (se 4 (by rfl) ⟨704826, by rfl⟩ : syracuseStep 7518149 = 1409653) (by norm_num)
theorem B5012099 : Blo 2227435 5012099 := bstep (se 1 (by rfl) ⟨3759074, by rfl⟩ : syracuseStep 5012099 = 7518149) B7518149
theorem B3341399 : Blo 2227435 3341399 := bstep (se 1 (by rfl) ⟨2506049, by rfl⟩ : syracuseStep 3341399 = 5012099) B5012099
theorem B2227599 : Blo 2227435 2227599 := bstep (se 1 (by rfl) ⟨1670699, by rfl⟩ : syracuseStep 2227599 = 3341399) B3341399
theorem B3341405 : Blo 2227435 3341405 := bbase (se 3 (by rfl) ⟨626513, by rfl⟩ : syracuseStep 3341405 = 1253027) (by norm_num)
theorem B2227603 : Blo 2227435 2227603 := bstep (se 1 (by rfl) ⟨1670702, by rfl⟩ : syracuseStep 2227603 = 3341405) B3341405
theorem B5012117 : Blo 2227435 5012117 := bbase (se 6 (by rfl) ⟨117471, by rfl⟩ : syracuseStep 5012117 = 234943) (by norm_num)
theorem B3341411 : Blo 2227435 3341411 := bstep (se 1 (by rfl) ⟨2506058, by rfl⟩ : syracuseStep 3341411 = 5012117) B5012117
theorem B2227607 : Blo 2227435 2227607 := bstep (se 1 (by rfl) ⟨1670705, by rfl⟩ : syracuseStep 2227607 = 3341411) B3341411
theorem B3568205 : Blo 2227435 3568205 := bbase (se 3 (by rfl) ⟨669038, by rfl⟩ : syracuseStep 3568205 = 1338077) (by norm_num)
theorem B2378803 : Blo 2227435 2378803 := bstep (se 1 (by rfl) ⟨1784102, by rfl⟩ : syracuseStep 2378803 = 3568205) B3568205
theorem B3171737 : Blo 2227435 3171737 := bstep (se 2 (by rfl) ⟨1189401, by rfl⟩ : syracuseStep 3171737 = 2378803) B2378803
theorem B8457965 : Blo 2227435 8457965 := bstep (se 3 (by rfl) ⟨1585868, by rfl⟩ : syracuseStep 8457965 = 3171737) B3171737
theorem B5638643 : Blo 2227435 5638643 := bstep (se 1 (by rfl) ⟨4228982, by rfl⟩ : syracuseStep 5638643 = 8457965) B8457965
theorem B3759095 : Blo 2227435 3759095 := bstep (se 1 (by rfl) ⟨2819321, by rfl⟩ : syracuseStep 3759095 = 5638643) B5638643
theorem B2506063 : Blo 2227435 2506063 := bstep (se 1 (by rfl) ⟨1879547, by rfl⟩ : syracuseStep 2506063 = 3759095) B3759095
theorem B3341417 : Blo 2227435 3341417 := bstep (se 2 (by rfl) ⟨1253031, by rfl⟩ : syracuseStep 3341417 = 2506063) B2506063
theorem B2227611 : Blo 2227435 2227611 := bstep (se 1 (by rfl) ⟨1670708, by rfl⟩ : syracuseStep 2227611 = 3341417) B3341417
theorem B4822525 : Blo 2227435 4822525 := bbase (se 3 (by rfl) ⟨904223, by rfl⟩ : syracuseStep 4822525 = 1808447) (by norm_num)
theorem B6430033 : Blo 2227435 6430033 := bstep (se 2 (by rfl) ⟨2411262, by rfl⟩ : syracuseStep 6430033 = 4822525) B4822525
theorem B8573377 : Blo 2227435 8573377 := bstep (se 2 (by rfl) ⟨3215016, by rfl⟩ : syracuseStep 8573377 = 6430033) B6430033
theorem B11431169 : Blo 2227435 11431169 := bstep (se 2 (by rfl) ⟨4286688, by rfl⟩ : syracuseStep 11431169 = 8573377) B8573377
theorem B7620779 : Blo 2227435 7620779 := bstep (se 1 (by rfl) ⟨5715584, by rfl⟩ : syracuseStep 7620779 = 11431169) B11431169
theorem B5080519 : Blo 2227435 5080519 := bstep (se 1 (by rfl) ⟨3810389, by rfl⟩ : syracuseStep 5080519 = 7620779) B7620779
theorem B6774025 : Blo 2227435 6774025 := bstep (se 2 (by rfl) ⟨2540259, by rfl⟩ : syracuseStep 6774025 = 5080519) B5080519
theorem B9032033 : Blo 2227435 9032033 := bstep (se 2 (by rfl) ⟨3387012, by rfl⟩ : syracuseStep 9032033 = 6774025) B6774025
theorem B24085421 : Blo 2227435 24085421 := bstep (se 3 (by rfl) ⟨4516016, by rfl⟩ : syracuseStep 24085421 = 9032033) B9032033
theorem B16056947 : Blo 2227435 16056947 := bstep (se 1 (by rfl) ⟨12042710, by rfl⟩ : syracuseStep 16056947 = 24085421) B24085421
theorem B10704631 : Blo 2227435 10704631 := bstep (se 1 (by rfl) ⟨8028473, by rfl⟩ : syracuseStep 10704631 = 16056947) B16056947
theorem B14272841 : Blo 2227435 14272841 := bstep (se 2 (by rfl) ⟨5352315, by rfl⟩ : syracuseStep 14272841 = 10704631) B10704631
theorem B9515227 : Blo 2227435 9515227 := bstep (se 1 (by rfl) ⟨7136420, by rfl⟩ : syracuseStep 9515227 = 14272841) B14272841
theorem B12686969 : Blo 2227435 12686969 := bstep (se 2 (by rfl) ⟨4757613, by rfl⟩ : syracuseStep 12686969 = 9515227) B9515227
theorem B8457979 : Blo 2227435 8457979 := bstep (se 1 (by rfl) ⟨6343484, by rfl⟩ : syracuseStep 8457979 = 12686969) B12686969
theorem B11277305 : Blo 2227435 11277305 := bstep (se 2 (by rfl) ⟨4228989, by rfl⟩ : syracuseStep 11277305 = 8457979) B8457979
theorem B7518203 : Blo 2227435 7518203 := bstep (se 1 (by rfl) ⟨5638652, by rfl⟩ : syracuseStep 7518203 = 11277305) B11277305
theorem B5012135 : Blo 2227435 5012135 := bstep (se 1 (by rfl) ⟨3759101, by rfl⟩ : syracuseStep 5012135 = 7518203) B7518203
theorem B3341423 : Blo 2227435 3341423 := bstep (se 1 (by rfl) ⟨2506067, by rfl⟩ : syracuseStep 3341423 = 5012135) B5012135
theorem B2227615 : Blo 2227435 2227615 := bstep (se 1 (by rfl) ⟨1670711, by rfl⟩ : syracuseStep 2227615 = 3341423) B3341423
theorem B3341429 : Blo 2227435 3341429 := bbase (se 5 (by rfl) ⟨156629, by rfl⟩ : syracuseStep 3341429 = 313259) (by norm_num)
theorem B2227619 : Blo 2227435 2227619 := bstep (se 1 (by rfl) ⟨1670714, by rfl⟩ : syracuseStep 2227619 = 3341429) B3341429
theorem B4229005 : Blo 2227435 4229005 := bbase (se 3 (by rfl) ⟨792938, by rfl⟩ : syracuseStep 4229005 = 1585877) (by norm_num)
theorem B5638673 : Blo 2227435 5638673 := bstep (se 2 (by rfl) ⟨2114502, by rfl⟩ : syracuseStep 5638673 = 4229005) B4229005
theorem B3759115 : Blo 2227435 3759115 := bstep (se 1 (by rfl) ⟨2819336, by rfl⟩ : syracuseStep 3759115 = 5638673) B5638673
theorem B5012153 : Blo 2227435 5012153 := bstep (se 2 (by rfl) ⟨1879557, by rfl⟩ : syracuseStep 5012153 = 3759115) B3759115
theorem B3341435 : Blo 2227435 3341435 := bstep (se 1 (by rfl) ⟨2506076, by rfl⟩ : syracuseStep 3341435 = 5012153) B5012153
theorem B2227623 : Blo 2227435 2227623 := bstep (se 1 (by rfl) ⟨1670717, by rfl⟩ : syracuseStep 2227623 = 3341435) B3341435
theorem B2506081 : Blo 2227435 2506081 := bbase (se 2 (by rfl) ⟨939780, by rfl⟩ : syracuseStep 2506081 = 1879561) (by norm_num)
theorem B3341441 : Blo 2227435 3341441 := bstep (se 2 (by rfl) ⟨1253040, by rfl⟩ : syracuseStep 3341441 = 2506081) B2506081
theorem B2227627 : Blo 2227435 2227627 := bstep (se 1 (by rfl) ⟨1670720, by rfl⟩ : syracuseStep 2227627 = 3341441) B3341441
theorem B5638693 : Blo 2227435 5638693 := bbase (se 4 (by rfl) ⟨528627, by rfl⟩ : syracuseStep 5638693 = 1057255) (by norm_num)
theorem B7518257 : Blo 2227435 7518257 := bstep (se 2 (by rfl) ⟨2819346, by rfl⟩ : syracuseStep 7518257 = 5638693) B5638693
theorem B5012171 : Blo 2227435 5012171 := bstep (se 1 (by rfl) ⟨3759128, by rfl⟩ : syracuseStep 5012171 = 7518257) B7518257
theorem B3341447 : Blo 2227435 3341447 := bstep (se 1 (by rfl) ⟨2506085, by rfl⟩ : syracuseStep 3341447 = 5012171) B5012171
theorem B2227631 : Blo 2227435 2227631 := bstep (se 1 (by rfl) ⟨1670723, by rfl⟩ : syracuseStep 2227631 = 3341447) B3341447
theorem B3341453 : Blo 2227435 3341453 := bbase (se 3 (by rfl) ⟨626522, by rfl⟩ : syracuseStep 3341453 = 1253045) (by norm_num)
theorem B2227635 : Blo 2227435 2227635 := bstep (se 1 (by rfl) ⟨1670726, by rfl⟩ : syracuseStep 2227635 = 3341453) B3341453
theorem B5012189 : Blo 2227435 5012189 := bbase (se 3 (by rfl) ⟨939785, by rfl⟩ : syracuseStep 5012189 = 1879571) (by norm_num)
theorem B3341459 : Blo 2227435 3341459 := bstep (se 1 (by rfl) ⟨2506094, by rfl⟩ : syracuseStep 3341459 = 5012189) B5012189
theorem B2227639 : Blo 2227435 2227639 := bstep (se 1 (by rfl) ⟨1670729, by rfl⟩ : syracuseStep 2227639 = 3341459) B3341459
theorem B3759149 : Blo 2227435 3759149 := bbase (se 3 (by rfl) ⟨704840, by rfl⟩ : syracuseStep 3759149 = 1409681) (by norm_num)
theorem B2506099 : Blo 2227435 2506099 := bstep (se 1 (by rfl) ⟨1879574, by rfl⟩ : syracuseStep 2506099 = 3759149) B3759149
theorem B3341465 : Blo 2227435 3341465 := bstep (se 2 (by rfl) ⟨1253049, by rfl⟩ : syracuseStep 3341465 = 2506099) B2506099
theorem B2227643 : Blo 2227435 2227643 := bstep (se 1 (by rfl) ⟨1670732, by rfl⟩ : syracuseStep 2227643 = 3341465) B3341465
theorem B3387061 : Blo 2227435 3387061 := bbase (se 5 (by rfl) ⟨158768, by rfl⟩ : syracuseStep 3387061 = 317537) (by norm_num)
theorem B4516081 : Blo 2227435 4516081 := bstep (se 2 (by rfl) ⟨1693530, by rfl⟩ : syracuseStep 4516081 = 3387061) B3387061
theorem B24085765 : Blo 2227435 24085765 := bstep (se 4 (by rfl) ⟨2258040, by rfl⟩ : syracuseStep 24085765 = 4516081) B4516081
theorem B32114353 : Blo 2227435 32114353 := bstep (se 2 (by rfl) ⟨12042882, by rfl⟩ : syracuseStep 32114353 = 24085765) B24085765
theorem B42819137 : Blo 2227435 42819137 := bstep (se 2 (by rfl) ⟨16057176, by rfl⟩ : syracuseStep 42819137 = 32114353) B32114353
theorem B28546091 : Blo 2227435 28546091 := bstep (se 1 (by rfl) ⟨21409568, by rfl⟩ : syracuseStep 28546091 = 42819137) B42819137
theorem B19030727 : Blo 2227435 19030727 := bstep (se 1 (by rfl) ⟨14273045, by rfl⟩ : syracuseStep 19030727 = 28546091) B28546091
theorem B12687151 : Blo 2227435 12687151 := bstep (se 1 (by rfl) ⟨9515363, by rfl⟩ : syracuseStep 12687151 = 19030727) B19030727
theorem B16916201 : Blo 2227435 16916201 := bstep (se 2 (by rfl) ⟨6343575, by rfl⟩ : syracuseStep 16916201 = 12687151) B12687151
theorem B11277467 : Blo 2227435 11277467 := bstep (se 1 (by rfl) ⟨8458100, by rfl⟩ : syracuseStep 11277467 = 16916201) B16916201
theorem B7518311 : Blo 2227435 7518311 := bstep (se 1 (by rfl) ⟨5638733, by rfl⟩ : syracuseStep 7518311 = 11277467) B11277467
theorem B5012207 : Blo 2227435 5012207 := bstep (se 1 (by rfl) ⟨3759155, by rfl⟩ : syracuseStep 5012207 = 7518311) B7518311
theorem B3341471 : Blo 2227435 3341471 := bstep (se 1 (by rfl) ⟨2506103, by rfl⟩ : syracuseStep 3341471 = 5012207) B5012207
theorem B2227647 : Blo 2227435 2227647 := bstep (se 1 (by rfl) ⟨1670735, by rfl⟩ : syracuseStep 2227647 = 3341471) B3341471
theorem B3341477 : Blo 2227435 3341477 := bbase (se 4 (by rfl) ⟨313263, by rfl⟩ : syracuseStep 3341477 = 626527) (by norm_num)
theorem B2227651 : Blo 2227435 2227651 := bstep (se 1 (by rfl) ⟨1670738, by rfl⟩ : syracuseStep 2227651 = 3341477) B3341477
theorem B2819377 : Blo 2227435 2819377 := bbase (se 2 (by rfl) ⟨1057266, by rfl⟩ : syracuseStep 2819377 = 2114533) (by norm_num)
theorem B3759169 : Blo 2227435 3759169 := bstep (se 2 (by rfl) ⟨1409688, by rfl⟩ : syracuseStep 3759169 = 2819377) B2819377
theorem B5012225 : Blo 2227435 5012225 := bstep (se 2 (by rfl) ⟨1879584, by rfl⟩ : syracuseStep 5012225 = 3759169) B3759169
theorem B3341483 : Blo 2227435 3341483 := bstep (se 1 (by rfl) ⟨2506112, by rfl⟩ : syracuseStep 3341483 = 5012225) B5012225
theorem B2227655 : Blo 2227435 2227655 := bstep (se 1 (by rfl) ⟨1670741, by rfl⟩ : syracuseStep 2227655 = 3341483) B3341483
theorem B2506117 : Blo 2227435 2506117 := bbase (se 4 (by rfl) ⟨234948, by rfl⟩ : syracuseStep 2506117 = 469897) (by norm_num)
theorem B3341489 : Blo 2227435 3341489 := bstep (se 2 (by rfl) ⟨1253058, by rfl⟩ : syracuseStep 3341489 = 2506117) B2506117
theorem B2227659 : Blo 2227435 2227659 := bstep (se 1 (by rfl) ⟨1670744, by rfl⟩ : syracuseStep 2227659 = 3341489) B3341489
theorem B4757717 : Blo 2227435 4757717 := bbase (se 7 (by rfl) ⟨55754, by rfl⟩ : syracuseStep 4757717 = 111509) (by norm_num)
theorem B3171811 : Blo 2227435 3171811 := bstep (se 1 (by rfl) ⟨2378858, by rfl⟩ : syracuseStep 3171811 = 4757717) B4757717
theorem B4229081 : Blo 2227435 4229081 := bstep (se 2 (by rfl) ⟨1585905, by rfl⟩ : syracuseStep 4229081 = 3171811) B3171811
theorem B2819387 : Blo 2227435 2819387 := bstep (se 1 (by rfl) ⟨2114540, by rfl⟩ : syracuseStep 2819387 = 4229081) B4229081
theorem B7518365 : Blo 2227435 7518365 := bstep (se 3 (by rfl) ⟨1409693, by rfl⟩ : syracuseStep 7518365 = 2819387) B2819387
theorem B5012243 : Blo 2227435 5012243 := bstep (se 1 (by rfl) ⟨3759182, by rfl⟩ : syracuseStep 5012243 = 7518365) B7518365
theorem B3341495 : Blo 2227435 3341495 := bstep (se 1 (by rfl) ⟨2506121, by rfl⟩ : syracuseStep 3341495 = 5012243) B5012243
theorem B2227663 : Blo 2227435 2227663 := bstep (se 1 (by rfl) ⟨1670747, by rfl⟩ : syracuseStep 2227663 = 3341495) B3341495
theorem B3341501 : Blo 2227435 3341501 := bbase (se 3 (by rfl) ⟨626531, by rfl⟩ : syracuseStep 3341501 = 1253063) (by norm_num)
theorem B2227667 : Blo 2227435 2227667 := bstep (se 1 (by rfl) ⟨1670750, by rfl⟩ : syracuseStep 2227667 = 3341501) B3341501
theorem B5012261 : Blo 2227435 5012261 := bbase (se 4 (by rfl) ⟨469899, by rfl⟩ : syracuseStep 5012261 = 939799) (by norm_num)
theorem B3341507 : Blo 2227435 3341507 := bstep (se 1 (by rfl) ⟨2506130, by rfl⟩ : syracuseStep 3341507 = 5012261) B5012261
theorem B2227671 : Blo 2227435 2227671 := bstep (se 1 (by rfl) ⟨1670753, by rfl⟩ : syracuseStep 2227671 = 3341507) B3341507
theorem B5638805 : Blo 2227435 5638805 := bbase (se 6 (by rfl) ⟨132159, by rfl⟩ : syracuseStep 5638805 = 264319) (by norm_num)
theorem B3759203 : Blo 2227435 3759203 := bstep (se 1 (by rfl) ⟨2819402, by rfl⟩ : syracuseStep 3759203 = 5638805) B5638805
theorem B2506135 : Blo 2227435 2506135 := bstep (se 1 (by rfl) ⟨1879601, by rfl⟩ : syracuseStep 2506135 = 3759203) B3759203
theorem B3341513 : Blo 2227435 3341513 := bstep (se 2 (by rfl) ⟨1253067, by rfl⟩ : syracuseStep 3341513 = 2506135) B2506135
theorem B2227675 : Blo 2227435 2227675 := bstep (se 1 (by rfl) ⟨1670756, by rfl⟩ : syracuseStep 2227675 = 3341513) B3341513
theorem B3010765 : Blo 2227435 3010765 := bbase (se 3 (by rfl) ⟨564518, by rfl⟩ : syracuseStep 3010765 = 1129037) (by norm_num)
theorem B4014353 : Blo 2227435 4014353 := bstep (se 2 (by rfl) ⟨1505382, by rfl⟩ : syracuseStep 4014353 = 3010765) B3010765
theorem B2676235 : Blo 2227435 2676235 := bstep (se 1 (by rfl) ⟨2007176, by rfl⟩ : syracuseStep 2676235 = 4014353) B4014353
theorem B3568313 : Blo 2227435 3568313 := bstep (se 2 (by rfl) ⟨1338117, by rfl⟩ : syracuseStep 3568313 = 2676235) B2676235
theorem B9515501 : Blo 2227435 9515501 := bstep (se 3 (by rfl) ⟨1784156, by rfl⟩ : syracuseStep 9515501 = 3568313) B3568313
theorem B6343667 : Blo 2227435 6343667 := bstep (se 1 (by rfl) ⟨4757750, by rfl⟩ : syracuseStep 6343667 = 9515501) B9515501
theorem B4229111 : Blo 2227435 4229111 := bstep (se 1 (by rfl) ⟨3171833, by rfl⟩ : syracuseStep 4229111 = 6343667) B6343667
theorem B11277629 : Blo 2227435 11277629 := bstep (se 3 (by rfl) ⟨2114555, by rfl⟩ : syracuseStep 11277629 = 4229111) B4229111
theorem B7518419 : Blo 2227435 7518419 := bstep (se 1 (by rfl) ⟨5638814, by rfl⟩ : syracuseStep 7518419 = 11277629) B11277629
theorem B5012279 : Blo 2227435 5012279 := bstep (se 1 (by rfl) ⟨3759209, by rfl⟩ : syracuseStep 5012279 = 7518419) B7518419
theorem B3341519 : Blo 2227435 3341519 := bstep (se 1 (by rfl) ⟨2506139, by rfl⟩ : syracuseStep 3341519 = 5012279) B5012279
theorem B2227679 : Blo 2227435 2227679 := bstep (se 1 (by rfl) ⟨1670759, by rfl⟩ : syracuseStep 2227679 = 3341519) B3341519
theorem B3341525 : Blo 2227435 3341525 := bbase (se 7 (by rfl) ⟨39158, by rfl⟩ : syracuseStep 3341525 = 78317) (by norm_num)
theorem B2227683 : Blo 2227435 2227683 := bstep (se 1 (by rfl) ⟨1670762, by rfl⟩ : syracuseStep 2227683 = 3341525) B3341525
theorem B3171845 : Blo 2227435 3171845 := bbase (se 4 (by rfl) ⟨297360, by rfl⟩ : syracuseStep 3171845 = 594721) (by norm_num)
theorem B8458253 : Blo 2227435 8458253 := bstep (se 3 (by rfl) ⟨1585922, by rfl⟩ : syracuseStep 8458253 = 3171845) B3171845
theorem B5638835 : Blo 2227435 5638835 := bstep (se 1 (by rfl) ⟨4229126, by rfl⟩ : syracuseStep 5638835 = 8458253) B8458253
theorem B3759223 : Blo 2227435 3759223 := bstep (se 1 (by rfl) ⟨2819417, by rfl⟩ : syracuseStep 3759223 = 5638835) B5638835
theorem B5012297 : Blo 2227435 5012297 := bstep (se 2 (by rfl) ⟨1879611, by rfl⟩ : syracuseStep 5012297 = 3759223) B3759223
theorem B3341531 : Blo 2227435 3341531 := bstep (se 1 (by rfl) ⟨2506148, by rfl⟩ : syracuseStep 3341531 = 5012297) B5012297
theorem B2227687 : Blo 2227435 2227687 := bstep (se 1 (by rfl) ⟨1670765, by rfl⟩ : syracuseStep 2227687 = 3341531) B3341531
theorem B2506153 : Blo 2227435 2506153 := bbase (se 2 (by rfl) ⟨939807, by rfl⟩ : syracuseStep 2506153 = 1879615) (by norm_num)
theorem B3341537 : Blo 2227435 3341537 := bstep (se 2 (by rfl) ⟨1253076, by rfl⟩ : syracuseStep 3341537 = 2506153) B2506153
theorem B2227691 : Blo 2227435 2227691 := bstep (se 1 (by rfl) ⟨1670768, by rfl⟩ : syracuseStep 2227691 = 3341537) B3341537
theorem B7136677 : Blo 2227435 7136677 := bbase (se 4 (by rfl) ⟨669063, by rfl⟩ : syracuseStep 7136677 = 1338127) (by norm_num)
theorem B9515569 : Blo 2227435 9515569 := bstep (se 2 (by rfl) ⟨3568338, by rfl⟩ : syracuseStep 9515569 = 7136677) B7136677
theorem B12687425 : Blo 2227435 12687425 := bstep (se 2 (by rfl) ⟨4757784, by rfl⟩ : syracuseStep 12687425 = 9515569) B9515569
theorem B8458283 : Blo 2227435 8458283 := bstep (se 1 (by rfl) ⟨6343712, by rfl⟩ : syracuseStep 8458283 = 12687425) B12687425
theorem B5638855 : Blo 2227435 5638855 := bstep (se 1 (by rfl) ⟨4229141, by rfl⟩ : syracuseStep 5638855 = 8458283) B8458283
theorem B7518473 : Blo 2227435 7518473 := bstep (se 2 (by rfl) ⟨2819427, by rfl⟩ : syracuseStep 7518473 = 5638855) B5638855
theorem B5012315 : Blo 2227435 5012315 := bstep (se 1 (by rfl) ⟨3759236, by rfl⟩ : syracuseStep 5012315 = 7518473) B7518473
theorem B3341543 : Blo 2227435 3341543 := bstep (se 1 (by rfl) ⟨2506157, by rfl⟩ : syracuseStep 3341543 = 5012315) B5012315
theorem B2227695 : Blo 2227435 2227695 := bstep (se 1 (by rfl) ⟨1670771, by rfl⟩ : syracuseStep 2227695 = 3341543) B3341543
theorem B3341549 : Blo 2227435 3341549 := bbase (se 3 (by rfl) ⟨626540, by rfl⟩ : syracuseStep 3341549 = 1253081) (by norm_num)
theorem B2227699 : Blo 2227435 2227699 := bstep (se 1 (by rfl) ⟨1670774, by rfl⟩ : syracuseStep 2227699 = 3341549) B3341549
theorem B5012333 : Blo 2227435 5012333 := bbase (se 3 (by rfl) ⟨939812, by rfl⟩ : syracuseStep 5012333 = 1879625) (by norm_num)
theorem B3341555 : Blo 2227435 3341555 := bstep (se 1 (by rfl) ⟨2506166, by rfl⟩ : syracuseStep 3341555 = 5012333) B5012333
theorem B2227703 : Blo 2227435 2227703 := bstep (se 1 (by rfl) ⟨1670777, by rfl⟩ : syracuseStep 2227703 = 3341555) B3341555
theorem B4229165 : Blo 2227435 4229165 := bbase (se 3 (by rfl) ⟨792968, by rfl⟩ : syracuseStep 4229165 = 1585937) (by norm_num)
theorem B2819443 : Blo 2227435 2819443 := bstep (se 1 (by rfl) ⟨2114582, by rfl⟩ : syracuseStep 2819443 = 4229165) B4229165
theorem B3759257 : Blo 2227435 3759257 := bstep (se 2 (by rfl) ⟨1409721, by rfl⟩ : syracuseStep 3759257 = 2819443) B2819443
theorem B2506171 : Blo 2227435 2506171 := bstep (se 1 (by rfl) ⟨1879628, by rfl⟩ : syracuseStep 2506171 = 3759257) B3759257
theorem B3341561 : Blo 2227435 3341561 := bstep (se 2 (by rfl) ⟨1253085, by rfl⟩ : syracuseStep 3341561 = 2506171) B2506171
theorem B2227707 : Blo 2227435 2227707 := bstep (se 1 (by rfl) ⟨1670780, by rfl⟩ : syracuseStep 2227707 = 3341561) B3341561
theorem B36129685 : Blo 2227435 36129685 := bbase (se 6 (by rfl) ⟨846789, by rfl⟩ : syracuseStep 36129685 = 1693579) (by norm_num)
theorem B48172913 : Blo 2227435 48172913 := bstep (se 2 (by rfl) ⟨18064842, by rfl⟩ : syracuseStep 48172913 = 36129685) B36129685
theorem B32115275 : Blo 2227435 32115275 := bstep (se 1 (by rfl) ⟨24086456, by rfl⟩ : syracuseStep 32115275 = 48172913) B48172913
theorem B21410183 : Blo 2227435 21410183 := bstep (se 1 (by rfl) ⟨16057637, by rfl⟩ : syracuseStep 21410183 = 32115275) B32115275
theorem B57093821 : Blo 2227435 57093821 := bstep (se 3 (by rfl) ⟨10705091, by rfl⟩ : syracuseStep 57093821 = 21410183) B21410183
theorem B38062547 : Blo 2227435 38062547 := bstep (se 1 (by rfl) ⟨28546910, by rfl⟩ : syracuseStep 38062547 = 57093821) B57093821
theorem B25375031 : Blo 2227435 25375031 := bstep (se 1 (by rfl) ⟨19031273, by rfl⟩ : syracuseStep 25375031 = 38062547) B38062547
theorem B16916687 : Blo 2227435 16916687 := bstep (se 1 (by rfl) ⟨12687515, by rfl⟩ : syracuseStep 16916687 = 25375031) B25375031
theorem B11277791 : Blo 2227435 11277791 := bstep (se 1 (by rfl) ⟨8458343, by rfl⟩ : syracuseStep 11277791 = 16916687) B16916687
theorem B7518527 : Blo 2227435 7518527 := bstep (se 1 (by rfl) ⟨5638895, by rfl⟩ : syracuseStep 7518527 = 11277791) B11277791
theorem B5012351 : Blo 2227435 5012351 := bstep (se 1 (by rfl) ⟨3759263, by rfl⟩ : syracuseStep 5012351 = 7518527) B7518527
theorem B3341567 : Blo 2227435 3341567 := bstep (se 1 (by rfl) ⟨2506175, by rfl⟩ : syracuseStep 3341567 = 5012351) B5012351
theorem B2227711 : Blo 2227435 2227711 := bstep (se 1 (by rfl) ⟨1670783, by rfl⟩ : syracuseStep 2227711 = 3341567) B3341567
theorem B3341573 : Blo 2227435 3341573 := bbase (se 4 (by rfl) ⟨313272, by rfl⟩ : syracuseStep 3341573 = 626545) (by norm_num)
theorem B2227715 : Blo 2227435 2227715 := bstep (se 1 (by rfl) ⟨1670786, by rfl⟩ : syracuseStep 2227715 = 3341573) B3341573
theorem B3759277 : Blo 2227435 3759277 := bbase (se 3 (by rfl) ⟨704864, by rfl⟩ : syracuseStep 3759277 = 1409729) (by norm_num)
theorem B5012369 : Blo 2227435 5012369 := bstep (se 2 (by rfl) ⟨1879638, by rfl⟩ : syracuseStep 5012369 = 3759277) B3759277
theorem B3341579 : Blo 2227435 3341579 := bstep (se 1 (by rfl) ⟨2506184, by rfl⟩ : syracuseStep 3341579 = 5012369) B5012369
theorem B2227719 : Blo 2227435 2227719 := bstep (se 1 (by rfl) ⟨1670789, by rfl⟩ : syracuseStep 2227719 = 3341579) B3341579
theorem B2506189 : Blo 2227435 2506189 := bbase (se 3 (by rfl) ⟨469910, by rfl⟩ : syracuseStep 2506189 = 939821) (by norm_num)
theorem B3341585 : Blo 2227435 3341585 := bstep (se 2 (by rfl) ⟨1253094, by rfl⟩ : syracuseStep 3341585 = 2506189) B2506189
theorem B2227723 : Blo 2227435 2227723 := bstep (se 1 (by rfl) ⟨1670792, by rfl⟩ : syracuseStep 2227723 = 3341585) B3341585
theorem B7518581 : Blo 2227435 7518581 := bbase (se 5 (by rfl) ⟨352433, by rfl⟩ : syracuseStep 7518581 = 704867) (by norm_num)
theorem B5012387 : Blo 2227435 5012387 := bstep (se 1 (by rfl) ⟨3759290, by rfl⟩ : syracuseStep 5012387 = 7518581) B7518581
theorem B3341591 : Blo 2227435 3341591 := bstep (se 1 (by rfl) ⟨2506193, by rfl⟩ : syracuseStep 3341591 = 5012387) B5012387
theorem B2227727 : Blo 2227435 2227727 := bstep (se 1 (by rfl) ⟨1670795, by rfl⟩ : syracuseStep 2227727 = 3341591) B3341591
theorem B3341597 : Blo 2227435 3341597 := bbase (se 3 (by rfl) ⟨626549, by rfl⟩ : syracuseStep 3341597 = 1253099) (by norm_num)
theorem B2227731 : Blo 2227435 2227731 := bstep (se 1 (by rfl) ⟨1670798, by rfl⟩ : syracuseStep 2227731 = 3341597) B3341597
theorem B5012405 : Blo 2227435 5012405 := bbase (se 5 (by rfl) ⟨234956, by rfl⟩ : syracuseStep 5012405 = 469913) (by norm_num)
theorem B3341603 : Blo 2227435 3341603 := bstep (se 1 (by rfl) ⟨2506202, by rfl⟩ : syracuseStep 3341603 = 5012405) B5012405
theorem B2227735 : Blo 2227435 2227735 := bstep (se 1 (by rfl) ⟨1670801, by rfl⟩ : syracuseStep 2227735 = 3341603) B3341603
theorem B4014461 : Blo 2227435 4014461 := bbase (se 3 (by rfl) ⟨752711, by rfl⟩ : syracuseStep 4014461 = 1505423) (by norm_num)
theorem B10705229 : Blo 2227435 10705229 := bstep (se 3 (by rfl) ⟨2007230, by rfl⟩ : syracuseStep 10705229 = 4014461) B4014461
theorem B7136819 : Blo 2227435 7136819 := bstep (se 1 (by rfl) ⟨5352614, by rfl⟩ : syracuseStep 7136819 = 10705229) B10705229
theorem B4757879 : Blo 2227435 4757879 := bstep (se 1 (by rfl) ⟨3568409, by rfl⟩ : syracuseStep 4757879 = 7136819) B7136819
theorem B12687677 : Blo 2227435 12687677 := bstep (se 3 (by rfl) ⟨2378939, by rfl⟩ : syracuseStep 12687677 = 4757879) B4757879
theorem B8458451 : Blo 2227435 8458451 := bstep (se 1 (by rfl) ⟨6343838, by rfl⟩ : syracuseStep 8458451 = 12687677) B12687677
theorem B5638967 : Blo 2227435 5638967 := bstep (se 1 (by rfl) ⟨4229225, by rfl⟩ : syracuseStep 5638967 = 8458451) B8458451
theorem B3759311 : Blo 2227435 3759311 := bstep (se 1 (by rfl) ⟨2819483, by rfl⟩ : syracuseStep 3759311 = 5638967) B5638967
theorem B2506207 : Blo 2227435 2506207 := bstep (se 1 (by rfl) ⟨1879655, by rfl⟩ : syracuseStep 2506207 = 3759311) B3759311
theorem B3341609 : Blo 2227435 3341609 := bstep (se 2 (by rfl) ⟨1253103, by rfl⟩ : syracuseStep 3341609 = 2506207) B2506207
theorem B2227739 : Blo 2227435 2227739 := bstep (se 1 (by rfl) ⟨1670804, by rfl⟩ : syracuseStep 2227739 = 3341609) B3341609
theorem B9645605 : Blo 2227435 9645605 := bbase (se 4 (by rfl) ⟨904275, by rfl⟩ : syracuseStep 9645605 = 1808551) (by norm_num)
theorem B6430403 : Blo 2227435 6430403 := bstep (se 1 (by rfl) ⟨4822802, by rfl⟩ : syracuseStep 6430403 = 9645605) B9645605
theorem B4286935 : Blo 2227435 4286935 := bstep (se 1 (by rfl) ⟨3215201, by rfl⟩ : syracuseStep 4286935 = 6430403) B6430403
theorem B5715913 : Blo 2227435 5715913 := bstep (se 2 (by rfl) ⟨2143467, by rfl⟩ : syracuseStep 5715913 = 4286935) B4286935
theorem B7621217 : Blo 2227435 7621217 := bstep (se 2 (by rfl) ⟨2857956, by rfl⟩ : syracuseStep 7621217 = 5715913) B5715913
theorem B5080811 : Blo 2227435 5080811 := bstep (se 1 (by rfl) ⟨3810608, by rfl⟩ : syracuseStep 5080811 = 7621217) B7621217
theorem B54195317 : Blo 2227435 54195317 := bstep (se 5 (by rfl) ⟨2540405, by rfl⟩ : syracuseStep 54195317 = 5080811) B5080811
theorem B36130211 : Blo 2227435 36130211 := bstep (se 1 (by rfl) ⟨27097658, by rfl⟩ : syracuseStep 36130211 = 54195317) B54195317
theorem B24086807 : Blo 2227435 24086807 := bstep (se 1 (by rfl) ⟨18065105, by rfl⟩ : syracuseStep 24086807 = 36130211) B36130211
theorem B16057871 : Blo 2227435 16057871 := bstep (se 1 (by rfl) ⟨12043403, by rfl⟩ : syracuseStep 16057871 = 24086807) B24086807
theorem B10705247 : Blo 2227435 10705247 := bstep (se 1 (by rfl) ⟨8028935, by rfl⟩ : syracuseStep 10705247 = 16057871) B16057871
theorem B7136831 : Blo 2227435 7136831 := bstep (se 1 (by rfl) ⟨5352623, by rfl⟩ : syracuseStep 7136831 = 10705247) B10705247
theorem B4757887 : Blo 2227435 4757887 := bstep (se 1 (by rfl) ⟨3568415, by rfl⟩ : syracuseStep 4757887 = 7136831) B7136831
theorem B6343849 : Blo 2227435 6343849 := bstep (se 2 (by rfl) ⟨2378943, by rfl⟩ : syracuseStep 6343849 = 4757887) B4757887
theorem B8458465 : Blo 2227435 8458465 := bstep (se 2 (by rfl) ⟨3171924, by rfl⟩ : syracuseStep 8458465 = 6343849) B6343849
theorem B11277953 : Blo 2227435 11277953 := bstep (se 2 (by rfl) ⟨4229232, by rfl⟩ : syracuseStep 11277953 = 8458465) B8458465
theorem B7518635 : Blo 2227435 7518635 := bstep (se 1 (by rfl) ⟨5638976, by rfl⟩ : syracuseStep 7518635 = 11277953) B11277953
theorem B5012423 : Blo 2227435 5012423 := bstep (se 1 (by rfl) ⟨3759317, by rfl⟩ : syracuseStep 5012423 = 7518635) B7518635
theorem B3341615 : Blo 2227435 3341615 := bstep (se 1 (by rfl) ⟨2506211, by rfl⟩ : syracuseStep 3341615 = 5012423) B5012423
theorem B2227743 : Blo 2227435 2227743 := bstep (se 1 (by rfl) ⟨1670807, by rfl⟩ : syracuseStep 2227743 = 3341615) B3341615
theorem B3341621 : Blo 2227435 3341621 := bbase (se 5 (by rfl) ⟨156638, by rfl⟩ : syracuseStep 3341621 = 313277) (by norm_num)
theorem B2227747 : Blo 2227435 2227747 := bstep (se 1 (by rfl) ⟨1670810, by rfl⟩ : syracuseStep 2227747 = 3341621) B3341621
theorem B5638997 : Blo 2227435 5638997 := bbase (se 9 (by rfl) ⟨16520, by rfl⟩ : syracuseStep 5638997 = 33041) (by norm_num)
theorem B3759331 : Blo 2227435 3759331 := bstep (se 1 (by rfl) ⟨2819498, by rfl⟩ : syracuseStep 3759331 = 5638997) B5638997
theorem B5012441 : Blo 2227435 5012441 := bstep (se 2 (by rfl) ⟨1879665, by rfl⟩ : syracuseStep 5012441 = 3759331) B3759331
theorem B3341627 : Blo 2227435 3341627 := bstep (se 1 (by rfl) ⟨2506220, by rfl⟩ : syracuseStep 3341627 = 5012441) B5012441
theorem B2227751 : Blo 2227435 2227751 := bstep (se 1 (by rfl) ⟨1670813, by rfl⟩ : syracuseStep 2227751 = 3341627) B3341627
theorem B2506225 : Blo 2227435 2506225 := bbase (se 2 (by rfl) ⟨939834, by rfl⟩ : syracuseStep 2506225 = 1879669) (by norm_num)
theorem B3341633 : Blo 2227435 3341633 := bstep (se 2 (by rfl) ⟨1253112, by rfl⟩ : syracuseStep 3341633 = 2506225) B2506225
theorem B2227755 : Blo 2227435 2227755 := bstep (se 1 (by rfl) ⟨1670816, by rfl⟩ : syracuseStep 2227755 = 3341633) B3341633
theorem B2540425 : Blo 2227435 2540425 := bbase (se 2 (by rfl) ⟨952659, by rfl⟩ : syracuseStep 2540425 = 1905319) (by norm_num)
theorem B3387233 : Blo 2227435 3387233 := bstep (se 2 (by rfl) ⟨1270212, by rfl⟩ : syracuseStep 3387233 = 2540425) B2540425
theorem B2258155 : Blo 2227435 2258155 := bstep (se 1 (by rfl) ⟨1693616, by rfl⟩ : syracuseStep 2258155 = 3387233) B3387233
theorem B3010873 : Blo 2227435 3010873 := bstep (se 2 (by rfl) ⟨1129077, by rfl⟩ : syracuseStep 3010873 = 2258155) B2258155
theorem B4014497 : Blo 2227435 4014497 := bstep (se 2 (by rfl) ⟨1505436, by rfl⟩ : syracuseStep 4014497 = 3010873) B3010873
theorem B2676331 : Blo 2227435 2676331 := bstep (se 1 (by rfl) ⟨2007248, by rfl⟩ : syracuseStep 2676331 = 4014497) B4014497
theorem B14273765 : Blo 2227435 14273765 := bstep (se 4 (by rfl) ⟨1338165, by rfl⟩ : syracuseStep 14273765 = 2676331) B2676331
theorem B9515843 : Blo 2227435 9515843 := bstep (se 1 (by rfl) ⟨7136882, by rfl⟩ : syracuseStep 9515843 = 14273765) B14273765
theorem B6343895 : Blo 2227435 6343895 := bstep (se 1 (by rfl) ⟨4757921, by rfl⟩ : syracuseStep 6343895 = 9515843) B9515843
theorem B4229263 : Blo 2227435 4229263 := bstep (se 1 (by rfl) ⟨3171947, by rfl⟩ : syracuseStep 4229263 = 6343895) B6343895
theorem B5639017 : Blo 2227435 5639017 := bstep (se 2 (by rfl) ⟨2114631, by rfl⟩ : syracuseStep 5639017 = 4229263) B4229263
theorem B7518689 : Blo 2227435 7518689 := bstep (se 2 (by rfl) ⟨2819508, by rfl⟩ : syracuseStep 7518689 = 5639017) B5639017
theorem B5012459 : Blo 2227435 5012459 := bstep (se 1 (by rfl) ⟨3759344, by rfl⟩ : syracuseStep 5012459 = 7518689) B7518689
theorem B3341639 : Blo 2227435 3341639 := bstep (se 1 (by rfl) ⟨2506229, by rfl⟩ : syracuseStep 3341639 = 5012459) B5012459
theorem B2227759 : Blo 2227435 2227759 := bstep (se 1 (by rfl) ⟨1670819, by rfl⟩ : syracuseStep 2227759 = 3341639) B3341639
theorem B3341645 : Blo 2227435 3341645 := bbase (se 3 (by rfl) ⟨626558, by rfl⟩ : syracuseStep 3341645 = 1253117) (by norm_num)
theorem B2227763 : Blo 2227435 2227763 := bstep (se 1 (by rfl) ⟨1670822, by rfl⟩ : syracuseStep 2227763 = 3341645) B3341645
theorem B5012477 : Blo 2227435 5012477 := bbase (se 3 (by rfl) ⟨939839, by rfl⟩ : syracuseStep 5012477 = 1879679) (by norm_num)
theorem B3341651 : Blo 2227435 3341651 := bstep (se 1 (by rfl) ⟨2506238, by rfl⟩ : syracuseStep 3341651 = 5012477) B5012477
theorem B2227767 : Blo 2227435 2227767 := bstep (se 1 (by rfl) ⟨1670825, by rfl⟩ : syracuseStep 2227767 = 3341651) B3341651
theorem B3759365 : Blo 2227435 3759365 := bbase (se 4 (by rfl) ⟨352440, by rfl⟩ : syracuseStep 3759365 = 704881) (by norm_num)
theorem B2506243 : Blo 2227435 2506243 := bstep (se 1 (by rfl) ⟨1879682, by rfl⟩ : syracuseStep 2506243 = 3759365) B3759365
theorem B3341657 : Blo 2227435 3341657 := bstep (se 2 (by rfl) ⟨1253121, by rfl⟩ : syracuseStep 3341657 = 2506243) B2506243
theorem B2227771 : Blo 2227435 2227771 := bstep (se 1 (by rfl) ⟨1670828, by rfl⟩ : syracuseStep 2227771 = 3341657) B3341657
theorem B16917173 : Blo 2227435 16917173 := bbase (se 5 (by rfl) ⟨792992, by rfl⟩ : syracuseStep 16917173 = 1585985) (by norm_num)
theorem B11278115 : Blo 2227435 11278115 := bstep (se 1 (by rfl) ⟨8458586, by rfl⟩ : syracuseStep 11278115 = 16917173) B16917173
theorem B7518743 : Blo 2227435 7518743 := bstep (se 1 (by rfl) ⟨5639057, by rfl⟩ : syracuseStep 7518743 = 11278115) B11278115
theorem B5012495 : Blo 2227435 5012495 := bstep (se 1 (by rfl) ⟨3759371, by rfl⟩ : syracuseStep 5012495 = 7518743) B7518743
theorem B3341663 : Blo 2227435 3341663 := bstep (se 1 (by rfl) ⟨2506247, by rfl⟩ : syracuseStep 3341663 = 5012495) B5012495
theorem B2227775 : Blo 2227435 2227775 := bstep (se 1 (by rfl) ⟨1670831, by rfl⟩ : syracuseStep 2227775 = 3341663) B3341663
theorem B3341669 : Blo 2227435 3341669 := bbase (se 4 (by rfl) ⟨313281, by rfl⟩ : syracuseStep 3341669 = 626563) (by norm_num)
theorem B2227779 : Blo 2227435 2227779 := bstep (se 1 (by rfl) ⟨1670834, by rfl⟩ : syracuseStep 2227779 = 3341669) B3341669
theorem B4229309 : Blo 2227435 4229309 := bbase (se 3 (by rfl) ⟨792995, by rfl⟩ : syracuseStep 4229309 = 1585991) (by norm_num)
theorem B2819539 : Blo 2227435 2819539 := bstep (se 1 (by rfl) ⟨2114654, by rfl⟩ : syracuseStep 2819539 = 4229309) B4229309
theorem B3759385 : Blo 2227435 3759385 := bstep (se 2 (by rfl) ⟨1409769, by rfl⟩ : syracuseStep 3759385 = 2819539) B2819539
theorem B5012513 : Blo 2227435 5012513 := bstep (se 2 (by rfl) ⟨1879692, by rfl⟩ : syracuseStep 5012513 = 3759385) B3759385
theorem B3341675 : Blo 2227435 3341675 := bstep (se 1 (by rfl) ⟨2506256, by rfl⟩ : syracuseStep 3341675 = 5012513) B5012513
theorem B2227783 : Blo 2227435 2227783 := bstep (se 1 (by rfl) ⟨1670837, by rfl⟩ : syracuseStep 2227783 = 3341675) B3341675
theorem B2506261 : Blo 2227435 2506261 := bbase (se 6 (by rfl) ⟨58740, by rfl⟩ : syracuseStep 2506261 = 117481) (by norm_num)
theorem B3341681 : Blo 2227435 3341681 := bstep (se 2 (by rfl) ⟨1253130, by rfl⟩ : syracuseStep 3341681 = 2506261) B2506261
theorem B2227787 : Blo 2227435 2227787 := bstep (se 1 (by rfl) ⟨1670840, by rfl⟩ : syracuseStep 2227787 = 3341681) B3341681
theorem B2819549 : Blo 2227435 2819549 := bbase (se 3 (by rfl) ⟨528665, by rfl⟩ : syracuseStep 2819549 = 1057331) (by norm_num)
theorem B7518797 : Blo 2227435 7518797 := bstep (se 3 (by rfl) ⟨1409774, by rfl⟩ : syracuseStep 7518797 = 2819549) B2819549
theorem B5012531 : Blo 2227435 5012531 := bstep (se 1 (by rfl) ⟨3759398, by rfl⟩ : syracuseStep 5012531 = 7518797) B7518797
theorem B3341687 : Blo 2227435 3341687 := bstep (se 1 (by rfl) ⟨2506265, by rfl⟩ : syracuseStep 3341687 = 5012531) B5012531
theorem B2227791 : Blo 2227435 2227791 := bstep (se 1 (by rfl) ⟨1670843, by rfl⟩ : syracuseStep 2227791 = 3341687) B3341687
theorem B3341693 : Blo 2227435 3341693 := bbase (se 3 (by rfl) ⟨626567, by rfl⟩ : syracuseStep 3341693 = 1253135) (by norm_num)
theorem B2227795 : Blo 2227435 2227795 := bstep (se 1 (by rfl) ⟨1670846, by rfl⟩ : syracuseStep 2227795 = 3341693) B3341693
theorem B5012549 : Blo 2227435 5012549 := bbase (se 4 (by rfl) ⟨469926, by rfl⟩ : syracuseStep 5012549 = 939853) (by norm_num)
theorem B3341699 : Blo 2227435 3341699 := bstep (se 1 (by rfl) ⟨2506274, by rfl⟩ : syracuseStep 3341699 = 5012549) B5012549
theorem B2227799 : Blo 2227435 2227799 := bstep (se 1 (by rfl) ⟨1670849, by rfl⟩ : syracuseStep 2227799 = 3341699) B3341699
theorem B6344021 : Blo 2227435 6344021 := bbase (se 11 (by rfl) ⟨4646, by rfl⟩ : syracuseStep 6344021 = 9293) (by norm_num)
theorem B4229347 : Blo 2227435 4229347 := bstep (se 1 (by rfl) ⟨3172010, by rfl⟩ : syracuseStep 4229347 = 6344021) B6344021
theorem B5639129 : Blo 2227435 5639129 := bstep (se 2 (by rfl) ⟨2114673, by rfl⟩ : syracuseStep 5639129 = 4229347) B4229347
theorem B3759419 : Blo 2227435 3759419 := bstep (se 1 (by rfl) ⟨2819564, by rfl⟩ : syracuseStep 3759419 = 5639129) B5639129
theorem B2506279 : Blo 2227435 2506279 := bstep (se 1 (by rfl) ⟨1879709, by rfl⟩ : syracuseStep 2506279 = 3759419) B3759419
theorem B3341705 : Blo 2227435 3341705 := bstep (se 2 (by rfl) ⟨1253139, by rfl⟩ : syracuseStep 3341705 = 2506279) B2506279
theorem B2227803 : Blo 2227435 2227803 := bstep (se 1 (by rfl) ⟨1670852, by rfl⟩ : syracuseStep 2227803 = 3341705) B3341705
theorem B11278277 : Blo 2227435 11278277 := bbase (se 4 (by rfl) ⟨1057338, by rfl⟩ : syracuseStep 11278277 = 2114677) (by norm_num)
theorem B7518851 : Blo 2227435 7518851 := bstep (se 1 (by rfl) ⟨5639138, by rfl⟩ : syracuseStep 7518851 = 11278277) B11278277
theorem B5012567 : Blo 2227435 5012567 := bstep (se 1 (by rfl) ⟨3759425, by rfl⟩ : syracuseStep 5012567 = 7518851) B7518851
theorem B3341711 : Blo 2227435 3341711 := bstep (se 1 (by rfl) ⟨2506283, by rfl⟩ : syracuseStep 3341711 = 5012567) B5012567
theorem B2227807 : Blo 2227435 2227807 := bstep (se 1 (by rfl) ⟨1670855, by rfl⟩ : syracuseStep 2227807 = 3341711) B3341711
theorem B3341717 : Blo 2227435 3341717 := bbase (se 6 (by rfl) ⟨78321, by rfl⟩ : syracuseStep 3341717 = 156643) (by norm_num)
theorem B2227811 : Blo 2227435 2227811 := bstep (se 1 (by rfl) ⟨1670858, by rfl⟩ : syracuseStep 2227811 = 3341717) B3341717
theorem B5352797 : Blo 2227435 5352797 := bbase (se 3 (by rfl) ⟨1003649, by rfl⟩ : syracuseStep 5352797 = 2007299) (by norm_num)
theorem B3568531 : Blo 2227435 3568531 := bstep (se 1 (by rfl) ⟨2676398, by rfl⟩ : syracuseStep 3568531 = 5352797) B5352797
theorem B4758041 : Blo 2227435 4758041 := bstep (se 2 (by rfl) ⟨1784265, by rfl⟩ : syracuseStep 4758041 = 3568531) B3568531
theorem B12688109 : Blo 2227435 12688109 := bstep (se 3 (by rfl) ⟨2379020, by rfl⟩ : syracuseStep 12688109 = 4758041) B4758041
theorem B8458739 : Blo 2227435 8458739 := bstep (se 1 (by rfl) ⟨6344054, by rfl⟩ : syracuseStep 8458739 = 12688109) B12688109
theorem B5639159 : Blo 2227435 5639159 := bstep (se 1 (by rfl) ⟨4229369, by rfl⟩ : syracuseStep 5639159 = 8458739) B8458739
theorem B3759439 : Blo 2227435 3759439 := bstep (se 1 (by rfl) ⟨2819579, by rfl⟩ : syracuseStep 3759439 = 5639159) B5639159
theorem B5012585 : Blo 2227435 5012585 := bstep (se 2 (by rfl) ⟨1879719, by rfl⟩ : syracuseStep 5012585 = 3759439) B3759439
theorem B3341723 : Blo 2227435 3341723 := bstep (se 1 (by rfl) ⟨2506292, by rfl⟩ : syracuseStep 3341723 = 5012585) B5012585
theorem B2227815 : Blo 2227435 2227815 := bstep (se 1 (by rfl) ⟨1670861, by rfl⟩ : syracuseStep 2227815 = 3341723) B3341723
theorem B2506297 : Blo 2227435 2506297 := bbase (se 2 (by rfl) ⟨939861, by rfl⟩ : syracuseStep 2506297 = 1879723) (by norm_num)
theorem B3341729 : Blo 2227435 3341729 := bstep (se 2 (by rfl) ⟨1253148, by rfl⟩ : syracuseStep 3341729 = 2506297) B2506297
theorem B2227819 : Blo 2227435 2227819 := bstep (se 1 (by rfl) ⟨1670864, by rfl⟩ : syracuseStep 2227819 = 3341729) B3341729
theorem B2379029 : Blo 2227435 2379029 := bbase (se 6 (by rfl) ⟨55758, by rfl⟩ : syracuseStep 2379029 = 111517) (by norm_num)
theorem B6344077 : Blo 2227435 6344077 := bstep (se 3 (by rfl) ⟨1189514, by rfl⟩ : syracuseStep 6344077 = 2379029) B2379029
theorem B8458769 : Blo 2227435 8458769 := bstep (se 2 (by rfl) ⟨3172038, by rfl⟩ : syracuseStep 8458769 = 6344077) B6344077
theorem B5639179 : Blo 2227435 5639179 := bstep (se 1 (by rfl) ⟨4229384, by rfl⟩ : syracuseStep 5639179 = 8458769) B8458769
theorem B7518905 : Blo 2227435 7518905 := bstep (se 2 (by rfl) ⟨2819589, by rfl⟩ : syracuseStep 7518905 = 5639179) B5639179
theorem B5012603 : Blo 2227435 5012603 := bstep (se 1 (by rfl) ⟨3759452, by rfl⟩ : syracuseStep 5012603 = 7518905) B7518905
theorem B3341735 : Blo 2227435 3341735 := bstep (se 1 (by rfl) ⟨2506301, by rfl⟩ : syracuseStep 3341735 = 5012603) B5012603
theorem B2227823 : Blo 2227435 2227823 := bstep (se 1 (by rfl) ⟨1670867, by rfl⟩ : syracuseStep 2227823 = 3341735) B3341735
theorem B3341741 : Blo 2227435 3341741 := bbase (se 3 (by rfl) ⟨626576, by rfl⟩ : syracuseStep 3341741 = 1253153) (by norm_num)
theorem B2227827 : Blo 2227435 2227827 := bstep (se 1 (by rfl) ⟨1670870, by rfl⟩ : syracuseStep 2227827 = 3341741) B3341741
theorem B5012621 : Blo 2227435 5012621 := bbase (se 3 (by rfl) ⟨939866, by rfl⟩ : syracuseStep 5012621 = 1879733) (by norm_num)
theorem B3341747 : Blo 2227435 3341747 := bstep (se 1 (by rfl) ⟨2506310, by rfl⟩ : syracuseStep 3341747 = 5012621) B5012621
theorem B2227831 : Blo 2227435 2227831 := bstep (se 1 (by rfl) ⟨1670873, by rfl⟩ : syracuseStep 2227831 = 3341747) B3341747
theorem B2819605 : Blo 2227435 2819605 := bbase (se 6 (by rfl) ⟨66084, by rfl⟩ : syracuseStep 2819605 = 132169) (by norm_num)
theorem B3759473 : Blo 2227435 3759473 := bstep (se 2 (by rfl) ⟨1409802, by rfl⟩ : syracuseStep 3759473 = 2819605) B2819605
theorem B2506315 : Blo 2227435 2506315 := bstep (se 1 (by rfl) ⟨1879736, by rfl⟩ : syracuseStep 2506315 = 3759473) B3759473
theorem B3341753 : Blo 2227435 3341753 := bstep (se 2 (by rfl) ⟨1253157, by rfl⟩ : syracuseStep 3341753 = 2506315) B2506315
theorem B2227835 : Blo 2227435 2227835 := bstep (se 1 (by rfl) ⟨1670876, by rfl⟩ : syracuseStep 2227835 = 3341753) B3341753
theorem B5081029 : Blo 2227435 5081029 := bbase (se 4 (by rfl) ⟨476346, by rfl⟩ : syracuseStep 5081029 = 952693) (by norm_num)
theorem B27098821 : Blo 2227435 27098821 := bstep (se 4 (by rfl) ⟨2540514, by rfl⟩ : syracuseStep 27098821 = 5081029) B5081029
theorem B36131761 : Blo 2227435 36131761 := bstep (se 2 (by rfl) ⟨13549410, by rfl⟩ : syracuseStep 36131761 = 27098821) B27098821
theorem B48175681 : Blo 2227435 48175681 := bstep (se 2 (by rfl) ⟨18065880, by rfl⟩ : syracuseStep 48175681 = 36131761) B36131761
theorem B64234241 : Blo 2227435 64234241 := bstep (se 2 (by rfl) ⟨24087840, by rfl⟩ : syracuseStep 64234241 = 48175681) B48175681
theorem B42822827 : Blo 2227435 42822827 := bstep (se 1 (by rfl) ⟨32117120, by rfl⟩ : syracuseStep 42822827 = 64234241) B64234241
theorem B28548551 : Blo 2227435 28548551 := bstep (se 1 (by rfl) ⟨21411413, by rfl⟩ : syracuseStep 28548551 = 42822827) B42822827
theorem B19032367 : Blo 2227435 19032367 := bstep (se 1 (by rfl) ⟨14274275, by rfl⟩ : syracuseStep 19032367 = 28548551) B28548551
theorem B25376489 : Blo 2227435 25376489 := bstep (se 2 (by rfl) ⟨9516183, by rfl⟩ : syracuseStep 25376489 = 19032367) B19032367
theorem B16917659 : Blo 2227435 16917659 := bstep (se 1 (by rfl) ⟨12688244, by rfl⟩ : syracuseStep 16917659 = 25376489) B25376489
theorem B11278439 : Blo 2227435 11278439 := bstep (se 1 (by rfl) ⟨8458829, by rfl⟩ : syracuseStep 11278439 = 16917659) B16917659
theorem B7518959 : Blo 2227435 7518959 := bstep (se 1 (by rfl) ⟨5639219, by rfl⟩ : syracuseStep 7518959 = 11278439) B11278439
theorem B5012639 : Blo 2227435 5012639 := bstep (se 1 (by rfl) ⟨3759479, by rfl⟩ : syracuseStep 5012639 = 7518959) B7518959
theorem B3341759 : Blo 2227435 3341759 := bstep (se 1 (by rfl) ⟨2506319, by rfl⟩ : syracuseStep 3341759 = 5012639) B5012639
theorem B2227839 : Blo 2227435 2227839 := bstep (se 1 (by rfl) ⟨1670879, by rfl⟩ : syracuseStep 2227839 = 3341759) B3341759
theorem B3341765 : Blo 2227435 3341765 := bbase (se 4 (by rfl) ⟨313290, by rfl⟩ : syracuseStep 3341765 = 626581) (by norm_num)
theorem B2227843 : Blo 2227435 2227843 := bstep (se 1 (by rfl) ⟨1670882, by rfl⟩ : syracuseStep 2227843 = 3341765) B3341765
theorem B3759493 : Blo 2227435 3759493 := bbase (se 4 (by rfl) ⟨352452, by rfl⟩ : syracuseStep 3759493 = 704905) (by norm_num)
theorem B5012657 : Blo 2227435 5012657 := bstep (se 2 (by rfl) ⟨1879746, by rfl⟩ : syracuseStep 5012657 = 3759493) B3759493
theorem B3341771 : Blo 2227435 3341771 := bstep (se 1 (by rfl) ⟨2506328, by rfl⟩ : syracuseStep 3341771 = 5012657) B5012657
theorem B2227847 : Blo 2227435 2227847 := bstep (se 1 (by rfl) ⟨1670885, by rfl⟩ : syracuseStep 2227847 = 3341771) B3341771
theorem B2506333 : Blo 2227435 2506333 := bbase (se 3 (by rfl) ⟨469937, by rfl⟩ : syracuseStep 2506333 = 939875) (by norm_num)
theorem B3341777 : Blo 2227435 3341777 := bstep (se 2 (by rfl) ⟨1253166, by rfl⟩ : syracuseStep 3341777 = 2506333) B2506333
theorem B2227851 : Blo 2227435 2227851 := bstep (se 1 (by rfl) ⟨1670888, by rfl⟩ : syracuseStep 2227851 = 3341777) B3341777
theorem B7519013 : Blo 2227435 7519013 := bbase (se 4 (by rfl) ⟨704907, by rfl⟩ : syracuseStep 7519013 = 1409815) (by norm_num)
theorem B5012675 : Blo 2227435 5012675 := bstep (se 1 (by rfl) ⟨3759506, by rfl⟩ : syracuseStep 5012675 = 7519013) B7519013
theorem B3341783 : Blo 2227435 3341783 := bstep (se 1 (by rfl) ⟨2506337, by rfl⟩ : syracuseStep 3341783 = 5012675) B5012675
theorem B2227855 : Blo 2227435 2227855 := bstep (se 1 (by rfl) ⟨1670891, by rfl⟩ : syracuseStep 2227855 = 3341783) B3341783
theorem B3341789 : Blo 2227435 3341789 := bbase (se 3 (by rfl) ⟨626585, by rfl⟩ : syracuseStep 3341789 = 1253171) (by norm_num)
theorem B2227859 : Blo 2227435 2227859 := bstep (se 1 (by rfl) ⟨1670894, by rfl⟩ : syracuseStep 2227859 = 3341789) B3341789
theorem B5012693 : Blo 2227435 5012693 := bbase (se 7 (by rfl) ⟨58742, by rfl⟩ : syracuseStep 5012693 = 117485) (by norm_num)
theorem B3341795 : Blo 2227435 3341795 := bstep (se 1 (by rfl) ⟨2506346, by rfl⟩ : syracuseStep 3341795 = 5012693) B5012693
theorem B2227863 : Blo 2227435 2227863 := bstep (se 1 (by rfl) ⟨1670897, by rfl⟩ : syracuseStep 2227863 = 3341795) B3341795
theorem B2676461 : Blo 2227435 2676461 := bbase (se 3 (by rfl) ⟨501836, by rfl⟩ : syracuseStep 2676461 = 1003673) (by norm_num)
theorem B7137229 : Blo 2227435 7137229 := bstep (se 3 (by rfl) ⟨1338230, by rfl⟩ : syracuseStep 7137229 = 2676461) B2676461
theorem B9516305 : Blo 2227435 9516305 := bstep (se 2 (by rfl) ⟨3568614, by rfl⟩ : syracuseStep 9516305 = 7137229) B7137229
theorem B6344203 : Blo 2227435 6344203 := bstep (se 1 (by rfl) ⟨4758152, by rfl⟩ : syracuseStep 6344203 = 9516305) B9516305
theorem B8458937 : Blo 2227435 8458937 := bstep (se 2 (by rfl) ⟨3172101, by rfl⟩ : syracuseStep 8458937 = 6344203) B6344203
theorem B5639291 : Blo 2227435 5639291 := bstep (se 1 (by rfl) ⟨4229468, by rfl⟩ : syracuseStep 5639291 = 8458937) B8458937
theorem B3759527 : Blo 2227435 3759527 := bstep (se 1 (by rfl) ⟨2819645, by rfl⟩ : syracuseStep 3759527 = 5639291) B5639291
theorem B2506351 : Blo 2227435 2506351 := bstep (se 1 (by rfl) ⟨1879763, by rfl⟩ : syracuseStep 2506351 = 3759527) B3759527
theorem B3341801 : Blo 2227435 3341801 := bstep (se 2 (by rfl) ⟨1253175, by rfl⟩ : syracuseStep 3341801 = 2506351) B2506351
theorem B2227867 : Blo 2227435 2227867 := bstep (se 1 (by rfl) ⟨1670900, by rfl⟩ : syracuseStep 2227867 = 3341801) B3341801
theorem B10705861 : Blo 2227435 10705861 := bbase (se 4 (by rfl) ⟨1003674, by rfl⟩ : syracuseStep 10705861 = 2007349) (by norm_num)
theorem B14274481 : Blo 2227435 14274481 := bstep (se 2 (by rfl) ⟨5352930, by rfl⟩ : syracuseStep 14274481 = 10705861) B10705861
theorem B19032641 : Blo 2227435 19032641 := bstep (se 2 (by rfl) ⟨7137240, by rfl⟩ : syracuseStep 19032641 = 14274481) B14274481
theorem B12688427 : Blo 2227435 12688427 := bstep (se 1 (by rfl) ⟨9516320, by rfl⟩ : syracuseStep 12688427 = 19032641) B19032641
theorem B8458951 : Blo 2227435 8458951 := bstep (se 1 (by rfl) ⟨6344213, by rfl⟩ : syracuseStep 8458951 = 12688427) B12688427
theorem B11278601 : Blo 2227435 11278601 := bstep (se 2 (by rfl) ⟨4229475, by rfl⟩ : syracuseStep 11278601 = 8458951) B8458951
theorem B7519067 : Blo 2227435 7519067 := bstep (se 1 (by rfl) ⟨5639300, by rfl⟩ : syracuseStep 7519067 = 11278601) B11278601
theorem B5012711 : Blo 2227435 5012711 := bstep (se 1 (by rfl) ⟨3759533, by rfl⟩ : syracuseStep 5012711 = 7519067) B7519067
theorem B3341807 : Blo 2227435 3341807 := bstep (se 1 (by rfl) ⟨2506355, by rfl⟩ : syracuseStep 3341807 = 5012711) B5012711
theorem B2227871 : Blo 2227435 2227871 := bstep (se 1 (by rfl) ⟨1670903, by rfl⟩ : syracuseStep 2227871 = 3341807) B3341807
theorem B3341813 : Blo 2227435 3341813 := bbase (se 5 (by rfl) ⟨156647, by rfl⟩ : syracuseStep 3341813 = 313295) (by norm_num)
theorem B2227875 : Blo 2227435 2227875 := bstep (se 1 (by rfl) ⟨1670906, by rfl⟩ : syracuseStep 2227875 = 3341813) B3341813
theorem B2379089 : Blo 2227435 2379089 := bbase (se 2 (by rfl) ⟨892158, by rfl⟩ : syracuseStep 2379089 = 1784317) (by norm_num)
theorem B6344237 : Blo 2227435 6344237 := bstep (se 3 (by rfl) ⟨1189544, by rfl⟩ : syracuseStep 6344237 = 2379089) B2379089
theorem B4229491 : Blo 2227435 4229491 := bstep (se 1 (by rfl) ⟨3172118, by rfl⟩ : syracuseStep 4229491 = 6344237) B6344237
theorem B5639321 : Blo 2227435 5639321 := bstep (se 2 (by rfl) ⟨2114745, by rfl⟩ : syracuseStep 5639321 = 4229491) B4229491
theorem B3759547 : Blo 2227435 3759547 := bstep (se 1 (by rfl) ⟨2819660, by rfl⟩ : syracuseStep 3759547 = 5639321) B5639321
theorem B5012729 : Blo 2227435 5012729 := bstep (se 2 (by rfl) ⟨1879773, by rfl⟩ : syracuseStep 5012729 = 3759547) B3759547
theorem B3341819 : Blo 2227435 3341819 := bstep (se 1 (by rfl) ⟨2506364, by rfl⟩ : syracuseStep 3341819 = 5012729) B5012729
theorem B2227879 : Blo 2227435 2227879 := bstep (se 1 (by rfl) ⟨1670909, by rfl⟩ : syracuseStep 2227879 = 3341819) B3341819
theorem B2506369 : Blo 2227435 2506369 := bbase (se 2 (by rfl) ⟨939888, by rfl⟩ : syracuseStep 2506369 = 1879777) (by norm_num)
theorem B3341825 : Blo 2227435 3341825 := bstep (se 2 (by rfl) ⟨1253184, by rfl⟩ : syracuseStep 3341825 = 2506369) B2506369
theorem B2227883 : Blo 2227435 2227883 := bstep (se 1 (by rfl) ⟨1670912, by rfl⟩ : syracuseStep 2227883 = 3341825) B3341825
theorem B5639341 : Blo 2227435 5639341 := bbase (se 3 (by rfl) ⟨1057376, by rfl⟩ : syracuseStep 5639341 = 2114753) (by norm_num)
theorem B7519121 : Blo 2227435 7519121 := bstep (se 2 (by rfl) ⟨2819670, by rfl⟩ : syracuseStep 7519121 = 5639341) B5639341
theorem B5012747 : Blo 2227435 5012747 := bstep (se 1 (by rfl) ⟨3759560, by rfl⟩ : syracuseStep 5012747 = 7519121) B7519121
theorem B3341831 : Blo 2227435 3341831 := bstep (se 1 (by rfl) ⟨2506373, by rfl⟩ : syracuseStep 3341831 = 5012747) B5012747
theorem B2227887 : Blo 2227435 2227887 := bstep (se 1 (by rfl) ⟨1670915, by rfl⟩ : syracuseStep 2227887 = 3341831) B3341831
theorem B3341837 : Blo 2227435 3341837 := bbase (se 3 (by rfl) ⟨626594, by rfl⟩ : syracuseStep 3341837 = 1253189) (by norm_num)
theorem B2227891 : Blo 2227435 2227891 := bstep (se 1 (by rfl) ⟨1670918, by rfl⟩ : syracuseStep 2227891 = 3341837) B3341837
theorem B5012765 : Blo 2227435 5012765 := bbase (se 3 (by rfl) ⟨939893, by rfl⟩ : syracuseStep 5012765 = 1879787) (by norm_num)
theorem B3341843 : Blo 2227435 3341843 := bstep (se 1 (by rfl) ⟨2506382, by rfl⟩ : syracuseStep 3341843 = 5012765) B5012765
theorem B2227895 : Blo 2227435 2227895 := bstep (se 1 (by rfl) ⟨1670921, by rfl⟩ : syracuseStep 2227895 = 3341843) B3341843
theorem B3759581 : Blo 2227435 3759581 := bbase (se 3 (by rfl) ⟨704921, by rfl⟩ : syracuseStep 3759581 = 1409843) (by norm_num)
theorem B2506387 : Blo 2227435 2506387 := bstep (se 1 (by rfl) ⟨1879790, by rfl⟩ : syracuseStep 2506387 = 3759581) B3759581
theorem B3341849 : Blo 2227435 3341849 := bstep (se 2 (by rfl) ⟨1253193, by rfl⟩ : syracuseStep 3341849 = 2506387) B2506387
theorem B2227899 : Blo 2227435 2227899 := bstep (se 1 (by rfl) ⟨1670924, by rfl⟩ : syracuseStep 2227899 = 3341849) B3341849
theorem B11588629 : Blo 2227435 11588629 := bbase (se 6 (by rfl) ⟨271608, by rfl⟩ : syracuseStep 11588629 = 543217) (by norm_num)
theorem B15451505 : Blo 2227435 15451505 := bstep (se 2 (by rfl) ⟨5794314, by rfl⟩ : syracuseStep 15451505 = 11588629) B11588629
theorem B10301003 : Blo 2227435 10301003 := bstep (se 1 (by rfl) ⟨7725752, by rfl⟩ : syracuseStep 10301003 = 15451505) B15451505
theorem B6867335 : Blo 2227435 6867335 := bstep (se 1 (by rfl) ⟨5150501, by rfl⟩ : syracuseStep 6867335 = 10301003) B10301003
theorem B4578223 : Blo 2227435 4578223 := bstep (se 1 (by rfl) ⟨3433667, by rfl⟩ : syracuseStep 4578223 = 6867335) B6867335
theorem B6104297 : Blo 2227435 6104297 := bstep (se 2 (by rfl) ⟨2289111, by rfl⟩ : syracuseStep 6104297 = 4578223) B4578223
theorem B4069531 : Blo 2227435 4069531 := bstep (se 1 (by rfl) ⟨3052148, by rfl⟩ : syracuseStep 4069531 = 6104297) B6104297
theorem B21704165 : Blo 2227435 21704165 := bstep (se 4 (by rfl) ⟨2034765, by rfl⟩ : syracuseStep 21704165 = 4069531) B4069531
theorem B14469443 : Blo 2227435 14469443 := bstep (se 1 (by rfl) ⟨10852082, by rfl⟩ : syracuseStep 14469443 = 21704165) B21704165
theorem B9646295 : Blo 2227435 9646295 := bstep (se 1 (by rfl) ⟨7234721, by rfl⟩ : syracuseStep 9646295 = 14469443) B14469443
theorem B25723453 : Blo 2227435 25723453 := bstep (se 3 (by rfl) ⟨4823147, by rfl⟩ : syracuseStep 25723453 = 9646295) B9646295
theorem B34297937 : Blo 2227435 34297937 := bstep (se 2 (by rfl) ⟨12861726, by rfl⟩ : syracuseStep 34297937 = 25723453) B25723453
theorem B22865291 : Blo 2227435 22865291 := bstep (se 1 (by rfl) ⟨17148968, by rfl⟩ : syracuseStep 22865291 = 34297937) B34297937
theorem B15243527 : Blo 2227435 15243527 := bstep (se 1 (by rfl) ⟨11432645, by rfl⟩ : syracuseStep 15243527 = 22865291) B22865291
theorem B10162351 : Blo 2227435 10162351 := bstep (se 1 (by rfl) ⟨7621763, by rfl⟩ : syracuseStep 10162351 = 15243527) B15243527
theorem B54199205 : Blo 2227435 54199205 := bstep (se 4 (by rfl) ⟨5081175, by rfl⟩ : syracuseStep 54199205 = 10162351) B10162351
theorem B36132803 : Blo 2227435 36132803 := bstep (se 1 (by rfl) ⟨27099602, by rfl⟩ : syracuseStep 36132803 = 54199205) B54199205
theorem B24088535 : Blo 2227435 24088535 := bstep (se 1 (by rfl) ⟨18066401, by rfl⟩ : syracuseStep 24088535 = 36132803) B36132803
theorem B16059023 : Blo 2227435 16059023 := bstep (se 1 (by rfl) ⟨12044267, by rfl⟩ : syracuseStep 16059023 = 24088535) B24088535
theorem B10706015 : Blo 2227435 10706015 := bstep (se 1 (by rfl) ⟨8029511, by rfl⟩ : syracuseStep 10706015 = 16059023) B16059023
theorem B7137343 : Blo 2227435 7137343 := bstep (se 1 (by rfl) ⟨5353007, by rfl⟩ : syracuseStep 7137343 = 10706015) B10706015
theorem B9516457 : Blo 2227435 9516457 := bstep (se 2 (by rfl) ⟨3568671, by rfl⟩ : syracuseStep 9516457 = 7137343) B7137343
theorem B12688609 : Blo 2227435 12688609 := bstep (se 2 (by rfl) ⟨4758228, by rfl⟩ : syracuseStep 12688609 = 9516457) B9516457
theorem B16918145 : Blo 2227435 16918145 := bstep (se 2 (by rfl) ⟨6344304, by rfl⟩ : syracuseStep 16918145 = 12688609) B12688609
theorem B11278763 : Blo 2227435 11278763 := bstep (se 1 (by rfl) ⟨8459072, by rfl⟩ : syracuseStep 11278763 = 16918145) B16918145
theorem B7519175 : Blo 2227435 7519175 := bstep (se 1 (by rfl) ⟨5639381, by rfl⟩ : syracuseStep 7519175 = 11278763) B11278763
theorem B5012783 : Blo 2227435 5012783 := bstep (se 1 (by rfl) ⟨3759587, by rfl⟩ : syracuseStep 5012783 = 7519175) B7519175
theorem B3341855 : Blo 2227435 3341855 := bstep (se 1 (by rfl) ⟨2506391, by rfl⟩ : syracuseStep 3341855 = 5012783) B5012783
theorem B2227903 : Blo 2227435 2227903 := bstep (se 1 (by rfl) ⟨1670927, by rfl⟩ : syracuseStep 2227903 = 3341855) B3341855
theorem B3341861 : Blo 2227435 3341861 := bbase (se 4 (by rfl) ⟨313299, by rfl⟩ : syracuseStep 3341861 = 626599) (by norm_num)
theorem B2227907 : Blo 2227435 2227907 := bstep (se 1 (by rfl) ⟨1670930, by rfl⟩ : syracuseStep 2227907 = 3341861) B3341861
theorem B2819701 : Blo 2227435 2819701 := bbase (se 5 (by rfl) ⟨132173, by rfl⟩ : syracuseStep 2819701 = 264347) (by norm_num)
theorem B3759601 : Blo 2227435 3759601 := bstep (se 2 (by rfl) ⟨1409850, by rfl⟩ : syracuseStep 3759601 = 2819701) B2819701
theorem B5012801 : Blo 2227435 5012801 := bstep (se 2 (by rfl) ⟨1879800, by rfl⟩ : syracuseStep 5012801 = 3759601) B3759601
theorem B3341867 : Blo 2227435 3341867 := bstep (se 1 (by rfl) ⟨2506400, by rfl⟩ : syracuseStep 3341867 = 5012801) B5012801
theorem B2227911 : Blo 2227435 2227911 := bstep (se 1 (by rfl) ⟨1670933, by rfl⟩ : syracuseStep 2227911 = 3341867) B3341867
theorem B2506405 : Blo 2227435 2506405 := bbase (se 4 (by rfl) ⟨234975, by rfl⟩ : syracuseStep 2506405 = 469951) (by norm_num)
theorem B3341873 : Blo 2227435 3341873 := bstep (se 2 (by rfl) ⟨1253202, by rfl⟩ : syracuseStep 3341873 = 2506405) B2506405
theorem B2227915 : Blo 2227435 2227915 := bstep (se 1 (by rfl) ⟨1670936, by rfl⟩ : syracuseStep 2227915 = 3341873) B3341873
theorem B3433693 : Blo 2227435 3433693 := bbase (se 3 (by rfl) ⟨643817, by rfl⟩ : syracuseStep 3433693 = 1287635) (by norm_num)
theorem B4578257 : Blo 2227435 4578257 := bstep (se 2 (by rfl) ⟨1716846, by rfl⟩ : syracuseStep 4578257 = 3433693) B3433693
theorem B3052171 : Blo 2227435 3052171 := bstep (se 1 (by rfl) ⟨2289128, by rfl⟩ : syracuseStep 3052171 = 4578257) B4578257
theorem B16278245 : Blo 2227435 16278245 := bstep (se 4 (by rfl) ⟨1526085, by rfl⟩ : syracuseStep 16278245 = 3052171) B3052171
theorem B10852163 : Blo 2227435 10852163 := bstep (se 1 (by rfl) ⟨8139122, by rfl⟩ : syracuseStep 10852163 = 16278245) B16278245
theorem B7234775 : Blo 2227435 7234775 := bstep (se 1 (by rfl) ⟨5426081, by rfl⟩ : syracuseStep 7234775 = 10852163) B10852163
theorem B4823183 : Blo 2227435 4823183 := bstep (se 1 (by rfl) ⟨3617387, by rfl⟩ : syracuseStep 4823183 = 7234775) B7234775
theorem B12861821 : Blo 2227435 12861821 := bstep (se 3 (by rfl) ⟨2411591, by rfl⟩ : syracuseStep 12861821 = 4823183) B4823183
theorem B8574547 : Blo 2227435 8574547 := bstep (se 1 (by rfl) ⟨6430910, by rfl⟩ : syracuseStep 8574547 = 12861821) B12861821
theorem B11432729 : Blo 2227435 11432729 := bstep (se 2 (by rfl) ⟨4287273, by rfl⟩ : syracuseStep 11432729 = 8574547) B8574547
theorem B7621819 : Blo 2227435 7621819 := bstep (se 1 (by rfl) ⟨5716364, by rfl⟩ : syracuseStep 7621819 = 11432729) B11432729
theorem B40649701 : Blo 2227435 40649701 := bstep (se 4 (by rfl) ⟨3810909, by rfl⟩ : syracuseStep 40649701 = 7621819) B7621819
theorem B54199601 : Blo 2227435 54199601 := bstep (se 2 (by rfl) ⟨20324850, by rfl⟩ : syracuseStep 54199601 = 40649701) B40649701
theorem B36133067 : Blo 2227435 36133067 := bstep (se 1 (by rfl) ⟨27099800, by rfl⟩ : syracuseStep 36133067 = 54199601) B54199601
theorem B24088711 : Blo 2227435 24088711 := bstep (se 1 (by rfl) ⟨18066533, by rfl⟩ : syracuseStep 24088711 = 36133067) B36133067
theorem B32118281 : Blo 2227435 32118281 := bstep (se 2 (by rfl) ⟨12044355, by rfl⟩ : syracuseStep 32118281 = 24088711) B24088711
theorem B21412187 : Blo 2227435 21412187 := bstep (se 1 (by rfl) ⟨16059140, by rfl⟩ : syracuseStep 21412187 = 32118281) B32118281
theorem B14274791 : Blo 2227435 14274791 := bstep (se 1 (by rfl) ⟨10706093, by rfl⟩ : syracuseStep 14274791 = 21412187) B21412187
theorem B9516527 : Blo 2227435 9516527 := bstep (se 1 (by rfl) ⟨7137395, by rfl⟩ : syracuseStep 9516527 = 14274791) B14274791
theorem B6344351 : Blo 2227435 6344351 := bstep (se 1 (by rfl) ⟨4758263, by rfl⟩ : syracuseStep 6344351 = 9516527) B9516527
theorem B4229567 : Blo 2227435 4229567 := bstep (se 1 (by rfl) ⟨3172175, by rfl⟩ : syracuseStep 4229567 = 6344351) B6344351
theorem B2819711 : Blo 2227435 2819711 := bstep (se 1 (by rfl) ⟨2114783, by rfl⟩ : syracuseStep 2819711 = 4229567) B4229567
theorem B7519229 : Blo 2227435 7519229 := bstep (se 3 (by rfl) ⟨1409855, by rfl⟩ : syracuseStep 7519229 = 2819711) B2819711
theorem B5012819 : Blo 2227435 5012819 := bstep (se 1 (by rfl) ⟨3759614, by rfl⟩ : syracuseStep 5012819 = 7519229) B7519229
theorem B3341879 : Blo 2227435 3341879 := bstep (se 1 (by rfl) ⟨2506409, by rfl⟩ : syracuseStep 3341879 = 5012819) B5012819
theorem B2227919 : Blo 2227435 2227919 := bstep (se 1 (by rfl) ⟨1670939, by rfl⟩ : syracuseStep 2227919 = 3341879) B3341879
theorem B3341885 : Blo 2227435 3341885 := bbase (se 3 (by rfl) ⟨626603, by rfl⟩ : syracuseStep 3341885 = 1253207) (by norm_num)
theorem B2227923 : Blo 2227435 2227923 := bstep (se 1 (by rfl) ⟨1670942, by rfl⟩ : syracuseStep 2227923 = 3341885) B3341885
theorem B5012837 : Blo 2227435 5012837 := bbase (se 4 (by rfl) ⟨469953, by rfl⟩ : syracuseStep 5012837 = 939907) (by norm_num)
theorem B3341891 : Blo 2227435 3341891 := bstep (se 1 (by rfl) ⟨2506418, by rfl⟩ : syracuseStep 3341891 = 5012837) B5012837
theorem B2227927 : Blo 2227435 2227927 := bstep (se 1 (by rfl) ⟨1670945, by rfl⟩ : syracuseStep 2227927 = 3341891) B3341891
theorem B5639453 : Blo 2227435 5639453 := bbase (se 3 (by rfl) ⟨1057397, by rfl⟩ : syracuseStep 5639453 = 2114795) (by norm_num)
theorem B3759635 : Blo 2227435 3759635 := bstep (se 1 (by rfl) ⟨2819726, by rfl⟩ : syracuseStep 3759635 = 5639453) B5639453
theorem B2506423 : Blo 2227435 2506423 := bstep (se 1 (by rfl) ⟨1879817, by rfl⟩ : syracuseStep 2506423 = 3759635) B3759635
theorem B3341897 : Blo 2227435 3341897 := bstep (se 2 (by rfl) ⟨1253211, by rfl⟩ : syracuseStep 3341897 = 2506423) B2506423
theorem B2227931 : Blo 2227435 2227931 := bstep (se 1 (by rfl) ⟨1670948, by rfl⟩ : syracuseStep 2227931 = 3341897) B3341897
theorem B4229597 : Blo 2227435 4229597 := bbase (se 3 (by rfl) ⟨793049, by rfl⟩ : syracuseStep 4229597 = 1586099) (by norm_num)
theorem B11278925 : Blo 2227435 11278925 := bstep (se 3 (by rfl) ⟨2114798, by rfl⟩ : syracuseStep 11278925 = 4229597) B4229597
theorem B7519283 : Blo 2227435 7519283 := bstep (se 1 (by rfl) ⟨5639462, by rfl⟩ : syracuseStep 7519283 = 11278925) B11278925
theorem B5012855 : Blo 2227435 5012855 := bstep (se 1 (by rfl) ⟨3759641, by rfl⟩ : syracuseStep 5012855 = 7519283) B7519283
theorem B3341903 : Blo 2227435 3341903 := bstep (se 1 (by rfl) ⟨2506427, by rfl⟩ : syracuseStep 3341903 = 5012855) B5012855
theorem B2227935 : Blo 2227435 2227935 := bstep (se 1 (by rfl) ⟨1670951, by rfl⟩ : syracuseStep 2227935 = 3341903) B3341903
theorem B3341909 : Blo 2227435 3341909 := bbase (se 8 (by rfl) ⟨19581, by rfl⟩ : syracuseStep 3341909 = 39163) (by norm_num)
theorem B2227939 : Blo 2227435 2227939 := bstep (se 1 (by rfl) ⟨1670954, by rfl⟩ : syracuseStep 2227939 = 3341909) B3341909
theorem B9516629 : Blo 2227435 9516629 := bbase (se 8 (by rfl) ⟨55761, by rfl⟩ : syracuseStep 9516629 = 111523) (by norm_num)
theorem B6344419 : Blo 2227435 6344419 := bstep (se 1 (by rfl) ⟨4758314, by rfl⟩ : syracuseStep 6344419 = 9516629) B9516629
theorem B8459225 : Blo 2227435 8459225 := bstep (se 2 (by rfl) ⟨3172209, by rfl⟩ : syracuseStep 8459225 = 6344419) B6344419
theorem B5639483 : Blo 2227435 5639483 := bstep (se 1 (by rfl) ⟨4229612, by rfl⟩ : syracuseStep 5639483 = 8459225) B8459225
theorem B3759655 : Blo 2227435 3759655 := bstep (se 1 (by rfl) ⟨2819741, by rfl⟩ : syracuseStep 3759655 = 5639483) B5639483
theorem B5012873 : Blo 2227435 5012873 := bstep (se 2 (by rfl) ⟨1879827, by rfl⟩ : syracuseStep 5012873 = 3759655) B3759655
theorem B3341915 : Blo 2227435 3341915 := bstep (se 1 (by rfl) ⟨2506436, by rfl⟩ : syracuseStep 3341915 = 5012873) B5012873
theorem B2227943 : Blo 2227435 2227943 := bstep (se 1 (by rfl) ⟨1670957, by rfl⟩ : syracuseStep 2227943 = 3341915) B3341915
theorem B2506441 : Blo 2227435 2506441 := bbase (se 2 (by rfl) ⟨939915, by rfl⟩ : syracuseStep 2506441 = 1879831) (by norm_num)
theorem B3341921 : Blo 2227435 3341921 := bstep (se 2 (by rfl) ⟨1253220, by rfl⟩ : syracuseStep 3341921 = 2506441) B2506441
theorem B2227947 : Blo 2227435 2227947 := bstep (se 1 (by rfl) ⟨1670960, by rfl⟩ : syracuseStep 2227947 = 3341921) B3341921
theorem B8029685 : Blo 2227435 8029685 := bbase (se 5 (by rfl) ⟨376391, by rfl⟩ : syracuseStep 8029685 = 752783) (by norm_num)
theorem B5353123 : Blo 2227435 5353123 := bstep (se 1 (by rfl) ⟨4014842, by rfl⟩ : syracuseStep 5353123 = 8029685) B8029685
theorem B7137497 : Blo 2227435 7137497 := bstep (se 2 (by rfl) ⟨2676561, by rfl⟩ : syracuseStep 7137497 = 5353123) B5353123
theorem B19033325 : Blo 2227435 19033325 := bstep (se 3 (by rfl) ⟨3568748, by rfl⟩ : syracuseStep 19033325 = 7137497) B7137497
theorem B12688883 : Blo 2227435 12688883 := bstep (se 1 (by rfl) ⟨9516662, by rfl⟩ : syracuseStep 12688883 = 19033325) B19033325
theorem B8459255 : Blo 2227435 8459255 := bstep (se 1 (by rfl) ⟨6344441, by rfl⟩ : syracuseStep 8459255 = 12688883) B12688883
theorem B5639503 : Blo 2227435 5639503 := bstep (se 1 (by rfl) ⟨4229627, by rfl⟩ : syracuseStep 5639503 = 8459255) B8459255
theorem B7519337 : Blo 2227435 7519337 := bstep (se 2 (by rfl) ⟨2819751, by rfl⟩ : syracuseStep 7519337 = 5639503) B5639503
theorem B5012891 : Blo 2227435 5012891 := bstep (se 1 (by rfl) ⟨3759668, by rfl⟩ : syracuseStep 5012891 = 7519337) B7519337
theorem B3341927 : Blo 2227435 3341927 := bstep (se 1 (by rfl) ⟨2506445, by rfl⟩ : syracuseStep 3341927 = 5012891) B5012891
theorem B2227951 : Blo 2227435 2227951 := bstep (se 1 (by rfl) ⟨1670963, by rfl⟩ : syracuseStep 2227951 = 3341927) B3341927
theorem B3341933 : Blo 2227435 3341933 := bbase (se 3 (by rfl) ⟨626612, by rfl⟩ : syracuseStep 3341933 = 1253225) (by norm_num)
theorem B2227955 : Blo 2227435 2227955 := bstep (se 1 (by rfl) ⟨1670966, by rfl⟩ : syracuseStep 2227955 = 3341933) B3341933
theorem B5012909 : Blo 2227435 5012909 := bbase (se 3 (by rfl) ⟨939920, by rfl⟩ : syracuseStep 5012909 = 1879841) (by norm_num)
theorem B3341939 : Blo 2227435 3341939 := bstep (se 1 (by rfl) ⟨2506454, by rfl⟩ : syracuseStep 3341939 = 5012909) B5012909
theorem B2227959 : Blo 2227435 2227959 := bstep (se 1 (by rfl) ⟨1670969, by rfl⟩ : syracuseStep 2227959 = 3341939) B3341939
theorem B2676577 : Blo 2227435 2676577 := bbase (se 2 (by rfl) ⟨1003716, by rfl⟩ : syracuseStep 2676577 = 2007433) (by norm_num)
theorem B3568769 : Blo 2227435 3568769 := bstep (se 2 (by rfl) ⟨1338288, by rfl⟩ : syracuseStep 3568769 = 2676577) B2676577
theorem B2379179 : Blo 2227435 2379179 := bstep (se 1 (by rfl) ⟨1784384, by rfl⟩ : syracuseStep 2379179 = 3568769) B3568769
theorem B6344477 : Blo 2227435 6344477 := bstep (se 3 (by rfl) ⟨1189589, by rfl⟩ : syracuseStep 6344477 = 2379179) B2379179
theorem B4229651 : Blo 2227435 4229651 := bstep (se 1 (by rfl) ⟨3172238, by rfl⟩ : syracuseStep 4229651 = 6344477) B6344477
theorem B2819767 : Blo 2227435 2819767 := bstep (se 1 (by rfl) ⟨2114825, by rfl⟩ : syracuseStep 2819767 = 4229651) B4229651
theorem B3759689 : Blo 2227435 3759689 := bstep (se 2 (by rfl) ⟨1409883, by rfl⟩ : syracuseStep 3759689 = 2819767) B2819767
theorem B2506459 : Blo 2227435 2506459 := bstep (se 1 (by rfl) ⟨1879844, by rfl⟩ : syracuseStep 2506459 = 3759689) B3759689
theorem B3341945 : Blo 2227435 3341945 := bstep (se 2 (by rfl) ⟨1253229, by rfl⟩ : syracuseStep 3341945 = 2506459) B2506459
theorem B2227963 : Blo 2227435 2227963 := bstep (se 1 (by rfl) ⟨1670972, by rfl⟩ : syracuseStep 2227963 = 3341945) B3341945
theorem B4287365 : Blo 2227435 4287365 := bbase (se 4 (by rfl) ⟨401940, by rfl⟩ : syracuseStep 4287365 = 803881) (by norm_num)
theorem B2858243 : Blo 2227435 2858243 := bstep (se 1 (by rfl) ⟨2143682, by rfl⟩ : syracuseStep 2858243 = 4287365) B4287365
theorem B30487925 : Blo 2227435 30487925 := bstep (se 5 (by rfl) ⟨1429121, by rfl⟩ : syracuseStep 30487925 = 2858243) B2858243
theorem B81301133 : Blo 2227435 81301133 := bstep (se 3 (by rfl) ⟨15243962, by rfl⟩ : syracuseStep 81301133 = 30487925) B30487925
theorem B54200755 : Blo 2227435 54200755 := bstep (se 1 (by rfl) ⟨40650566, by rfl⟩ : syracuseStep 54200755 = 81301133) B81301133
theorem B72267673 : Blo 2227435 72267673 := bstep (se 2 (by rfl) ⟨27100377, by rfl⟩ : syracuseStep 72267673 = 54200755) B54200755
theorem B96356897 : Blo 2227435 96356897 := bstep (se 2 (by rfl) ⟨36133836, by rfl⟩ : syracuseStep 96356897 = 72267673) B72267673
theorem B64237931 : Blo 2227435 64237931 := bstep (se 1 (by rfl) ⟨48178448, by rfl⟩ : syracuseStep 64237931 = 96356897) B96356897
theorem B42825287 : Blo 2227435 42825287 := bstep (se 1 (by rfl) ⟨32118965, by rfl⟩ : syracuseStep 42825287 = 64237931) B64237931
theorem B28550191 : Blo 2227435 28550191 := bstep (se 1 (by rfl) ⟨21412643, by rfl⟩ : syracuseStep 28550191 = 42825287) B42825287
theorem B38066921 : Blo 2227435 38066921 := bstep (se 2 (by rfl) ⟨14275095, by rfl⟩ : syracuseStep 38066921 = 28550191) B28550191
theorem B25377947 : Blo 2227435 25377947 := bstep (se 1 (by rfl) ⟨19033460, by rfl⟩ : syracuseStep 25377947 = 38066921) B38066921
theorem B16918631 : Blo 2227435 16918631 := bstep (se 1 (by rfl) ⟨12688973, by rfl⟩ : syracuseStep 16918631 = 25377947) B25377947
theorem B11279087 : Blo 2227435 11279087 := bstep (se 1 (by rfl) ⟨8459315, by rfl⟩ : syracuseStep 11279087 = 16918631) B16918631
theorem B7519391 : Blo 2227435 7519391 := bstep (se 1 (by rfl) ⟨5639543, by rfl⟩ : syracuseStep 7519391 = 11279087) B11279087
theorem B5012927 : Blo 2227435 5012927 := bstep (se 1 (by rfl) ⟨3759695, by rfl⟩ : syracuseStep 5012927 = 7519391) B7519391
theorem B3341951 : Blo 2227435 3341951 := bstep (se 1 (by rfl) ⟨2506463, by rfl⟩ : syracuseStep 3341951 = 5012927) B5012927
theorem B2227967 : Blo 2227435 2227967 := bstep (se 1 (by rfl) ⟨1670975, by rfl⟩ : syracuseStep 2227967 = 3341951) B3341951
theorem B3341957 : Blo 2227435 3341957 := bbase (se 4 (by rfl) ⟨313308, by rfl⟩ : syracuseStep 3341957 = 626617) (by norm_num)
theorem B2227971 : Blo 2227435 2227971 := bstep (se 1 (by rfl) ⟨1670978, by rfl⟩ : syracuseStep 2227971 = 3341957) B3341957
theorem B3759709 : Blo 2227435 3759709 := bbase (se 3 (by rfl) ⟨704945, by rfl⟩ : syracuseStep 3759709 = 1409891) (by norm_num)
theorem B5012945 : Blo 2227435 5012945 := bstep (se 2 (by rfl) ⟨1879854, by rfl⟩ : syracuseStep 5012945 = 3759709) B3759709
theorem B3341963 : Blo 2227435 3341963 := bstep (se 1 (by rfl) ⟨2506472, by rfl⟩ : syracuseStep 3341963 = 5012945) B5012945
theorem B2227975 : Blo 2227435 2227975 := bstep (se 1 (by rfl) ⟨1670981, by rfl⟩ : syracuseStep 2227975 = 3341963) B3341963
theorem B2506477 : Blo 2227435 2506477 := bbase (se 3 (by rfl) ⟨469964, by rfl⟩ : syracuseStep 2506477 = 939929) (by norm_num)
theorem B3341969 : Blo 2227435 3341969 := bstep (se 2 (by rfl) ⟨1253238, by rfl⟩ : syracuseStep 3341969 = 2506477) B2506477
theorem B2227979 : Blo 2227435 2227979 := bstep (se 1 (by rfl) ⟨1670984, by rfl⟩ : syracuseStep 2227979 = 3341969) B3341969
theorem B7519445 : Blo 2227435 7519445 := bbase (se 7 (by rfl) ⟨88118, by rfl⟩ : syracuseStep 7519445 = 176237) (by norm_num)
theorem B5012963 : Blo 2227435 5012963 := bstep (se 1 (by rfl) ⟨3759722, by rfl⟩ : syracuseStep 5012963 = 7519445) B7519445
theorem B3341975 : Blo 2227435 3341975 := bstep (se 1 (by rfl) ⟨2506481, by rfl⟩ : syracuseStep 3341975 = 5012963) B5012963
theorem B2227983 : Blo 2227435 2227983 := bstep (se 1 (by rfl) ⟨1670987, by rfl⟩ : syracuseStep 2227983 = 3341975) B3341975
theorem B3341981 : Blo 2227435 3341981 := bbase (se 3 (by rfl) ⟨626621, by rfl⟩ : syracuseStep 3341981 = 1253243) (by norm_num)
theorem B2227987 : Blo 2227435 2227987 := bstep (se 1 (by rfl) ⟨1670990, by rfl⟩ : syracuseStep 2227987 = 3341981) B3341981
theorem B5012981 : Blo 2227435 5012981 := bbase (se 5 (by rfl) ⟨234983, by rfl⟩ : syracuseStep 5012981 = 469967) (by norm_num)
theorem B3341987 : Blo 2227435 3341987 := bstep (se 1 (by rfl) ⟨2506490, by rfl⟩ : syracuseStep 3341987 = 5012981) B5012981
theorem B2227991 : Blo 2227435 2227991 := bstep (se 1 (by rfl) ⟨1670993, by rfl⟩ : syracuseStep 2227991 = 3341987) B3341987
theorem B2713133 : Blo 2227435 2713133 := bbase (se 3 (by rfl) ⟨508712, by rfl⟩ : syracuseStep 2713133 = 1017425) (by norm_num)
theorem B7235021 : Blo 2227435 7235021 := bstep (se 3 (by rfl) ⟨1356566, by rfl⟩ : syracuseStep 7235021 = 2713133) B2713133
theorem B19293389 : Blo 2227435 19293389 := bstep (se 3 (by rfl) ⟨3617510, by rfl⟩ : syracuseStep 19293389 = 7235021) B7235021
theorem B12862259 : Blo 2227435 12862259 := bstep (se 1 (by rfl) ⟨9646694, by rfl⟩ : syracuseStep 12862259 = 19293389) B19293389
theorem B8574839 : Blo 2227435 8574839 := bstep (se 1 (by rfl) ⟨6431129, by rfl⟩ : syracuseStep 8574839 = 12862259) B12862259
theorem B5716559 : Blo 2227435 5716559 := bstep (se 1 (by rfl) ⟨4287419, by rfl⟩ : syracuseStep 5716559 = 8574839) B8574839
theorem B15244157 : Blo 2227435 15244157 := bstep (se 3 (by rfl) ⟨2858279, by rfl⟩ : syracuseStep 15244157 = 5716559) B5716559
theorem B40651085 : Blo 2227435 40651085 := bstep (se 3 (by rfl) ⟨7622078, by rfl⟩ : syracuseStep 40651085 = 15244157) B15244157
theorem B108402893 : Blo 2227435 108402893 := bstep (se 3 (by rfl) ⟨20325542, by rfl⟩ : syracuseStep 108402893 = 40651085) B40651085
theorem B72268595 : Blo 2227435 72268595 := bstep (se 1 (by rfl) ⟨54201446, by rfl⟩ : syracuseStep 72268595 = 108402893) B108402893
theorem B48179063 : Blo 2227435 48179063 := bstep (se 1 (by rfl) ⟨36134297, by rfl⟩ : syracuseStep 48179063 = 72268595) B72268595
theorem B32119375 : Blo 2227435 32119375 := bstep (se 1 (by rfl) ⟨24089531, by rfl⟩ : syracuseStep 32119375 = 48179063) B48179063
theorem B42825833 : Blo 2227435 42825833 := bstep (se 2 (by rfl) ⟨16059687, by rfl⟩ : syracuseStep 42825833 = 32119375) B32119375
theorem B28550555 : Blo 2227435 28550555 := bstep (se 1 (by rfl) ⟨21412916, by rfl⟩ : syracuseStep 28550555 = 42825833) B42825833
theorem B19033703 : Blo 2227435 19033703 := bstep (se 1 (by rfl) ⟨14275277, by rfl⟩ : syracuseStep 19033703 = 28550555) B28550555
theorem B12689135 : Blo 2227435 12689135 := bstep (se 1 (by rfl) ⟨9516851, by rfl⟩ : syracuseStep 12689135 = 19033703) B19033703
theorem B8459423 : Blo 2227435 8459423 := bstep (se 1 (by rfl) ⟨6344567, by rfl⟩ : syracuseStep 8459423 = 12689135) B12689135
theorem B5639615 : Blo 2227435 5639615 := bstep (se 1 (by rfl) ⟨4229711, by rfl⟩ : syracuseStep 5639615 = 8459423) B8459423
theorem B3759743 : Blo 2227435 3759743 := bstep (se 1 (by rfl) ⟨2819807, by rfl⟩ : syracuseStep 3759743 = 5639615) B5639615
theorem B2506495 : Blo 2227435 2506495 := bstep (se 1 (by rfl) ⟨1879871, by rfl⟩ : syracuseStep 2506495 = 3759743) B3759743
theorem B3341993 : Blo 2227435 3341993 := bstep (se 2 (by rfl) ⟨1253247, by rfl⟩ : syracuseStep 3341993 = 2506495) B2506495
theorem B2227995 : Blo 2227435 2227995 := bstep (se 1 (by rfl) ⟨1670996, by rfl⟩ : syracuseStep 2227995 = 3341993) B3341993
theorem B2379217 : Blo 2227435 2379217 := bbase (se 2 (by rfl) ⟨892206, by rfl⟩ : syracuseStep 2379217 = 1784413) (by norm_num)
theorem B3172289 : Blo 2227435 3172289 := bstep (se 2 (by rfl) ⟨1189608, by rfl⟩ : syracuseStep 3172289 = 2379217) B2379217
theorem B8459437 : Blo 2227435 8459437 := bstep (se 3 (by rfl) ⟨1586144, by rfl⟩ : syracuseStep 8459437 = 3172289) B3172289
theorem B11279249 : Blo 2227435 11279249 := bstep (se 2 (by rfl) ⟨4229718, by rfl⟩ : syracuseStep 11279249 = 8459437) B8459437
theorem B7519499 : Blo 2227435 7519499 := bstep (se 1 (by rfl) ⟨5639624, by rfl⟩ : syracuseStep 7519499 = 11279249) B11279249
theorem B5012999 : Blo 2227435 5012999 := bstep (se 1 (by rfl) ⟨3759749, by rfl⟩ : syracuseStep 5012999 = 7519499) B7519499
theorem B3341999 : Blo 2227435 3341999 := bstep (se 1 (by rfl) ⟨2506499, by rfl⟩ : syracuseStep 3341999 = 5012999) B5012999
theorem B2227999 : Blo 2227435 2227999 := bstep (se 1 (by rfl) ⟨1670999, by rfl⟩ : syracuseStep 2227999 = 3341999) B3341999
theorem B3342005 : Blo 2227435 3342005 := bbase (se 5 (by rfl) ⟨156656, by rfl⟩ : syracuseStep 3342005 = 313313) (by norm_num)
theorem B2228003 : Blo 2227435 2228003 := bstep (se 1 (by rfl) ⟨1671002, by rfl⟩ : syracuseStep 2228003 = 3342005) B3342005
theorem B5639645 : Blo 2227435 5639645 := bbase (se 3 (by rfl) ⟨1057433, by rfl⟩ : syracuseStep 5639645 = 2114867) (by norm_num)
theorem B3759763 : Blo 2227435 3759763 := bstep (se 1 (by rfl) ⟨2819822, by rfl⟩ : syracuseStep 3759763 = 5639645) B5639645
theorem B5013017 : Blo 2227435 5013017 := bstep (se 2 (by rfl) ⟨1879881, by rfl⟩ : syracuseStep 5013017 = 3759763) B3759763
theorem B3342011 : Blo 2227435 3342011 := bstep (se 1 (by rfl) ⟨2506508, by rfl⟩ : syracuseStep 3342011 = 5013017) B5013017
theorem B2228007 : Blo 2227435 2228007 := bstep (se 1 (by rfl) ⟨1671005, by rfl⟩ : syracuseStep 2228007 = 3342011) B3342011
theorem B2506513 : Blo 2227435 2506513 := bbase (se 2 (by rfl) ⟨939942, by rfl⟩ : syracuseStep 2506513 = 1879885) (by norm_num)
theorem B3342017 : Blo 2227435 3342017 := bstep (se 2 (by rfl) ⟨1253256, by rfl⟩ : syracuseStep 3342017 = 2506513) B2506513
theorem B2228011 : Blo 2227435 2228011 := bstep (se 1 (by rfl) ⟨1671008, by rfl⟩ : syracuseStep 2228011 = 3342017) B3342017
theorem B4229749 : Blo 2227435 4229749 := bbase (se 5 (by rfl) ⟨198269, by rfl⟩ : syracuseStep 4229749 = 396539) (by norm_num)
theorem B5639665 : Blo 2227435 5639665 := bstep (se 2 (by rfl) ⟨2114874, by rfl⟩ : syracuseStep 5639665 = 4229749) B4229749
theorem B7519553 : Blo 2227435 7519553 := bstep (se 2 (by rfl) ⟨2819832, by rfl⟩ : syracuseStep 7519553 = 5639665) B5639665
theorem B5013035 : Blo 2227435 5013035 := bstep (se 1 (by rfl) ⟨3759776, by rfl⟩ : syracuseStep 5013035 = 7519553) B7519553
theorem B3342023 : Blo 2227435 3342023 := bstep (se 1 (by rfl) ⟨2506517, by rfl⟩ : syracuseStep 3342023 = 5013035) B5013035
theorem B2228015 : Blo 2227435 2228015 := bstep (se 1 (by rfl) ⟨1671011, by rfl⟩ : syracuseStep 2228015 = 3342023) B3342023
theorem B3342029 : Blo 2227435 3342029 := bbase (se 3 (by rfl) ⟨626630, by rfl⟩ : syracuseStep 3342029 = 1253261) (by norm_num)
theorem B2228019 : Blo 2227435 2228019 := bstep (se 1 (by rfl) ⟨1671014, by rfl⟩ : syracuseStep 2228019 = 3342029) B3342029
theorem B5013053 : Blo 2227435 5013053 := bbase (se 3 (by rfl) ⟨939947, by rfl⟩ : syracuseStep 5013053 = 1879895) (by norm_num)
theorem B3342035 : Blo 2227435 3342035 := bstep (se 1 (by rfl) ⟨2506526, by rfl⟩ : syracuseStep 3342035 = 5013053) B5013053
theorem B2228023 : Blo 2227435 2228023 := bstep (se 1 (by rfl) ⟨1671017, by rfl⟩ : syracuseStep 2228023 = 3342035) B3342035
theorem B3759797 : Blo 2227435 3759797 := bbase (se 5 (by rfl) ⟨176240, by rfl⟩ : syracuseStep 3759797 = 352481) (by norm_num)
theorem B2506531 : Blo 2227435 2506531 := bstep (se 1 (by rfl) ⟨1879898, by rfl⟩ : syracuseStep 2506531 = 3759797) B3759797
theorem B3342041 : Blo 2227435 3342041 := bstep (se 2 (by rfl) ⟨1253265, by rfl⟩ : syracuseStep 3342041 = 2506531) B2506531
theorem B2228027 : Blo 2227435 2228027 := bstep (se 1 (by rfl) ⟨1671020, by rfl⟩ : syracuseStep 2228027 = 3342041) B3342041
theorem B3568877 : Blo 2227435 3568877 := bbase (se 3 (by rfl) ⟨669164, by rfl⟩ : syracuseStep 3568877 = 1338329) (by norm_num)
theorem B2379251 : Blo 2227435 2379251 := bstep (se 1 (by rfl) ⟨1784438, by rfl⟩ : syracuseStep 2379251 = 3568877) B3568877
theorem B6344669 : Blo 2227435 6344669 := bstep (se 3 (by rfl) ⟨1189625, by rfl⟩ : syracuseStep 6344669 = 2379251) B2379251
theorem B16919117 : Blo 2227435 16919117 := bstep (se 3 (by rfl) ⟨3172334, by rfl⟩ : syracuseStep 16919117 = 6344669) B6344669
theorem B11279411 : Blo 2227435 11279411 := bstep (se 1 (by rfl) ⟨8459558, by rfl⟩ : syracuseStep 11279411 = 16919117) B16919117
theorem B7519607 : Blo 2227435 7519607 := bstep (se 1 (by rfl) ⟨5639705, by rfl⟩ : syracuseStep 7519607 = 11279411) B11279411
theorem B5013071 : Blo 2227435 5013071 := bstep (se 1 (by rfl) ⟨3759803, by rfl⟩ : syracuseStep 5013071 = 7519607) B7519607
theorem B3342047 : Blo 2227435 3342047 := bstep (se 1 (by rfl) ⟨2506535, by rfl⟩ : syracuseStep 3342047 = 5013071) B5013071
theorem B2228031 : Blo 2227435 2228031 := bstep (se 1 (by rfl) ⟨1671023, by rfl⟩ : syracuseStep 2228031 = 3342047) B3342047
theorem B3342053 : Blo 2227435 3342053 := bbase (se 4 (by rfl) ⟨313317, by rfl⟩ : syracuseStep 3342053 = 626635) (by norm_num)
theorem B2228035 : Blo 2227435 2228035 := bstep (se 1 (by rfl) ⟨1671026, by rfl⟩ : syracuseStep 2228035 = 3342053) B3342053
theorem B6344693 : Blo 2227435 6344693 := bbase (se 5 (by rfl) ⟨297407, by rfl⟩ : syracuseStep 6344693 = 594815) (by norm_num)
theorem B4229795 : Blo 2227435 4229795 := bstep (se 1 (by rfl) ⟨3172346, by rfl⟩ : syracuseStep 4229795 = 6344693) B6344693
theorem B2819863 : Blo 2227435 2819863 := bstep (se 1 (by rfl) ⟨2114897, by rfl⟩ : syracuseStep 2819863 = 4229795) B4229795
theorem B3759817 : Blo 2227435 3759817 := bstep (se 2 (by rfl) ⟨1409931, by rfl⟩ : syracuseStep 3759817 = 2819863) B2819863
theorem B5013089 : Blo 2227435 5013089 := bstep (se 2 (by rfl) ⟨1879908, by rfl⟩ : syracuseStep 5013089 = 3759817) B3759817
theorem B3342059 : Blo 2227435 3342059 := bstep (se 1 (by rfl) ⟨2506544, by rfl⟩ : syracuseStep 3342059 = 5013089) B5013089
theorem B2228039 : Blo 2227435 2228039 := bstep (se 1 (by rfl) ⟨1671029, by rfl⟩ : syracuseStep 2228039 = 3342059) B3342059
theorem B2506549 : Blo 2227435 2506549 := bbase (se 5 (by rfl) ⟨117494, by rfl⟩ : syracuseStep 2506549 = 234989) (by norm_num)
theorem B3342065 : Blo 2227435 3342065 := bstep (se 2 (by rfl) ⟨1253274, by rfl⟩ : syracuseStep 3342065 = 2506549) B2506549
theorem B2228043 : Blo 2227435 2228043 := bstep (se 1 (by rfl) ⟨1671032, by rfl⟩ : syracuseStep 2228043 = 3342065) B3342065
theorem B2819873 : Blo 2227435 2819873 := bbase (se 2 (by rfl) ⟨1057452, by rfl⟩ : syracuseStep 2819873 = 2114905) (by norm_num)
theorem B7519661 : Blo 2227435 7519661 := bstep (se 3 (by rfl) ⟨1409936, by rfl⟩ : syracuseStep 7519661 = 2819873) B2819873
theorem B5013107 : Blo 2227435 5013107 := bstep (se 1 (by rfl) ⟨3759830, by rfl⟩ : syracuseStep 5013107 = 7519661) B7519661
theorem B3342071 : Blo 2227435 3342071 := bstep (se 1 (by rfl) ⟨2506553, by rfl⟩ : syracuseStep 3342071 = 5013107) B5013107
theorem B2228047 : Blo 2227435 2228047 := bstep (se 1 (by rfl) ⟨1671035, by rfl⟩ : syracuseStep 2228047 = 3342071) B3342071
theorem B3342077 : Blo 2227435 3342077 := bbase (se 3 (by rfl) ⟨626639, by rfl⟩ : syracuseStep 3342077 = 1253279) (by norm_num)
theorem B2228051 : Blo 2227435 2228051 := bstep (se 1 (by rfl) ⟨1671038, by rfl⟩ : syracuseStep 2228051 = 3342077) B3342077
theorem B5013125 : Blo 2227435 5013125 := bbase (se 4 (by rfl) ⟨469980, by rfl⟩ : syracuseStep 5013125 = 939961) (by norm_num)
theorem B3342083 : Blo 2227435 3342083 := bstep (se 1 (by rfl) ⟨2506562, by rfl⟩ : syracuseStep 3342083 = 5013125) B5013125
theorem B2228055 : Blo 2227435 2228055 := bstep (se 1 (by rfl) ⟨1671041, by rfl⟩ : syracuseStep 2228055 = 3342083) B3342083
theorem B7137845 : Blo 2227435 7137845 := bbase (se 5 (by rfl) ⟨334586, by rfl⟩ : syracuseStep 7137845 = 669173) (by norm_num)
theorem B4758563 : Blo 2227435 4758563 := bstep (se 1 (by rfl) ⟨3568922, by rfl⟩ : syracuseStep 4758563 = 7137845) B7137845
theorem B3172375 : Blo 2227435 3172375 := bstep (se 1 (by rfl) ⟨2379281, by rfl⟩ : syracuseStep 3172375 = 4758563) B4758563
theorem B4229833 : Blo 2227435 4229833 := bstep (se 2 (by rfl) ⟨1586187, by rfl⟩ : syracuseStep 4229833 = 3172375) B3172375
theorem B5639777 : Blo 2227435 5639777 := bstep (se 2 (by rfl) ⟨2114916, by rfl⟩ : syracuseStep 5639777 = 4229833) B4229833
theorem B3759851 : Blo 2227435 3759851 := bstep (se 1 (by rfl) ⟨2819888, by rfl⟩ : syracuseStep 3759851 = 5639777) B5639777
theorem B2506567 : Blo 2227435 2506567 := bstep (se 1 (by rfl) ⟨1879925, by rfl⟩ : syracuseStep 2506567 = 3759851) B3759851
theorem B3342089 : Blo 2227435 3342089 := bstep (se 2 (by rfl) ⟨1253283, by rfl⟩ : syracuseStep 3342089 = 2506567) B2506567
theorem B2228059 : Blo 2227435 2228059 := bstep (se 1 (by rfl) ⟨1671044, by rfl⟩ : syracuseStep 2228059 = 3342089) B3342089
theorem B11279573 : Blo 2227435 11279573 := bbase (se 7 (by rfl) ⟨132182, by rfl⟩ : syracuseStep 11279573 = 264365) (by norm_num)
theorem B7519715 : Blo 2227435 7519715 := bstep (se 1 (by rfl) ⟨5639786, by rfl⟩ : syracuseStep 7519715 = 11279573) B11279573
theorem B5013143 : Blo 2227435 5013143 := bstep (se 1 (by rfl) ⟨3759857, by rfl⟩ : syracuseStep 5013143 = 7519715) B7519715
theorem B3342095 : Blo 2227435 3342095 := bstep (se 1 (by rfl) ⟨2506571, by rfl⟩ : syracuseStep 3342095 = 5013143) B5013143
theorem B2228063 : Blo 2227435 2228063 := bstep (se 1 (by rfl) ⟨1671047, by rfl⟩ : syracuseStep 2228063 = 3342095) B3342095
theorem B3342101 : Blo 2227435 3342101 := bbase (se 6 (by rfl) ⟨78330, by rfl⟩ : syracuseStep 3342101 = 156661) (by norm_num)
theorem B2228067 : Blo 2227435 2228067 := bstep (se 1 (by rfl) ⟨1671050, by rfl⟩ : syracuseStep 2228067 = 3342101) B3342101
theorem B23178997 : Blo 2227435 23178997 := bbase (se 5 (by rfl) ⟨1086515, by rfl⟩ : syracuseStep 23178997 = 2173031) (by norm_num)
theorem B30905329 : Blo 2227435 30905329 := bstep (se 2 (by rfl) ⟨11589498, by rfl⟩ : syracuseStep 30905329 = 23178997) B23178997
theorem B41207105 : Blo 2227435 41207105 := bstep (se 2 (by rfl) ⟨15452664, by rfl⟩ : syracuseStep 41207105 = 30905329) B30905329
theorem B27471403 : Blo 2227435 27471403 := bstep (se 1 (by rfl) ⟨20603552, by rfl⟩ : syracuseStep 27471403 = 41207105) B41207105
theorem B36628537 : Blo 2227435 36628537 := bstep (se 2 (by rfl) ⟨13735701, by rfl⟩ : syracuseStep 36628537 = 27471403) B27471403
theorem B48838049 : Blo 2227435 48838049 := bstep (se 2 (by rfl) ⟨18314268, by rfl⟩ : syracuseStep 48838049 = 36628537) B36628537
theorem B32558699 : Blo 2227435 32558699 := bstep (se 1 (by rfl) ⟨24419024, by rfl⟩ : syracuseStep 32558699 = 48838049) B48838049
theorem B21705799 : Blo 2227435 21705799 := bstep (se 1 (by rfl) ⟨16279349, by rfl⟩ : syracuseStep 21705799 = 32558699) B32558699
theorem B28941065 : Blo 2227435 28941065 := bstep (se 2 (by rfl) ⟨10852899, by rfl⟩ : syracuseStep 28941065 = 21705799) B21705799
theorem B19294043 : Blo 2227435 19294043 := bstep (se 1 (by rfl) ⟨14470532, by rfl⟩ : syracuseStep 19294043 = 28941065) B28941065
theorem B205803125 : Blo 2227435 205803125 := bstep (se 5 (by rfl) ⟨9647021, by rfl⟩ : syracuseStep 205803125 = 19294043) B19294043
theorem B137202083 : Blo 2227435 137202083 := bstep (se 1 (by rfl) ⟨102901562, by rfl⟩ : syracuseStep 137202083 = 205803125) B205803125
theorem B91468055 : Blo 2227435 91468055 := bstep (se 1 (by rfl) ⟨68601041, by rfl⟩ : syracuseStep 91468055 = 137202083) B137202083
theorem B243914813 : Blo 2227435 243914813 := bstep (se 3 (by rfl) ⟨45734027, by rfl⟩ : syracuseStep 243914813 = 91468055) B91468055
theorem B162609875 : Blo 2227435 162609875 := bstep (se 1 (by rfl) ⟨121957406, by rfl⟩ : syracuseStep 162609875 = 243914813) B243914813
theorem B108406583 : Blo 2227435 108406583 := bstep (se 1 (by rfl) ⟨81304937, by rfl⟩ : syracuseStep 108406583 = 162609875) B162609875
theorem B72271055 : Blo 2227435 72271055 := bstep (se 1 (by rfl) ⟨54203291, by rfl⟩ : syracuseStep 72271055 = 108406583) B108406583
theorem B48180703 : Blo 2227435 48180703 := bstep (se 1 (by rfl) ⟨36135527, by rfl⟩ : syracuseStep 48180703 = 72271055) B72271055
theorem B64240937 : Blo 2227435 64240937 := bstep (se 2 (by rfl) ⟨24090351, by rfl⟩ : syracuseStep 64240937 = 48180703) B48180703
theorem B42827291 : Blo 2227435 42827291 := bstep (se 1 (by rfl) ⟨32120468, by rfl⟩ : syracuseStep 42827291 = 64240937) B64240937
theorem B28551527 : Blo 2227435 28551527 := bstep (se 1 (by rfl) ⟨21413645, by rfl⟩ : syracuseStep 28551527 = 42827291) B42827291
theorem B19034351 : Blo 2227435 19034351 := bstep (se 1 (by rfl) ⟨14275763, by rfl⟩ : syracuseStep 19034351 = 28551527) B28551527
theorem B12689567 : Blo 2227435 12689567 := bstep (se 1 (by rfl) ⟨9517175, by rfl⟩ : syracuseStep 12689567 = 19034351) B19034351
theorem B8459711 : Blo 2227435 8459711 := bstep (se 1 (by rfl) ⟨6344783, by rfl⟩ : syracuseStep 8459711 = 12689567) B12689567
theorem B5639807 : Blo 2227435 5639807 := bstep (se 1 (by rfl) ⟨4229855, by rfl⟩ : syracuseStep 5639807 = 8459711) B8459711
theorem B3759871 : Blo 2227435 3759871 := bstep (se 1 (by rfl) ⟨2819903, by rfl⟩ : syracuseStep 3759871 = 5639807) B5639807
theorem B5013161 : Blo 2227435 5013161 := bstep (se 2 (by rfl) ⟨1879935, by rfl⟩ : syracuseStep 5013161 = 3759871) B3759871
theorem B3342107 : Blo 2227435 3342107 := bstep (se 1 (by rfl) ⟨2506580, by rfl⟩ : syracuseStep 3342107 = 5013161) B5013161
theorem B2228071 : Blo 2227435 2228071 := bstep (se 1 (by rfl) ⟨1671053, by rfl⟩ : syracuseStep 2228071 = 3342107) B3342107
theorem B2506585 : Blo 2227435 2506585 := bbase (se 2 (by rfl) ⟨939969, by rfl⟩ : syracuseStep 2506585 = 1879939) (by norm_num)
theorem B3342113 : Blo 2227435 3342113 := bstep (se 2 (by rfl) ⟨1253292, by rfl⟩ : syracuseStep 3342113 = 2506585) B2506585
theorem B2228075 : Blo 2227435 2228075 := bstep (se 1 (by rfl) ⟨1671056, by rfl⟩ : syracuseStep 2228075 = 3342113) B3342113
theorem B4758605 : Blo 2227435 4758605 := bbase (se 3 (by rfl) ⟨892238, by rfl⟩ : syracuseStep 4758605 = 1784477) (by norm_num)
theorem B3172403 : Blo 2227435 3172403 := bstep (se 1 (by rfl) ⟨2379302, by rfl⟩ : syracuseStep 3172403 = 4758605) B4758605
theorem B8459741 : Blo 2227435 8459741 := bstep (se 3 (by rfl) ⟨1586201, by rfl⟩ : syracuseStep 8459741 = 3172403) B3172403
theorem B5639827 : Blo 2227435 5639827 := bstep (se 1 (by rfl) ⟨4229870, by rfl⟩ : syracuseStep 5639827 = 8459741) B8459741
theorem B7519769 : Blo 2227435 7519769 := bstep (se 2 (by rfl) ⟨2819913, by rfl⟩ : syracuseStep 7519769 = 5639827) B5639827
theorem B5013179 : Blo 2227435 5013179 := bstep (se 1 (by rfl) ⟨3759884, by rfl⟩ : syracuseStep 5013179 = 7519769) B7519769
theorem B3342119 : Blo 2227435 3342119 := bstep (se 1 (by rfl) ⟨2506589, by rfl⟩ : syracuseStep 3342119 = 5013179) B5013179
theorem B2228079 : Blo 2227435 2228079 := bstep (se 1 (by rfl) ⟨1671059, by rfl⟩ : syracuseStep 2228079 = 3342119) B3342119
theorem B3342125 : Blo 2227435 3342125 := bbase (se 3 (by rfl) ⟨626648, by rfl⟩ : syracuseStep 3342125 = 1253297) (by norm_num)
theorem B2228083 : Blo 2227435 2228083 := bstep (se 1 (by rfl) ⟨1671062, by rfl⟩ : syracuseStep 2228083 = 3342125) B3342125
theorem B5013197 : Blo 2227435 5013197 := bbase (se 3 (by rfl) ⟨939974, by rfl⟩ : syracuseStep 5013197 = 1879949) (by norm_num)
theorem B3342131 : Blo 2227435 3342131 := bstep (se 1 (by rfl) ⟨2506598, by rfl⟩ : syracuseStep 3342131 = 5013197) B5013197
theorem B2228087 : Blo 2227435 2228087 := bstep (se 1 (by rfl) ⟨1671065, by rfl⟩ : syracuseStep 2228087 = 3342131) B3342131
theorem B2819929 : Blo 2227435 2819929 := bbase (se 2 (by rfl) ⟨1057473, by rfl⟩ : syracuseStep 2819929 = 2114947) (by norm_num)
theorem B3759905 : Blo 2227435 3759905 := bstep (se 2 (by rfl) ⟨1409964, by rfl⟩ : syracuseStep 3759905 = 2819929) B2819929
theorem B2506603 : Blo 2227435 2506603 := bstep (se 1 (by rfl) ⟨1879952, by rfl⟩ : syracuseStep 2506603 = 3759905) B3759905
theorem B3342137 : Blo 2227435 3342137 := bstep (se 2 (by rfl) ⟨1253301, by rfl⟩ : syracuseStep 3342137 = 2506603) B2506603
theorem B2228091 : Blo 2227435 2228091 := bstep (se 1 (by rfl) ⟨1671068, by rfl⟩ : syracuseStep 2228091 = 3342137) B3342137
theorem B5353469 : Blo 2227435 5353469 := bbase (se 3 (by rfl) ⟨1003775, by rfl⟩ : syracuseStep 5353469 = 2007551) (by norm_num)
theorem B3568979 : Blo 2227435 3568979 := bstep (se 1 (by rfl) ⟨2676734, by rfl⟩ : syracuseStep 3568979 = 5353469) B5353469
theorem B9517277 : Blo 2227435 9517277 := bstep (se 3 (by rfl) ⟨1784489, by rfl⟩ : syracuseStep 9517277 = 3568979) B3568979
theorem B25379405 : Blo 2227435 25379405 := bstep (se 3 (by rfl) ⟨4758638, by rfl⟩ : syracuseStep 25379405 = 9517277) B9517277
theorem B16919603 : Blo 2227435 16919603 := bstep (se 1 (by rfl) ⟨12689702, by rfl⟩ : syracuseStep 16919603 = 25379405) B25379405
theorem B11279735 : Blo 2227435 11279735 := bstep (se 1 (by rfl) ⟨8459801, by rfl⟩ : syracuseStep 11279735 = 16919603) B16919603
theorem B7519823 : Blo 2227435 7519823 := bstep (se 1 (by rfl) ⟨5639867, by rfl⟩ : syracuseStep 7519823 = 11279735) B11279735
theorem B5013215 : Blo 2227435 5013215 := bstep (se 1 (by rfl) ⟨3759911, by rfl⟩ : syracuseStep 5013215 = 7519823) B7519823
theorem B3342143 : Blo 2227435 3342143 := bstep (se 1 (by rfl) ⟨2506607, by rfl⟩ : syracuseStep 3342143 = 5013215) B5013215
theorem B2228095 : Blo 2227435 2228095 := bstep (se 1 (by rfl) ⟨1671071, by rfl⟩ : syracuseStep 2228095 = 3342143) B3342143
theorem B3342149 : Blo 2227435 3342149 := bbase (se 4 (by rfl) ⟨313326, by rfl⟩ : syracuseStep 3342149 = 626653) (by norm_num)
theorem B2228099 : Blo 2227435 2228099 := bstep (se 1 (by rfl) ⟨1671074, by rfl⟩ : syracuseStep 2228099 = 3342149) B3342149
theorem B3759925 : Blo 2227435 3759925 := bbase (se 5 (by rfl) ⟨176246, by rfl⟩ : syracuseStep 3759925 = 352493) (by norm_num)
theorem B5013233 : Blo 2227435 5013233 := bstep (se 2 (by rfl) ⟨1879962, by rfl⟩ : syracuseStep 5013233 = 3759925) B3759925
theorem B3342155 : Blo 2227435 3342155 := bstep (se 1 (by rfl) ⟨2506616, by rfl⟩ : syracuseStep 3342155 = 5013233) B5013233
theorem B2228103 : Blo 2227435 2228103 := bstep (se 1 (by rfl) ⟨1671077, by rfl⟩ : syracuseStep 2228103 = 3342155) B3342155
theorem B2506621 : Blo 2227435 2506621 := bbase (se 3 (by rfl) ⟨469991, by rfl⟩ : syracuseStep 2506621 = 939983) (by norm_num)
theorem B3342161 : Blo 2227435 3342161 := bstep (se 2 (by rfl) ⟨1253310, by rfl⟩ : syracuseStep 3342161 = 2506621) B2506621
theorem B2228107 : Blo 2227435 2228107 := bstep (se 1 (by rfl) ⟨1671080, by rfl⟩ : syracuseStep 2228107 = 3342161) B3342161
theorem B7519877 : Blo 2227435 7519877 := bbase (se 4 (by rfl) ⟨704988, by rfl⟩ : syracuseStep 7519877 = 1409977) (by norm_num)
theorem B5013251 : Blo 2227435 5013251 := bstep (se 1 (by rfl) ⟨3759938, by rfl⟩ : syracuseStep 5013251 = 7519877) B7519877
theorem B3342167 : Blo 2227435 3342167 := bstep (se 1 (by rfl) ⟨2506625, by rfl⟩ : syracuseStep 3342167 = 5013251) B5013251
theorem B2228111 : Blo 2227435 2228111 := bstep (se 1 (by rfl) ⟨1671083, by rfl⟩ : syracuseStep 2228111 = 3342167) B3342167
theorem B3342173 : Blo 2227435 3342173 := bbase (se 3 (by rfl) ⟨626657, by rfl⟩ : syracuseStep 3342173 = 1253315) (by norm_num)
theorem B2228115 : Blo 2227435 2228115 := bstep (se 1 (by rfl) ⟨1671086, by rfl⟩ : syracuseStep 2228115 = 3342173) B3342173
theorem B5013269 : Blo 2227435 5013269 := bbase (se 6 (by rfl) ⟨117498, by rfl⟩ : syracuseStep 5013269 = 234997) (by norm_num)
theorem B3342179 : Blo 2227435 3342179 := bstep (se 1 (by rfl) ⟨2506634, by rfl⟩ : syracuseStep 3342179 = 5013269) B5013269
theorem B2228119 : Blo 2227435 2228119 := bstep (se 1 (by rfl) ⟨1671089, by rfl⟩ : syracuseStep 2228119 = 3342179) B3342179
theorem B8459909 : Blo 2227435 8459909 := bbase (se 4 (by rfl) ⟨793116, by rfl⟩ : syracuseStep 8459909 = 1586233) (by norm_num)
theorem B5639939 : Blo 2227435 5639939 := bstep (se 1 (by rfl) ⟨4229954, by rfl⟩ : syracuseStep 5639939 = 8459909) B8459909
theorem B3759959 : Blo 2227435 3759959 := bstep (se 1 (by rfl) ⟨2819969, by rfl⟩ : syracuseStep 3759959 = 5639939) B5639939
theorem B2506639 : Blo 2227435 2506639 := bstep (se 1 (by rfl) ⟨1879979, by rfl⟩ : syracuseStep 2506639 = 3759959) B3759959
theorem B3342185 : Blo 2227435 3342185 := bstep (se 2 (by rfl) ⟨1253319, by rfl⟩ : syracuseStep 3342185 = 2506639) B2506639
theorem B2228123 : Blo 2227435 2228123 := bstep (se 1 (by rfl) ⟨1671092, by rfl⟩ : syracuseStep 2228123 = 3342185) B3342185
theorem B2676773 : Blo 2227435 2676773 := bbase (se 4 (by rfl) ⟨250947, by rfl⟩ : syracuseStep 2676773 = 501895) (by norm_num)
theorem B7138061 : Blo 2227435 7138061 := bstep (se 3 (by rfl) ⟨1338386, by rfl⟩ : syracuseStep 7138061 = 2676773) B2676773
theorem B4758707 : Blo 2227435 4758707 := bstep (se 1 (by rfl) ⟨3569030, by rfl⟩ : syracuseStep 4758707 = 7138061) B7138061
theorem B12689885 : Blo 2227435 12689885 := bstep (se 3 (by rfl) ⟨2379353, by rfl⟩ : syracuseStep 12689885 = 4758707) B4758707
theorem B8459923 : Blo 2227435 8459923 := bstep (se 1 (by rfl) ⟨6344942, by rfl⟩ : syracuseStep 8459923 = 12689885) B12689885
theorem B11279897 : Blo 2227435 11279897 := bstep (se 2 (by rfl) ⟨4229961, by rfl⟩ : syracuseStep 11279897 = 8459923) B8459923
theorem B7519931 : Blo 2227435 7519931 := bstep (se 1 (by rfl) ⟨5639948, by rfl⟩ : syracuseStep 7519931 = 11279897) B11279897
theorem B5013287 : Blo 2227435 5013287 := bstep (se 1 (by rfl) ⟨3759965, by rfl⟩ : syracuseStep 5013287 = 7519931) B7519931
theorem B3342191 : Blo 2227435 3342191 := bstep (se 1 (by rfl) ⟨2506643, by rfl⟩ : syracuseStep 3342191 = 5013287) B5013287
theorem B2228127 : Blo 2227435 2228127 := bstep (se 1 (by rfl) ⟨1671095, by rfl⟩ : syracuseStep 2228127 = 3342191) B3342191
theorem B3342197 : Blo 2227435 3342197 := bbase (se 5 (by rfl) ⟨156665, by rfl⟩ : syracuseStep 3342197 = 313331) (by norm_num)
theorem B2228131 : Blo 2227435 2228131 := bstep (se 1 (by rfl) ⟨1671098, by rfl⟩ : syracuseStep 2228131 = 3342197) B3342197
theorem B4758725 : Blo 2227435 4758725 := bbase (se 4 (by rfl) ⟨446130, by rfl⟩ : syracuseStep 4758725 = 892261) (by norm_num)
theorem B3172483 : Blo 2227435 3172483 := bstep (se 1 (by rfl) ⟨2379362, by rfl⟩ : syracuseStep 3172483 = 4758725) B4758725
theorem B4229977 : Blo 2227435 4229977 := bstep (se 2 (by rfl) ⟨1586241, by rfl⟩ : syracuseStep 4229977 = 3172483) B3172483
theorem B5639969 : Blo 2227435 5639969 := bstep (se 2 (by rfl) ⟨2114988, by rfl⟩ : syracuseStep 5639969 = 4229977) B4229977
theorem B3759979 : Blo 2227435 3759979 := bstep (se 1 (by rfl) ⟨2819984, by rfl⟩ : syracuseStep 3759979 = 5639969) B5639969
theorem B5013305 : Blo 2227435 5013305 := bstep (se 2 (by rfl) ⟨1879989, by rfl⟩ : syracuseStep 5013305 = 3759979) B3759979
theorem B3342203 : Blo 2227435 3342203 := bstep (se 1 (by rfl) ⟨2506652, by rfl⟩ : syracuseStep 3342203 = 5013305) B5013305
theorem B2228135 : Blo 2227435 2228135 := bstep (se 1 (by rfl) ⟨1671101, by rfl⟩ : syracuseStep 2228135 = 3342203) B3342203
theorem B2506657 : Blo 2227435 2506657 := bbase (se 2 (by rfl) ⟨939996, by rfl⟩ : syracuseStep 2506657 = 1879993) (by norm_num)
theorem B3342209 : Blo 2227435 3342209 := bstep (se 2 (by rfl) ⟨1253328, by rfl⟩ : syracuseStep 3342209 = 2506657) B2506657
theorem B2228139 : Blo 2227435 2228139 := bstep (se 1 (by rfl) ⟨1671104, by rfl⟩ : syracuseStep 2228139 = 3342209) B3342209
theorem B5639989 : Blo 2227435 5639989 := bbase (se 5 (by rfl) ⟨264374, by rfl⟩ : syracuseStep 5639989 = 528749) (by norm_num)
theorem B7519985 : Blo 2227435 7519985 := bstep (se 2 (by rfl) ⟨2819994, by rfl⟩ : syracuseStep 7519985 = 5639989) B5639989
theorem B5013323 : Blo 2227435 5013323 := bstep (se 1 (by rfl) ⟨3759992, by rfl⟩ : syracuseStep 5013323 = 7519985) B7519985
theorem B3342215 : Blo 2227435 3342215 := bstep (se 1 (by rfl) ⟨2506661, by rfl⟩ : syracuseStep 3342215 = 5013323) B5013323
theorem B2228143 : Blo 2227435 2228143 := bstep (se 1 (by rfl) ⟨1671107, by rfl⟩ : syracuseStep 2228143 = 3342215) B3342215
theorem B3342221 : Blo 2227435 3342221 := bbase (se 3 (by rfl) ⟨626666, by rfl⟩ : syracuseStep 3342221 = 1253333) (by norm_num)
theorem B2228147 : Blo 2227435 2228147 := bstep (se 1 (by rfl) ⟨1671110, by rfl⟩ : syracuseStep 2228147 = 3342221) B3342221
theorem B5013341 : Blo 2227435 5013341 := bbase (se 3 (by rfl) ⟨940001, by rfl⟩ : syracuseStep 5013341 = 1880003) (by norm_num)
theorem B3342227 : Blo 2227435 3342227 := bstep (se 1 (by rfl) ⟨2506670, by rfl⟩ : syracuseStep 3342227 = 5013341) B5013341
theorem B2228151 : Blo 2227435 2228151 := bstep (se 1 (by rfl) ⟨1671113, by rfl⟩ : syracuseStep 2228151 = 3342227) B3342227
theorem B3760013 : Blo 2227435 3760013 := bbase (se 3 (by rfl) ⟨705002, by rfl⟩ : syracuseStep 3760013 = 1410005) (by norm_num)
theorem B2506675 : Blo 2227435 2506675 := bstep (se 1 (by rfl) ⟨1880006, by rfl⟩ : syracuseStep 2506675 = 3760013) B3760013
theorem B3342233 : Blo 2227435 3342233 := bstep (se 2 (by rfl) ⟨1253337, by rfl⟩ : syracuseStep 3342233 = 2506675) B2506675
theorem B2228155 : Blo 2227435 2228155 := bstep (se 1 (by rfl) ⟨1671116, by rfl⟩ : syracuseStep 2228155 = 3342233) B3342233
theorem B3011413 : Blo 2227435 3011413 := bbase (se 9 (by rfl) ⟨8822, by rfl⟩ : syracuseStep 3011413 = 17645) (by norm_num)
theorem B4015217 : Blo 2227435 4015217 := bstep (se 2 (by rfl) ⟨1505706, by rfl⟩ : syracuseStep 4015217 = 3011413) B3011413
theorem B10707245 : Blo 2227435 10707245 := bstep (se 3 (by rfl) ⟨2007608, by rfl⟩ : syracuseStep 10707245 = 4015217) B4015217
theorem B7138163 : Blo 2227435 7138163 := bstep (se 1 (by rfl) ⟨5353622, by rfl⟩ : syracuseStep 7138163 = 10707245) B10707245
theorem B19035101 : Blo 2227435 19035101 := bstep (se 3 (by rfl) ⟨3569081, by rfl⟩ : syracuseStep 19035101 = 7138163) B7138163
theorem B12690067 : Blo 2227435 12690067 := bstep (se 1 (by rfl) ⟨9517550, by rfl⟩ : syracuseStep 12690067 = 19035101) B19035101
theorem B16920089 : Blo 2227435 16920089 := bstep (se 2 (by rfl) ⟨6345033, by rfl⟩ : syracuseStep 16920089 = 12690067) B12690067
theorem B11280059 : Blo 2227435 11280059 := bstep (se 1 (by rfl) ⟨8460044, by rfl⟩ : syracuseStep 11280059 = 16920089) B16920089
theorem B7520039 : Blo 2227435 7520039 := bstep (se 1 (by rfl) ⟨5640029, by rfl⟩ : syracuseStep 7520039 = 11280059) B11280059
theorem B5013359 : Blo 2227435 5013359 := bstep (se 1 (by rfl) ⟨3760019, by rfl⟩ : syracuseStep 5013359 = 7520039) B7520039
theorem B3342239 : Blo 2227435 3342239 := bstep (se 1 (by rfl) ⟨2506679, by rfl⟩ : syracuseStep 3342239 = 5013359) B5013359
theorem B2228159 : Blo 2227435 2228159 := bstep (se 1 (by rfl) ⟨1671119, by rfl⟩ : syracuseStep 2228159 = 3342239) B3342239
theorem B3342245 : Blo 2227435 3342245 := bbase (se 4 (by rfl) ⟨313335, by rfl⟩ : syracuseStep 3342245 = 626671) (by norm_num)
theorem B2228163 : Blo 2227435 2228163 := bstep (se 1 (by rfl) ⟨1671122, by rfl⟩ : syracuseStep 2228163 = 3342245) B3342245
theorem B2820025 : Blo 2227435 2820025 := bbase (se 2 (by rfl) ⟨1057509, by rfl⟩ : syracuseStep 2820025 = 2115019) (by norm_num)
theorem B3760033 : Blo 2227435 3760033 := bstep (se 2 (by rfl) ⟨1410012, by rfl⟩ : syracuseStep 3760033 = 2820025) B2820025
theorem B5013377 : Blo 2227435 5013377 := bstep (se 2 (by rfl) ⟨1880016, by rfl⟩ : syracuseStep 5013377 = 3760033) B3760033
theorem B3342251 : Blo 2227435 3342251 := bstep (se 1 (by rfl) ⟨2506688, by rfl⟩ : syracuseStep 3342251 = 5013377) B5013377
theorem B2228167 : Blo 2227435 2228167 := bstep (se 1 (by rfl) ⟨1671125, by rfl⟩ : syracuseStep 2228167 = 3342251) B3342251
theorem B2506693 : Blo 2227435 2506693 := bbase (se 4 (by rfl) ⟨235002, by rfl⟩ : syracuseStep 2506693 = 470005) (by norm_num)
theorem B3342257 : Blo 2227435 3342257 := bstep (se 2 (by rfl) ⟨1253346, by rfl⟩ : syracuseStep 3342257 = 2506693) B2506693
theorem B2228171 : Blo 2227435 2228171 := bstep (se 1 (by rfl) ⟨1671128, by rfl⟩ : syracuseStep 2228171 = 3342257) B3342257
theorem B4230053 : Blo 2227435 4230053 := bbase (se 4 (by rfl) ⟨396567, by rfl⟩ : syracuseStep 4230053 = 793135) (by norm_num)
theorem B2820035 : Blo 2227435 2820035 := bstep (se 1 (by rfl) ⟨2115026, by rfl⟩ : syracuseStep 2820035 = 4230053) B4230053
theorem B7520093 : Blo 2227435 7520093 := bstep (se 3 (by rfl) ⟨1410017, by rfl⟩ : syracuseStep 7520093 = 2820035) B2820035
theorem B5013395 : Blo 2227435 5013395 := bstep (se 1 (by rfl) ⟨3760046, by rfl⟩ : syracuseStep 5013395 = 7520093) B7520093
theorem B3342263 : Blo 2227435 3342263 := bstep (se 1 (by rfl) ⟨2506697, by rfl⟩ : syracuseStep 3342263 = 5013395) B5013395
theorem B2228175 : Blo 2227435 2228175 := bstep (se 1 (by rfl) ⟨1671131, by rfl⟩ : syracuseStep 2228175 = 3342263) B3342263
theorem B3342269 : Blo 2227435 3342269 := bbase (se 3 (by rfl) ⟨626675, by rfl⟩ : syracuseStep 3342269 = 1253351) (by norm_num)
theorem B2228179 : Blo 2227435 2228179 := bstep (se 1 (by rfl) ⟨1671134, by rfl⟩ : syracuseStep 2228179 = 3342269) B3342269
theorem B5013413 : Blo 2227435 5013413 := bbase (se 4 (by rfl) ⟨470007, by rfl⟩ : syracuseStep 5013413 = 940015) (by norm_num)
theorem B3342275 : Blo 2227435 3342275 := bstep (se 1 (by rfl) ⟨2506706, by rfl⟩ : syracuseStep 3342275 = 5013413) B5013413
theorem B2228183 : Blo 2227435 2228183 := bstep (se 1 (by rfl) ⟨1671137, by rfl⟩ : syracuseStep 2228183 = 3342275) B3342275
theorem B5640101 : Blo 2227435 5640101 := bbase (se 4 (by rfl) ⟨528759, by rfl⟩ : syracuseStep 5640101 = 1057519) (by norm_num)
theorem B3760067 : Blo 2227435 3760067 := bstep (se 1 (by rfl) ⟨2820050, by rfl⟩ : syracuseStep 3760067 = 5640101) B5640101
theorem B2506711 : Blo 2227435 2506711 := bstep (se 1 (by rfl) ⟨1880033, by rfl⟩ : syracuseStep 2506711 = 3760067) B3760067
theorem B3342281 : Blo 2227435 3342281 := bstep (se 2 (by rfl) ⟨1253355, by rfl⟩ : syracuseStep 3342281 = 2506711) B2506711
theorem B2228187 : Blo 2227435 2228187 := bstep (se 1 (by rfl) ⟨1671140, by rfl⟩ : syracuseStep 2228187 = 3342281) B3342281
theorem B6345125 : Blo 2227435 6345125 := bbase (se 4 (by rfl) ⟨594855, by rfl⟩ : syracuseStep 6345125 = 1189711) (by norm_num)
theorem B4230083 : Blo 2227435 4230083 := bstep (se 1 (by rfl) ⟨3172562, by rfl⟩ : syracuseStep 4230083 = 6345125) B6345125
theorem B11280221 : Blo 2227435 11280221 := bstep (se 3 (by rfl) ⟨2115041, by rfl⟩ : syracuseStep 11280221 = 4230083) B4230083
theorem B7520147 : Blo 2227435 7520147 := bstep (se 1 (by rfl) ⟨5640110, by rfl⟩ : syracuseStep 7520147 = 11280221) B11280221
theorem B5013431 : Blo 2227435 5013431 := bstep (se 1 (by rfl) ⟨3760073, by rfl⟩ : syracuseStep 5013431 = 7520147) B7520147
theorem B3342287 : Blo 2227435 3342287 := bstep (se 1 (by rfl) ⟨2506715, by rfl⟩ : syracuseStep 3342287 = 5013431) B5013431
theorem B2228191 : Blo 2227435 2228191 := bstep (se 1 (by rfl) ⟨1671143, by rfl⟩ : syracuseStep 2228191 = 3342287) B3342287
theorem B3342293 : Blo 2227435 3342293 := bbase (se 7 (by rfl) ⟨39167, by rfl⟩ : syracuseStep 3342293 = 78335) (by norm_num)
theorem B2228195 : Blo 2227435 2228195 := bstep (se 1 (by rfl) ⟨1671146, by rfl⟩ : syracuseStep 2228195 = 3342293) B3342293
theorem B8460197 : Blo 2227435 8460197 := bbase (se 4 (by rfl) ⟨793143, by rfl⟩ : syracuseStep 8460197 = 1586287) (by norm_num)
theorem B5640131 : Blo 2227435 5640131 := bstep (se 1 (by rfl) ⟨4230098, by rfl⟩ : syracuseStep 5640131 = 8460197) B8460197
theorem B3760087 : Blo 2227435 3760087 := bstep (se 1 (by rfl) ⟨2820065, by rfl⟩ : syracuseStep 3760087 = 5640131) B5640131
theorem B5013449 : Blo 2227435 5013449 := bstep (se 2 (by rfl) ⟨1880043, by rfl⟩ : syracuseStep 5013449 = 3760087) B3760087
theorem B3342299 : Blo 2227435 3342299 := bstep (se 1 (by rfl) ⟨2506724, by rfl⟩ : syracuseStep 3342299 = 5013449) B5013449
theorem B2228199 : Blo 2227435 2228199 := bstep (se 1 (by rfl) ⟨1671149, by rfl⟩ : syracuseStep 2228199 = 3342299) B3342299
theorem B2506729 : Blo 2227435 2506729 := bbase (se 2 (by rfl) ⟨940023, by rfl⟩ : syracuseStep 2506729 = 1880047) (by norm_num)
theorem B3342305 : Blo 2227435 3342305 := bstep (se 2 (by rfl) ⟨1253364, by rfl⟩ : syracuseStep 3342305 = 2506729) B2506729
theorem B2228203 : Blo 2227435 2228203 := bstep (se 1 (by rfl) ⟨1671152, by rfl⟩ : syracuseStep 2228203 = 3342305) B3342305
theorem B2258609 : Blo 2227435 2258609 := bbase (se 2 (by rfl) ⟨846978, by rfl⟩ : syracuseStep 2258609 = 1693957) (by norm_num)
theorem B6022957 : Blo 2227435 6022957 := bstep (se 3 (by rfl) ⟨1129304, by rfl⟩ : syracuseStep 6022957 = 2258609) B2258609
theorem B8030609 : Blo 2227435 8030609 := bstep (se 2 (by rfl) ⟨3011478, by rfl⟩ : syracuseStep 8030609 = 6022957) B6022957
theorem B5353739 : Blo 2227435 5353739 := bstep (se 1 (by rfl) ⟨4015304, by rfl⟩ : syracuseStep 5353739 = 8030609) B8030609
theorem B3569159 : Blo 2227435 3569159 := bstep (se 1 (by rfl) ⟨2676869, by rfl⟩ : syracuseStep 3569159 = 5353739) B5353739
theorem B2379439 : Blo 2227435 2379439 := bstep (se 1 (by rfl) ⟨1784579, by rfl⟩ : syracuseStep 2379439 = 3569159) B3569159
theorem B12690341 : Blo 2227435 12690341 := bstep (se 4 (by rfl) ⟨1189719, by rfl⟩ : syracuseStep 12690341 = 2379439) B2379439
theorem B8460227 : Blo 2227435 8460227 := bstep (se 1 (by rfl) ⟨6345170, by rfl⟩ : syracuseStep 8460227 = 12690341) B12690341
theorem B5640151 : Blo 2227435 5640151 := bstep (se 1 (by rfl) ⟨4230113, by rfl⟩ : syracuseStep 5640151 = 8460227) B8460227
theorem B7520201 : Blo 2227435 7520201 := bstep (se 2 (by rfl) ⟨2820075, by rfl⟩ : syracuseStep 7520201 = 5640151) B5640151
theorem B5013467 : Blo 2227435 5013467 := bstep (se 1 (by rfl) ⟨3760100, by rfl⟩ : syracuseStep 5013467 = 7520201) B7520201
theorem B3342311 : Blo 2227435 3342311 := bstep (se 1 (by rfl) ⟨2506733, by rfl⟩ : syracuseStep 3342311 = 5013467) B5013467
theorem B2228207 : Blo 2227435 2228207 := bstep (se 1 (by rfl) ⟨1671155, by rfl⟩ : syracuseStep 2228207 = 3342311) B3342311
theorem B3342317 : Blo 2227435 3342317 := bbase (se 3 (by rfl) ⟨626684, by rfl⟩ : syracuseStep 3342317 = 1253369) (by norm_num)
theorem B2228211 : Blo 2227435 2228211 := bstep (se 1 (by rfl) ⟨1671158, by rfl⟩ : syracuseStep 2228211 = 3342317) B3342317
theorem B5013485 : Blo 2227435 5013485 := bbase (se 3 (by rfl) ⟨940028, by rfl⟩ : syracuseStep 5013485 = 1880057) (by norm_num)
theorem B3342323 : Blo 2227435 3342323 := bstep (se 1 (by rfl) ⟨2506742, by rfl⟩ : syracuseStep 3342323 = 5013485) B5013485
theorem B2228215 : Blo 2227435 2228215 := bstep (se 1 (by rfl) ⟨1671161, by rfl⟩ : syracuseStep 2228215 = 3342323) B3342323
theorem B4287853 : Blo 2227435 4287853 := bbase (se 3 (by rfl) ⟨803972, by rfl⟩ : syracuseStep 4287853 = 1607945) (by norm_num)
theorem B5717137 : Blo 2227435 5717137 := bstep (se 2 (by rfl) ⟨2143926, by rfl⟩ : syracuseStep 5717137 = 4287853) B4287853
theorem B7622849 : Blo 2227435 7622849 := bstep (se 2 (by rfl) ⟨2858568, by rfl⟩ : syracuseStep 7622849 = 5717137) B5717137
theorem B20327597 : Blo 2227435 20327597 := bstep (se 3 (by rfl) ⟨3811424, by rfl⟩ : syracuseStep 20327597 = 7622849) B7622849
theorem B13551731 : Blo 2227435 13551731 := bstep (se 1 (by rfl) ⟨10163798, by rfl⟩ : syracuseStep 13551731 = 20327597) B20327597
theorem B9034487 : Blo 2227435 9034487 := bstep (se 1 (by rfl) ⟨6775865, by rfl⟩ : syracuseStep 9034487 = 13551731) B13551731
theorem B6022991 : Blo 2227435 6022991 := bstep (se 1 (by rfl) ⟨4517243, by rfl⟩ : syracuseStep 6022991 = 9034487) B9034487
theorem B4015327 : Blo 2227435 4015327 := bstep (se 1 (by rfl) ⟨3011495, by rfl⟩ : syracuseStep 4015327 = 6022991) B6022991
theorem B5353769 : Blo 2227435 5353769 := bstep (se 2 (by rfl) ⟨2007663, by rfl⟩ : syracuseStep 5353769 = 4015327) B4015327
theorem B3569179 : Blo 2227435 3569179 := bstep (se 1 (by rfl) ⟨2676884, by rfl⟩ : syracuseStep 3569179 = 5353769) B5353769
theorem B4758905 : Blo 2227435 4758905 := bstep (se 2 (by rfl) ⟨1784589, by rfl⟩ : syracuseStep 4758905 = 3569179) B3569179
theorem B3172603 : Blo 2227435 3172603 := bstep (se 1 (by rfl) ⟨2379452, by rfl⟩ : syracuseStep 3172603 = 4758905) B4758905
theorem B4230137 : Blo 2227435 4230137 := bstep (se 2 (by rfl) ⟨1586301, by rfl⟩ : syracuseStep 4230137 = 3172603) B3172603
theorem B2820091 : Blo 2227435 2820091 := bstep (se 1 (by rfl) ⟨2115068, by rfl⟩ : syracuseStep 2820091 = 4230137) B4230137
theorem B3760121 : Blo 2227435 3760121 := bstep (se 2 (by rfl) ⟨1410045, by rfl⟩ : syracuseStep 3760121 = 2820091) B2820091
theorem B2506747 : Blo 2227435 2506747 := bstep (se 1 (by rfl) ⟨1880060, by rfl⟩ : syracuseStep 2506747 = 3760121) B3760121
theorem B3342329 : Blo 2227435 3342329 := bstep (se 2 (by rfl) ⟨1253373, by rfl⟩ : syracuseStep 3342329 = 2506747) B2506747
theorem B2228219 : Blo 2227435 2228219 := bstep (se 1 (by rfl) ⟨1671164, by rfl⟩ : syracuseStep 2228219 = 3342329) B3342329
theorem B7250885 : Blo 2227435 7250885 := bbase (se 4 (by rfl) ⟨679770, by rfl⟩ : syracuseStep 7250885 = 1359541) (by norm_num)
theorem B4833923 : Blo 2227435 4833923 := bstep (se 1 (by rfl) ⟨3625442, by rfl⟩ : syracuseStep 4833923 = 7250885) B7250885
theorem B12890461 : Blo 2227435 12890461 := bstep (se 3 (by rfl) ⟨2416961, by rfl⟩ : syracuseStep 12890461 = 4833923) B4833923
theorem B17187281 : Blo 2227435 17187281 := bstep (se 2 (by rfl) ⟨6445230, by rfl⟩ : syracuseStep 17187281 = 12890461) B12890461
theorem B11458187 : Blo 2227435 11458187 := bstep (se 1 (by rfl) ⟨8593640, by rfl⟩ : syracuseStep 11458187 = 17187281) B17187281
theorem B488882645 : Blo 2227435 488882645 := bstep (se 7 (by rfl) ⟨5729093, by rfl⟩ : syracuseStep 488882645 = 11458187) B11458187
theorem B325921763 : Blo 2227435 325921763 := bstep (se 1 (by rfl) ⟨244441322, by rfl⟩ : syracuseStep 325921763 = 488882645) B488882645
theorem B869124701 : Blo 2227435 869124701 := bstep (se 3 (by rfl) ⟨162960881, by rfl⟩ : syracuseStep 869124701 = 325921763) B325921763
theorem B2317665869 : Blo 2227435 2317665869 := bstep (se 3 (by rfl) ⟨434562350, by rfl⟩ : syracuseStep 2317665869 = 869124701) B869124701
theorem B1545110579 : Blo 2227435 1545110579 := bstep (se 1 (by rfl) ⟨1158832934, by rfl⟩ : syracuseStep 1545110579 = 2317665869) B2317665869
theorem B4120294877 : Blo 2227435 4120294877 := bstep (se 3 (by rfl) ⟨772555289, by rfl⟩ : syracuseStep 4120294877 = 1545110579) B1545110579
theorem B2746863251 : Blo 2227435 2746863251 := bstep (se 1 (by rfl) ⟨2060147438, by rfl⟩ : syracuseStep 2746863251 = 4120294877) B4120294877
theorem B1831242167 : Blo 2227435 1831242167 := bstep (se 1 (by rfl) ⟨1373431625, by rfl⟩ : syracuseStep 1831242167 = 2746863251) B2746863251
theorem B1220828111 : Blo 2227435 1220828111 := bstep (se 1 (by rfl) ⟨915621083, by rfl⟩ : syracuseStep 1220828111 = 1831242167) B1831242167
theorem B813885407 : Blo 2227435 813885407 := bstep (se 1 (by rfl) ⟨610414055, by rfl⟩ : syracuseStep 813885407 = 1220828111) B1220828111
theorem B542590271 : Blo 2227435 542590271 := bstep (se 1 (by rfl) ⟨406942703, by rfl⟩ : syracuseStep 542590271 = 813885407) B813885407
theorem B361726847 : Blo 2227435 361726847 := bstep (se 1 (by rfl) ⟨271295135, by rfl⟩ : syracuseStep 361726847 = 542590271) B542590271
theorem B241151231 : Blo 2227435 241151231 := bstep (se 1 (by rfl) ⟨180863423, by rfl⟩ : syracuseStep 241151231 = 361726847) B361726847
theorem B643069949 : Blo 2227435 643069949 := bstep (se 3 (by rfl) ⟨120575615, by rfl⟩ : syracuseStep 643069949 = 241151231) B241151231
theorem B1714853197 : Blo 2227435 1714853197 := bstep (se 3 (by rfl) ⟨321534974, by rfl⟩ : syracuseStep 1714853197 = 643069949) B643069949
theorem B2286470929 : Blo 2227435 2286470929 := bstep (se 2 (by rfl) ⟨857426598, by rfl⟩ : syracuseStep 2286470929 = 1714853197) B1714853197
theorem B3048627905 : Blo 2227435 3048627905 := bstep (se 2 (by rfl) ⟨1143235464, by rfl⟩ : syracuseStep 3048627905 = 2286470929) B2286470929
theorem B2032418603 : Blo 2227435 2032418603 := bstep (se 1 (by rfl) ⟨1524313952, by rfl⟩ : syracuseStep 2032418603 = 3048627905) B3048627905
theorem B1354945735 : Blo 2227435 1354945735 := bstep (se 1 (by rfl) ⟨1016209301, by rfl⟩ : syracuseStep 1354945735 = 2032418603) B2032418603
theorem B1806594313 : Blo 2227435 1806594313 := bstep (se 2 (by rfl) ⟨677472867, by rfl⟩ : syracuseStep 1806594313 = 1354945735) B1354945735
theorem B2408792417 : Blo 2227435 2408792417 := bstep (se 2 (by rfl) ⟨903297156, by rfl⟩ : syracuseStep 2408792417 = 1806594313) B1806594313
theorem B1605861611 : Blo 2227435 1605861611 := bstep (se 1 (by rfl) ⟨1204396208, by rfl⟩ : syracuseStep 1605861611 = 2408792417) B2408792417
theorem B1070574407 : Blo 2227435 1070574407 := bstep (se 1 (by rfl) ⟨802930805, by rfl⟩ : syracuseStep 1070574407 = 1605861611) B1605861611
theorem B713716271 : Blo 2227435 713716271 := bstep (se 1 (by rfl) ⟨535287203, by rfl⟩ : syracuseStep 713716271 = 1070574407) B1070574407
theorem B475810847 : Blo 2227435 475810847 := bstep (se 1 (by rfl) ⟨356858135, by rfl⟩ : syracuseStep 475810847 = 713716271) B713716271
theorem B317207231 : Blo 2227435 317207231 := bstep (se 1 (by rfl) ⟨237905423, by rfl⟩ : syracuseStep 317207231 = 475810847) B475810847
theorem B211471487 : Blo 2227435 211471487 := bstep (se 1 (by rfl) ⟨158603615, by rfl⟩ : syracuseStep 211471487 = 317207231) B317207231
theorem B140980991 : Blo 2227435 140980991 := bstep (se 1 (by rfl) ⟨105735743, by rfl⟩ : syracuseStep 140980991 = 211471487) B211471487
theorem B375949309 : Blo 2227435 375949309 := bstep (se 3 (by rfl) ⟨70490495, by rfl⟩ : syracuseStep 375949309 = 140980991) B140980991
theorem B501265745 : Blo 2227435 501265745 := bstep (se 2 (by rfl) ⟨187974654, by rfl⟩ : syracuseStep 501265745 = 375949309) B375949309
theorem B334177163 : Blo 2227435 334177163 := bstep (se 1 (by rfl) ⟨250632872, by rfl⟩ : syracuseStep 334177163 = 501265745) B501265745
theorem B222784775 : Blo 2227435 222784775 := bstep (se 1 (by rfl) ⟨167088581, by rfl⟩ : syracuseStep 222784775 = 334177163) B334177163
theorem B148523183 : Blo 2227435 148523183 := bstep (se 1 (by rfl) ⟨111392387, by rfl⟩ : syracuseStep 148523183 = 222784775) B222784775
theorem B99015455 : Blo 2227435 99015455 := bstep (se 1 (by rfl) ⟨74261591, by rfl⟩ : syracuseStep 99015455 = 148523183) B148523183
theorem B66010303 : Blo 2227435 66010303 := bstep (se 1 (by rfl) ⟨49507727, by rfl⟩ : syracuseStep 66010303 = 99015455) B99015455
theorem B88013737 : Blo 2227435 88013737 := bstep (se 2 (by rfl) ⟨33005151, by rfl⟩ : syracuseStep 88013737 = 66010303) B66010303
theorem B117351649 : Blo 2227435 117351649 := bstep (se 2 (by rfl) ⟨44006868, by rfl⟩ : syracuseStep 117351649 = 88013737) B88013737
theorem B625875461 : Blo 2227435 625875461 := bstep (se 4 (by rfl) ⟨58675824, by rfl⟩ : syracuseStep 625875461 = 117351649) B117351649
theorem B417250307 : Blo 2227435 417250307 := bstep (se 1 (by rfl) ⟨312937730, by rfl⟩ : syracuseStep 417250307 = 625875461) B625875461
theorem B278166871 : Blo 2227435 278166871 := bstep (se 1 (by rfl) ⟨208625153, by rfl⟩ : syracuseStep 278166871 = 417250307) B417250307
theorem B370889161 : Blo 2227435 370889161 := bstep (se 2 (by rfl) ⟨139083435, by rfl⟩ : syracuseStep 370889161 = 278166871) B278166871
theorem B1978075525 : Blo 2227435 1978075525 := bstep (se 4 (by rfl) ⟨185444580, by rfl⟩ : syracuseStep 1978075525 = 370889161) B370889161
theorem B2637434033 : Blo 2227435 2637434033 := bstep (se 2 (by rfl) ⟨989037762, by rfl⟩ : syracuseStep 2637434033 = 1978075525) B1978075525
theorem B1758289355 : Blo 2227435 1758289355 := bstep (se 1 (by rfl) ⟨1318717016, by rfl⟩ : syracuseStep 1758289355 = 2637434033) B2637434033
theorem B1172192903 : Blo 2227435 1172192903 := bstep (se 1 (by rfl) ⟨879144677, by rfl⟩ : syracuseStep 1172192903 = 1758289355) B1758289355
theorem B781461935 : Blo 2227435 781461935 := bstep (se 1 (by rfl) ⟨586096451, by rfl⟩ : syracuseStep 781461935 = 1172192903) B1172192903
theorem B520974623 : Blo 2227435 520974623 := bstep (se 1 (by rfl) ⟨390730967, by rfl⟩ : syracuseStep 520974623 = 781461935) B781461935
theorem B1389265661 : Blo 2227435 1389265661 := bstep (se 3 (by rfl) ⟨260487311, by rfl⟩ : syracuseStep 1389265661 = 520974623) B520974623
theorem B926177107 : Blo 2227435 926177107 := bstep (se 1 (by rfl) ⟨694632830, by rfl⟩ : syracuseStep 926177107 = 1389265661) B1389265661
theorem B1234902809 : Blo 2227435 1234902809 := bstep (se 2 (by rfl) ⟨463088553, by rfl⟩ : syracuseStep 1234902809 = 926177107) B926177107
theorem B823268539 : Blo 2227435 823268539 := bstep (se 1 (by rfl) ⟨617451404, by rfl⟩ : syracuseStep 823268539 = 1234902809) B1234902809
theorem B1097691385 : Blo 2227435 1097691385 := bstep (se 2 (by rfl) ⟨411634269, by rfl⟩ : syracuseStep 1097691385 = 823268539) B823268539
theorem B1463588513 : Blo 2227435 1463588513 := bstep (se 2 (by rfl) ⟨548845692, by rfl⟩ : syracuseStep 1463588513 = 1097691385) B1097691385
theorem B975725675 : Blo 2227435 975725675 := bstep (se 1 (by rfl) ⟨731794256, by rfl⟩ : syracuseStep 975725675 = 1463588513) B1463588513
theorem B650483783 : Blo 2227435 650483783 := bstep (se 1 (by rfl) ⟨487862837, by rfl⟩ : syracuseStep 650483783 = 975725675) B975725675
theorem B433655855 : Blo 2227435 433655855 := bstep (se 1 (by rfl) ⟨325241891, by rfl⟩ : syracuseStep 433655855 = 650483783) B650483783
theorem B289103903 : Blo 2227435 289103903 := bstep (se 1 (by rfl) ⟨216827927, by rfl⟩ : syracuseStep 289103903 = 433655855) B433655855
theorem B192735935 : Blo 2227435 192735935 := bstep (se 1 (by rfl) ⟨144551951, by rfl⟩ : syracuseStep 192735935 = 289103903) B289103903
theorem B128490623 : Blo 2227435 128490623 := bstep (se 1 (by rfl) ⟨96367967, by rfl⟩ : syracuseStep 128490623 = 192735935) B192735935
theorem B85660415 : Blo 2227435 85660415 := bstep (se 1 (by rfl) ⟨64245311, by rfl⟩ : syracuseStep 85660415 = 128490623) B128490623
theorem B57106943 : Blo 2227435 57106943 := bstep (se 1 (by rfl) ⟨42830207, by rfl⟩ : syracuseStep 57106943 = 85660415) B85660415
theorem B38071295 : Blo 2227435 38071295 := bstep (se 1 (by rfl) ⟨28553471, by rfl⟩ : syracuseStep 38071295 = 57106943) B57106943
theorem B25380863 : Blo 2227435 25380863 := bstep (se 1 (by rfl) ⟨19035647, by rfl⟩ : syracuseStep 25380863 = 38071295) B38071295
theorem B16920575 : Blo 2227435 16920575 := bstep (se 1 (by rfl) ⟨12690431, by rfl⟩ : syracuseStep 16920575 = 25380863) B25380863
theorem B11280383 : Blo 2227435 11280383 := bstep (se 1 (by rfl) ⟨8460287, by rfl⟩ : syracuseStep 11280383 = 16920575) B16920575
theorem B7520255 : Blo 2227435 7520255 := bstep (se 1 (by rfl) ⟨5640191, by rfl⟩ : syracuseStep 7520255 = 11280383) B11280383
theorem B5013503 : Blo 2227435 5013503 := bstep (se 1 (by rfl) ⟨3760127, by rfl⟩ : syracuseStep 5013503 = 7520255) B7520255
theorem B3342335 : Blo 2227435 3342335 := bstep (se 1 (by rfl) ⟨2506751, by rfl⟩ : syracuseStep 3342335 = 5013503) B5013503
theorem B2228223 : Blo 2227435 2228223 := bstep (se 1 (by rfl) ⟨1671167, by rfl⟩ : syracuseStep 2228223 = 3342335) B3342335
theorem B3342341 : Blo 2227435 3342341 := bbase (se 4 (by rfl) ⟨313344, by rfl⟩ : syracuseStep 3342341 = 626689) (by norm_num)
theorem B2228227 : Blo 2227435 2228227 := bstep (se 1 (by rfl) ⟨1671170, by rfl⟩ : syracuseStep 2228227 = 3342341) B3342341
theorem B3760141 : Blo 2227435 3760141 := bbase (se 3 (by rfl) ⟨705026, by rfl⟩ : syracuseStep 3760141 = 1410053) (by norm_num)
theorem B5013521 : Blo 2227435 5013521 := bstep (se 2 (by rfl) ⟨1880070, by rfl⟩ : syracuseStep 5013521 = 3760141) B3760141
theorem B3342347 : Blo 2227435 3342347 := bstep (se 1 (by rfl) ⟨2506760, by rfl⟩ : syracuseStep 3342347 = 5013521) B5013521
theorem B2228231 : Blo 2227435 2228231 := bstep (se 1 (by rfl) ⟨1671173, by rfl⟩ : syracuseStep 2228231 = 3342347) B3342347
theorem B2506765 : Blo 2227435 2506765 := bbase (se 3 (by rfl) ⟨470018, by rfl⟩ : syracuseStep 2506765 = 940037) (by norm_num)
theorem B3342353 : Blo 2227435 3342353 := bstep (se 2 (by rfl) ⟨1253382, by rfl⟩ : syracuseStep 3342353 = 2506765) B2506765
theorem B2228235 : Blo 2227435 2228235 := bstep (se 1 (by rfl) ⟨1671176, by rfl⟩ : syracuseStep 2228235 = 3342353) B3342353
theorem B7520309 : Blo 2227435 7520309 := bbase (se 5 (by rfl) ⟨352514, by rfl⟩ : syracuseStep 7520309 = 705029) (by norm_num)
theorem B5013539 : Blo 2227435 5013539 := bstep (se 1 (by rfl) ⟨3760154, by rfl⟩ : syracuseStep 5013539 = 7520309) B7520309
theorem B3342359 : Blo 2227435 3342359 := bstep (se 1 (by rfl) ⟨2506769, by rfl⟩ : syracuseStep 3342359 = 5013539) B5013539
theorem B2228239 : Blo 2227435 2228239 := bstep (se 1 (by rfl) ⟨1671179, by rfl⟩ : syracuseStep 2228239 = 3342359) B3342359
theorem B3342365 : Blo 2227435 3342365 := bbase (se 3 (by rfl) ⟨626693, by rfl⟩ : syracuseStep 3342365 = 1253387) (by norm_num)
theorem B2228243 : Blo 2227435 2228243 := bstep (se 1 (by rfl) ⟨1671182, by rfl⟩ : syracuseStep 2228243 = 3342365) B3342365
theorem B5013557 : Blo 2227435 5013557 := bbase (se 5 (by rfl) ⟨235010, by rfl⟩ : syracuseStep 5013557 = 470021) (by norm_num)
theorem B3342371 : Blo 2227435 3342371 := bstep (se 1 (by rfl) ⟨2506778, by rfl⟩ : syracuseStep 3342371 = 5013557) B5013557
theorem B2228247 : Blo 2227435 2228247 := bstep (se 1 (by rfl) ⟨1671185, by rfl⟩ : syracuseStep 2228247 = 3342371) B3342371
theorem B6105253 : Blo 2227435 6105253 := bbase (se 4 (by rfl) ⟨572367, by rfl⟩ : syracuseStep 6105253 = 1144735) (by norm_num)
theorem B8140337 : Blo 2227435 8140337 := bstep (se 2 (by rfl) ⟨3052626, by rfl⟩ : syracuseStep 8140337 = 6105253) B6105253
theorem B5426891 : Blo 2227435 5426891 := bstep (se 1 (by rfl) ⟨4070168, by rfl⟩ : syracuseStep 5426891 = 8140337) B8140337
theorem B3617927 : Blo 2227435 3617927 := bstep (se 1 (by rfl) ⟨2713445, by rfl⟩ : syracuseStep 3617927 = 5426891) B5426891
theorem B2411951 : Blo 2227435 2411951 := bstep (se 1 (by rfl) ⟨1808963, by rfl⟩ : syracuseStep 2411951 = 3617927) B3617927
theorem B6431869 : Blo 2227435 6431869 := bstep (se 3 (by rfl) ⟨1205975, by rfl⟩ : syracuseStep 6431869 = 2411951) B2411951
theorem B34303301 : Blo 2227435 34303301 := bstep (se 4 (by rfl) ⟨3215934, by rfl⟩ : syracuseStep 34303301 = 6431869) B6431869
theorem B22868867 : Blo 2227435 22868867 := bstep (se 1 (by rfl) ⟨17151650, by rfl⟩ : syracuseStep 22868867 = 34303301) B34303301
theorem B15245911 : Blo 2227435 15245911 := bstep (se 1 (by rfl) ⟨11434433, by rfl⟩ : syracuseStep 15245911 = 22868867) B22868867
theorem B20327881 : Blo 2227435 20327881 := bstep (se 2 (by rfl) ⟨7622955, by rfl⟩ : syracuseStep 20327881 = 15245911) B15245911
theorem B27103841 : Blo 2227435 27103841 := bstep (se 2 (by rfl) ⟨10163940, by rfl⟩ : syracuseStep 27103841 = 20327881) B20327881
theorem B18069227 : Blo 2227435 18069227 := bstep (se 1 (by rfl) ⟨13551920, by rfl⟩ : syracuseStep 18069227 = 27103841) B27103841
theorem B12046151 : Blo 2227435 12046151 := bstep (se 1 (by rfl) ⟨9034613, by rfl⟩ : syracuseStep 12046151 = 18069227) B18069227
theorem B8030767 : Blo 2227435 8030767 := bstep (se 1 (by rfl) ⟨6023075, by rfl⟩ : syracuseStep 8030767 = 12046151) B12046151
theorem B10707689 : Blo 2227435 10707689 := bstep (se 2 (by rfl) ⟨4015383, by rfl⟩ : syracuseStep 10707689 = 8030767) B8030767
theorem B7138459 : Blo 2227435 7138459 := bstep (se 1 (by rfl) ⟨5353844, by rfl⟩ : syracuseStep 7138459 = 10707689) B10707689
theorem B9517945 : Blo 2227435 9517945 := bstep (se 2 (by rfl) ⟨3569229, by rfl⟩ : syracuseStep 9517945 = 7138459) B7138459
theorem B12690593 : Blo 2227435 12690593 := bstep (se 2 (by rfl) ⟨4758972, by rfl⟩ : syracuseStep 12690593 = 9517945) B9517945
theorem B8460395 : Blo 2227435 8460395 := bstep (se 1 (by rfl) ⟨6345296, by rfl⟩ : syracuseStep 8460395 = 12690593) B12690593
theorem B5640263 : Blo 2227435 5640263 := bstep (se 1 (by rfl) ⟨4230197, by rfl⟩ : syracuseStep 5640263 = 8460395) B8460395
theorem B3760175 : Blo 2227435 3760175 := bstep (se 1 (by rfl) ⟨2820131, by rfl⟩ : syracuseStep 3760175 = 5640263) B5640263
theorem B2506783 : Blo 2227435 2506783 := bstep (se 1 (by rfl) ⟨1880087, by rfl⟩ : syracuseStep 2506783 = 3760175) B3760175
theorem B3342377 : Blo 2227435 3342377 := bstep (se 2 (by rfl) ⟨1253391, by rfl⟩ : syracuseStep 3342377 = 2506783) B2506783
theorem B2228251 : Blo 2227435 2228251 := bstep (se 1 (by rfl) ⟨1671188, by rfl⟩ : syracuseStep 2228251 = 3342377) B3342377
theorem B5221597 : Blo 2227435 5221597 := bbase (se 3 (by rfl) ⟨979049, by rfl⟩ : syracuseStep 5221597 = 1958099) (by norm_num)
theorem B6962129 : Blo 2227435 6962129 := bstep (se 2 (by rfl) ⟨2610798, by rfl⟩ : syracuseStep 6962129 = 5221597) B5221597
theorem B4641419 : Blo 2227435 4641419 := bstep (se 1 (by rfl) ⟨3481064, by rfl⟩ : syracuseStep 4641419 = 6962129) B6962129
theorem B12377117 : Blo 2227435 12377117 := bstep (se 3 (by rfl) ⟨2320709, by rfl⟩ : syracuseStep 12377117 = 4641419) B4641419
theorem B8251411 : Blo 2227435 8251411 := bstep (se 1 (by rfl) ⟨6188558, by rfl⟩ : syracuseStep 8251411 = 12377117) B12377117
theorem B11001881 : Blo 2227435 11001881 := bstep (se 2 (by rfl) ⟨4125705, by rfl⟩ : syracuseStep 11001881 = 8251411) B8251411
theorem B7334587 : Blo 2227435 7334587 := bstep (se 1 (by rfl) ⟨5500940, by rfl⟩ : syracuseStep 7334587 = 11001881) B11001881
theorem B9779449 : Blo 2227435 9779449 := bstep (se 2 (by rfl) ⟨3667293, by rfl⟩ : syracuseStep 9779449 = 7334587) B7334587
theorem B13039265 : Blo 2227435 13039265 := bstep (se 2 (by rfl) ⟨4889724, by rfl⟩ : syracuseStep 13039265 = 9779449) B9779449
theorem B8692843 : Blo 2227435 8692843 := bstep (se 1 (by rfl) ⟨6519632, by rfl⟩ : syracuseStep 8692843 = 13039265) B13039265
theorem B11590457 : Blo 2227435 11590457 := bstep (se 2 (by rfl) ⟨4346421, by rfl⟩ : syracuseStep 11590457 = 8692843) B8692843
theorem B30907885 : Blo 2227435 30907885 := bstep (se 3 (by rfl) ⟨5795228, by rfl⟩ : syracuseStep 30907885 = 11590457) B11590457
theorem B41210513 : Blo 2227435 41210513 := bstep (se 2 (by rfl) ⟨15453942, by rfl⟩ : syracuseStep 41210513 = 30907885) B30907885
theorem B27473675 : Blo 2227435 27473675 := bstep (se 1 (by rfl) ⟨20605256, by rfl⟩ : syracuseStep 27473675 = 41210513) B41210513
theorem B73263133 : Blo 2227435 73263133 := bstep (se 3 (by rfl) ⟨13736837, by rfl⟩ : syracuseStep 73263133 = 27473675) B27473675
theorem B97684177 : Blo 2227435 97684177 := bstep (se 2 (by rfl) ⟨36631566, by rfl⟩ : syracuseStep 97684177 = 73263133) B73263133
theorem B130245569 : Blo 2227435 130245569 := bstep (se 2 (by rfl) ⟨48842088, by rfl⟩ : syracuseStep 130245569 = 97684177) B97684177
theorem B86830379 : Blo 2227435 86830379 := bstep (se 1 (by rfl) ⟨65122784, by rfl⟩ : syracuseStep 86830379 = 130245569) B130245569
theorem B57886919 : Blo 2227435 57886919 := bstep (se 1 (by rfl) ⟨43415189, by rfl⟩ : syracuseStep 57886919 = 86830379) B86830379
theorem B38591279 : Blo 2227435 38591279 := bstep (se 1 (by rfl) ⟨28943459, by rfl⟩ : syracuseStep 38591279 = 57886919) B57886919
theorem B25727519 : Blo 2227435 25727519 := bstep (se 1 (by rfl) ⟨19295639, by rfl⟩ : syracuseStep 25727519 = 38591279) B38591279
theorem B17151679 : Blo 2227435 17151679 := bstep (se 1 (by rfl) ⟨12863759, by rfl⟩ : syracuseStep 17151679 = 25727519) B25727519
theorem B22868905 : Blo 2227435 22868905 := bstep (se 2 (by rfl) ⟨8575839, by rfl⟩ : syracuseStep 22868905 = 17151679) B17151679
theorem B30491873 : Blo 2227435 30491873 := bstep (se 2 (by rfl) ⟨11434452, by rfl⟩ : syracuseStep 30491873 = 22868905) B22868905
theorem B20327915 : Blo 2227435 20327915 := bstep (se 1 (by rfl) ⟨15245936, by rfl⟩ : syracuseStep 20327915 = 30491873) B30491873
theorem B13551943 : Blo 2227435 13551943 := bstep (se 1 (by rfl) ⟨10163957, by rfl⟩ : syracuseStep 13551943 = 20327915) B20327915
theorem B18069257 : Blo 2227435 18069257 := bstep (se 2 (by rfl) ⟨6775971, by rfl⟩ : syracuseStep 18069257 = 13551943) B13551943
theorem B12046171 : Blo 2227435 12046171 := bstep (se 1 (by rfl) ⟨9034628, by rfl⟩ : syracuseStep 12046171 = 18069257) B18069257
theorem B16061561 : Blo 2227435 16061561 := bstep (se 2 (by rfl) ⟨6023085, by rfl⟩ : syracuseStep 16061561 = 12046171) B12046171
theorem B10707707 : Blo 2227435 10707707 := bstep (se 1 (by rfl) ⟨8030780, by rfl⟩ : syracuseStep 10707707 = 16061561) B16061561
theorem B7138471 : Blo 2227435 7138471 := bstep (se 1 (by rfl) ⟨5353853, by rfl⟩ : syracuseStep 7138471 = 10707707) B10707707
theorem B9517961 : Blo 2227435 9517961 := bstep (se 2 (by rfl) ⟨3569235, by rfl⟩ : syracuseStep 9517961 = 7138471) B7138471
theorem B6345307 : Blo 2227435 6345307 := bstep (se 1 (by rfl) ⟨4758980, by rfl⟩ : syracuseStep 6345307 = 9517961) B9517961
theorem B8460409 : Blo 2227435 8460409 := bstep (se 2 (by rfl) ⟨3172653, by rfl⟩ : syracuseStep 8460409 = 6345307) B6345307
theorem B11280545 : Blo 2227435 11280545 := bstep (se 2 (by rfl) ⟨4230204, by rfl⟩ : syracuseStep 11280545 = 8460409) B8460409
theorem B7520363 : Blo 2227435 7520363 := bstep (se 1 (by rfl) ⟨5640272, by rfl⟩ : syracuseStep 7520363 = 11280545) B11280545
theorem B5013575 : Blo 2227435 5013575 := bstep (se 1 (by rfl) ⟨3760181, by rfl⟩ : syracuseStep 5013575 = 7520363) B7520363
theorem B3342383 : Blo 2227435 3342383 := bstep (se 1 (by rfl) ⟨2506787, by rfl⟩ : syracuseStep 3342383 = 5013575) B5013575
theorem B2228255 : Blo 2227435 2228255 := bstep (se 1 (by rfl) ⟨1671191, by rfl⟩ : syracuseStep 2228255 = 3342383) B3342383
theorem B3342389 : Blo 2227435 3342389 := bbase (se 5 (by rfl) ⟨156674, by rfl⟩ : syracuseStep 3342389 = 313349) (by norm_num)
theorem B2228259 : Blo 2227435 2228259 := bstep (se 1 (by rfl) ⟨1671194, by rfl⟩ : syracuseStep 2228259 = 3342389) B3342389
theorem B5640293 : Blo 2227435 5640293 := bbase (se 4 (by rfl) ⟨528777, by rfl⟩ : syracuseStep 5640293 = 1057555) (by norm_num)
theorem B3760195 : Blo 2227435 3760195 := bstep (se 1 (by rfl) ⟨2820146, by rfl⟩ : syracuseStep 3760195 = 5640293) B5640293
theorem B5013593 : Blo 2227435 5013593 := bstep (se 2 (by rfl) ⟨1880097, by rfl⟩ : syracuseStep 5013593 = 3760195) B3760195
theorem B3342395 : Blo 2227435 3342395 := bstep (se 1 (by rfl) ⟨2506796, by rfl⟩ : syracuseStep 3342395 = 5013593) B5013593
theorem B2228263 : Blo 2227435 2228263 := bstep (se 1 (by rfl) ⟨1671197, by rfl⟩ : syracuseStep 2228263 = 3342395) B3342395
theorem B2506801 : Blo 2227435 2506801 := bbase (se 2 (by rfl) ⟨940050, by rfl⟩ : syracuseStep 2506801 = 1880101) (by norm_num)
theorem B3342401 : Blo 2227435 3342401 := bstep (se 2 (by rfl) ⟨1253400, by rfl⟩ : syracuseStep 3342401 = 2506801) B2506801
theorem B2228267 : Blo 2227435 2228267 := bstep (se 1 (by rfl) ⟨1671200, by rfl⟩ : syracuseStep 2228267 = 3342401) B3342401
theorem B6776021 : Blo 2227435 6776021 := bbase (se 7 (by rfl) ⟨79406, by rfl⟩ : syracuseStep 6776021 = 158813) (by norm_num)
theorem B18069389 : Blo 2227435 18069389 := bstep (se 3 (by rfl) ⟨3388010, by rfl⟩ : syracuseStep 18069389 = 6776021) B6776021
theorem B12046259 : Blo 2227435 12046259 := bstep (se 1 (by rfl) ⟨9034694, by rfl⟩ : syracuseStep 12046259 = 18069389) B18069389
theorem B8030839 : Blo 2227435 8030839 := bstep (se 1 (by rfl) ⟨6023129, by rfl⟩ : syracuseStep 8030839 = 12046259) B12046259
theorem B10707785 : Blo 2227435 10707785 := bstep (se 2 (by rfl) ⟨4015419, by rfl⟩ : syracuseStep 10707785 = 8030839) B8030839
theorem B7138523 : Blo 2227435 7138523 := bstep (se 1 (by rfl) ⟨5353892, by rfl⟩ : syracuseStep 7138523 = 10707785) B10707785
theorem B4759015 : Blo 2227435 4759015 := bstep (se 1 (by rfl) ⟨3569261, by rfl⟩ : syracuseStep 4759015 = 7138523) B7138523
theorem B6345353 : Blo 2227435 6345353 := bstep (se 2 (by rfl) ⟨2379507, by rfl⟩ : syracuseStep 6345353 = 4759015) B4759015
theorem B4230235 : Blo 2227435 4230235 := bstep (se 1 (by rfl) ⟨3172676, by rfl⟩ : syracuseStep 4230235 = 6345353) B6345353
theorem B5640313 : Blo 2227435 5640313 := bstep (se 2 (by rfl) ⟨2115117, by rfl⟩ : syracuseStep 5640313 = 4230235) B4230235
theorem B7520417 : Blo 2227435 7520417 := bstep (se 2 (by rfl) ⟨2820156, by rfl⟩ : syracuseStep 7520417 = 5640313) B5640313
theorem B5013611 : Blo 2227435 5013611 := bstep (se 1 (by rfl) ⟨3760208, by rfl⟩ : syracuseStep 5013611 = 7520417) B7520417
theorem B3342407 : Blo 2227435 3342407 := bstep (se 1 (by rfl) ⟨2506805, by rfl⟩ : syracuseStep 3342407 = 5013611) B5013611
theorem B2228271 : Blo 2227435 2228271 := bstep (se 1 (by rfl) ⟨1671203, by rfl⟩ : syracuseStep 2228271 = 3342407) B3342407
theorem B3342413 : Blo 2227435 3342413 := bbase (se 3 (by rfl) ⟨626702, by rfl⟩ : syracuseStep 3342413 = 1253405) (by norm_num)
theorem B2228275 : Blo 2227435 2228275 := bstep (se 1 (by rfl) ⟨1671206, by rfl⟩ : syracuseStep 2228275 = 3342413) B3342413
theorem B5013629 : Blo 2227435 5013629 := bbase (se 3 (by rfl) ⟨940055, by rfl⟩ : syracuseStep 5013629 = 1880111) (by norm_num)
theorem B3342419 : Blo 2227435 3342419 := bstep (se 1 (by rfl) ⟨2506814, by rfl⟩ : syracuseStep 3342419 = 5013629) B5013629
theorem B2228279 : Blo 2227435 2228279 := bstep (se 1 (by rfl) ⟨1671209, by rfl⟩ : syracuseStep 2228279 = 3342419) B3342419
theorem B3760229 : Blo 2227435 3760229 := bbase (se 4 (by rfl) ⟨352521, by rfl⟩ : syracuseStep 3760229 = 705043) (by norm_num)
theorem B2506819 : Blo 2227435 2506819 := bstep (se 1 (by rfl) ⟨1880114, by rfl⟩ : syracuseStep 2506819 = 3760229) B3760229
theorem B3342425 : Blo 2227435 3342425 := bstep (se 2 (by rfl) ⟨1253409, by rfl⟩ : syracuseStep 3342425 = 2506819) B2506819
theorem B2228283 : Blo 2227435 2228283 := bstep (se 1 (by rfl) ⟨1671212, by rfl⟩ : syracuseStep 2228283 = 3342425) B3342425
theorem B6023173 : Blo 2227435 6023173 := bbase (se 4 (by rfl) ⟨564672, by rfl⟩ : syracuseStep 6023173 = 1129345) (by norm_num)
theorem B8030897 : Blo 2227435 8030897 := bstep (se 2 (by rfl) ⟨3011586, by rfl⟩ : syracuseStep 8030897 = 6023173) B6023173
theorem B5353931 : Blo 2227435 5353931 := bstep (se 1 (by rfl) ⟨4015448, by rfl⟩ : syracuseStep 5353931 = 8030897) B8030897
theorem B3569287 : Blo 2227435 3569287 := bstep (se 1 (by rfl) ⟨2676965, by rfl⟩ : syracuseStep 3569287 = 5353931) B5353931
theorem B4759049 : Blo 2227435 4759049 := bstep (se 2 (by rfl) ⟨1784643, by rfl⟩ : syracuseStep 4759049 = 3569287) B3569287
theorem B3172699 : Blo 2227435 3172699 := bstep (se 1 (by rfl) ⟨2379524, by rfl⟩ : syracuseStep 3172699 = 4759049) B4759049
theorem B16921061 : Blo 2227435 16921061 := bstep (se 4 (by rfl) ⟨1586349, by rfl⟩ : syracuseStep 16921061 = 3172699) B3172699
theorem B11280707 : Blo 2227435 11280707 := bstep (se 1 (by rfl) ⟨8460530, by rfl⟩ : syracuseStep 11280707 = 16921061) B16921061
theorem B7520471 : Blo 2227435 7520471 := bstep (se 1 (by rfl) ⟨5640353, by rfl⟩ : syracuseStep 7520471 = 11280707) B11280707
theorem B5013647 : Blo 2227435 5013647 := bstep (se 1 (by rfl) ⟨3760235, by rfl⟩ : syracuseStep 5013647 = 7520471) B7520471
theorem B3342431 : Blo 2227435 3342431 := bstep (se 1 (by rfl) ⟨2506823, by rfl⟩ : syracuseStep 3342431 = 5013647) B5013647
theorem B2228287 : Blo 2227435 2228287 := bstep (se 1 (by rfl) ⟨1671215, by rfl⟩ : syracuseStep 2228287 = 3342431) B3342431
theorem B3342437 : Blo 2227435 3342437 := bbase (se 4 (by rfl) ⟨313353, by rfl⟩ : syracuseStep 3342437 = 626707) (by norm_num)
theorem B2228291 : Blo 2227435 2228291 := bstep (se 1 (by rfl) ⟨1671218, by rfl⟩ : syracuseStep 2228291 = 3342437) B3342437
theorem B10302821 : Blo 2227435 10302821 := bbase (se 4 (by rfl) ⟨965889, by rfl⟩ : syracuseStep 10302821 = 1931779) (by norm_num)
theorem B6868547 : Blo 2227435 6868547 := bstep (se 1 (by rfl) ⟨5151410, by rfl⟩ : syracuseStep 6868547 = 10302821) B10302821
theorem B4579031 : Blo 2227435 4579031 := bstep (se 1 (by rfl) ⟨3434273, by rfl⟩ : syracuseStep 4579031 = 6868547) B6868547
theorem B12210749 : Blo 2227435 12210749 := bstep (se 3 (by rfl) ⟨2289515, by rfl⟩ : syracuseStep 12210749 = 4579031) B4579031
theorem B8140499 : Blo 2227435 8140499 := bstep (se 1 (by rfl) ⟨6105374, by rfl⟩ : syracuseStep 8140499 = 12210749) B12210749
theorem B5426999 : Blo 2227435 5426999 := bstep (se 1 (by rfl) ⟨4070249, by rfl⟩ : syracuseStep 5426999 = 8140499) B8140499
theorem B3617999 : Blo 2227435 3617999 := bstep (se 1 (by rfl) ⟨2713499, by rfl⟩ : syracuseStep 3617999 = 5426999) B5426999
theorem B2411999 : Blo 2227435 2411999 := bstep (se 1 (by rfl) ⟨1808999, by rfl⟩ : syracuseStep 2411999 = 3617999) B3617999
theorem B25727989 : Blo 2227435 25727989 := bstep (se 5 (by rfl) ⟨1205999, by rfl⟩ : syracuseStep 25727989 = 2411999) B2411999
theorem B34303985 : Blo 2227435 34303985 := bstep (se 2 (by rfl) ⟨12863994, by rfl⟩ : syracuseStep 34303985 = 25727989) B25727989
theorem B22869323 : Blo 2227435 22869323 := bstep (se 1 (by rfl) ⟨17151992, by rfl⟩ : syracuseStep 22869323 = 34303985) B34303985
theorem B15246215 : Blo 2227435 15246215 := bstep (se 1 (by rfl) ⟨11434661, by rfl⟩ : syracuseStep 15246215 = 22869323) B22869323
theorem B10164143 : Blo 2227435 10164143 := bstep (se 1 (by rfl) ⟨7623107, by rfl⟩ : syracuseStep 10164143 = 15246215) B15246215
theorem B27104381 : Blo 2227435 27104381 := bstep (se 3 (by rfl) ⟨5082071, by rfl⟩ : syracuseStep 27104381 = 10164143) B10164143
theorem B18069587 : Blo 2227435 18069587 := bstep (se 1 (by rfl) ⟨13552190, by rfl⟩ : syracuseStep 18069587 = 27104381) B27104381
theorem B12046391 : Blo 2227435 12046391 := bstep (se 1 (by rfl) ⟨9034793, by rfl⟩ : syracuseStep 12046391 = 18069587) B18069587
theorem B8030927 : Blo 2227435 8030927 := bstep (se 1 (by rfl) ⟨6023195, by rfl⟩ : syracuseStep 8030927 = 12046391) B12046391
theorem B5353951 : Blo 2227435 5353951 := bstep (se 1 (by rfl) ⟨4015463, by rfl⟩ : syracuseStep 5353951 = 8030927) B8030927
theorem B7138601 : Blo 2227435 7138601 := bstep (se 2 (by rfl) ⟨2676975, by rfl⟩ : syracuseStep 7138601 = 5353951) B5353951
theorem B4759067 : Blo 2227435 4759067 := bstep (se 1 (by rfl) ⟨3569300, by rfl⟩ : syracuseStep 4759067 = 7138601) B7138601
theorem B3172711 : Blo 2227435 3172711 := bstep (se 1 (by rfl) ⟨2379533, by rfl⟩ : syracuseStep 3172711 = 4759067) B4759067
theorem B4230281 : Blo 2227435 4230281 := bstep (se 2 (by rfl) ⟨1586355, by rfl⟩ : syracuseStep 4230281 = 3172711) B3172711
theorem B2820187 : Blo 2227435 2820187 := bstep (se 1 (by rfl) ⟨2115140, by rfl⟩ : syracuseStep 2820187 = 4230281) B4230281
theorem B3760249 : Blo 2227435 3760249 := bstep (se 2 (by rfl) ⟨1410093, by rfl⟩ : syracuseStep 3760249 = 2820187) B2820187
theorem B5013665 : Blo 2227435 5013665 := bstep (se 2 (by rfl) ⟨1880124, by rfl⟩ : syracuseStep 5013665 = 3760249) B3760249
theorem B3342443 : Blo 2227435 3342443 := bstep (se 1 (by rfl) ⟨2506832, by rfl⟩ : syracuseStep 3342443 = 5013665) B5013665
theorem B2228295 : Blo 2227435 2228295 := bstep (se 1 (by rfl) ⟨1671221, by rfl⟩ : syracuseStep 2228295 = 3342443) B3342443
theorem B2506837 : Blo 2227435 2506837 := bbase (se 8 (by rfl) ⟨14688, by rfl⟩ : syracuseStep 2506837 = 29377) (by norm_num)
theorem B3342449 : Blo 2227435 3342449 := bstep (se 2 (by rfl) ⟨1253418, by rfl⟩ : syracuseStep 3342449 = 2506837) B2506837
theorem B2228299 : Blo 2227435 2228299 := bstep (se 1 (by rfl) ⟨1671224, by rfl⟩ : syracuseStep 2228299 = 3342449) B3342449
theorem B2820197 : Blo 2227435 2820197 := bbase (se 4 (by rfl) ⟨264393, by rfl⟩ : syracuseStep 2820197 = 528787) (by norm_num)
theorem B7520525 : Blo 2227435 7520525 := bstep (se 3 (by rfl) ⟨1410098, by rfl⟩ : syracuseStep 7520525 = 2820197) B2820197
theorem B5013683 : Blo 2227435 5013683 := bstep (se 1 (by rfl) ⟨3760262, by rfl⟩ : syracuseStep 5013683 = 7520525) B7520525
theorem B3342455 : Blo 2227435 3342455 := bstep (se 1 (by rfl) ⟨2506841, by rfl⟩ : syracuseStep 3342455 = 5013683) B5013683
theorem B2228303 : Blo 2227435 2228303 := bstep (se 1 (by rfl) ⟨1671227, by rfl⟩ : syracuseStep 2228303 = 3342455) B3342455
theorem B3342461 : Blo 2227435 3342461 := bbase (se 3 (by rfl) ⟨626711, by rfl⟩ : syracuseStep 3342461 = 1253423) (by norm_num)
theorem B2228307 : Blo 2227435 2228307 := bstep (se 1 (by rfl) ⟨1671230, by rfl⟩ : syracuseStep 2228307 = 3342461) B3342461
theorem B5013701 : Blo 2227435 5013701 := bbase (se 4 (by rfl) ⟨470034, by rfl⟩ : syracuseStep 5013701 = 940069) (by norm_num)
theorem B3342467 : Blo 2227435 3342467 := bstep (se 1 (by rfl) ⟨2506850, by rfl⟩ : syracuseStep 3342467 = 5013701) B5013701
theorem B2228311 : Blo 2227435 2228311 := bstep (se 1 (by rfl) ⟨1671233, by rfl⟩ : syracuseStep 2228311 = 3342467) B3342467
theorem B4517437 : Blo 2227435 4517437 := bbase (se 3 (by rfl) ⟨847019, by rfl⟩ : syracuseStep 4517437 = 1694039) (by norm_num)
theorem B6023249 : Blo 2227435 6023249 := bstep (se 2 (by rfl) ⟨2258718, by rfl⟩ : syracuseStep 6023249 = 4517437) B4517437
theorem B4015499 : Blo 2227435 4015499 := bstep (se 1 (by rfl) ⟨3011624, by rfl⟩ : syracuseStep 4015499 = 6023249) B6023249
theorem B10707997 : Blo 2227435 10707997 := bstep (se 3 (by rfl) ⟨2007749, by rfl⟩ : syracuseStep 10707997 = 4015499) B4015499
theorem B14277329 : Blo 2227435 14277329 := bstep (se 2 (by rfl) ⟨5353998, by rfl⟩ : syracuseStep 14277329 = 10707997) B10707997
theorem B9518219 : Blo 2227435 9518219 := bstep (se 1 (by rfl) ⟨7138664, by rfl⟩ : syracuseStep 9518219 = 14277329) B14277329
theorem B6345479 : Blo 2227435 6345479 := bstep (se 1 (by rfl) ⟨4759109, by rfl⟩ : syracuseStep 6345479 = 9518219) B9518219
theorem B4230319 : Blo 2227435 4230319 := bstep (se 1 (by rfl) ⟨3172739, by rfl⟩ : syracuseStep 4230319 = 6345479) B6345479
theorem B5640425 : Blo 2227435 5640425 := bstep (se 2 (by rfl) ⟨2115159, by rfl⟩ : syracuseStep 5640425 = 4230319) B4230319
theorem B3760283 : Blo 2227435 3760283 := bstep (se 1 (by rfl) ⟨2820212, by rfl⟩ : syracuseStep 3760283 = 5640425) B5640425
theorem B2506855 : Blo 2227435 2506855 := bstep (se 1 (by rfl) ⟨1880141, by rfl⟩ : syracuseStep 2506855 = 3760283) B3760283
theorem B3342473 : Blo 2227435 3342473 := bstep (se 2 (by rfl) ⟨1253427, by rfl⟩ : syracuseStep 3342473 = 2506855) B2506855
theorem B2228315 : Blo 2227435 2228315 := bstep (se 1 (by rfl) ⟨1671236, by rfl⟩ : syracuseStep 2228315 = 3342473) B3342473
theorem B11280869 : Blo 2227435 11280869 := bbase (se 4 (by rfl) ⟨1057581, by rfl⟩ : syracuseStep 11280869 = 2115163) (by norm_num)
theorem B7520579 : Blo 2227435 7520579 := bstep (se 1 (by rfl) ⟨5640434, by rfl⟩ : syracuseStep 7520579 = 11280869) B11280869
theorem B5013719 : Blo 2227435 5013719 := bstep (se 1 (by rfl) ⟨3760289, by rfl⟩ : syracuseStep 5013719 = 7520579) B7520579
theorem B3342479 : Blo 2227435 3342479 := bstep (se 1 (by rfl) ⟨2506859, by rfl⟩ : syracuseStep 3342479 = 5013719) B5013719
theorem B2228319 : Blo 2227435 2228319 := bstep (se 1 (by rfl) ⟨1671239, by rfl⟩ : syracuseStep 2228319 = 3342479) B3342479
theorem B3342485 : Blo 2227435 3342485 := bbase (se 6 (by rfl) ⟨78339, by rfl⟩ : syracuseStep 3342485 = 156679) (by norm_num)
theorem B2228323 : Blo 2227435 2228323 := bstep (se 1 (by rfl) ⟨1671242, by rfl⟩ : syracuseStep 2228323 = 3342485) B3342485
theorem B4517461 : Blo 2227435 4517461 := bbase (se 8 (by rfl) ⟨26469, by rfl⟩ : syracuseStep 4517461 = 52939) (by norm_num)
theorem B6023281 : Blo 2227435 6023281 := bstep (se 2 (by rfl) ⟨2258730, by rfl⟩ : syracuseStep 6023281 = 4517461) B4517461
theorem B8031041 : Blo 2227435 8031041 := bstep (se 2 (by rfl) ⟨3011640, by rfl⟩ : syracuseStep 8031041 = 6023281) B6023281
theorem B5354027 : Blo 2227435 5354027 := bstep (se 1 (by rfl) ⟨4015520, by rfl⟩ : syracuseStep 5354027 = 8031041) B8031041
theorem B3569351 : Blo 2227435 3569351 := bstep (se 1 (by rfl) ⟨2677013, by rfl⟩ : syracuseStep 3569351 = 5354027) B5354027
theorem B9518269 : Blo 2227435 9518269 := bstep (se 3 (by rfl) ⟨1784675, by rfl⟩ : syracuseStep 9518269 = 3569351) B3569351
theorem B12691025 : Blo 2227435 12691025 := bstep (se 2 (by rfl) ⟨4759134, by rfl⟩ : syracuseStep 12691025 = 9518269) B9518269
theorem B8460683 : Blo 2227435 8460683 := bstep (se 1 (by rfl) ⟨6345512, by rfl⟩ : syracuseStep 8460683 = 12691025) B12691025
theorem B5640455 : Blo 2227435 5640455 := bstep (se 1 (by rfl) ⟨4230341, by rfl⟩ : syracuseStep 5640455 = 8460683) B8460683
theorem B3760303 : Blo 2227435 3760303 := bstep (se 1 (by rfl) ⟨2820227, by rfl⟩ : syracuseStep 3760303 = 5640455) B5640455
theorem B5013737 : Blo 2227435 5013737 := bstep (se 2 (by rfl) ⟨1880151, by rfl⟩ : syracuseStep 5013737 = 3760303) B3760303
theorem B3342491 : Blo 2227435 3342491 := bstep (se 1 (by rfl) ⟨2506868, by rfl⟩ : syracuseStep 3342491 = 5013737) B5013737
theorem B2228327 : Blo 2227435 2228327 := bstep (se 1 (by rfl) ⟨1671245, by rfl⟩ : syracuseStep 2228327 = 3342491) B3342491
theorem B2506873 : Blo 2227435 2506873 := bbase (se 2 (by rfl) ⟨940077, by rfl⟩ : syracuseStep 2506873 = 1880155) (by norm_num)
theorem B3342497 : Blo 2227435 3342497 := bstep (se 2 (by rfl) ⟨1253436, by rfl⟩ : syracuseStep 3342497 = 2506873) B2506873
theorem B2228331 : Blo 2227435 2228331 := bstep (se 1 (by rfl) ⟨1671248, by rfl⟩ : syracuseStep 2228331 = 3342497) B3342497
theorem B3811621 : Blo 2227435 3811621 := bbase (se 4 (by rfl) ⟨357339, by rfl⟩ : syracuseStep 3811621 = 714679) (by norm_num)
theorem B5082161 : Blo 2227435 5082161 := bstep (se 2 (by rfl) ⟨1905810, by rfl⟩ : syracuseStep 5082161 = 3811621) B3811621
theorem B13552429 : Blo 2227435 13552429 := bstep (se 3 (by rfl) ⟨2541080, by rfl⟩ : syracuseStep 13552429 = 5082161) B5082161
theorem B18069905 : Blo 2227435 18069905 := bstep (se 2 (by rfl) ⟨6776214, by rfl⟩ : syracuseStep 18069905 = 13552429) B13552429
theorem B48186413 : Blo 2227435 48186413 := bstep (se 3 (by rfl) ⟨9034952, by rfl⟩ : syracuseStep 48186413 = 18069905) B18069905
theorem B32124275 : Blo 2227435 32124275 := bstep (se 1 (by rfl) ⟨24093206, by rfl⟩ : syracuseStep 32124275 = 48186413) B48186413
theorem B21416183 : Blo 2227435 21416183 := bstep (se 1 (by rfl) ⟨16062137, by rfl⟩ : syracuseStep 21416183 = 32124275) B32124275
theorem B14277455 : Blo 2227435 14277455 := bstep (se 1 (by rfl) ⟨10708091, by rfl⟩ : syracuseStep 14277455 = 21416183) B21416183
theorem B9518303 : Blo 2227435 9518303 := bstep (se 1 (by rfl) ⟨7138727, by rfl⟩ : syracuseStep 9518303 = 14277455) B14277455
theorem B6345535 : Blo 2227435 6345535 := bstep (se 1 (by rfl) ⟨4759151, by rfl⟩ : syracuseStep 6345535 = 9518303) B9518303
theorem B8460713 : Blo 2227435 8460713 := bstep (se 2 (by rfl) ⟨3172767, by rfl⟩ : syracuseStep 8460713 = 6345535) B6345535
theorem B5640475 : Blo 2227435 5640475 := bstep (se 1 (by rfl) ⟨4230356, by rfl⟩ : syracuseStep 5640475 = 8460713) B8460713
theorem B7520633 : Blo 2227435 7520633 := bstep (se 2 (by rfl) ⟨2820237, by rfl⟩ : syracuseStep 7520633 = 5640475) B5640475
theorem B5013755 : Blo 2227435 5013755 := bstep (se 1 (by rfl) ⟨3760316, by rfl⟩ : syracuseStep 5013755 = 7520633) B7520633
theorem B3342503 : Blo 2227435 3342503 := bstep (se 1 (by rfl) ⟨2506877, by rfl⟩ : syracuseStep 3342503 = 5013755) B5013755
theorem B2228335 : Blo 2227435 2228335 := bstep (se 1 (by rfl) ⟨1671251, by rfl⟩ : syracuseStep 2228335 = 3342503) B3342503
theorem B3342509 : Blo 2227435 3342509 := bbase (se 3 (by rfl) ⟨626720, by rfl⟩ : syracuseStep 3342509 = 1253441) (by norm_num)
theorem B2228339 : Blo 2227435 2228339 := bstep (se 1 (by rfl) ⟨1671254, by rfl⟩ : syracuseStep 2228339 = 3342509) B3342509
theorem B5013773 : Blo 2227435 5013773 := bbase (se 3 (by rfl) ⟨940082, by rfl⟩ : syracuseStep 5013773 = 1880165) (by norm_num)
theorem B3342515 : Blo 2227435 3342515 := bstep (se 1 (by rfl) ⟨2506886, by rfl⟩ : syracuseStep 3342515 = 5013773) B5013773
theorem B2228343 : Blo 2227435 2228343 := bstep (se 1 (by rfl) ⟨1671257, by rfl⟩ : syracuseStep 2228343 = 3342515) B3342515
theorem B2820253 : Blo 2227435 2820253 := bbase (se 3 (by rfl) ⟨528797, by rfl⟩ : syracuseStep 2820253 = 1057595) (by norm_num)
theorem B3760337 : Blo 2227435 3760337 := bstep (se 2 (by rfl) ⟨1410126, by rfl⟩ : syracuseStep 3760337 = 2820253) B2820253
theorem B2506891 : Blo 2227435 2506891 := bstep (se 1 (by rfl) ⟨1880168, by rfl⟩ : syracuseStep 2506891 = 3760337) B3760337
theorem B3342521 : Blo 2227435 3342521 := bstep (se 2 (by rfl) ⟨1253445, by rfl⟩ : syracuseStep 3342521 = 2506891) B2506891
theorem B2228347 : Blo 2227435 2228347 := bstep (se 1 (by rfl) ⟨1671260, by rfl⟩ : syracuseStep 2228347 = 3342521) B3342521
theorem B3569389 : Blo 2227435 3569389 := bbase (se 3 (by rfl) ⟨669260, by rfl⟩ : syracuseStep 3569389 = 1338521) (by norm_num)
theorem B19036741 : Blo 2227435 19036741 := bstep (se 4 (by rfl) ⟨1784694, by rfl⟩ : syracuseStep 19036741 = 3569389) B3569389
theorem B25382321 : Blo 2227435 25382321 := bstep (se 2 (by rfl) ⟨9518370, by rfl⟩ : syracuseStep 25382321 = 19036741) B19036741
theorem B16921547 : Blo 2227435 16921547 := bstep (se 1 (by rfl) ⟨12691160, by rfl⟩ : syracuseStep 16921547 = 25382321) B25382321
theorem B11281031 : Blo 2227435 11281031 := bstep (se 1 (by rfl) ⟨8460773, by rfl⟩ : syracuseStep 11281031 = 16921547) B16921547
theorem B7520687 : Blo 2227435 7520687 := bstep (se 1 (by rfl) ⟨5640515, by rfl⟩ : syracuseStep 7520687 = 11281031) B11281031
theorem B5013791 : Blo 2227435 5013791 := bstep (se 1 (by rfl) ⟨3760343, by rfl⟩ : syracuseStep 5013791 = 7520687) B7520687
theorem B3342527 : Blo 2227435 3342527 := bstep (se 1 (by rfl) ⟨2506895, by rfl⟩ : syracuseStep 3342527 = 5013791) B5013791
theorem B2228351 : Blo 2227435 2228351 := bstep (se 1 (by rfl) ⟨1671263, by rfl⟩ : syracuseStep 2228351 = 3342527) B3342527
theorem B3342533 : Blo 2227435 3342533 := bbase (se 4 (by rfl) ⟨313362, by rfl⟩ : syracuseStep 3342533 = 626725) (by norm_num)
theorem B2228355 : Blo 2227435 2228355 := bstep (se 1 (by rfl) ⟨1671266, by rfl⟩ : syracuseStep 2228355 = 3342533) B3342533
theorem B3760357 : Blo 2227435 3760357 := bbase (se 4 (by rfl) ⟨352533, by rfl⟩ : syracuseStep 3760357 = 705067) (by norm_num)
theorem B5013809 : Blo 2227435 5013809 := bstep (se 2 (by rfl) ⟨1880178, by rfl⟩ : syracuseStep 5013809 = 3760357) B3760357
theorem B3342539 : Blo 2227435 3342539 := bstep (se 1 (by rfl) ⟨2506904, by rfl⟩ : syracuseStep 3342539 = 5013809) B5013809
theorem B2228359 : Blo 2227435 2228359 := bstep (se 1 (by rfl) ⟨1671269, by rfl⟩ : syracuseStep 2228359 = 3342539) B3342539
theorem B2506909 : Blo 2227435 2506909 := bbase (se 3 (by rfl) ⟨470045, by rfl⟩ : syracuseStep 2506909 = 940091) (by norm_num)
theorem B3342545 : Blo 2227435 3342545 := bstep (se 2 (by rfl) ⟨1253454, by rfl⟩ : syracuseStep 3342545 = 2506909) B2506909
theorem B2228363 : Blo 2227435 2228363 := bstep (se 1 (by rfl) ⟨1671272, by rfl⟩ : syracuseStep 2228363 = 3342545) B3342545
theorem B7520741 : Blo 2227435 7520741 := bbase (se 4 (by rfl) ⟨705069, by rfl⟩ : syracuseStep 7520741 = 1410139) (by norm_num)
theorem B5013827 : Blo 2227435 5013827 := bstep (se 1 (by rfl) ⟨3760370, by rfl⟩ : syracuseStep 5013827 = 7520741) B7520741
theorem B3342551 : Blo 2227435 3342551 := bstep (se 1 (by rfl) ⟨2506913, by rfl⟩ : syracuseStep 3342551 = 5013827) B5013827
theorem B2228367 : Blo 2227435 2228367 := bstep (se 1 (by rfl) ⟨1671275, by rfl⟩ : syracuseStep 2228367 = 3342551) B3342551
theorem B3342557 : Blo 2227435 3342557 := bbase (se 3 (by rfl) ⟨626729, by rfl⟩ : syracuseStep 3342557 = 1253459) (by norm_num)
theorem B2228371 : Blo 2227435 2228371 := bstep (se 1 (by rfl) ⟨1671278, by rfl⟩ : syracuseStep 2228371 = 3342557) B3342557
theorem B5013845 : Blo 2227435 5013845 := bbase (se 10 (by rfl) ⟨7344, by rfl⟩ : syracuseStep 5013845 = 14689) (by norm_num)
theorem B3342563 : Blo 2227435 3342563 := bstep (se 1 (by rfl) ⟨2506922, by rfl⟩ : syracuseStep 3342563 = 5013845) B5013845
theorem B2228375 : Blo 2227435 2228375 := bstep (se 1 (by rfl) ⟨1671281, by rfl⟩ : syracuseStep 2228375 = 3342563) B3342563
theorem B8140805 : Blo 2227435 8140805 := bbase (se 4 (by rfl) ⟨763200, by rfl⟩ : syracuseStep 8140805 = 1526401) (by norm_num)
theorem B5427203 : Blo 2227435 5427203 := bstep (se 1 (by rfl) ⟨4070402, by rfl⟩ : syracuseStep 5427203 = 8140805) B8140805
theorem B14472541 : Blo 2227435 14472541 := bstep (se 3 (by rfl) ⟨2713601, by rfl⟩ : syracuseStep 14472541 = 5427203) B5427203
theorem B19296721 : Blo 2227435 19296721 := bstep (se 2 (by rfl) ⟨7236270, by rfl⟩ : syracuseStep 19296721 = 14472541) B14472541
theorem B102915845 : Blo 2227435 102915845 := bstep (se 4 (by rfl) ⟨9648360, by rfl⟩ : syracuseStep 102915845 = 19296721) B19296721
theorem B68610563 : Blo 2227435 68610563 := bstep (se 1 (by rfl) ⟨51457922, by rfl⟩ : syracuseStep 68610563 = 102915845) B102915845
theorem B45740375 : Blo 2227435 45740375 := bstep (se 1 (by rfl) ⟨34305281, by rfl⟩ : syracuseStep 45740375 = 68610563) B68610563
theorem B30493583 : Blo 2227435 30493583 := bstep (se 1 (by rfl) ⟨22870187, by rfl⟩ : syracuseStep 30493583 = 45740375) B45740375
theorem B20329055 : Blo 2227435 20329055 := bstep (se 1 (by rfl) ⟨15246791, by rfl⟩ : syracuseStep 20329055 = 30493583) B30493583
theorem B13552703 : Blo 2227435 13552703 := bstep (se 1 (by rfl) ⟨10164527, by rfl⟩ : syracuseStep 13552703 = 20329055) B20329055
theorem B9035135 : Blo 2227435 9035135 := bstep (se 1 (by rfl) ⟨6776351, by rfl⟩ : syracuseStep 9035135 = 13552703) B13552703
theorem B6023423 : Blo 2227435 6023423 := bstep (se 1 (by rfl) ⟨4517567, by rfl⟩ : syracuseStep 6023423 = 9035135) B9035135
theorem B4015615 : Blo 2227435 4015615 := bstep (se 1 (by rfl) ⟨3011711, by rfl⟩ : syracuseStep 4015615 = 6023423) B6023423
theorem B5354153 : Blo 2227435 5354153 := bstep (se 2 (by rfl) ⟨2007807, by rfl⟩ : syracuseStep 5354153 = 4015615) B4015615
theorem B3569435 : Blo 2227435 3569435 := bstep (se 1 (by rfl) ⟨2677076, by rfl⟩ : syracuseStep 3569435 = 5354153) B5354153
theorem B2379623 : Blo 2227435 2379623 := bstep (se 1 (by rfl) ⟨1784717, by rfl⟩ : syracuseStep 2379623 = 3569435) B3569435
theorem B6345661 : Blo 2227435 6345661 := bstep (se 3 (by rfl) ⟨1189811, by rfl⟩ : syracuseStep 6345661 = 2379623) B2379623
theorem B8460881 : Blo 2227435 8460881 := bstep (se 2 (by rfl) ⟨3172830, by rfl⟩ : syracuseStep 8460881 = 6345661) B6345661
theorem B5640587 : Blo 2227435 5640587 := bstep (se 1 (by rfl) ⟨4230440, by rfl⟩ : syracuseStep 5640587 = 8460881) B8460881
theorem B3760391 : Blo 2227435 3760391 := bstep (se 1 (by rfl) ⟨2820293, by rfl⟩ : syracuseStep 3760391 = 5640587) B5640587
theorem B2506927 : Blo 2227435 2506927 := bstep (se 1 (by rfl) ⟨1880195, by rfl⟩ : syracuseStep 2506927 = 3760391) B3760391
theorem B3342569 : Blo 2227435 3342569 := bstep (se 2 (by rfl) ⟨1253463, by rfl⟩ : syracuseStep 3342569 = 2506927) B2506927
theorem B2228379 : Blo 2227435 2228379 := bstep (se 1 (by rfl) ⟨1671284, by rfl⟩ : syracuseStep 2228379 = 3342569) B3342569
theorem B3216125 : Blo 2227435 3216125 := bbase (se 3 (by rfl) ⟨603023, by rfl⟩ : syracuseStep 3216125 = 1206047) (by norm_num)
theorem B8576333 : Blo 2227435 8576333 := bstep (se 3 (by rfl) ⟨1608062, by rfl⟩ : syracuseStep 8576333 = 3216125) B3216125
theorem B5717555 : Blo 2227435 5717555 := bstep (se 1 (by rfl) ⟨4288166, by rfl⟩ : syracuseStep 5717555 = 8576333) B8576333
theorem B3811703 : Blo 2227435 3811703 := bstep (se 1 (by rfl) ⟨2858777, by rfl⟩ : syracuseStep 3811703 = 5717555) B5717555
theorem B10164541 : Blo 2227435 10164541 := bstep (se 3 (by rfl) ⟨1905851, by rfl⟩ : syracuseStep 10164541 = 3811703) B3811703
theorem B13552721 : Blo 2227435 13552721 := bstep (se 2 (by rfl) ⟨5082270, by rfl⟩ : syracuseStep 13552721 = 10164541) B10164541
theorem B9035147 : Blo 2227435 9035147 := bstep (se 1 (by rfl) ⟨6776360, by rfl⟩ : syracuseStep 9035147 = 13552721) B13552721
theorem B6023431 : Blo 2227435 6023431 := bstep (se 1 (by rfl) ⟨4517573, by rfl⟩ : syracuseStep 6023431 = 9035147) B9035147
theorem B8031241 : Blo 2227435 8031241 := bstep (se 2 (by rfl) ⟨3011715, by rfl⟩ : syracuseStep 8031241 = 6023431) B6023431
theorem B42833285 : Blo 2227435 42833285 := bstep (se 4 (by rfl) ⟨4015620, by rfl⟩ : syracuseStep 42833285 = 8031241) B8031241
theorem B28555523 : Blo 2227435 28555523 := bstep (se 1 (by rfl) ⟨21416642, by rfl⟩ : syracuseStep 28555523 = 42833285) B42833285
theorem B19037015 : Blo 2227435 19037015 := bstep (se 1 (by rfl) ⟨14277761, by rfl⟩ : syracuseStep 19037015 = 28555523) B28555523
theorem B12691343 : Blo 2227435 12691343 := bstep (se 1 (by rfl) ⟨9518507, by rfl⟩ : syracuseStep 12691343 = 19037015) B19037015
theorem B8460895 : Blo 2227435 8460895 := bstep (se 1 (by rfl) ⟨6345671, by rfl⟩ : syracuseStep 8460895 = 12691343) B12691343
theorem B11281193 : Blo 2227435 11281193 := bstep (se 2 (by rfl) ⟨4230447, by rfl⟩ : syracuseStep 11281193 = 8460895) B8460895
theorem B7520795 : Blo 2227435 7520795 := bstep (se 1 (by rfl) ⟨5640596, by rfl⟩ : syracuseStep 7520795 = 11281193) B11281193
theorem B5013863 : Blo 2227435 5013863 := bstep (se 1 (by rfl) ⟨3760397, by rfl⟩ : syracuseStep 5013863 = 7520795) B7520795
theorem B3342575 : Blo 2227435 3342575 := bstep (se 1 (by rfl) ⟨2506931, by rfl⟩ : syracuseStep 3342575 = 5013863) B5013863
theorem B2228383 : Blo 2227435 2228383 := bstep (se 1 (by rfl) ⟨1671287, by rfl⟩ : syracuseStep 2228383 = 3342575) B3342575
theorem B3342581 : Blo 2227435 3342581 := bbase (se 5 (by rfl) ⟨156683, by rfl⟩ : syracuseStep 3342581 = 313367) (by norm_num)
theorem B2228387 : Blo 2227435 2228387 := bstep (se 1 (by rfl) ⟨1671290, by rfl⟩ : syracuseStep 2228387 = 3342581) B3342581
theorem B3811717 : Blo 2227435 3811717 := bbase (se 4 (by rfl) ⟨357348, by rfl⟩ : syracuseStep 3811717 = 714697) (by norm_num)
theorem B20329157 : Blo 2227435 20329157 := bstep (se 4 (by rfl) ⟨1905858, by rfl⟩ : syracuseStep 20329157 = 3811717) B3811717
theorem B13552771 : Blo 2227435 13552771 := bstep (se 1 (by rfl) ⟨10164578, by rfl⟩ : syracuseStep 13552771 = 20329157) B20329157
theorem B18070361 : Blo 2227435 18070361 := bstep (se 2 (by rfl) ⟨6776385, by rfl⟩ : syracuseStep 18070361 = 13552771) B13552771
theorem B12046907 : Blo 2227435 12046907 := bstep (se 1 (by rfl) ⟨9035180, by rfl⟩ : syracuseStep 12046907 = 18070361) B18070361
theorem B32125085 : Blo 2227435 32125085 := bstep (se 3 (by rfl) ⟨6023453, by rfl⟩ : syracuseStep 32125085 = 12046907) B12046907
theorem B21416723 : Blo 2227435 21416723 := bstep (se 1 (by rfl) ⟨16062542, by rfl⟩ : syracuseStep 21416723 = 32125085) B32125085
theorem B14277815 : Blo 2227435 14277815 := bstep (se 1 (by rfl) ⟨10708361, by rfl⟩ : syracuseStep 14277815 = 21416723) B21416723
theorem B9518543 : Blo 2227435 9518543 := bstep (se 1 (by rfl) ⟨7138907, by rfl⟩ : syracuseStep 9518543 = 14277815) B14277815
theorem B6345695 : Blo 2227435 6345695 := bstep (se 1 (by rfl) ⟨4759271, by rfl⟩ : syracuseStep 6345695 = 9518543) B9518543
theorem B4230463 : Blo 2227435 4230463 := bstep (se 1 (by rfl) ⟨3172847, by rfl⟩ : syracuseStep 4230463 = 6345695) B6345695
theorem B5640617 : Blo 2227435 5640617 := bstep (se 2 (by rfl) ⟨2115231, by rfl⟩ : syracuseStep 5640617 = 4230463) B4230463
theorem B3760411 : Blo 2227435 3760411 := bstep (se 1 (by rfl) ⟨2820308, by rfl⟩ : syracuseStep 3760411 = 5640617) B5640617
theorem B5013881 : Blo 2227435 5013881 := bstep (se 2 (by rfl) ⟨1880205, by rfl⟩ : syracuseStep 5013881 = 3760411) B3760411
theorem B3342587 : Blo 2227435 3342587 := bstep (se 1 (by rfl) ⟨2506940, by rfl⟩ : syracuseStep 3342587 = 5013881) B5013881
theorem B2228391 : Blo 2227435 2228391 := bstep (se 1 (by rfl) ⟨1671293, by rfl⟩ : syracuseStep 2228391 = 3342587) B3342587
theorem B2506945 : Blo 2227435 2506945 := bbase (se 2 (by rfl) ⟨940104, by rfl⟩ : syracuseStep 2506945 = 1880209) (by norm_num)
theorem B3342593 : Blo 2227435 3342593 := bstep (se 2 (by rfl) ⟨1253472, by rfl⟩ : syracuseStep 3342593 = 2506945) B2506945
theorem B2228395 : Blo 2227435 2228395 := bstep (se 1 (by rfl) ⟨1671296, by rfl⟩ : syracuseStep 2228395 = 3342593) B3342593
theorem B5640637 : Blo 2227435 5640637 := bbase (se 3 (by rfl) ⟨1057619, by rfl⟩ : syracuseStep 5640637 = 2115239) (by norm_num)
theorem B7520849 : Blo 2227435 7520849 := bstep (se 2 (by rfl) ⟨2820318, by rfl⟩ : syracuseStep 7520849 = 5640637) B5640637
theorem B5013899 : Blo 2227435 5013899 := bstep (se 1 (by rfl) ⟨3760424, by rfl⟩ : syracuseStep 5013899 = 7520849) B7520849
theorem B3342599 : Blo 2227435 3342599 := bstep (se 1 (by rfl) ⟨2506949, by rfl⟩ : syracuseStep 3342599 = 5013899) B5013899
theorem B2228399 : Blo 2227435 2228399 := bstep (se 1 (by rfl) ⟨1671299, by rfl⟩ : syracuseStep 2228399 = 3342599) B3342599
theorem B3342605 : Blo 2227435 3342605 := bbase (se 3 (by rfl) ⟨626738, by rfl⟩ : syracuseStep 3342605 = 1253477) (by norm_num)
theorem B2228403 : Blo 2227435 2228403 := bstep (se 1 (by rfl) ⟨1671302, by rfl⟩ : syracuseStep 2228403 = 3342605) B3342605
theorem B5013917 : Blo 2227435 5013917 := bbase (se 3 (by rfl) ⟨940109, by rfl⟩ : syracuseStep 5013917 = 1880219) (by norm_num)
theorem B3342611 : Blo 2227435 3342611 := bstep (se 1 (by rfl) ⟨2506958, by rfl⟩ : syracuseStep 3342611 = 5013917) B5013917
theorem B2228407 : Blo 2227435 2228407 := bstep (se 1 (by rfl) ⟨1671305, by rfl⟩ : syracuseStep 2228407 = 3342611) B3342611
theorem B3760445 : Blo 2227435 3760445 := bbase (se 3 (by rfl) ⟨705083, by rfl⟩ : syracuseStep 3760445 = 1410167) (by norm_num)
theorem B2506963 : Blo 2227435 2506963 := bstep (se 1 (by rfl) ⟨1880222, by rfl⟩ : syracuseStep 2506963 = 3760445) B3760445
theorem B3342617 : Blo 2227435 3342617 := bstep (se 2 (by rfl) ⟨1253481, by rfl⟩ : syracuseStep 3342617 = 2506963) B2506963
theorem B2228411 : Blo 2227435 2228411 := bstep (se 1 (by rfl) ⟨1671308, by rfl⟩ : syracuseStep 2228411 = 3342617) B3342617
theorem B2379661 : Blo 2227435 2379661 := bbase (se 3 (by rfl) ⟨446186, by rfl⟩ : syracuseStep 2379661 = 892373) (by norm_num)
theorem B12691525 : Blo 2227435 12691525 := bstep (se 4 (by rfl) ⟨1189830, by rfl⟩ : syracuseStep 12691525 = 2379661) B2379661
theorem B16922033 : Blo 2227435 16922033 := bstep (se 2 (by rfl) ⟨6345762, by rfl⟩ : syracuseStep 16922033 = 12691525) B12691525
theorem B11281355 : Blo 2227435 11281355 := bstep (se 1 (by rfl) ⟨8461016, by rfl⟩ : syracuseStep 11281355 = 16922033) B16922033
theorem B7520903 : Blo 2227435 7520903 := bstep (se 1 (by rfl) ⟨5640677, by rfl⟩ : syracuseStep 7520903 = 11281355) B11281355
theorem B5013935 : Blo 2227435 5013935 := bstep (se 1 (by rfl) ⟨3760451, by rfl⟩ : syracuseStep 5013935 = 7520903) B7520903
theorem B3342623 : Blo 2227435 3342623 := bstep (se 1 (by rfl) ⟨2506967, by rfl⟩ : syracuseStep 3342623 = 5013935) B5013935
theorem B2228415 : Blo 2227435 2228415 := bstep (se 1 (by rfl) ⟨1671311, by rfl⟩ : syracuseStep 2228415 = 3342623) B3342623
theorem B3342629 : Blo 2227435 3342629 := bbase (se 4 (by rfl) ⟨313371, by rfl⟩ : syracuseStep 3342629 = 626743) (by norm_num)
theorem B2228419 : Blo 2227435 2228419 := bstep (se 1 (by rfl) ⟨1671314, by rfl⟩ : syracuseStep 2228419 = 3342629) B3342629
theorem B2820349 : Blo 2227435 2820349 := bbase (se 3 (by rfl) ⟨528815, by rfl⟩ : syracuseStep 2820349 = 1057631) (by norm_num)
theorem B3760465 : Blo 2227435 3760465 := bstep (se 2 (by rfl) ⟨1410174, by rfl⟩ : syracuseStep 3760465 = 2820349) B2820349
theorem B5013953 : Blo 2227435 5013953 := bstep (se 2 (by rfl) ⟨1880232, by rfl⟩ : syracuseStep 5013953 = 3760465) B3760465
theorem B3342635 : Blo 2227435 3342635 := bstep (se 1 (by rfl) ⟨2506976, by rfl⟩ : syracuseStep 3342635 = 5013953) B5013953
theorem B2228423 : Blo 2227435 2228423 := bstep (se 1 (by rfl) ⟨1671317, by rfl⟩ : syracuseStep 2228423 = 3342635) B3342635
theorem B2506981 : Blo 2227435 2506981 := bbase (se 4 (by rfl) ⟨235029, by rfl⟩ : syracuseStep 2506981 = 470059) (by norm_num)
theorem B3342641 : Blo 2227435 3342641 := bstep (se 2 (by rfl) ⟨1253490, by rfl⟩ : syracuseStep 3342641 = 2506981) B2506981
theorem B2228427 : Blo 2227435 2228427 := bstep (se 1 (by rfl) ⟨1671320, by rfl⟩ : syracuseStep 2228427 = 3342641) B3342641
theorem B4759357 : Blo 2227435 4759357 := bbase (se 3 (by rfl) ⟨892379, by rfl⟩ : syracuseStep 4759357 = 1784759) (by norm_num)
theorem B6345809 : Blo 2227435 6345809 := bstep (se 2 (by rfl) ⟨2379678, by rfl⟩ : syracuseStep 6345809 = 4759357) B4759357
theorem B4230539 : Blo 2227435 4230539 := bstep (se 1 (by rfl) ⟨3172904, by rfl⟩ : syracuseStep 4230539 = 6345809) B6345809
theorem B2820359 : Blo 2227435 2820359 := bstep (se 1 (by rfl) ⟨2115269, by rfl⟩ : syracuseStep 2820359 = 4230539) B4230539
theorem B7520957 : Blo 2227435 7520957 := bstep (se 3 (by rfl) ⟨1410179, by rfl⟩ : syracuseStep 7520957 = 2820359) B2820359
theorem B5013971 : Blo 2227435 5013971 := bstep (se 1 (by rfl) ⟨3760478, by rfl⟩ : syracuseStep 5013971 = 7520957) B7520957
theorem B3342647 : Blo 2227435 3342647 := bstep (se 1 (by rfl) ⟨2506985, by rfl⟩ : syracuseStep 3342647 = 5013971) B5013971
theorem B2228431 : Blo 2227435 2228431 := bstep (se 1 (by rfl) ⟨1671323, by rfl⟩ : syracuseStep 2228431 = 3342647) B3342647
theorem B3342653 : Blo 2227435 3342653 := bbase (se 3 (by rfl) ⟨626747, by rfl⟩ : syracuseStep 3342653 = 1253495) (by norm_num)
theorem B2228435 : Blo 2227435 2228435 := bstep (se 1 (by rfl) ⟨1671326, by rfl⟩ : syracuseStep 2228435 = 3342653) B3342653
theorem B5013989 : Blo 2227435 5013989 := bbase (se 4 (by rfl) ⟨470061, by rfl⟩ : syracuseStep 5013989 = 940123) (by norm_num)
theorem B3342659 : Blo 2227435 3342659 := bstep (se 1 (by rfl) ⟨2506994, by rfl⟩ : syracuseStep 3342659 = 5013989) B5013989
theorem B2228439 : Blo 2227435 2228439 := bstep (se 1 (by rfl) ⟨1671329, by rfl⟩ : syracuseStep 2228439 = 3342659) B3342659
theorem B5640749 : Blo 2227435 5640749 := bbase (se 3 (by rfl) ⟨1057640, by rfl⟩ : syracuseStep 5640749 = 2115281) (by norm_num)
theorem B3760499 : Blo 2227435 3760499 := bstep (se 1 (by rfl) ⟨2820374, by rfl⟩ : syracuseStep 3760499 = 5640749) B5640749
theorem B2506999 : Blo 2227435 2506999 := bstep (se 1 (by rfl) ⟨1880249, by rfl⟩ : syracuseStep 2506999 = 3760499) B3760499
theorem B3342665 : Blo 2227435 3342665 := bstep (se 2 (by rfl) ⟨1253499, by rfl⟩ : syracuseStep 3342665 = 2506999) B2506999
theorem B2228443 : Blo 2227435 2228443 := bstep (se 1 (by rfl) ⟨1671332, by rfl⟩ : syracuseStep 2228443 = 3342665) B3342665
theorem B24094421 : Blo 2227435 24094421 := bbase (se 7 (by rfl) ⟨282356, by rfl⟩ : syracuseStep 24094421 = 564713) (by norm_num)
theorem B16062947 : Blo 2227435 16062947 := bstep (se 1 (by rfl) ⟨12047210, by rfl⟩ : syracuseStep 16062947 = 24094421) B24094421
theorem B10708631 : Blo 2227435 10708631 := bstep (se 1 (by rfl) ⟨8031473, by rfl⟩ : syracuseStep 10708631 = 16062947) B16062947
theorem B7139087 : Blo 2227435 7139087 := bstep (se 1 (by rfl) ⟨5354315, by rfl⟩ : syracuseStep 7139087 = 10708631) B10708631
theorem B4759391 : Blo 2227435 4759391 := bstep (se 1 (by rfl) ⟨3569543, by rfl⟩ : syracuseStep 4759391 = 7139087) B7139087
theorem B3172927 : Blo 2227435 3172927 := bstep (se 1 (by rfl) ⟨2379695, by rfl⟩ : syracuseStep 3172927 = 4759391) B4759391
theorem B4230569 : Blo 2227435 4230569 := bstep (se 2 (by rfl) ⟨1586463, by rfl⟩ : syracuseStep 4230569 = 3172927) B3172927
theorem B11281517 : Blo 2227435 11281517 := bstep (se 3 (by rfl) ⟨2115284, by rfl⟩ : syracuseStep 11281517 = 4230569) B4230569
theorem B7521011 : Blo 2227435 7521011 := bstep (se 1 (by rfl) ⟨5640758, by rfl⟩ : syracuseStep 7521011 = 11281517) B11281517
theorem B5014007 : Blo 2227435 5014007 := bstep (se 1 (by rfl) ⟨3760505, by rfl⟩ : syracuseStep 5014007 = 7521011) B7521011
theorem B3342671 : Blo 2227435 3342671 := bstep (se 1 (by rfl) ⟨2507003, by rfl⟩ : syracuseStep 3342671 = 5014007) B5014007
theorem B2228447 : Blo 2227435 2228447 := bstep (se 1 (by rfl) ⟨1671335, by rfl⟩ : syracuseStep 2228447 = 3342671) B3342671
theorem B3342677 : Blo 2227435 3342677 := bbase (se 10 (by rfl) ⟨4896, by rfl⟩ : syracuseStep 3342677 = 9793) (by norm_num)
theorem B2228451 : Blo 2227435 2228451 := bstep (se 1 (by rfl) ⟨1671338, by rfl⟩ : syracuseStep 2228451 = 3342677) B3342677
theorem B6345877 : Blo 2227435 6345877 := bbase (se 6 (by rfl) ⟨148731, by rfl⟩ : syracuseStep 6345877 = 297463) (by norm_num)
theorem B8461169 : Blo 2227435 8461169 := bstep (se 2 (by rfl) ⟨3172938, by rfl⟩ : syracuseStep 8461169 = 6345877) B6345877
theorem B5640779 : Blo 2227435 5640779 := bstep (se 1 (by rfl) ⟨4230584, by rfl⟩ : syracuseStep 5640779 = 8461169) B8461169
theorem B3760519 : Blo 2227435 3760519 := bstep (se 1 (by rfl) ⟨2820389, by rfl⟩ : syracuseStep 3760519 = 5640779) B5640779
theorem B5014025 : Blo 2227435 5014025 := bstep (se 2 (by rfl) ⟨1880259, by rfl⟩ : syracuseStep 5014025 = 3760519) B3760519
theorem B3342683 : Blo 2227435 3342683 := bstep (se 1 (by rfl) ⟨2507012, by rfl⟩ : syracuseStep 3342683 = 5014025) B5014025
theorem B2228455 : Blo 2227435 2228455 := bstep (se 1 (by rfl) ⟨1671341, by rfl⟩ : syracuseStep 2228455 = 3342683) B3342683
theorem B2507017 : Blo 2227435 2507017 := bbase (se 2 (by rfl) ⟨940131, by rfl⟩ : syracuseStep 2507017 = 1880263) (by norm_num)
theorem B3342689 : Blo 2227435 3342689 := bstep (se 2 (by rfl) ⟨1253508, by rfl⟩ : syracuseStep 3342689 = 2507017) B2507017
theorem B2228459 : Blo 2227435 2228459 := bstep (se 1 (by rfl) ⟨1671344, by rfl⟩ : syracuseStep 2228459 = 3342689) B3342689
theorem B4015765 : Blo 2227435 4015765 := bbase (se 6 (by rfl) ⟨94119, by rfl⟩ : syracuseStep 4015765 = 188239) (by norm_num)
theorem B5354353 : Blo 2227435 5354353 := bstep (se 2 (by rfl) ⟨2007882, by rfl⟩ : syracuseStep 5354353 = 4015765) B4015765
theorem B28556549 : Blo 2227435 28556549 := bstep (se 4 (by rfl) ⟨2677176, by rfl⟩ : syracuseStep 28556549 = 5354353) B5354353
theorem B19037699 : Blo 2227435 19037699 := bstep (se 1 (by rfl) ⟨14278274, by rfl⟩ : syracuseStep 19037699 = 28556549) B28556549
theorem B12691799 : Blo 2227435 12691799 := bstep (se 1 (by rfl) ⟨9518849, by rfl⟩ : syracuseStep 12691799 = 19037699) B19037699
theorem B8461199 : Blo 2227435 8461199 := bstep (se 1 (by rfl) ⟨6345899, by rfl⟩ : syracuseStep 8461199 = 12691799) B12691799
theorem B5640799 : Blo 2227435 5640799 := bstep (se 1 (by rfl) ⟨4230599, by rfl⟩ : syracuseStep 5640799 = 8461199) B8461199
theorem B7521065 : Blo 2227435 7521065 := bstep (se 2 (by rfl) ⟨2820399, by rfl⟩ : syracuseStep 7521065 = 5640799) B5640799
theorem B5014043 : Blo 2227435 5014043 := bstep (se 1 (by rfl) ⟨3760532, by rfl⟩ : syracuseStep 5014043 = 7521065) B7521065
theorem B3342695 : Blo 2227435 3342695 := bstep (se 1 (by rfl) ⟨2507021, by rfl⟩ : syracuseStep 3342695 = 5014043) B5014043
theorem B2228463 : Blo 2227435 2228463 := bstep (se 1 (by rfl) ⟨1671347, by rfl⟩ : syracuseStep 2228463 = 3342695) B3342695
theorem B3342701 : Blo 2227435 3342701 := bbase (se 3 (by rfl) ⟨626756, by rfl⟩ : syracuseStep 3342701 = 1253513) (by norm_num)
theorem B2228467 : Blo 2227435 2228467 := bstep (se 1 (by rfl) ⟨1671350, by rfl⟩ : syracuseStep 2228467 = 3342701) B3342701
theorem B5014061 : Blo 2227435 5014061 := bbase (se 3 (by rfl) ⟨940136, by rfl⟩ : syracuseStep 5014061 = 1880273) (by norm_num)
theorem B3342707 : Blo 2227435 3342707 := bstep (se 1 (by rfl) ⟨2507030, by rfl⟩ : syracuseStep 3342707 = 5014061) B5014061
theorem B2228471 : Blo 2227435 2228471 := bstep (se 1 (by rfl) ⟨1671353, by rfl⟩ : syracuseStep 2228471 = 3342707) B3342707
theorem B2541241 : Blo 2227435 2541241 := bbase (se 2 (by rfl) ⟨952965, by rfl⟩ : syracuseStep 2541241 = 1905931) (by norm_num)
theorem B3388321 : Blo 2227435 3388321 := bstep (se 2 (by rfl) ⟨1270620, by rfl⟩ : syracuseStep 3388321 = 2541241) B2541241
theorem B18071045 : Blo 2227435 18071045 := bstep (se 4 (by rfl) ⟨1694160, by rfl⟩ : syracuseStep 18071045 = 3388321) B3388321
theorem B12047363 : Blo 2227435 12047363 := bstep (se 1 (by rfl) ⟨9035522, by rfl⟩ : syracuseStep 12047363 = 18071045) B18071045
theorem B8031575 : Blo 2227435 8031575 := bstep (se 1 (by rfl) ⟨6023681, by rfl⟩ : syracuseStep 8031575 = 12047363) B12047363
theorem B21417533 : Blo 2227435 21417533 := bstep (se 3 (by rfl) ⟨4015787, by rfl⟩ : syracuseStep 21417533 = 8031575) B8031575
theorem B14278355 : Blo 2227435 14278355 := bstep (se 1 (by rfl) ⟨10708766, by rfl⟩ : syracuseStep 14278355 = 21417533) B21417533
theorem B9518903 : Blo 2227435 9518903 := bstep (se 1 (by rfl) ⟨7139177, by rfl⟩ : syracuseStep 9518903 = 14278355) B14278355
theorem B6345935 : Blo 2227435 6345935 := bstep (se 1 (by rfl) ⟨4759451, by rfl⟩ : syracuseStep 6345935 = 9518903) B9518903
theorem B4230623 : Blo 2227435 4230623 := bstep (se 1 (by rfl) ⟨3172967, by rfl⟩ : syracuseStep 4230623 = 6345935) B6345935
theorem B2820415 : Blo 2227435 2820415 := bstep (se 1 (by rfl) ⟨2115311, by rfl⟩ : syracuseStep 2820415 = 4230623) B4230623
theorem B3760553 : Blo 2227435 3760553 := bstep (se 2 (by rfl) ⟨1410207, by rfl⟩ : syracuseStep 3760553 = 2820415) B2820415
theorem B2507035 : Blo 2227435 2507035 := bstep (se 1 (by rfl) ⟨1880276, by rfl⟩ : syracuseStep 2507035 = 3760553) B3760553
theorem B3342713 : Blo 2227435 3342713 := bstep (se 2 (by rfl) ⟨1253517, by rfl⟩ : syracuseStep 3342713 = 2507035) B2507035
theorem B2228475 : Blo 2227435 2228475 := bstep (se 1 (by rfl) ⟨1671356, by rfl⟩ : syracuseStep 2228475 = 3342713) B3342713
theorem B38075669 : Blo 2227435 38075669 := bbase (se 6 (by rfl) ⟨892398, by rfl⟩ : syracuseStep 38075669 = 1784797) (by norm_num)
theorem B25383779 : Blo 2227435 25383779 := bstep (se 1 (by rfl) ⟨19037834, by rfl⟩ : syracuseStep 25383779 = 38075669) B38075669
theorem B16922519 : Blo 2227435 16922519 := bstep (se 1 (by rfl) ⟨12691889, by rfl⟩ : syracuseStep 16922519 = 25383779) B25383779
theorem B11281679 : Blo 2227435 11281679 := bstep (se 1 (by rfl) ⟨8461259, by rfl⟩ : syracuseStep 11281679 = 16922519) B16922519
theorem B7521119 : Blo 2227435 7521119 := bstep (se 1 (by rfl) ⟨5640839, by rfl⟩ : syracuseStep 7521119 = 11281679) B11281679
theorem B5014079 : Blo 2227435 5014079 := bstep (se 1 (by rfl) ⟨3760559, by rfl⟩ : syracuseStep 5014079 = 7521119) B7521119
theorem B3342719 : Blo 2227435 3342719 := bstep (se 1 (by rfl) ⟨2507039, by rfl⟩ : syracuseStep 3342719 = 5014079) B5014079
theorem B2228479 : Blo 2227435 2228479 := bstep (se 1 (by rfl) ⟨1671359, by rfl⟩ : syracuseStep 2228479 = 3342719) B3342719
theorem B3342725 : Blo 2227435 3342725 := bbase (se 4 (by rfl) ⟨313380, by rfl⟩ : syracuseStep 3342725 = 626761) (by norm_num)
theorem B2228483 : Blo 2227435 2228483 := bstep (se 1 (by rfl) ⟨1671362, by rfl⟩ : syracuseStep 2228483 = 3342725) B3342725
theorem B3760573 : Blo 2227435 3760573 := bbase (se 3 (by rfl) ⟨705107, by rfl⟩ : syracuseStep 3760573 = 1410215) (by norm_num)
theorem B5014097 : Blo 2227435 5014097 := bstep (se 2 (by rfl) ⟨1880286, by rfl⟩ : syracuseStep 5014097 = 3760573) B3760573
theorem B3342731 : Blo 2227435 3342731 := bstep (se 1 (by rfl) ⟨2507048, by rfl⟩ : syracuseStep 3342731 = 5014097) B5014097
theorem B2228487 : Blo 2227435 2228487 := bstep (se 1 (by rfl) ⟨1671365, by rfl⟩ : syracuseStep 2228487 = 3342731) B3342731
theorem B2507053 : Blo 2227435 2507053 := bbase (se 3 (by rfl) ⟨470072, by rfl⟩ : syracuseStep 2507053 = 940145) (by norm_num)
theorem B3342737 : Blo 2227435 3342737 := bstep (se 2 (by rfl) ⟨1253526, by rfl⟩ : syracuseStep 3342737 = 2507053) B2507053
theorem B2228491 : Blo 2227435 2228491 := bstep (se 1 (by rfl) ⟨1671368, by rfl⟩ : syracuseStep 2228491 = 3342737) B3342737
theorem B7521173 : Blo 2227435 7521173 := bbase (se 6 (by rfl) ⟨176277, by rfl⟩ : syracuseStep 7521173 = 352555) (by norm_num)
theorem B5014115 : Blo 2227435 5014115 := bstep (se 1 (by rfl) ⟨3760586, by rfl⟩ : syracuseStep 5014115 = 7521173) B7521173
theorem B3342743 : Blo 2227435 3342743 := bstep (se 1 (by rfl) ⟨2507057, by rfl⟩ : syracuseStep 3342743 = 5014115) B5014115
theorem B2228495 : Blo 2227435 2228495 := bstep (se 1 (by rfl) ⟨1671371, by rfl⟩ : syracuseStep 2228495 = 3342743) B3342743
theorem B3342749 : Blo 2227435 3342749 := bbase (se 3 (by rfl) ⟨626765, by rfl⟩ : syracuseStep 3342749 = 1253531) (by norm_num)
theorem B2228499 : Blo 2227435 2228499 := bstep (se 1 (by rfl) ⟨1671374, by rfl⟩ : syracuseStep 2228499 = 3342749) B3342749
theorem B5014133 : Blo 2227435 5014133 := bbase (se 5 (by rfl) ⟨235037, by rfl⟩ : syracuseStep 5014133 = 470075) (by norm_num)
theorem B3342755 : Blo 2227435 3342755 := bstep (se 1 (by rfl) ⟨2507066, by rfl⟩ : syracuseStep 3342755 = 5014133) B5014133
theorem B2228503 : Blo 2227435 2228503 := bstep (se 1 (by rfl) ⟨1671377, by rfl⟩ : syracuseStep 2228503 = 3342755) B3342755
theorem B2541277 : Blo 2227435 2541277 := bbase (se 3 (by rfl) ⟨476489, by rfl⟩ : syracuseStep 2541277 = 952979) (by norm_num)
theorem B13553477 : Blo 2227435 13553477 := bstep (se 4 (by rfl) ⟨1270638, by rfl⟩ : syracuseStep 13553477 = 2541277) B2541277
theorem B9035651 : Blo 2227435 9035651 := bstep (se 1 (by rfl) ⟨6776738, by rfl⟩ : syracuseStep 9035651 = 13553477) B13553477
theorem B24095069 : Blo 2227435 24095069 := bstep (se 3 (by rfl) ⟨4517825, by rfl⟩ : syracuseStep 24095069 = 9035651) B9035651
theorem B16063379 : Blo 2227435 16063379 := bstep (se 1 (by rfl) ⟨12047534, by rfl⟩ : syracuseStep 16063379 = 24095069) B24095069
theorem B10708919 : Blo 2227435 10708919 := bstep (se 1 (by rfl) ⟨8031689, by rfl⟩ : syracuseStep 10708919 = 16063379) B16063379
theorem B7139279 : Blo 2227435 7139279 := bstep (se 1 (by rfl) ⟨5354459, by rfl⟩ : syracuseStep 7139279 = 10708919) B10708919
theorem B19038077 : Blo 2227435 19038077 := bstep (se 3 (by rfl) ⟨3569639, by rfl⟩ : syracuseStep 19038077 = 7139279) B7139279
theorem B12692051 : Blo 2227435 12692051 := bstep (se 1 (by rfl) ⟨9519038, by rfl⟩ : syracuseStep 12692051 = 19038077) B19038077
theorem B8461367 : Blo 2227435 8461367 := bstep (se 1 (by rfl) ⟨6346025, by rfl⟩ : syracuseStep 8461367 = 12692051) B12692051
theorem B5640911 : Blo 2227435 5640911 := bstep (se 1 (by rfl) ⟨4230683, by rfl⟩ : syracuseStep 5640911 = 8461367) B8461367
theorem B3760607 : Blo 2227435 3760607 := bstep (se 1 (by rfl) ⟨2820455, by rfl⟩ : syracuseStep 3760607 = 5640911) B5640911
theorem B2507071 : Blo 2227435 2507071 := bstep (se 1 (by rfl) ⟨1880303, by rfl⟩ : syracuseStep 2507071 = 3760607) B3760607
theorem B3342761 : Blo 2227435 3342761 := bstep (se 2 (by rfl) ⟨1253535, by rfl⟩ : syracuseStep 3342761 = 2507071) B2507071
theorem B2228507 : Blo 2227435 2228507 := bstep (se 1 (by rfl) ⟨1671380, by rfl⟩ : syracuseStep 2228507 = 3342761) B3342761
theorem B8461381 : Blo 2227435 8461381 := bbase (se 4 (by rfl) ⟨793254, by rfl⟩ : syracuseStep 8461381 = 1586509) (by norm_num)
theorem B11281841 : Blo 2227435 11281841 := bstep (se 2 (by rfl) ⟨4230690, by rfl⟩ : syracuseStep 11281841 = 8461381) B8461381
theorem B7521227 : Blo 2227435 7521227 := bstep (se 1 (by rfl) ⟨5640920, by rfl⟩ : syracuseStep 7521227 = 11281841) B11281841
theorem B5014151 : Blo 2227435 5014151 := bstep (se 1 (by rfl) ⟨3760613, by rfl⟩ : syracuseStep 5014151 = 7521227) B7521227
theorem B3342767 : Blo 2227435 3342767 := bstep (se 1 (by rfl) ⟨2507075, by rfl⟩ : syracuseStep 3342767 = 5014151) B5014151
theorem B2228511 : Blo 2227435 2228511 := bstep (se 1 (by rfl) ⟨1671383, by rfl⟩ : syracuseStep 2228511 = 3342767) B3342767
theorem B3342773 : Blo 2227435 3342773 := bbase (se 5 (by rfl) ⟨156692, by rfl⟩ : syracuseStep 3342773 = 313385) (by norm_num)
theorem B2228515 : Blo 2227435 2228515 := bstep (se 1 (by rfl) ⟨1671386, by rfl⟩ : syracuseStep 2228515 = 3342773) B3342773
theorem B5640941 : Blo 2227435 5640941 := bbase (se 3 (by rfl) ⟨1057676, by rfl⟩ : syracuseStep 5640941 = 2115353) (by norm_num)
theorem B3760627 : Blo 2227435 3760627 := bstep (se 1 (by rfl) ⟨2820470, by rfl⟩ : syracuseStep 3760627 = 5640941) B5640941
theorem B5014169 : Blo 2227435 5014169 := bstep (se 2 (by rfl) ⟨1880313, by rfl⟩ : syracuseStep 5014169 = 3760627) B3760627
theorem B3342779 : Blo 2227435 3342779 := bstep (se 1 (by rfl) ⟨2507084, by rfl⟩ : syracuseStep 3342779 = 5014169) B5014169
theorem B2228519 : Blo 2227435 2228519 := bstep (se 1 (by rfl) ⟨1671389, by rfl⟩ : syracuseStep 2228519 = 3342779) B3342779
theorem B2507089 : Blo 2227435 2507089 := bbase (se 2 (by rfl) ⟨940158, by rfl⟩ : syracuseStep 2507089 = 1880317) (by norm_num)
theorem B3342785 : Blo 2227435 3342785 := bstep (se 2 (by rfl) ⟨1253544, by rfl⟩ : syracuseStep 3342785 = 2507089) B2507089
theorem B2228523 : Blo 2227435 2228523 := bstep (se 1 (by rfl) ⟨1671392, by rfl⟩ : syracuseStep 2228523 = 3342785) B3342785
theorem B2379781 : Blo 2227435 2379781 := bbase (se 4 (by rfl) ⟨223104, by rfl⟩ : syracuseStep 2379781 = 446209) (by norm_num)
theorem B3173041 : Blo 2227435 3173041 := bstep (se 2 (by rfl) ⟨1189890, by rfl⟩ : syracuseStep 3173041 = 2379781) B2379781
theorem B4230721 : Blo 2227435 4230721 := bstep (se 2 (by rfl) ⟨1586520, by rfl⟩ : syracuseStep 4230721 = 3173041) B3173041
theorem B5640961 : Blo 2227435 5640961 := bstep (se 2 (by rfl) ⟨2115360, by rfl⟩ : syracuseStep 5640961 = 4230721) B4230721
theorem B7521281 : Blo 2227435 7521281 := bstep (se 2 (by rfl) ⟨2820480, by rfl⟩ : syracuseStep 7521281 = 5640961) B5640961
theorem B5014187 : Blo 2227435 5014187 := bstep (se 1 (by rfl) ⟨3760640, by rfl⟩ : syracuseStep 5014187 = 7521281) B7521281
theorem B3342791 : Blo 2227435 3342791 := bstep (se 1 (by rfl) ⟨2507093, by rfl⟩ : syracuseStep 3342791 = 5014187) B5014187
theorem B2228527 : Blo 2227435 2228527 := bstep (se 1 (by rfl) ⟨1671395, by rfl⟩ : syracuseStep 2228527 = 3342791) B3342791
theorem B3342797 : Blo 2227435 3342797 := bbase (se 3 (by rfl) ⟨626774, by rfl⟩ : syracuseStep 3342797 = 1253549) (by norm_num)
theorem B2228531 : Blo 2227435 2228531 := bstep (se 1 (by rfl) ⟨1671398, by rfl⟩ : syracuseStep 2228531 = 3342797) B3342797
theorem B5014205 : Blo 2227435 5014205 := bbase (se 3 (by rfl) ⟨940163, by rfl⟩ : syracuseStep 5014205 = 1880327) (by norm_num)
theorem B3342803 : Blo 2227435 3342803 := bstep (se 1 (by rfl) ⟨2507102, by rfl⟩ : syracuseStep 3342803 = 5014205) B5014205
theorem B2228535 : Blo 2227435 2228535 := bstep (se 1 (by rfl) ⟨1671401, by rfl⟩ : syracuseStep 2228535 = 3342803) B3342803
theorem B3760661 : Blo 2227435 3760661 := bbase (se 6 (by rfl) ⟨88140, by rfl⟩ : syracuseStep 3760661 = 176281) (by norm_num)
theorem B2507107 : Blo 2227435 2507107 := bstep (se 1 (by rfl) ⟨1880330, by rfl⟩ : syracuseStep 2507107 = 3760661) B3760661
theorem B3342809 : Blo 2227435 3342809 := bstep (se 2 (by rfl) ⟨1253553, by rfl⟩ : syracuseStep 3342809 = 2507107) B2507107
theorem B2228539 : Blo 2227435 2228539 := bstep (se 1 (by rfl) ⟨1671404, by rfl⟩ : syracuseStep 2228539 = 3342809) B3342809
theorem B4015909 : Blo 2227435 4015909 := bbase (se 4 (by rfl) ⟨376491, by rfl⟩ : syracuseStep 4015909 = 752983) (by norm_num)
theorem B21418181 : Blo 2227435 21418181 := bstep (se 4 (by rfl) ⟨2007954, by rfl⟩ : syracuseStep 21418181 = 4015909) B4015909
theorem B14278787 : Blo 2227435 14278787 := bstep (se 1 (by rfl) ⟨10709090, by rfl⟩ : syracuseStep 14278787 = 21418181) B21418181
theorem B9519191 : Blo 2227435 9519191 := bstep (se 1 (by rfl) ⟨7139393, by rfl⟩ : syracuseStep 9519191 = 14278787) B14278787
theorem B6346127 : Blo 2227435 6346127 := bstep (se 1 (by rfl) ⟨4759595, by rfl⟩ : syracuseStep 6346127 = 9519191) B9519191
theorem B16923005 : Blo 2227435 16923005 := bstep (se 3 (by rfl) ⟨3173063, by rfl⟩ : syracuseStep 16923005 = 6346127) B6346127
theorem B11282003 : Blo 2227435 11282003 := bstep (se 1 (by rfl) ⟨8461502, by rfl⟩ : syracuseStep 11282003 = 16923005) B16923005
theorem B7521335 : Blo 2227435 7521335 := bstep (se 1 (by rfl) ⟨5641001, by rfl⟩ : syracuseStep 7521335 = 11282003) B11282003
theorem B5014223 : Blo 2227435 5014223 := bstep (se 1 (by rfl) ⟨3760667, by rfl⟩ : syracuseStep 5014223 = 7521335) B7521335
theorem B3342815 : Blo 2227435 3342815 := bstep (se 1 (by rfl) ⟨2507111, by rfl⟩ : syracuseStep 3342815 = 5014223) B5014223
theorem B2228543 : Blo 2227435 2228543 := bstep (se 1 (by rfl) ⟨1671407, by rfl⟩ : syracuseStep 2228543 = 3342815) B3342815
theorem B3342821 : Blo 2227435 3342821 := bbase (se 4 (by rfl) ⟨313389, by rfl⟩ : syracuseStep 3342821 = 626779) (by norm_num)
theorem B2228547 : Blo 2227435 2228547 := bstep (se 1 (by rfl) ⟨1671410, by rfl⟩ : syracuseStep 2228547 = 3342821) B3342821
theorem B12212149 : Blo 2227435 12212149 := bbase (se 5 (by rfl) ⟨572444, by rfl⟩ : syracuseStep 12212149 = 1144889) (by norm_num)
theorem B16282865 : Blo 2227435 16282865 := bstep (se 2 (by rfl) ⟨6106074, by rfl⟩ : syracuseStep 16282865 = 12212149) B12212149
theorem B10855243 : Blo 2227435 10855243 := bstep (se 1 (by rfl) ⟨8141432, by rfl⟩ : syracuseStep 10855243 = 16282865) B16282865
theorem B14473657 : Blo 2227435 14473657 := bstep (se 2 (by rfl) ⟨5427621, by rfl⟩ : syracuseStep 14473657 = 10855243) B10855243
theorem B19298209 : Blo 2227435 19298209 := bstep (se 2 (by rfl) ⟨7236828, by rfl⟩ : syracuseStep 19298209 = 14473657) B14473657
theorem B25730945 : Blo 2227435 25730945 := bstep (se 2 (by rfl) ⟨9649104, by rfl⟩ : syracuseStep 25730945 = 19298209) B19298209
theorem B17153963 : Blo 2227435 17153963 := bstep (se 1 (by rfl) ⟨12865472, by rfl⟩ : syracuseStep 17153963 = 25730945) B25730945
theorem B11435975 : Blo 2227435 11435975 := bstep (se 1 (by rfl) ⟨8576981, by rfl⟩ : syracuseStep 11435975 = 17153963) B17153963
theorem B7623983 : Blo 2227435 7623983 := bstep (se 1 (by rfl) ⟨5717987, by rfl⟩ : syracuseStep 7623983 = 11435975) B11435975
theorem B5082655 : Blo 2227435 5082655 := bstep (se 1 (by rfl) ⟨3811991, by rfl⟩ : syracuseStep 5082655 = 7623983) B7623983
theorem B6776873 : Blo 2227435 6776873 := bstep (se 2 (by rfl) ⟨2541327, by rfl⟩ : syracuseStep 6776873 = 5082655) B5082655
theorem B4517915 : Blo 2227435 4517915 := bstep (se 1 (by rfl) ⟨3388436, by rfl⟩ : syracuseStep 4517915 = 6776873) B6776873
theorem B12047773 : Blo 2227435 12047773 := bstep (se 3 (by rfl) ⟨2258957, by rfl⟩ : syracuseStep 12047773 = 4517915) B4517915
theorem B16063697 : Blo 2227435 16063697 := bstep (se 2 (by rfl) ⟨6023886, by rfl⟩ : syracuseStep 16063697 = 12047773) B12047773
theorem B10709131 : Blo 2227435 10709131 := bstep (se 1 (by rfl) ⟨8031848, by rfl⟩ : syracuseStep 10709131 = 16063697) B16063697
theorem B14278841 : Blo 2227435 14278841 := bstep (se 2 (by rfl) ⟨5354565, by rfl⟩ : syracuseStep 14278841 = 10709131) B10709131
theorem B9519227 : Blo 2227435 9519227 := bstep (se 1 (by rfl) ⟨7139420, by rfl⟩ : syracuseStep 9519227 = 14278841) B14278841
theorem B6346151 : Blo 2227435 6346151 := bstep (se 1 (by rfl) ⟨4759613, by rfl⟩ : syracuseStep 6346151 = 9519227) B9519227
theorem B4230767 : Blo 2227435 4230767 := bstep (se 1 (by rfl) ⟨3173075, by rfl⟩ : syracuseStep 4230767 = 6346151) B6346151
theorem B2820511 : Blo 2227435 2820511 := bstep (se 1 (by rfl) ⟨2115383, by rfl⟩ : syracuseStep 2820511 = 4230767) B4230767
theorem B3760681 : Blo 2227435 3760681 := bstep (se 2 (by rfl) ⟨1410255, by rfl⟩ : syracuseStep 3760681 = 2820511) B2820511
theorem B5014241 : Blo 2227435 5014241 := bstep (se 2 (by rfl) ⟨1880340, by rfl⟩ : syracuseStep 5014241 = 3760681) B3760681
theorem B3342827 : Blo 2227435 3342827 := bstep (se 1 (by rfl) ⟨2507120, by rfl⟩ : syracuseStep 3342827 = 5014241) B5014241
theorem B2228551 : Blo 2227435 2228551 := bstep (se 1 (by rfl) ⟨1671413, by rfl⟩ : syracuseStep 2228551 = 3342827) B3342827
theorem B2507125 : Blo 2227435 2507125 := bbase (se 5 (by rfl) ⟨117521, by rfl⟩ : syracuseStep 2507125 = 235043) (by norm_num)
theorem B3342833 : Blo 2227435 3342833 := bstep (se 2 (by rfl) ⟨1253562, by rfl⟩ : syracuseStep 3342833 = 2507125) B2507125
theorem B2228555 : Blo 2227435 2228555 := bstep (se 1 (by rfl) ⟨1671416, by rfl⟩ : syracuseStep 2228555 = 3342833) B3342833
theorem B2820521 : Blo 2227435 2820521 := bbase (se 2 (by rfl) ⟨1057695, by rfl⟩ : syracuseStep 2820521 = 2115391) (by norm_num)
theorem B7521389 : Blo 2227435 7521389 := bstep (se 3 (by rfl) ⟨1410260, by rfl⟩ : syracuseStep 7521389 = 2820521) B2820521
theorem B5014259 : Blo 2227435 5014259 := bstep (se 1 (by rfl) ⟨3760694, by rfl⟩ : syracuseStep 5014259 = 7521389) B7521389
theorem B3342839 : Blo 2227435 3342839 := bstep (se 1 (by rfl) ⟨2507129, by rfl⟩ : syracuseStep 3342839 = 5014259) B5014259
theorem B2228559 : Blo 2227435 2228559 := bstep (se 1 (by rfl) ⟨1671419, by rfl⟩ : syracuseStep 2228559 = 3342839) B3342839
theorem B3342845 : Blo 2227435 3342845 := bbase (se 3 (by rfl) ⟨626783, by rfl⟩ : syracuseStep 3342845 = 1253567) (by norm_num)
theorem B2228563 : Blo 2227435 2228563 := bstep (se 1 (by rfl) ⟨1671422, by rfl⟩ : syracuseStep 2228563 = 3342845) B3342845
theorem B5014277 : Blo 2227435 5014277 := bbase (se 4 (by rfl) ⟨470088, by rfl⟩ : syracuseStep 5014277 = 940177) (by norm_num)
theorem B3342851 : Blo 2227435 3342851 := bstep (se 1 (by rfl) ⟨2507138, by rfl⟩ : syracuseStep 3342851 = 5014277) B5014277
theorem B2228567 : Blo 2227435 2228567 := bstep (se 1 (by rfl) ⟨1671425, by rfl⟩ : syracuseStep 2228567 = 3342851) B3342851
theorem B4230805 : Blo 2227435 4230805 := bbase (se 6 (by rfl) ⟨99159, by rfl⟩ : syracuseStep 4230805 = 198319) (by norm_num)
theorem B5641073 : Blo 2227435 5641073 := bstep (se 2 (by rfl) ⟨2115402, by rfl⟩ : syracuseStep 5641073 = 4230805) B4230805
theorem B3760715 : Blo 2227435 3760715 := bstep (se 1 (by rfl) ⟨2820536, by rfl⟩ : syracuseStep 3760715 = 5641073) B5641073
theorem B2507143 : Blo 2227435 2507143 := bstep (se 1 (by rfl) ⟨1880357, by rfl⟩ : syracuseStep 2507143 = 3760715) B3760715
theorem B3342857 : Blo 2227435 3342857 := bstep (se 2 (by rfl) ⟨1253571, by rfl⟩ : syracuseStep 3342857 = 2507143) B2507143
theorem B2228571 : Blo 2227435 2228571 := bstep (se 1 (by rfl) ⟨1671428, by rfl⟩ : syracuseStep 2228571 = 3342857) B3342857
theorem B11282165 : Blo 2227435 11282165 := bbase (se 5 (by rfl) ⟨528851, by rfl⟩ : syracuseStep 11282165 = 1057703) (by norm_num)
theorem B7521443 : Blo 2227435 7521443 := bstep (se 1 (by rfl) ⟨5641082, by rfl⟩ : syracuseStep 7521443 = 11282165) B11282165
theorem B5014295 : Blo 2227435 5014295 := bstep (se 1 (by rfl) ⟨3760721, by rfl⟩ : syracuseStep 5014295 = 7521443) B7521443
theorem B3342863 : Blo 2227435 3342863 := bstep (se 1 (by rfl) ⟨2507147, by rfl⟩ : syracuseStep 3342863 = 5014295) B5014295
theorem B2228575 : Blo 2227435 2228575 := bstep (se 1 (by rfl) ⟨1671431, by rfl⟩ : syracuseStep 2228575 = 3342863) B3342863
theorem B3342869 : Blo 2227435 3342869 := bbase (se 6 (by rfl) ⟨78348, by rfl⟩ : syracuseStep 3342869 = 156697) (by norm_num)
theorem B2228579 : Blo 2227435 2228579 := bstep (se 1 (by rfl) ⟨1671434, by rfl⟩ : syracuseStep 2228579 = 3342869) B3342869
theorem B2677321 : Blo 2227435 2677321 := bbase (se 2 (by rfl) ⟨1003995, by rfl⟩ : syracuseStep 2677321 = 2007991) (by norm_num)
theorem B3569761 : Blo 2227435 3569761 := bstep (se 2 (by rfl) ⟨1338660, by rfl⟩ : syracuseStep 3569761 = 2677321) B2677321
theorem B19038725 : Blo 2227435 19038725 := bstep (se 4 (by rfl) ⟨1784880, by rfl⟩ : syracuseStep 19038725 = 3569761) B3569761
theorem B12692483 : Blo 2227435 12692483 := bstep (se 1 (by rfl) ⟨9519362, by rfl⟩ : syracuseStep 12692483 = 19038725) B19038725
theorem B8461655 : Blo 2227435 8461655 := bstep (se 1 (by rfl) ⟨6346241, by rfl⟩ : syracuseStep 8461655 = 12692483) B12692483
theorem B5641103 : Blo 2227435 5641103 := bstep (se 1 (by rfl) ⟨4230827, by rfl⟩ : syracuseStep 5641103 = 8461655) B8461655
theorem B3760735 : Blo 2227435 3760735 := bstep (se 1 (by rfl) ⟨2820551, by rfl⟩ : syracuseStep 3760735 = 5641103) B5641103
theorem B5014313 : Blo 2227435 5014313 := bstep (se 2 (by rfl) ⟨1880367, by rfl⟩ : syracuseStep 5014313 = 3760735) B3760735
theorem B3342875 : Blo 2227435 3342875 := bstep (se 1 (by rfl) ⟨2507156, by rfl⟩ : syracuseStep 3342875 = 5014313) B5014313
theorem B2228583 : Blo 2227435 2228583 := bstep (se 1 (by rfl) ⟨1671437, by rfl⟩ : syracuseStep 2228583 = 3342875) B3342875
theorem B2507161 : Blo 2227435 2507161 := bbase (se 2 (by rfl) ⟨940185, by rfl⟩ : syracuseStep 2507161 = 1880371) (by norm_num)
theorem B3342881 : Blo 2227435 3342881 := bstep (se 2 (by rfl) ⟨1253580, by rfl⟩ : syracuseStep 3342881 = 2507161) B2507161
theorem B2228587 : Blo 2227435 2228587 := bstep (se 1 (by rfl) ⟨1671440, by rfl⟩ : syracuseStep 2228587 = 3342881) B3342881
theorem B8461685 : Blo 2227435 8461685 := bbase (se 5 (by rfl) ⟨396641, by rfl⟩ : syracuseStep 8461685 = 793283) (by norm_num)
theorem B5641123 : Blo 2227435 5641123 := bstep (se 1 (by rfl) ⟨4230842, by rfl⟩ : syracuseStep 5641123 = 8461685) B8461685
theorem B7521497 : Blo 2227435 7521497 := bstep (se 2 (by rfl) ⟨2820561, by rfl⟩ : syracuseStep 7521497 = 5641123) B5641123
theorem B5014331 : Blo 2227435 5014331 := bstep (se 1 (by rfl) ⟨3760748, by rfl⟩ : syracuseStep 5014331 = 7521497) B7521497
theorem B3342887 : Blo 2227435 3342887 := bstep (se 1 (by rfl) ⟨2507165, by rfl⟩ : syracuseStep 3342887 = 5014331) B5014331
theorem B2228591 : Blo 2227435 2228591 := bstep (se 1 (by rfl) ⟨1671443, by rfl⟩ : syracuseStep 2228591 = 3342887) B3342887
theorem B3342893 : Blo 2227435 3342893 := bbase (se 3 (by rfl) ⟨626792, by rfl⟩ : syracuseStep 3342893 = 1253585) (by norm_num)
theorem B2228595 : Blo 2227435 2228595 := bstep (se 1 (by rfl) ⟨1671446, by rfl⟩ : syracuseStep 2228595 = 3342893) B3342893
theorem B5014349 : Blo 2227435 5014349 := bbase (se 3 (by rfl) ⟨940190, by rfl⟩ : syracuseStep 5014349 = 1880381) (by norm_num)
theorem B3342899 : Blo 2227435 3342899 := bstep (se 1 (by rfl) ⟨2507174, by rfl⟩ : syracuseStep 3342899 = 5014349) B5014349
theorem B2228599 : Blo 2227435 2228599 := bstep (se 1 (by rfl) ⟨1671449, by rfl⟩ : syracuseStep 2228599 = 3342899) B3342899
theorem B2820577 : Blo 2227435 2820577 := bbase (se 2 (by rfl) ⟨1057716, by rfl⟩ : syracuseStep 2820577 = 2115433) (by norm_num)
theorem B3760769 : Blo 2227435 3760769 := bstep (se 2 (by rfl) ⟨1410288, by rfl⟩ : syracuseStep 3760769 = 2820577) B2820577
theorem B2507179 : Blo 2227435 2507179 := bstep (se 1 (by rfl) ⟨1880384, by rfl⟩ : syracuseStep 2507179 = 3760769) B3760769
theorem B3342905 : Blo 2227435 3342905 := bstep (se 2 (by rfl) ⟨1253589, by rfl⟩ : syracuseStep 3342905 = 2507179) B2507179
theorem B2228603 : Blo 2227435 2228603 := bstep (se 1 (by rfl) ⟨1671452, by rfl⟩ : syracuseStep 2228603 = 3342905) B3342905
theorem B25385237 : Blo 2227435 25385237 := bbase (se 6 (by rfl) ⟨594966, by rfl⟩ : syracuseStep 25385237 = 1189933) (by norm_num)
theorem B16923491 : Blo 2227435 16923491 := bstep (se 1 (by rfl) ⟨12692618, by rfl⟩ : syracuseStep 16923491 = 25385237) B25385237
theorem B11282327 : Blo 2227435 11282327 := bstep (se 1 (by rfl) ⟨8461745, by rfl⟩ : syracuseStep 11282327 = 16923491) B16923491
theorem B7521551 : Blo 2227435 7521551 := bstep (se 1 (by rfl) ⟨5641163, by rfl⟩ : syracuseStep 7521551 = 11282327) B11282327
theorem B5014367 : Blo 2227435 5014367 := bstep (se 1 (by rfl) ⟨3760775, by rfl⟩ : syracuseStep 5014367 = 7521551) B7521551
theorem B3342911 : Blo 2227435 3342911 := bstep (se 1 (by rfl) ⟨2507183, by rfl⟩ : syracuseStep 3342911 = 5014367) B5014367
theorem B2228607 : Blo 2227435 2228607 := bstep (se 1 (by rfl) ⟨1671455, by rfl⟩ : syracuseStep 2228607 = 3342911) B3342911
theorem B3342917 : Blo 2227435 3342917 := bbase (se 4 (by rfl) ⟨313398, by rfl⟩ : syracuseStep 3342917 = 626797) (by norm_num)
theorem B2228611 : Blo 2227435 2228611 := bstep (se 1 (by rfl) ⟨1671458, by rfl⟩ : syracuseStep 2228611 = 3342917) B3342917
theorem B3760789 : Blo 2227435 3760789 := bbase (se 6 (by rfl) ⟨88143, by rfl⟩ : syracuseStep 3760789 = 176287) (by norm_num)
theorem B5014385 : Blo 2227435 5014385 := bstep (se 2 (by rfl) ⟨1880394, by rfl⟩ : syracuseStep 5014385 = 3760789) B3760789
theorem B3342923 : Blo 2227435 3342923 := bstep (se 1 (by rfl) ⟨2507192, by rfl⟩ : syracuseStep 3342923 = 5014385) B5014385
theorem B2228615 : Blo 2227435 2228615 := bstep (se 1 (by rfl) ⟨1671461, by rfl⟩ : syracuseStep 2228615 = 3342923) B3342923
theorem B2507197 : Blo 2227435 2507197 := bbase (se 3 (by rfl) ⟨470099, by rfl⟩ : syracuseStep 2507197 = 940199) (by norm_num)
theorem B3342929 : Blo 2227435 3342929 := bstep (se 2 (by rfl) ⟨1253598, by rfl⟩ : syracuseStep 3342929 = 2507197) B2507197
theorem B2228619 : Blo 2227435 2228619 := bstep (se 1 (by rfl) ⟨1671464, by rfl⟩ : syracuseStep 2228619 = 3342929) B3342929
theorem B7521605 : Blo 2227435 7521605 := bbase (se 4 (by rfl) ⟨705150, by rfl⟩ : syracuseStep 7521605 = 1410301) (by norm_num)
theorem B5014403 : Blo 2227435 5014403 := bstep (se 1 (by rfl) ⟨3760802, by rfl⟩ : syracuseStep 5014403 = 7521605) B7521605
theorem B3342935 : Blo 2227435 3342935 := bstep (se 1 (by rfl) ⟨2507201, by rfl⟩ : syracuseStep 3342935 = 5014403) B5014403
theorem B2228623 : Blo 2227435 2228623 := bstep (se 1 (by rfl) ⟨1671467, by rfl⟩ : syracuseStep 2228623 = 3342935) B3342935
theorem B3342941 : Blo 2227435 3342941 := bbase (se 3 (by rfl) ⟨626801, by rfl⟩ : syracuseStep 3342941 = 1253603) (by norm_num)
theorem B2228627 : Blo 2227435 2228627 := bstep (se 1 (by rfl) ⟨1671470, by rfl⟩ : syracuseStep 2228627 = 3342941) B3342941
theorem B5014421 : Blo 2227435 5014421 := bbase (se 6 (by rfl) ⟨117525, by rfl⟩ : syracuseStep 5014421 = 235051) (by norm_num)
theorem B3342947 : Blo 2227435 3342947 := bstep (se 1 (by rfl) ⟨2507210, by rfl⟩ : syracuseStep 3342947 = 5014421) B5014421
theorem B2228631 : Blo 2227435 2228631 := bstep (se 1 (by rfl) ⟨1671473, by rfl⟩ : syracuseStep 2228631 = 3342947) B3342947
theorem B3569845 : Blo 2227435 3569845 := bbase (se 5 (by rfl) ⟨167336, by rfl⟩ : syracuseStep 3569845 = 334673) (by norm_num)
theorem B4759793 : Blo 2227435 4759793 := bstep (se 2 (by rfl) ⟨1784922, by rfl⟩ : syracuseStep 4759793 = 3569845) B3569845
theorem B3173195 : Blo 2227435 3173195 := bstep (se 1 (by rfl) ⟨2379896, by rfl⟩ : syracuseStep 3173195 = 4759793) B4759793
theorem B8461853 : Blo 2227435 8461853 := bstep (se 3 (by rfl) ⟨1586597, by rfl⟩ : syracuseStep 8461853 = 3173195) B3173195
theorem B5641235 : Blo 2227435 5641235 := bstep (se 1 (by rfl) ⟨4230926, by rfl⟩ : syracuseStep 5641235 = 8461853) B8461853
theorem B3760823 : Blo 2227435 3760823 := bstep (se 1 (by rfl) ⟨2820617, by rfl⟩ : syracuseStep 3760823 = 5641235) B5641235
theorem B2507215 : Blo 2227435 2507215 := bstep (se 1 (by rfl) ⟨1880411, by rfl⟩ : syracuseStep 2507215 = 3760823) B3760823
theorem B3342953 : Blo 2227435 3342953 := bstep (se 2 (by rfl) ⟨1253607, by rfl⟩ : syracuseStep 3342953 = 2507215) B2507215
theorem B2228635 : Blo 2227435 2228635 := bstep (se 1 (by rfl) ⟨1671476, by rfl⟩ : syracuseStep 2228635 = 3342953) B3342953
theorem B7139701 : Blo 2227435 7139701 := bbase (se 5 (by rfl) ⟨334673, by rfl⟩ : syracuseStep 7139701 = 669347) (by norm_num)
theorem B9519601 : Blo 2227435 9519601 := bstep (se 2 (by rfl) ⟨3569850, by rfl⟩ : syracuseStep 9519601 = 7139701) B7139701
theorem B12692801 : Blo 2227435 12692801 := bstep (se 2 (by rfl) ⟨4759800, by rfl⟩ : syracuseStep 12692801 = 9519601) B9519601
theorem B8461867 : Blo 2227435 8461867 := bstep (se 1 (by rfl) ⟨6346400, by rfl⟩ : syracuseStep 8461867 = 12692801) B12692801
theorem B11282489 : Blo 2227435 11282489 := bstep (se 2 (by rfl) ⟨4230933, by rfl⟩ : syracuseStep 11282489 = 8461867) B8461867
theorem B7521659 : Blo 2227435 7521659 := bstep (se 1 (by rfl) ⟨5641244, by rfl⟩ : syracuseStep 7521659 = 11282489) B11282489
theorem B5014439 : Blo 2227435 5014439 := bstep (se 1 (by rfl) ⟨3760829, by rfl⟩ : syracuseStep 5014439 = 7521659) B7521659
theorem B3342959 : Blo 2227435 3342959 := bstep (se 1 (by rfl) ⟨2507219, by rfl⟩ : syracuseStep 3342959 = 5014439) B5014439
theorem B2228639 : Blo 2227435 2228639 := bstep (se 1 (by rfl) ⟨1671479, by rfl⟩ : syracuseStep 2228639 = 3342959) B3342959
theorem B3342965 : Blo 2227435 3342965 := bbase (se 5 (by rfl) ⟨156701, by rfl⟩ : syracuseStep 3342965 = 313403) (by norm_num)
theorem B2228643 : Blo 2227435 2228643 := bstep (se 1 (by rfl) ⟨1671482, by rfl⟩ : syracuseStep 2228643 = 3342965) B3342965
theorem B4230949 : Blo 2227435 4230949 := bbase (se 4 (by rfl) ⟨396651, by rfl⟩ : syracuseStep 4230949 = 793303) (by norm_num)
theorem B5641265 : Blo 2227435 5641265 := bstep (se 2 (by rfl) ⟨2115474, by rfl⟩ : syracuseStep 5641265 = 4230949) B4230949
theorem B3760843 : Blo 2227435 3760843 := bstep (se 1 (by rfl) ⟨2820632, by rfl⟩ : syracuseStep 3760843 = 5641265) B5641265
theorem B5014457 : Blo 2227435 5014457 := bstep (se 2 (by rfl) ⟨1880421, by rfl⟩ : syracuseStep 5014457 = 3760843) B3760843
theorem B3342971 : Blo 2227435 3342971 := bstep (se 1 (by rfl) ⟨2507228, by rfl⟩ : syracuseStep 3342971 = 5014457) B5014457
theorem B2228647 : Blo 2227435 2228647 := bstep (se 1 (by rfl) ⟨1671485, by rfl⟩ : syracuseStep 2228647 = 3342971) B3342971
theorem B2507233 : Blo 2227435 2507233 := bbase (se 2 (by rfl) ⟨940212, by rfl⟩ : syracuseStep 2507233 = 1880425) (by norm_num)
theorem B3342977 : Blo 2227435 3342977 := bstep (se 2 (by rfl) ⟨1253616, by rfl⟩ : syracuseStep 3342977 = 2507233) B2507233
theorem B2228651 : Blo 2227435 2228651 := bstep (se 1 (by rfl) ⟨1671488, by rfl⟩ : syracuseStep 2228651 = 3342977) B3342977
theorem B5641285 : Blo 2227435 5641285 := bbase (se 4 (by rfl) ⟨528870, by rfl⟩ : syracuseStep 5641285 = 1057741) (by norm_num)
theorem B7521713 : Blo 2227435 7521713 := bstep (se 2 (by rfl) ⟨2820642, by rfl⟩ : syracuseStep 7521713 = 5641285) B5641285
theorem B5014475 : Blo 2227435 5014475 := bstep (se 1 (by rfl) ⟨3760856, by rfl⟩ : syracuseStep 5014475 = 7521713) B7521713
theorem B3342983 : Blo 2227435 3342983 := bstep (se 1 (by rfl) ⟨2507237, by rfl⟩ : syracuseStep 3342983 = 5014475) B5014475
theorem B2228655 : Blo 2227435 2228655 := bstep (se 1 (by rfl) ⟨1671491, by rfl⟩ : syracuseStep 2228655 = 3342983) B3342983
theorem B3342989 : Blo 2227435 3342989 := bbase (se 3 (by rfl) ⟨626810, by rfl⟩ : syracuseStep 3342989 = 1253621) (by norm_num)
theorem B2228659 : Blo 2227435 2228659 := bstep (se 1 (by rfl) ⟨1671494, by rfl⟩ : syracuseStep 2228659 = 3342989) B3342989
theorem B5014493 : Blo 2227435 5014493 := bbase (se 3 (by rfl) ⟨940217, by rfl⟩ : syracuseStep 5014493 = 1880435) (by norm_num)
theorem B3342995 : Blo 2227435 3342995 := bstep (se 1 (by rfl) ⟨2507246, by rfl⟩ : syracuseStep 3342995 = 5014493) B5014493
theorem B2228663 : Blo 2227435 2228663 := bstep (se 1 (by rfl) ⟨1671497, by rfl⟩ : syracuseStep 2228663 = 3342995) B3342995
theorem B3760877 : Blo 2227435 3760877 := bbase (se 3 (by rfl) ⟨705164, by rfl⟩ : syracuseStep 3760877 = 1410329) (by norm_num)
theorem B2507251 : Blo 2227435 2507251 := bstep (se 1 (by rfl) ⟨1880438, by rfl⟩ : syracuseStep 2507251 = 3760877) B3760877
theorem B3343001 : Blo 2227435 3343001 := bstep (se 2 (by rfl) ⟨1253625, by rfl⟩ : syracuseStep 3343001 = 2507251) B2507251
theorem B2228667 : Blo 2227435 2228667 := bstep (se 1 (by rfl) ⟨1671500, by rfl⟩ : syracuseStep 2228667 = 3343001) B3343001
theorem B18072629 : Blo 2227435 18072629 := bbase (se 5 (by rfl) ⟨847154, by rfl⟩ : syracuseStep 18072629 = 1694309) (by norm_num)
theorem B12048419 : Blo 2227435 12048419 := bstep (se 1 (by rfl) ⟨9036314, by rfl⟩ : syracuseStep 12048419 = 18072629) B18072629
theorem B8032279 : Blo 2227435 8032279 := bstep (se 1 (by rfl) ⟨6024209, by rfl⟩ : syracuseStep 8032279 = 12048419) B12048419
theorem B10709705 : Blo 2227435 10709705 := bstep (se 2 (by rfl) ⟨4016139, by rfl⟩ : syracuseStep 10709705 = 8032279) B8032279
theorem B28559213 : Blo 2227435 28559213 := bstep (se 3 (by rfl) ⟨5354852, by rfl⟩ : syracuseStep 28559213 = 10709705) B10709705
theorem B19039475 : Blo 2227435 19039475 := bstep (se 1 (by rfl) ⟨14279606, by rfl⟩ : syracuseStep 19039475 = 28559213) B28559213
theorem B12692983 : Blo 2227435 12692983 := bstep (se 1 (by rfl) ⟨9519737, by rfl⟩ : syracuseStep 12692983 = 19039475) B19039475
theorem B16923977 : Blo 2227435 16923977 := bstep (se 2 (by rfl) ⟨6346491, by rfl⟩ : syracuseStep 16923977 = 12692983) B12692983
theorem B11282651 : Blo 2227435 11282651 := bstep (se 1 (by rfl) ⟨8461988, by rfl⟩ : syracuseStep 11282651 = 16923977) B16923977
theorem B7521767 : Blo 2227435 7521767 := bstep (se 1 (by rfl) ⟨5641325, by rfl⟩ : syracuseStep 7521767 = 11282651) B11282651
theorem B5014511 : Blo 2227435 5014511 := bstep (se 1 (by rfl) ⟨3760883, by rfl⟩ : syracuseStep 5014511 = 7521767) B7521767
theorem B3343007 : Blo 2227435 3343007 := bstep (se 1 (by rfl) ⟨2507255, by rfl⟩ : syracuseStep 3343007 = 5014511) B5014511
theorem B2228671 : Blo 2227435 2228671 := bstep (se 1 (by rfl) ⟨1671503, by rfl⟩ : syracuseStep 2228671 = 3343007) B3343007
theorem B3343013 : Blo 2227435 3343013 := bbase (se 4 (by rfl) ⟨313407, by rfl⟩ : syracuseStep 3343013 = 626815) (by norm_num)
theorem B2228675 : Blo 2227435 2228675 := bstep (se 1 (by rfl) ⟨1671506, by rfl⟩ : syracuseStep 2228675 = 3343013) B3343013
theorem B2820673 : Blo 2227435 2820673 := bbase (se 2 (by rfl) ⟨1057752, by rfl⟩ : syracuseStep 2820673 = 2115505) (by norm_num)
theorem B3760897 : Blo 2227435 3760897 := bstep (se 2 (by rfl) ⟨1410336, by rfl⟩ : syracuseStep 3760897 = 2820673) B2820673
theorem B5014529 : Blo 2227435 5014529 := bstep (se 2 (by rfl) ⟨1880448, by rfl⟩ : syracuseStep 5014529 = 3760897) B3760897
theorem B3343019 : Blo 2227435 3343019 := bstep (se 1 (by rfl) ⟨2507264, by rfl⟩ : syracuseStep 3343019 = 5014529) B5014529
theorem B2228679 : Blo 2227435 2228679 := bstep (se 1 (by rfl) ⟨1671509, by rfl⟩ : syracuseStep 2228679 = 3343019) B3343019
theorem B2507269 : Blo 2227435 2507269 := bbase (se 4 (by rfl) ⟨235056, by rfl⟩ : syracuseStep 2507269 = 470113) (by norm_num)
theorem B3343025 : Blo 2227435 3343025 := bstep (se 2 (by rfl) ⟨1253634, by rfl⟩ : syracuseStep 3343025 = 2507269) B2507269
theorem B2228683 : Blo 2227435 2228683 := bstep (se 1 (by rfl) ⟨1671512, by rfl⟩ : syracuseStep 2228683 = 3343025) B3343025
theorem B3173269 : Blo 2227435 3173269 := bbase (se 6 (by rfl) ⟨74373, by rfl⟩ : syracuseStep 3173269 = 148747) (by norm_num)
theorem B4231025 : Blo 2227435 4231025 := bstep (se 2 (by rfl) ⟨1586634, by rfl⟩ : syracuseStep 4231025 = 3173269) B3173269
theorem B2820683 : Blo 2227435 2820683 := bstep (se 1 (by rfl) ⟨2115512, by rfl⟩ : syracuseStep 2820683 = 4231025) B4231025
theorem B7521821 : Blo 2227435 7521821 := bstep (se 3 (by rfl) ⟨1410341, by rfl⟩ : syracuseStep 7521821 = 2820683) B2820683
theorem B5014547 : Blo 2227435 5014547 := bstep (se 1 (by rfl) ⟨3760910, by rfl⟩ : syracuseStep 5014547 = 7521821) B7521821
theorem B3343031 : Blo 2227435 3343031 := bstep (se 1 (by rfl) ⟨2507273, by rfl⟩ : syracuseStep 3343031 = 5014547) B5014547
theorem B2228687 : Blo 2227435 2228687 := bstep (se 1 (by rfl) ⟨1671515, by rfl⟩ : syracuseStep 2228687 = 3343031) B3343031
theorem B3343037 : Blo 2227435 3343037 := bbase (se 3 (by rfl) ⟨626819, by rfl⟩ : syracuseStep 3343037 = 1253639) (by norm_num)
theorem B2228691 : Blo 2227435 2228691 := bstep (se 1 (by rfl) ⟨1671518, by rfl⟩ : syracuseStep 2228691 = 3343037) B3343037
theorem B5014565 : Blo 2227435 5014565 := bbase (se 4 (by rfl) ⟨470115, by rfl⟩ : syracuseStep 5014565 = 940231) (by norm_num)
theorem B3343043 : Blo 2227435 3343043 := bstep (se 1 (by rfl) ⟨2507282, by rfl⟩ : syracuseStep 3343043 = 5014565) B5014565
theorem B2228695 : Blo 2227435 2228695 := bstep (se 1 (by rfl) ⟨1671521, by rfl⟩ : syracuseStep 2228695 = 3343043) B3343043
theorem B5641397 : Blo 2227435 5641397 := bbase (se 5 (by rfl) ⟨264440, by rfl⟩ : syracuseStep 5641397 = 528881) (by norm_num)
theorem B3760931 : Blo 2227435 3760931 := bstep (se 1 (by rfl) ⟨2820698, by rfl⟩ : syracuseStep 3760931 = 5641397) B5641397
theorem B2507287 : Blo 2227435 2507287 := bstep (se 1 (by rfl) ⟨1880465, by rfl⟩ : syracuseStep 2507287 = 3760931) B3760931
theorem B3343049 : Blo 2227435 3343049 := bstep (se 2 (by rfl) ⟨1253643, by rfl⟩ : syracuseStep 3343049 = 2507287) B2507287
theorem B2228699 : Blo 2227435 2228699 := bstep (se 1 (by rfl) ⟨1671524, by rfl⟩ : syracuseStep 2228699 = 3343049) B3343049
theorem B2677465 : Blo 2227435 2677465 := bbase (se 2 (by rfl) ⟨1004049, by rfl⟩ : syracuseStep 2677465 = 2008099) (by norm_num)
theorem B14279813 : Blo 2227435 14279813 := bstep (se 4 (by rfl) ⟨1338732, by rfl⟩ : syracuseStep 14279813 = 2677465) B2677465
theorem B9519875 : Blo 2227435 9519875 := bstep (se 1 (by rfl) ⟨7139906, by rfl⟩ : syracuseStep 9519875 = 14279813) B14279813
theorem B6346583 : Blo 2227435 6346583 := bstep (se 1 (by rfl) ⟨4759937, by rfl⟩ : syracuseStep 6346583 = 9519875) B9519875
theorem B4231055 : Blo 2227435 4231055 := bstep (se 1 (by rfl) ⟨3173291, by rfl⟩ : syracuseStep 4231055 = 6346583) B6346583
theorem B11282813 : Blo 2227435 11282813 := bstep (se 3 (by rfl) ⟨2115527, by rfl⟩ : syracuseStep 11282813 = 4231055) B4231055
theorem B7521875 : Blo 2227435 7521875 := bstep (se 1 (by rfl) ⟨5641406, by rfl⟩ : syracuseStep 7521875 = 11282813) B11282813
theorem B5014583 : Blo 2227435 5014583 := bstep (se 1 (by rfl) ⟨3760937, by rfl⟩ : syracuseStep 5014583 = 7521875) B7521875
theorem B3343055 : Blo 2227435 3343055 := bstep (se 1 (by rfl) ⟨2507291, by rfl⟩ : syracuseStep 3343055 = 5014583) B5014583
theorem B2228703 : Blo 2227435 2228703 := bstep (se 1 (by rfl) ⟨1671527, by rfl⟩ : syracuseStep 2228703 = 3343055) B3343055
theorem B3343061 : Blo 2227435 3343061 := bbase (se 7 (by rfl) ⟨39176, by rfl⟩ : syracuseStep 3343061 = 78353) (by norm_num)
theorem B2228707 : Blo 2227435 2228707 := bstep (se 1 (by rfl) ⟨1671530, by rfl⟩ : syracuseStep 2228707 = 3343061) B3343061
theorem B4016213 : Blo 2227435 4016213 := bbase (se 8 (by rfl) ⟨23532, by rfl⟩ : syracuseStep 4016213 = 47065) (by norm_num)
theorem B2677475 : Blo 2227435 2677475 := bstep (se 1 (by rfl) ⟨2008106, by rfl⟩ : syracuseStep 2677475 = 4016213) B4016213
theorem B7139933 : Blo 2227435 7139933 := bstep (se 3 (by rfl) ⟨1338737, by rfl⟩ : syracuseStep 7139933 = 2677475) B2677475
theorem B4759955 : Blo 2227435 4759955 := bstep (se 1 (by rfl) ⟨3569966, by rfl⟩ : syracuseStep 4759955 = 7139933) B7139933
theorem B3173303 : Blo 2227435 3173303 := bstep (se 1 (by rfl) ⟨2379977, by rfl⟩ : syracuseStep 3173303 = 4759955) B4759955
theorem B8462141 : Blo 2227435 8462141 := bstep (se 3 (by rfl) ⟨1586651, by rfl⟩ : syracuseStep 8462141 = 3173303) B3173303
theorem B5641427 : Blo 2227435 5641427 := bstep (se 1 (by rfl) ⟨4231070, by rfl⟩ : syracuseStep 5641427 = 8462141) B8462141
theorem B3760951 : Blo 2227435 3760951 := bstep (se 1 (by rfl) ⟨2820713, by rfl⟩ : syracuseStep 3760951 = 5641427) B5641427
theorem B5014601 : Blo 2227435 5014601 := bstep (se 2 (by rfl) ⟨1880475, by rfl⟩ : syracuseStep 5014601 = 3760951) B3760951
theorem B3343067 : Blo 2227435 3343067 := bstep (se 1 (by rfl) ⟨2507300, by rfl⟩ : syracuseStep 3343067 = 5014601) B5014601
theorem B2228711 : Blo 2227435 2228711 := bstep (se 1 (by rfl) ⟨1671533, by rfl⟩ : syracuseStep 2228711 = 3343067) B3343067
theorem B2507305 : Blo 2227435 2507305 := bbase (se 2 (by rfl) ⟨940239, by rfl⟩ : syracuseStep 2507305 = 1880479) (by norm_num)
theorem B3343073 : Blo 2227435 3343073 := bstep (se 2 (by rfl) ⟨1253652, by rfl⟩ : syracuseStep 3343073 = 2507305) B2507305
theorem B2228715 : Blo 2227435 2228715 := bstep (se 1 (by rfl) ⟨1671536, by rfl⟩ : syracuseStep 2228715 = 3343073) B3343073
theorem B9649829 : Blo 2227435 9649829 := bbase (se 4 (by rfl) ⟨904671, by rfl⟩ : syracuseStep 9649829 = 1809343) (by norm_num)
theorem B6433219 : Blo 2227435 6433219 := bstep (se 1 (by rfl) ⟨4824914, by rfl⟩ : syracuseStep 6433219 = 9649829) B9649829
theorem B8577625 : Blo 2227435 8577625 := bstep (se 2 (by rfl) ⟨3216609, by rfl⟩ : syracuseStep 8577625 = 6433219) B6433219
theorem B11436833 : Blo 2227435 11436833 := bstep (se 2 (by rfl) ⟨4288812, by rfl⟩ : syracuseStep 11436833 = 8577625) B8577625
theorem B30498221 : Blo 2227435 30498221 := bstep (se 3 (by rfl) ⟨5718416, by rfl⟩ : syracuseStep 30498221 = 11436833) B11436833
theorem B20332147 : Blo 2227435 20332147 := bstep (se 1 (by rfl) ⟨15249110, by rfl⟩ : syracuseStep 20332147 = 30498221) B30498221
theorem B27109529 : Blo 2227435 27109529 := bstep (se 2 (by rfl) ⟨10166073, by rfl⟩ : syracuseStep 27109529 = 20332147) B20332147
theorem B18073019 : Blo 2227435 18073019 := bstep (se 1 (by rfl) ⟨13554764, by rfl⟩ : syracuseStep 18073019 = 27109529) B27109529
theorem B12048679 : Blo 2227435 12048679 := bstep (se 1 (by rfl) ⟨9036509, by rfl⟩ : syracuseStep 12048679 = 18073019) B18073019
theorem B16064905 : Blo 2227435 16064905 := bstep (se 2 (by rfl) ⟨6024339, by rfl⟩ : syracuseStep 16064905 = 12048679) B12048679
theorem B21419873 : Blo 2227435 21419873 := bstep (se 2 (by rfl) ⟨8032452, by rfl⟩ : syracuseStep 21419873 = 16064905) B16064905
theorem B14279915 : Blo 2227435 14279915 := bstep (se 1 (by rfl) ⟨10709936, by rfl⟩ : syracuseStep 14279915 = 21419873) B21419873
theorem B9519943 : Blo 2227435 9519943 := bstep (se 1 (by rfl) ⟨7139957, by rfl⟩ : syracuseStep 9519943 = 14279915) B14279915
theorem B12693257 : Blo 2227435 12693257 := bstep (se 2 (by rfl) ⟨4759971, by rfl⟩ : syracuseStep 12693257 = 9519943) B9519943
theorem B8462171 : Blo 2227435 8462171 := bstep (se 1 (by rfl) ⟨6346628, by rfl⟩ : syracuseStep 8462171 = 12693257) B12693257
theorem B5641447 : Blo 2227435 5641447 := bstep (se 1 (by rfl) ⟨4231085, by rfl⟩ : syracuseStep 5641447 = 8462171) B8462171
theorem B7521929 : Blo 2227435 7521929 := bstep (se 2 (by rfl) ⟨2820723, by rfl⟩ : syracuseStep 7521929 = 5641447) B5641447
theorem B5014619 : Blo 2227435 5014619 := bstep (se 1 (by rfl) ⟨3760964, by rfl⟩ : syracuseStep 5014619 = 7521929) B7521929
theorem B3343079 : Blo 2227435 3343079 := bstep (se 1 (by rfl) ⟨2507309, by rfl⟩ : syracuseStep 3343079 = 5014619) B5014619
theorem B2228719 : Blo 2227435 2228719 := bstep (se 1 (by rfl) ⟨1671539, by rfl⟩ : syracuseStep 2228719 = 3343079) B3343079
theorem B3343085 : Blo 2227435 3343085 := bbase (se 3 (by rfl) ⟨626828, by rfl⟩ : syracuseStep 3343085 = 1253657) (by norm_num)
theorem B2228723 : Blo 2227435 2228723 := bstep (se 1 (by rfl) ⟨1671542, by rfl⟩ : syracuseStep 2228723 = 3343085) B3343085
theorem B5014637 : Blo 2227435 5014637 := bbase (se 3 (by rfl) ⟨940244, by rfl⟩ : syracuseStep 5014637 = 1880489) (by norm_num)
theorem B3343091 : Blo 2227435 3343091 := bstep (se 1 (by rfl) ⟨2507318, by rfl⟩ : syracuseStep 3343091 = 5014637) B5014637
theorem B2228727 : Blo 2227435 2228727 := bstep (se 1 (by rfl) ⟨1671545, by rfl⟩ : syracuseStep 2228727 = 3343091) B3343091
theorem B4231109 : Blo 2227435 4231109 := bbase (se 4 (by rfl) ⟨396666, by rfl⟩ : syracuseStep 4231109 = 793333) (by norm_num)
theorem B2820739 : Blo 2227435 2820739 := bstep (se 1 (by rfl) ⟨2115554, by rfl⟩ : syracuseStep 2820739 = 4231109) B4231109
theorem B3760985 : Blo 2227435 3760985 := bstep (se 2 (by rfl) ⟨1410369, by rfl⟩ : syracuseStep 3760985 = 2820739) B2820739
theorem B2507323 : Blo 2227435 2507323 := bstep (se 1 (by rfl) ⟨1880492, by rfl⟩ : syracuseStep 2507323 = 3760985) B3760985
theorem B3343097 : Blo 2227435 3343097 := bstep (se 2 (by rfl) ⟨1253661, by rfl⟩ : syracuseStep 3343097 = 2507323) B2507323
theorem B2228731 : Blo 2227435 2228731 := bstep (se 1 (by rfl) ⟨1671548, by rfl⟩ : syracuseStep 2228731 = 3343097) B3343097
theorem B2859229 : Blo 2227435 2859229 := bbase (se 3 (by rfl) ⟨536105, by rfl⟩ : syracuseStep 2859229 = 1072211) (by norm_num)
theorem B15249221 : Blo 2227435 15249221 := bstep (se 4 (by rfl) ⟨1429614, by rfl⟩ : syracuseStep 15249221 = 2859229) B2859229
theorem B10166147 : Blo 2227435 10166147 := bstep (se 1 (by rfl) ⟨7624610, by rfl⟩ : syracuseStep 10166147 = 15249221) B15249221
theorem B6777431 : Blo 2227435 6777431 := bstep (se 1 (by rfl) ⟨5083073, by rfl⟩ : syracuseStep 6777431 = 10166147) B10166147
theorem B4518287 : Blo 2227435 4518287 := bstep (se 1 (by rfl) ⟨3388715, by rfl⟩ : syracuseStep 4518287 = 6777431) B6777431
theorem B3012191 : Blo 2227435 3012191 := bstep (se 1 (by rfl) ⟨2259143, by rfl⟩ : syracuseStep 3012191 = 4518287) B4518287
theorem B32130037 : Blo 2227435 32130037 := bstep (se 5 (by rfl) ⟨1506095, by rfl⟩ : syracuseStep 32130037 = 3012191) B3012191
theorem B42840049 : Blo 2227435 42840049 := bstep (se 2 (by rfl) ⟨16065018, by rfl⟩ : syracuseStep 42840049 = 32130037) B32130037
theorem B57120065 : Blo 2227435 57120065 := bstep (se 2 (by rfl) ⟨21420024, by rfl⟩ : syracuseStep 57120065 = 42840049) B42840049
theorem B38080043 : Blo 2227435 38080043 := bstep (se 1 (by rfl) ⟨28560032, by rfl⟩ : syracuseStep 38080043 = 57120065) B57120065
theorem B25386695 : Blo 2227435 25386695 := bstep (se 1 (by rfl) ⟨19040021, by rfl⟩ : syracuseStep 25386695 = 38080043) B38080043
theorem B16924463 : Blo 2227435 16924463 := bstep (se 1 (by rfl) ⟨12693347, by rfl⟩ : syracuseStep 16924463 = 25386695) B25386695
theorem B11282975 : Blo 2227435 11282975 := bstep (se 1 (by rfl) ⟨8462231, by rfl⟩ : syracuseStep 11282975 = 16924463) B16924463
theorem B7521983 : Blo 2227435 7521983 := bstep (se 1 (by rfl) ⟨5641487, by rfl⟩ : syracuseStep 7521983 = 11282975) B11282975
theorem B5014655 : Blo 2227435 5014655 := bstep (se 1 (by rfl) ⟨3760991, by rfl⟩ : syracuseStep 5014655 = 7521983) B7521983
theorem B3343103 : Blo 2227435 3343103 := bstep (se 1 (by rfl) ⟨2507327, by rfl⟩ : syracuseStep 3343103 = 5014655) B5014655
theorem B2228735 : Blo 2227435 2228735 := bstep (se 1 (by rfl) ⟨1671551, by rfl⟩ : syracuseStep 2228735 = 3343103) B3343103
theorem B3343109 : Blo 2227435 3343109 := bbase (se 4 (by rfl) ⟨313416, by rfl⟩ : syracuseStep 3343109 = 626833) (by norm_num)
theorem B2228739 : Blo 2227435 2228739 := bstep (se 1 (by rfl) ⟨1671554, by rfl⟩ : syracuseStep 2228739 = 3343109) B3343109
theorem B3761005 : Blo 2227435 3761005 := bbase (se 3 (by rfl) ⟨705188, by rfl⟩ : syracuseStep 3761005 = 1410377) (by norm_num)
theorem B5014673 : Blo 2227435 5014673 := bstep (se 2 (by rfl) ⟨1880502, by rfl⟩ : syracuseStep 5014673 = 3761005) B3761005
theorem B3343115 : Blo 2227435 3343115 := bstep (se 1 (by rfl) ⟨2507336, by rfl⟩ : syracuseStep 3343115 = 5014673) B5014673
theorem B2228743 : Blo 2227435 2228743 := bstep (se 1 (by rfl) ⟨1671557, by rfl⟩ : syracuseStep 2228743 = 3343115) B3343115
theorem B2507341 : Blo 2227435 2507341 := bbase (se 3 (by rfl) ⟨470126, by rfl⟩ : syracuseStep 2507341 = 940253) (by norm_num)
theorem B3343121 : Blo 2227435 3343121 := bstep (se 2 (by rfl) ⟨1253670, by rfl⟩ : syracuseStep 3343121 = 2507341) B2507341
theorem B2228747 : Blo 2227435 2228747 := bstep (se 1 (by rfl) ⟨1671560, by rfl⟩ : syracuseStep 2228747 = 3343121) B3343121
theorem B7522037 : Blo 2227435 7522037 := bbase (se 5 (by rfl) ⟨352595, by rfl⟩ : syracuseStep 7522037 = 705191) (by norm_num)
theorem B5014691 : Blo 2227435 5014691 := bstep (se 1 (by rfl) ⟨3761018, by rfl⟩ : syracuseStep 5014691 = 7522037) B7522037
theorem B3343127 : Blo 2227435 3343127 := bstep (se 1 (by rfl) ⟨2507345, by rfl⟩ : syracuseStep 3343127 = 5014691) B5014691
theorem B2228751 : Blo 2227435 2228751 := bstep (se 1 (by rfl) ⟨1671563, by rfl⟩ : syracuseStep 2228751 = 3343127) B3343127
theorem B3343133 : Blo 2227435 3343133 := bbase (se 3 (by rfl) ⟨626837, by rfl⟩ : syracuseStep 3343133 = 1253675) (by norm_num)
theorem B2228755 : Blo 2227435 2228755 := bstep (se 1 (by rfl) ⟨1671566, by rfl⟩ : syracuseStep 2228755 = 3343133) B3343133
theorem B5014709 : Blo 2227435 5014709 := bbase (se 5 (by rfl) ⟨235064, by rfl⟩ : syracuseStep 5014709 = 470129) (by norm_num)
theorem B3343139 : Blo 2227435 3343139 := bstep (se 1 (by rfl) ⟨2507354, by rfl⟩ : syracuseStep 3343139 = 5014709) B5014709
theorem B2228759 : Blo 2227435 2228759 := bstep (se 1 (by rfl) ⟨1671569, by rfl⟩ : syracuseStep 2228759 = 3343139) B3343139
theorem B2380033 : Blo 2227435 2380033 := bbase (se 2 (by rfl) ⟨892512, by rfl⟩ : syracuseStep 2380033 = 1785025) (by norm_num)
theorem B12693509 : Blo 2227435 12693509 := bstep (se 4 (by rfl) ⟨1190016, by rfl⟩ : syracuseStep 12693509 = 2380033) B2380033
theorem B8462339 : Blo 2227435 8462339 := bstep (se 1 (by rfl) ⟨6346754, by rfl⟩ : syracuseStep 8462339 = 12693509) B12693509
theorem B5641559 : Blo 2227435 5641559 := bstep (se 1 (by rfl) ⟨4231169, by rfl⟩ : syracuseStep 5641559 = 8462339) B8462339
theorem B3761039 : Blo 2227435 3761039 := bstep (se 1 (by rfl) ⟨2820779, by rfl⟩ : syracuseStep 3761039 = 5641559) B5641559
theorem B2507359 : Blo 2227435 2507359 := bstep (se 1 (by rfl) ⟨1880519, by rfl⟩ : syracuseStep 2507359 = 3761039) B3761039
theorem B3343145 : Blo 2227435 3343145 := bstep (se 2 (by rfl) ⟨1253679, by rfl⟩ : syracuseStep 3343145 = 2507359) B2507359
theorem B2228763 : Blo 2227435 2228763 := bstep (se 1 (by rfl) ⟨1671572, by rfl⟩ : syracuseStep 2228763 = 3343145) B3343145
theorem B2380037 : Blo 2227435 2380037 := bbase (se 4 (by rfl) ⟨223128, by rfl⟩ : syracuseStep 2380037 = 446257) (by norm_num)
theorem B6346765 : Blo 2227435 6346765 := bstep (se 3 (by rfl) ⟨1190018, by rfl⟩ : syracuseStep 6346765 = 2380037) B2380037
theorem B8462353 : Blo 2227435 8462353 := bstep (se 2 (by rfl) ⟨3173382, by rfl⟩ : syracuseStep 8462353 = 6346765) B6346765
theorem B11283137 : Blo 2227435 11283137 := bstep (se 2 (by rfl) ⟨4231176, by rfl⟩ : syracuseStep 11283137 = 8462353) B8462353
theorem B7522091 : Blo 2227435 7522091 := bstep (se 1 (by rfl) ⟨5641568, by rfl⟩ : syracuseStep 7522091 = 11283137) B11283137
theorem B5014727 : Blo 2227435 5014727 := bstep (se 1 (by rfl) ⟨3761045, by rfl⟩ : syracuseStep 5014727 = 7522091) B7522091
theorem B3343151 : Blo 2227435 3343151 := bstep (se 1 (by rfl) ⟨2507363, by rfl⟩ : syracuseStep 3343151 = 5014727) B5014727
theorem B2228767 : Blo 2227435 2228767 := bstep (se 1 (by rfl) ⟨1671575, by rfl⟩ : syracuseStep 2228767 = 3343151) B3343151
theorem B3343157 : Blo 2227435 3343157 := bbase (se 5 (by rfl) ⟨156710, by rfl⟩ : syracuseStep 3343157 = 313421) (by norm_num)
theorem B2228771 : Blo 2227435 2228771 := bstep (se 1 (by rfl) ⟨1671578, by rfl⟩ : syracuseStep 2228771 = 3343157) B3343157
theorem B5641589 : Blo 2227435 5641589 := bbase (se 5 (by rfl) ⟨264449, by rfl⟩ : syracuseStep 5641589 = 528899) (by norm_num)
theorem B3761059 : Blo 2227435 3761059 := bstep (se 1 (by rfl) ⟨2820794, by rfl⟩ : syracuseStep 3761059 = 5641589) B5641589
theorem B5014745 : Blo 2227435 5014745 := bstep (se 2 (by rfl) ⟨1880529, by rfl⟩ : syracuseStep 5014745 = 3761059) B3761059
theorem B3343163 : Blo 2227435 3343163 := bstep (se 1 (by rfl) ⟨2507372, by rfl⟩ : syracuseStep 3343163 = 5014745) B5014745
theorem B2228775 : Blo 2227435 2228775 := bstep (se 1 (by rfl) ⟨1671581, by rfl⟩ : syracuseStep 2228775 = 3343163) B3343163
theorem B2507377 : Blo 2227435 2507377 := bbase (se 2 (by rfl) ⟨940266, by rfl⟩ : syracuseStep 2507377 = 1880533) (by norm_num)
theorem B3343169 : Blo 2227435 3343169 := bstep (se 2 (by rfl) ⟨1253688, by rfl⟩ : syracuseStep 3343169 = 2507377) B2507377
theorem B2228779 : Blo 2227435 2228779 := bstep (se 1 (by rfl) ⟨1671584, by rfl⟩ : syracuseStep 2228779 = 3343169) B3343169
theorem B10710245 : Blo 2227435 10710245 := bbase (se 4 (by rfl) ⟨1004085, by rfl⟩ : syracuseStep 10710245 = 2008171) (by norm_num)
theorem B7140163 : Blo 2227435 7140163 := bstep (se 1 (by rfl) ⟨5355122, by rfl⟩ : syracuseStep 7140163 = 10710245) B10710245
theorem B9520217 : Blo 2227435 9520217 := bstep (se 2 (by rfl) ⟨3570081, by rfl⟩ : syracuseStep 9520217 = 7140163) B7140163
theorem B6346811 : Blo 2227435 6346811 := bstep (se 1 (by rfl) ⟨4760108, by rfl⟩ : syracuseStep 6346811 = 9520217) B9520217
theorem B4231207 : Blo 2227435 4231207 := bstep (se 1 (by rfl) ⟨3173405, by rfl⟩ : syracuseStep 4231207 = 6346811) B6346811
theorem B5641609 : Blo 2227435 5641609 := bstep (se 2 (by rfl) ⟨2115603, by rfl⟩ : syracuseStep 5641609 = 4231207) B4231207
theorem B7522145 : Blo 2227435 7522145 := bstep (se 2 (by rfl) ⟨2820804, by rfl⟩ : syracuseStep 7522145 = 5641609) B5641609
theorem B5014763 : Blo 2227435 5014763 := bstep (se 1 (by rfl) ⟨3761072, by rfl⟩ : syracuseStep 5014763 = 7522145) B7522145
theorem B3343175 : Blo 2227435 3343175 := bstep (se 1 (by rfl) ⟨2507381, by rfl⟩ : syracuseStep 3343175 = 5014763) B5014763
theorem B2228783 : Blo 2227435 2228783 := bstep (se 1 (by rfl) ⟨1671587, by rfl⟩ : syracuseStep 2228783 = 3343175) B3343175
theorem B3343181 : Blo 2227435 3343181 := bbase (se 3 (by rfl) ⟨626846, by rfl⟩ : syracuseStep 3343181 = 1253693) (by norm_num)
theorem B2228787 : Blo 2227435 2228787 := bstep (se 1 (by rfl) ⟨1671590, by rfl⟩ : syracuseStep 2228787 = 3343181) B3343181
theorem B5014781 : Blo 2227435 5014781 := bbase (se 3 (by rfl) ⟨940271, by rfl⟩ : syracuseStep 5014781 = 1880543) (by norm_num)
theorem B3343187 : Blo 2227435 3343187 := bstep (se 1 (by rfl) ⟨2507390, by rfl⟩ : syracuseStep 3343187 = 5014781) B5014781
theorem B2228791 : Blo 2227435 2228791 := bstep (se 1 (by rfl) ⟨1671593, by rfl⟩ : syracuseStep 2228791 = 3343187) B3343187
theorem B3761093 : Blo 2227435 3761093 := bbase (se 4 (by rfl) ⟨352602, by rfl⟩ : syracuseStep 3761093 = 705205) (by norm_num)
theorem B2507395 : Blo 2227435 2507395 := bstep (se 1 (by rfl) ⟨1880546, by rfl⟩ : syracuseStep 2507395 = 3761093) B3761093
theorem B3343193 : Blo 2227435 3343193 := bstep (se 2 (by rfl) ⟨1253697, by rfl⟩ : syracuseStep 3343193 = 2507395) B2507395
theorem B2228795 : Blo 2227435 2228795 := bstep (se 1 (by rfl) ⟨1671596, by rfl⟩ : syracuseStep 2228795 = 3343193) B3343193
theorem B16924949 : Blo 2227435 16924949 := bbase (se 6 (by rfl) ⟨396678, by rfl⟩ : syracuseStep 16924949 = 793357) (by norm_num)
theorem B11283299 : Blo 2227435 11283299 := bstep (se 1 (by rfl) ⟨8462474, by rfl⟩ : syracuseStep 11283299 = 16924949) B16924949
theorem B7522199 : Blo 2227435 7522199 := bstep (se 1 (by rfl) ⟨5641649, by rfl⟩ : syracuseStep 7522199 = 11283299) B11283299
theorem B5014799 : Blo 2227435 5014799 := bstep (se 1 (by rfl) ⟨3761099, by rfl⟩ : syracuseStep 5014799 = 7522199) B7522199
theorem B3343199 : Blo 2227435 3343199 := bstep (se 1 (by rfl) ⟨2507399, by rfl⟩ : syracuseStep 3343199 = 5014799) B5014799
theorem B2228799 : Blo 2227435 2228799 := bstep (se 1 (by rfl) ⟨1671599, by rfl⟩ : syracuseStep 2228799 = 3343199) B3343199
theorem B3343205 : Blo 2227435 3343205 := bbase (se 4 (by rfl) ⟨313425, by rfl⟩ : syracuseStep 3343205 = 626851) (by norm_num)
theorem B2228803 : Blo 2227435 2228803 := bstep (se 1 (by rfl) ⟨1671602, by rfl⟩ : syracuseStep 2228803 = 3343205) B3343205
theorem B4231253 : Blo 2227435 4231253 := bbase (se 8 (by rfl) ⟨24792, by rfl⟩ : syracuseStep 4231253 = 49585) (by norm_num)
theorem B2820835 : Blo 2227435 2820835 := bstep (se 1 (by rfl) ⟨2115626, by rfl⟩ : syracuseStep 2820835 = 4231253) B4231253
theorem B3761113 : Blo 2227435 3761113 := bstep (se 2 (by rfl) ⟨1410417, by rfl⟩ : syracuseStep 3761113 = 2820835) B2820835
theorem B5014817 : Blo 2227435 5014817 := bstep (se 2 (by rfl) ⟨1880556, by rfl⟩ : syracuseStep 5014817 = 3761113) B3761113
theorem B3343211 : Blo 2227435 3343211 := bstep (se 1 (by rfl) ⟨2507408, by rfl⟩ : syracuseStep 3343211 = 5014817) B5014817
theorem B2228807 : Blo 2227435 2228807 := bstep (se 1 (by rfl) ⟨1671605, by rfl⟩ : syracuseStep 2228807 = 3343211) B3343211
theorem B2507413 : Blo 2227435 2507413 := bbase (se 6 (by rfl) ⟨58767, by rfl⟩ : syracuseStep 2507413 = 117535) (by norm_num)
theorem B3343217 : Blo 2227435 3343217 := bstep (se 2 (by rfl) ⟨1253706, by rfl⟩ : syracuseStep 3343217 = 2507413) B2507413
theorem B2228811 : Blo 2227435 2228811 := bstep (se 1 (by rfl) ⟨1671608, by rfl⟩ : syracuseStep 2228811 = 3343217) B3343217
theorem B2820845 : Blo 2227435 2820845 := bbase (se 3 (by rfl) ⟨528908, by rfl⟩ : syracuseStep 2820845 = 1057817) (by norm_num)
theorem B7522253 : Blo 2227435 7522253 := bstep (se 3 (by rfl) ⟨1410422, by rfl⟩ : syracuseStep 7522253 = 2820845) B2820845
theorem B5014835 : Blo 2227435 5014835 := bstep (se 1 (by rfl) ⟨3761126, by rfl⟩ : syracuseStep 5014835 = 7522253) B7522253
theorem B3343223 : Blo 2227435 3343223 := bstep (se 1 (by rfl) ⟨2507417, by rfl⟩ : syracuseStep 3343223 = 5014835) B5014835
theorem B2228815 : Blo 2227435 2228815 := bstep (se 1 (by rfl) ⟨1671611, by rfl⟩ : syracuseStep 2228815 = 3343223) B3343223
theorem B3343229 : Blo 2227435 3343229 := bbase (se 3 (by rfl) ⟨626855, by rfl⟩ : syracuseStep 3343229 = 1253711) (by norm_num)
theorem B2228819 : Blo 2227435 2228819 := bstep (se 1 (by rfl) ⟨1671614, by rfl⟩ : syracuseStep 2228819 = 3343229) B3343229
theorem B5014853 : Blo 2227435 5014853 := bbase (se 4 (by rfl) ⟨470142, by rfl⟩ : syracuseStep 5014853 = 940285) (by norm_num)
theorem B3343235 : Blo 2227435 3343235 := bstep (se 1 (by rfl) ⟨2507426, by rfl⟩ : syracuseStep 3343235 = 5014853) B5014853
theorem B2228823 : Blo 2227435 2228823 := bstep (se 1 (by rfl) ⟨1671617, by rfl⟩ : syracuseStep 2228823 = 3343235) B3343235
theorem B5355229 : Blo 2227435 5355229 := bbase (se 3 (by rfl) ⟨1004105, by rfl⟩ : syracuseStep 5355229 = 2008211) (by norm_num)
theorem B7140305 : Blo 2227435 7140305 := bstep (se 2 (by rfl) ⟨2677614, by rfl⟩ : syracuseStep 7140305 = 5355229) B5355229
theorem B4760203 : Blo 2227435 4760203 := bstep (se 1 (by rfl) ⟨3570152, by rfl⟩ : syracuseStep 4760203 = 7140305) B7140305
theorem B6346937 : Blo 2227435 6346937 := bstep (se 2 (by rfl) ⟨2380101, by rfl⟩ : syracuseStep 6346937 = 4760203) B4760203
theorem B4231291 : Blo 2227435 4231291 := bstep (se 1 (by rfl) ⟨3173468, by rfl⟩ : syracuseStep 4231291 = 6346937) B6346937
theorem B5641721 : Blo 2227435 5641721 := bstep (se 2 (by rfl) ⟨2115645, by rfl⟩ : syracuseStep 5641721 = 4231291) B4231291
theorem B3761147 : Blo 2227435 3761147 := bstep (se 1 (by rfl) ⟨2820860, by rfl⟩ : syracuseStep 3761147 = 5641721) B5641721
theorem B2507431 : Blo 2227435 2507431 := bstep (se 1 (by rfl) ⟨1880573, by rfl⟩ : syracuseStep 2507431 = 3761147) B3761147
theorem B3343241 : Blo 2227435 3343241 := bstep (se 2 (by rfl) ⟨1253715, by rfl⟩ : syracuseStep 3343241 = 2507431) B2507431
theorem B2228827 : Blo 2227435 2228827 := bstep (se 1 (by rfl) ⟨1671620, by rfl⟩ : syracuseStep 2228827 = 3343241) B3343241
theorem B11283461 : Blo 2227435 11283461 := bbase (se 4 (by rfl) ⟨1057824, by rfl⟩ : syracuseStep 11283461 = 2115649) (by norm_num)
theorem B7522307 : Blo 2227435 7522307 := bstep (se 1 (by rfl) ⟨5641730, by rfl⟩ : syracuseStep 7522307 = 11283461) B11283461
theorem B5014871 : Blo 2227435 5014871 := bstep (se 1 (by rfl) ⟨3761153, by rfl⟩ : syracuseStep 5014871 = 7522307) B7522307
theorem B3343247 : Blo 2227435 3343247 := bstep (se 1 (by rfl) ⟨2507435, by rfl⟩ : syracuseStep 3343247 = 5014871) B5014871
theorem B2228831 : Blo 2227435 2228831 := bstep (se 1 (by rfl) ⟨1671623, by rfl⟩ : syracuseStep 2228831 = 3343247) B3343247
theorem B3343253 : Blo 2227435 3343253 := bbase (se 6 (by rfl) ⟨78357, by rfl⟩ : syracuseStep 3343253 = 156715) (by norm_num)
theorem B2228835 : Blo 2227435 2228835 := bstep (se 1 (by rfl) ⟨1671626, by rfl⟩ : syracuseStep 2228835 = 3343253) B3343253
theorem B12693941 : Blo 2227435 12693941 := bbase (se 5 (by rfl) ⟨595028, by rfl⟩ : syracuseStep 12693941 = 1190057) (by norm_num)
theorem B8462627 : Blo 2227435 8462627 := bstep (se 1 (by rfl) ⟨6346970, by rfl⟩ : syracuseStep 8462627 = 12693941) B12693941
theorem B5641751 : Blo 2227435 5641751 := bstep (se 1 (by rfl) ⟨4231313, by rfl⟩ : syracuseStep 5641751 = 8462627) B8462627
theorem B3761167 : Blo 2227435 3761167 := bstep (se 1 (by rfl) ⟨2820875, by rfl⟩ : syracuseStep 3761167 = 5641751) B5641751
theorem B5014889 : Blo 2227435 5014889 := bstep (se 2 (by rfl) ⟨1880583, by rfl⟩ : syracuseStep 5014889 = 3761167) B3761167
theorem B3343259 : Blo 2227435 3343259 := bstep (se 1 (by rfl) ⟨2507444, by rfl⟩ : syracuseStep 3343259 = 5014889) B5014889
theorem B2228839 : Blo 2227435 2228839 := bstep (se 1 (by rfl) ⟨1671629, by rfl⟩ : syracuseStep 2228839 = 3343259) B3343259
theorem B2507449 : Blo 2227435 2507449 := bbase (se 2 (by rfl) ⟨940293, by rfl⟩ : syracuseStep 2507449 = 1880587) (by norm_num)
theorem B3343265 : Blo 2227435 3343265 := bstep (se 2 (by rfl) ⟨1253724, by rfl⟩ : syracuseStep 3343265 = 2507449) B2507449
theorem B2228843 : Blo 2227435 2228843 := bstep (se 1 (by rfl) ⟨1671632, by rfl⟩ : syracuseStep 2228843 = 3343265) B3343265
theorem B4760245 : Blo 2227435 4760245 := bbase (se 5 (by rfl) ⟨223136, by rfl⟩ : syracuseStep 4760245 = 446273) (by norm_num)
theorem B6346993 : Blo 2227435 6346993 := bstep (se 2 (by rfl) ⟨2380122, by rfl⟩ : syracuseStep 6346993 = 4760245) B4760245
theorem B8462657 : Blo 2227435 8462657 := bstep (se 2 (by rfl) ⟨3173496, by rfl⟩ : syracuseStep 8462657 = 6346993) B6346993
theorem B5641771 : Blo 2227435 5641771 := bstep (se 1 (by rfl) ⟨4231328, by rfl⟩ : syracuseStep 5641771 = 8462657) B8462657
theorem B7522361 : Blo 2227435 7522361 := bstep (se 2 (by rfl) ⟨2820885, by rfl⟩ : syracuseStep 7522361 = 5641771) B5641771
theorem B5014907 : Blo 2227435 5014907 := bstep (se 1 (by rfl) ⟨3761180, by rfl⟩ : syracuseStep 5014907 = 7522361) B7522361
theorem B3343271 : Blo 2227435 3343271 := bstep (se 1 (by rfl) ⟨2507453, by rfl⟩ : syracuseStep 3343271 = 5014907) B5014907
theorem B2228847 : Blo 2227435 2228847 := bstep (se 1 (by rfl) ⟨1671635, by rfl⟩ : syracuseStep 2228847 = 3343271) B3343271
theorem B3343277 : Blo 2227435 3343277 := bbase (se 3 (by rfl) ⟨626864, by rfl⟩ : syracuseStep 3343277 = 1253729) (by norm_num)
theorem B2228851 : Blo 2227435 2228851 := bstep (se 1 (by rfl) ⟨1671638, by rfl⟩ : syracuseStep 2228851 = 3343277) B3343277
theorem B5014925 : Blo 2227435 5014925 := bbase (se 3 (by rfl) ⟨940298, by rfl⟩ : syracuseStep 5014925 = 1880597) (by norm_num)
theorem B3343283 : Blo 2227435 3343283 := bstep (se 1 (by rfl) ⟨2507462, by rfl⟩ : syracuseStep 3343283 = 5014925) B5014925
theorem B2228855 : Blo 2227435 2228855 := bstep (se 1 (by rfl) ⟨1671641, by rfl⟩ : syracuseStep 2228855 = 3343283) B3343283
theorem B2820901 : Blo 2227435 2820901 := bbase (se 4 (by rfl) ⟨264459, by rfl⟩ : syracuseStep 2820901 = 528919) (by norm_num)
theorem B3761201 : Blo 2227435 3761201 := bstep (se 2 (by rfl) ⟨1410450, by rfl⟩ : syracuseStep 3761201 = 2820901) B2820901
theorem B2507467 : Blo 2227435 2507467 := bstep (se 1 (by rfl) ⟨1880600, by rfl⟩ : syracuseStep 2507467 = 3761201) B3761201
theorem B3343289 : Blo 2227435 3343289 := bstep (se 2 (by rfl) ⟨1253733, by rfl⟩ : syracuseStep 3343289 = 2507467) B2507467
theorem B2228859 : Blo 2227435 2228859 := bstep (se 1 (by rfl) ⟨1671644, by rfl⟩ : syracuseStep 2228859 = 3343289) B3343289
theorem B2412613 : Blo 2227435 2412613 := bbase (se 4 (by rfl) ⟨226182, by rfl⟩ : syracuseStep 2412613 = 452365) (by norm_num)
theorem B3216817 : Blo 2227435 3216817 := bstep (se 2 (by rfl) ⟨1206306, by rfl⟩ : syracuseStep 3216817 = 2412613) B2412613
theorem B17156357 : Blo 2227435 17156357 := bstep (se 4 (by rfl) ⟨1608408, by rfl⟩ : syracuseStep 17156357 = 3216817) B3216817
theorem B11437571 : Blo 2227435 11437571 := bstep (se 1 (by rfl) ⟨8578178, by rfl⟩ : syracuseStep 11437571 = 17156357) B17156357
theorem B7625047 : Blo 2227435 7625047 := bstep (se 1 (by rfl) ⟨5718785, by rfl⟩ : syracuseStep 7625047 = 11437571) B11437571
theorem B10166729 : Blo 2227435 10166729 := bstep (se 2 (by rfl) ⟨3812523, by rfl⟩ : syracuseStep 10166729 = 7625047) B7625047
theorem B27111277 : Blo 2227435 27111277 := bstep (se 3 (by rfl) ⟨5083364, by rfl⟩ : syracuseStep 27111277 = 10166729) B10166729
theorem B36148369 : Blo 2227435 36148369 := bstep (se 2 (by rfl) ⟨13555638, by rfl⟩ : syracuseStep 36148369 = 27111277) B27111277
theorem B48197825 : Blo 2227435 48197825 := bstep (se 2 (by rfl) ⟨18074184, by rfl⟩ : syracuseStep 48197825 = 36148369) B36148369
theorem B32131883 : Blo 2227435 32131883 := bstep (se 1 (by rfl) ⟨24098912, by rfl⟩ : syracuseStep 32131883 = 48197825) B48197825
theorem B21421255 : Blo 2227435 21421255 := bstep (se 1 (by rfl) ⟨16065941, by rfl⟩ : syracuseStep 21421255 = 32131883) B32131883
theorem B28561673 : Blo 2227435 28561673 := bstep (se 2 (by rfl) ⟨10710627, by rfl⟩ : syracuseStep 28561673 = 21421255) B21421255
theorem B19041115 : Blo 2227435 19041115 := bstep (se 1 (by rfl) ⟨14280836, by rfl⟩ : syracuseStep 19041115 = 28561673) B28561673
theorem B25388153 : Blo 2227435 25388153 := bstep (se 2 (by rfl) ⟨9520557, by rfl⟩ : syracuseStep 25388153 = 19041115) B19041115
theorem B16925435 : Blo 2227435 16925435 := bstep (se 1 (by rfl) ⟨12694076, by rfl⟩ : syracuseStep 16925435 = 25388153) B25388153
theorem B11283623 : Blo 2227435 11283623 := bstep (se 1 (by rfl) ⟨8462717, by rfl⟩ : syracuseStep 11283623 = 16925435) B16925435
theorem B7522415 : Blo 2227435 7522415 := bstep (se 1 (by rfl) ⟨5641811, by rfl⟩ : syracuseStep 7522415 = 11283623) B11283623
theorem B5014943 : Blo 2227435 5014943 := bstep (se 1 (by rfl) ⟨3761207, by rfl⟩ : syracuseStep 5014943 = 7522415) B7522415
theorem B3343295 : Blo 2227435 3343295 := bstep (se 1 (by rfl) ⟨2507471, by rfl⟩ : syracuseStep 3343295 = 5014943) B5014943
theorem B2228863 : Blo 2227435 2228863 := bstep (se 1 (by rfl) ⟨1671647, by rfl⟩ : syracuseStep 2228863 = 3343295) B3343295
theorem B3343301 : Blo 2227435 3343301 := bbase (se 4 (by rfl) ⟨313434, by rfl⟩ : syracuseStep 3343301 = 626869) (by norm_num)
theorem B2228867 : Blo 2227435 2228867 := bstep (se 1 (by rfl) ⟨1671650, by rfl⟩ : syracuseStep 2228867 = 3343301) B3343301
theorem B3761221 : Blo 2227435 3761221 := bbase (se 4 (by rfl) ⟨352614, by rfl⟩ : syracuseStep 3761221 = 705229) (by norm_num)
theorem B5014961 : Blo 2227435 5014961 := bstep (se 2 (by rfl) ⟨1880610, by rfl⟩ : syracuseStep 5014961 = 3761221) B3761221
theorem B3343307 : Blo 2227435 3343307 := bstep (se 1 (by rfl) ⟨2507480, by rfl⟩ : syracuseStep 3343307 = 5014961) B5014961
theorem B2228871 : Blo 2227435 2228871 := bstep (se 1 (by rfl) ⟨1671653, by rfl⟩ : syracuseStep 2228871 = 3343307) B3343307
theorem B2507485 : Blo 2227435 2507485 := bbase (se 3 (by rfl) ⟨470153, by rfl⟩ : syracuseStep 2507485 = 940307) (by norm_num)
theorem B3343313 : Blo 2227435 3343313 := bstep (se 2 (by rfl) ⟨1253742, by rfl⟩ : syracuseStep 3343313 = 2507485) B2507485
theorem B2228875 : Blo 2227435 2228875 := bstep (se 1 (by rfl) ⟨1671656, by rfl⟩ : syracuseStep 2228875 = 3343313) B3343313
theorem B7522469 : Blo 2227435 7522469 := bbase (se 4 (by rfl) ⟨705231, by rfl⟩ : syracuseStep 7522469 = 1410463) (by norm_num)
theorem B5014979 : Blo 2227435 5014979 := bstep (se 1 (by rfl) ⟨3761234, by rfl⟩ : syracuseStep 5014979 = 7522469) B7522469
theorem B3343319 : Blo 2227435 3343319 := bstep (se 1 (by rfl) ⟨2507489, by rfl⟩ : syracuseStep 3343319 = 5014979) B5014979
theorem B2228879 : Blo 2227435 2228879 := bstep (se 1 (by rfl) ⟨1671659, by rfl⟩ : syracuseStep 2228879 = 3343319) B3343319
theorem B3343325 : Blo 2227435 3343325 := bbase (se 3 (by rfl) ⟨626873, by rfl⟩ : syracuseStep 3343325 = 1253747) (by norm_num)
theorem B2228883 : Blo 2227435 2228883 := bstep (se 1 (by rfl) ⟨1671662, by rfl⟩ : syracuseStep 2228883 = 3343325) B3343325
theorem B5014997 : Blo 2227435 5014997 := bbase (se 7 (by rfl) ⟨58769, by rfl⟩ : syracuseStep 5014997 = 117539) (by norm_num)
theorem B3343331 : Blo 2227435 3343331 := bstep (se 1 (by rfl) ⟨2507498, by rfl⟩ : syracuseStep 3343331 = 5014997) B5014997
theorem B2228887 : Blo 2227435 2228887 := bstep (se 1 (by rfl) ⟨1671665, by rfl⟩ : syracuseStep 2228887 = 3343331) B3343331
theorem B24099221 : Blo 2227435 24099221 := bbase (se 6 (by rfl) ⟨564825, by rfl⟩ : syracuseStep 24099221 = 1129651) (by norm_num)
theorem B16066147 : Blo 2227435 16066147 := bstep (se 1 (by rfl) ⟨12049610, by rfl⟩ : syracuseStep 16066147 = 24099221) B24099221
theorem B21421529 : Blo 2227435 21421529 := bstep (se 2 (by rfl) ⟨8033073, by rfl⟩ : syracuseStep 21421529 = 16066147) B16066147
theorem B14281019 : Blo 2227435 14281019 := bstep (se 1 (by rfl) ⟨10710764, by rfl⟩ : syracuseStep 14281019 = 21421529) B21421529
theorem B9520679 : Blo 2227435 9520679 := bstep (se 1 (by rfl) ⟨7140509, by rfl⟩ : syracuseStep 9520679 = 14281019) B14281019
theorem B6347119 : Blo 2227435 6347119 := bstep (se 1 (by rfl) ⟨4760339, by rfl⟩ : syracuseStep 6347119 = 9520679) B9520679
theorem B8462825 : Blo 2227435 8462825 := bstep (se 2 (by rfl) ⟨3173559, by rfl⟩ : syracuseStep 8462825 = 6347119) B6347119
theorem B5641883 : Blo 2227435 5641883 := bstep (se 1 (by rfl) ⟨4231412, by rfl⟩ : syracuseStep 5641883 = 8462825) B8462825
theorem B3761255 : Blo 2227435 3761255 := bstep (se 1 (by rfl) ⟨2820941, by rfl⟩ : syracuseStep 3761255 = 5641883) B5641883
theorem B2507503 : Blo 2227435 2507503 := bstep (se 1 (by rfl) ⟨1880627, by rfl⟩ : syracuseStep 2507503 = 3761255) B3761255
theorem B3343337 : Blo 2227435 3343337 := bstep (se 2 (by rfl) ⟨1253751, by rfl⟩ : syracuseStep 3343337 = 2507503) B2507503
theorem B2228891 : Blo 2227435 2228891 := bstep (se 1 (by rfl) ⟨1671668, by rfl⟩ : syracuseStep 2228891 = 3343337) B3343337
theorem B2611549 : Blo 2227435 2611549 := bbase (se 3 (by rfl) ⟨489665, by rfl⟩ : syracuseStep 2611549 = 979331) (by norm_num)
theorem B3482065 : Blo 2227435 3482065 := bstep (se 2 (by rfl) ⟨1305774, by rfl⟩ : syracuseStep 3482065 = 2611549) B2611549
theorem B4642753 : Blo 2227435 4642753 := bstep (se 2 (by rfl) ⟨1741032, by rfl⟩ : syracuseStep 4642753 = 3482065) B3482065
theorem B6190337 : Blo 2227435 6190337 := bstep (se 2 (by rfl) ⟨2321376, by rfl⟩ : syracuseStep 6190337 = 4642753) B4642753
theorem B4126891 : Blo 2227435 4126891 := bstep (se 1 (by rfl) ⟨3095168, by rfl⟩ : syracuseStep 4126891 = 6190337) B6190337
theorem B5502521 : Blo 2227435 5502521 := bstep (se 2 (by rfl) ⟨2063445, by rfl⟩ : syracuseStep 5502521 = 4126891) B4126891
theorem B3668347 : Blo 2227435 3668347 := bstep (se 1 (by rfl) ⟨2751260, by rfl⟩ : syracuseStep 3668347 = 5502521) B5502521
theorem B19564517 : Blo 2227435 19564517 := bstep (se 4 (by rfl) ⟨1834173, by rfl⟩ : syracuseStep 19564517 = 3668347) B3668347
theorem B13043011 : Blo 2227435 13043011 := bstep (se 1 (by rfl) ⟨9782258, by rfl⟩ : syracuseStep 13043011 = 19564517) B19564517
theorem B17390681 : Blo 2227435 17390681 := bstep (se 2 (by rfl) ⟨6521505, by rfl⟩ : syracuseStep 17390681 = 13043011) B13043011
theorem B11593787 : Blo 2227435 11593787 := bstep (se 1 (by rfl) ⟨8695340, by rfl⟩ : syracuseStep 11593787 = 17390681) B17390681
theorem B30916765 : Blo 2227435 30916765 := bstep (se 3 (by rfl) ⟨5796893, by rfl⟩ : syracuseStep 30916765 = 11593787) B11593787
theorem B41222353 : Blo 2227435 41222353 := bstep (se 2 (by rfl) ⟨15458382, by rfl⟩ : syracuseStep 41222353 = 30916765) B30916765
theorem B54963137 : Blo 2227435 54963137 := bstep (se 2 (by rfl) ⟨20611176, by rfl⟩ : syracuseStep 54963137 = 41222353) B41222353
theorem B36642091 : Blo 2227435 36642091 := bstep (se 1 (by rfl) ⟨27481568, by rfl⟩ : syracuseStep 36642091 = 54963137) B54963137
theorem B48856121 : Blo 2227435 48856121 := bstep (se 2 (by rfl) ⟨18321045, by rfl⟩ : syracuseStep 48856121 = 36642091) B36642091
theorem B32570747 : Blo 2227435 32570747 := bstep (se 1 (by rfl) ⟨24428060, by rfl⟩ : syracuseStep 32570747 = 48856121) B48856121
theorem B21713831 : Blo 2227435 21713831 := bstep (se 1 (by rfl) ⟨16285373, by rfl⟩ : syracuseStep 21713831 = 32570747) B32570747
theorem B14475887 : Blo 2227435 14475887 := bstep (se 1 (by rfl) ⟨10856915, by rfl⟩ : syracuseStep 14475887 = 21713831) B21713831
theorem B9650591 : Blo 2227435 9650591 := bstep (se 1 (by rfl) ⟨7237943, by rfl⟩ : syracuseStep 9650591 = 14475887) B14475887
theorem B6433727 : Blo 2227435 6433727 := bstep (se 1 (by rfl) ⟨4825295, by rfl⟩ : syracuseStep 6433727 = 9650591) B9650591
theorem B17156605 : Blo 2227435 17156605 := bstep (se 3 (by rfl) ⟨3216863, by rfl⟩ : syracuseStep 17156605 = 6433727) B6433727
theorem B22875473 : Blo 2227435 22875473 := bstep (se 2 (by rfl) ⟨8578302, by rfl⟩ : syracuseStep 22875473 = 17156605) B17156605
theorem B61001261 : Blo 2227435 61001261 := bstep (se 3 (by rfl) ⟨11437736, by rfl⟩ : syracuseStep 61001261 = 22875473) B22875473
theorem B40667507 : Blo 2227435 40667507 := bstep (se 1 (by rfl) ⟨30500630, by rfl⟩ : syracuseStep 40667507 = 61001261) B61001261
theorem B27111671 : Blo 2227435 27111671 := bstep (se 1 (by rfl) ⟨20333753, by rfl⟩ : syracuseStep 27111671 = 40667507) B40667507
theorem B18074447 : Blo 2227435 18074447 := bstep (se 1 (by rfl) ⟨13555835, by rfl⟩ : syracuseStep 18074447 = 27111671) B27111671
theorem B12049631 : Blo 2227435 12049631 := bstep (se 1 (by rfl) ⟨9037223, by rfl⟩ : syracuseStep 12049631 = 18074447) B18074447
theorem B8033087 : Blo 2227435 8033087 := bstep (se 1 (by rfl) ⟨6024815, by rfl⟩ : syracuseStep 8033087 = 12049631) B12049631
theorem B5355391 : Blo 2227435 5355391 := bstep (se 1 (by rfl) ⟨4016543, by rfl⟩ : syracuseStep 5355391 = 8033087) B8033087
theorem B7140521 : Blo 2227435 7140521 := bstep (se 2 (by rfl) ⟨2677695, by rfl⟩ : syracuseStep 7140521 = 5355391) B5355391
theorem B19041389 : Blo 2227435 19041389 := bstep (se 3 (by rfl) ⟨3570260, by rfl⟩ : syracuseStep 19041389 = 7140521) B7140521
theorem B12694259 : Blo 2227435 12694259 := bstep (se 1 (by rfl) ⟨9520694, by rfl⟩ : syracuseStep 12694259 = 19041389) B19041389
theorem B8462839 : Blo 2227435 8462839 := bstep (se 1 (by rfl) ⟨6347129, by rfl⟩ : syracuseStep 8462839 = 12694259) B12694259
theorem B11283785 : Blo 2227435 11283785 := bstep (se 2 (by rfl) ⟨4231419, by rfl⟩ : syracuseStep 11283785 = 8462839) B8462839
theorem B7522523 : Blo 2227435 7522523 := bstep (se 1 (by rfl) ⟨5641892, by rfl⟩ : syracuseStep 7522523 = 11283785) B11283785
theorem B5015015 : Blo 2227435 5015015 := bstep (se 1 (by rfl) ⟨3761261, by rfl⟩ : syracuseStep 5015015 = 7522523) B7522523
theorem B3343343 : Blo 2227435 3343343 := bstep (se 1 (by rfl) ⟨2507507, by rfl⟩ : syracuseStep 3343343 = 5015015) B5015015
theorem B2228895 : Blo 2227435 2228895 := bstep (se 1 (by rfl) ⟨1671671, by rfl⟩ : syracuseStep 2228895 = 3343343) B3343343
theorem B3343349 : Blo 2227435 3343349 := bbase (se 5 (by rfl) ⟨156719, by rfl⟩ : syracuseStep 3343349 = 313439) (by norm_num)
theorem B2228899 : Blo 2227435 2228899 := bstep (se 1 (by rfl) ⟨1671674, by rfl⟩ : syracuseStep 2228899 = 3343349) B3343349
theorem B4760365 : Blo 2227435 4760365 := bbase (se 3 (by rfl) ⟨892568, by rfl⟩ : syracuseStep 4760365 = 1785137) (by norm_num)
theorem B6347153 : Blo 2227435 6347153 := bstep (se 2 (by rfl) ⟨2380182, by rfl⟩ : syracuseStep 6347153 = 4760365) B4760365
theorem B4231435 : Blo 2227435 4231435 := bstep (se 1 (by rfl) ⟨3173576, by rfl⟩ : syracuseStep 4231435 = 6347153) B6347153
theorem B5641913 : Blo 2227435 5641913 := bstep (se 2 (by rfl) ⟨2115717, by rfl⟩ : syracuseStep 5641913 = 4231435) B4231435
theorem B3761275 : Blo 2227435 3761275 := bstep (se 1 (by rfl) ⟨2820956, by rfl⟩ : syracuseStep 3761275 = 5641913) B5641913
theorem B5015033 : Blo 2227435 5015033 := bstep (se 2 (by rfl) ⟨1880637, by rfl⟩ : syracuseStep 5015033 = 3761275) B3761275
theorem B3343355 : Blo 2227435 3343355 := bstep (se 1 (by rfl) ⟨2507516, by rfl⟩ : syracuseStep 3343355 = 5015033) B5015033
theorem B2228903 : Blo 2227435 2228903 := bstep (se 1 (by rfl) ⟨1671677, by rfl⟩ : syracuseStep 2228903 = 3343355) B3343355
theorem B2507521 : Blo 2227435 2507521 := bbase (se 2 (by rfl) ⟨940320, by rfl⟩ : syracuseStep 2507521 = 1880641) (by norm_num)
theorem B3343361 : Blo 2227435 3343361 := bstep (se 2 (by rfl) ⟨1253760, by rfl⟩ : syracuseStep 3343361 = 2507521) B2507521
theorem B2228907 : Blo 2227435 2228907 := bstep (se 1 (by rfl) ⟨1671680, by rfl⟩ : syracuseStep 2228907 = 3343361) B3343361
theorem B5641933 : Blo 2227435 5641933 := bbase (se 3 (by rfl) ⟨1057862, by rfl⟩ : syracuseStep 5641933 = 2115725) (by norm_num)
theorem B7522577 : Blo 2227435 7522577 := bstep (se 2 (by rfl) ⟨2820966, by rfl⟩ : syracuseStep 7522577 = 5641933) B5641933
theorem B5015051 : Blo 2227435 5015051 := bstep (se 1 (by rfl) ⟨3761288, by rfl⟩ : syracuseStep 5015051 = 7522577) B7522577
theorem B3343367 : Blo 2227435 3343367 := bstep (se 1 (by rfl) ⟨2507525, by rfl⟩ : syracuseStep 3343367 = 5015051) B5015051
theorem B2228911 : Blo 2227435 2228911 := bstep (se 1 (by rfl) ⟨1671683, by rfl⟩ : syracuseStep 2228911 = 3343367) B3343367
theorem B3343373 : Blo 2227435 3343373 := bbase (se 3 (by rfl) ⟨626882, by rfl⟩ : syracuseStep 3343373 = 1253765) (by norm_num)
theorem B2228915 : Blo 2227435 2228915 := bstep (se 1 (by rfl) ⟨1671686, by rfl⟩ : syracuseStep 2228915 = 3343373) B3343373
theorem B5015069 : Blo 2227435 5015069 := bbase (se 3 (by rfl) ⟨940325, by rfl⟩ : syracuseStep 5015069 = 1880651) (by norm_num)
theorem B3343379 : Blo 2227435 3343379 := bstep (se 1 (by rfl) ⟨2507534, by rfl⟩ : syracuseStep 3343379 = 5015069) B5015069
theorem B2228919 : Blo 2227435 2228919 := bstep (se 1 (by rfl) ⟨1671689, by rfl⟩ : syracuseStep 2228919 = 3343379) B3343379
theorem B3761309 : Blo 2227435 3761309 := bbase (se 3 (by rfl) ⟨705245, by rfl⟩ : syracuseStep 3761309 = 1410491) (by norm_num)
theorem B2507539 : Blo 2227435 2507539 := bstep (se 1 (by rfl) ⟨1880654, by rfl⟩ : syracuseStep 2507539 = 3761309) B3761309
theorem B3343385 : Blo 2227435 3343385 := bstep (se 2 (by rfl) ⟨1253769, by rfl⟩ : syracuseStep 3343385 = 2507539) B2507539
theorem B2228923 : Blo 2227435 2228923 := bstep (se 1 (by rfl) ⟨1671692, by rfl⟩ : syracuseStep 2228923 = 3343385) B3343385
theorem B4289213 : Blo 2227435 4289213 := bbase (se 3 (by rfl) ⟨804227, by rfl⟩ : syracuseStep 4289213 = 1608455) (by norm_num)
theorem B2859475 : Blo 2227435 2859475 := bstep (se 1 (by rfl) ⟨2144606, by rfl⟩ : syracuseStep 2859475 = 4289213) B4289213
theorem B3812633 : Blo 2227435 3812633 := bstep (se 2 (by rfl) ⟨1429737, by rfl⟩ : syracuseStep 3812633 = 2859475) B2859475
theorem B40668085 : Blo 2227435 40668085 := bstep (se 5 (by rfl) ⟨1906316, by rfl⟩ : syracuseStep 40668085 = 3812633) B3812633
theorem B54224113 : Blo 2227435 54224113 := bstep (se 2 (by rfl) ⟨20334042, by rfl⟩ : syracuseStep 54224113 = 40668085) B40668085
theorem B72298817 : Blo 2227435 72298817 := bstep (se 2 (by rfl) ⟨27112056, by rfl⟩ : syracuseStep 72298817 = 54224113) B54224113
theorem B48199211 : Blo 2227435 48199211 := bstep (se 1 (by rfl) ⟨36149408, by rfl⟩ : syracuseStep 48199211 = 72298817) B72298817
theorem B32132807 : Blo 2227435 32132807 := bstep (se 1 (by rfl) ⟨24099605, by rfl⟩ : syracuseStep 32132807 = 48199211) B48199211
theorem B21421871 : Blo 2227435 21421871 := bstep (se 1 (by rfl) ⟨16066403, by rfl⟩ : syracuseStep 21421871 = 32132807) B32132807
theorem B14281247 : Blo 2227435 14281247 := bstep (se 1 (by rfl) ⟨10710935, by rfl⟩ : syracuseStep 14281247 = 21421871) B21421871
theorem B9520831 : Blo 2227435 9520831 := bstep (se 1 (by rfl) ⟨7140623, by rfl⟩ : syracuseStep 9520831 = 14281247) B14281247
theorem B12694441 : Blo 2227435 12694441 := bstep (se 2 (by rfl) ⟨4760415, by rfl⟩ : syracuseStep 12694441 = 9520831) B9520831
theorem B16925921 : Blo 2227435 16925921 := bstep (se 2 (by rfl) ⟨6347220, by rfl⟩ : syracuseStep 16925921 = 12694441) B12694441
theorem B11283947 : Blo 2227435 11283947 := bstep (se 1 (by rfl) ⟨8462960, by rfl⟩ : syracuseStep 11283947 = 16925921) B16925921
theorem B7522631 : Blo 2227435 7522631 := bstep (se 1 (by rfl) ⟨5641973, by rfl⟩ : syracuseStep 7522631 = 11283947) B11283947
theorem B5015087 : Blo 2227435 5015087 := bstep (se 1 (by rfl) ⟨3761315, by rfl⟩ : syracuseStep 5015087 = 7522631) B7522631
theorem B3343391 : Blo 2227435 3343391 := bstep (se 1 (by rfl) ⟨2507543, by rfl⟩ : syracuseStep 3343391 = 5015087) B5015087
theorem B2228927 : Blo 2227435 2228927 := bstep (se 1 (by rfl) ⟨1671695, by rfl⟩ : syracuseStep 2228927 = 3343391) B3343391
theorem B3343397 : Blo 2227435 3343397 := bbase (se 4 (by rfl) ⟨313443, by rfl⟩ : syracuseStep 3343397 = 626887) (by norm_num)
theorem B2228931 : Blo 2227435 2228931 := bstep (se 1 (by rfl) ⟨1671698, by rfl⟩ : syracuseStep 2228931 = 3343397) B3343397
theorem B2820997 : Blo 2227435 2820997 := bbase (se 4 (by rfl) ⟨264468, by rfl⟩ : syracuseStep 2820997 = 528937) (by norm_num)
theorem B3761329 : Blo 2227435 3761329 := bstep (se 2 (by rfl) ⟨1410498, by rfl⟩ : syracuseStep 3761329 = 2820997) B2820997
theorem B5015105 : Blo 2227435 5015105 := bstep (se 2 (by rfl) ⟨1880664, by rfl⟩ : syracuseStep 5015105 = 3761329) B3761329
theorem B3343403 : Blo 2227435 3343403 := bstep (se 1 (by rfl) ⟨2507552, by rfl⟩ : syracuseStep 3343403 = 5015105) B5015105
theorem B2228935 : Blo 2227435 2228935 := bstep (se 1 (by rfl) ⟨1671701, by rfl⟩ : syracuseStep 2228935 = 3343403) B3343403
theorem B2507557 : Blo 2227435 2507557 := bbase (se 4 (by rfl) ⟨235083, by rfl⟩ : syracuseStep 2507557 = 470167) (by norm_num)
theorem B3343409 : Blo 2227435 3343409 := bstep (se 2 (by rfl) ⟨1253778, by rfl⟩ : syracuseStep 3343409 = 2507557) B2507557
theorem B2228939 : Blo 2227435 2228939 := bstep (se 1 (by rfl) ⟨1671704, by rfl⟩ : syracuseStep 2228939 = 3343409) B3343409
theorem B9520901 : Blo 2227435 9520901 := bbase (se 4 (by rfl) ⟨892584, by rfl⟩ : syracuseStep 9520901 = 1785169) (by norm_num)
theorem B6347267 : Blo 2227435 6347267 := bstep (se 1 (by rfl) ⟨4760450, by rfl⟩ : syracuseStep 6347267 = 9520901) B9520901
theorem B4231511 : Blo 2227435 4231511 := bstep (se 1 (by rfl) ⟨3173633, by rfl⟩ : syracuseStep 4231511 = 6347267) B6347267
theorem B2821007 : Blo 2227435 2821007 := bstep (se 1 (by rfl) ⟨2115755, by rfl⟩ : syracuseStep 2821007 = 4231511) B4231511
theorem B7522685 : Blo 2227435 7522685 := bstep (se 3 (by rfl) ⟨1410503, by rfl⟩ : syracuseStep 7522685 = 2821007) B2821007
theorem B5015123 : Blo 2227435 5015123 := bstep (se 1 (by rfl) ⟨3761342, by rfl⟩ : syracuseStep 5015123 = 7522685) B7522685
theorem B3343415 : Blo 2227435 3343415 := bstep (se 1 (by rfl) ⟨2507561, by rfl⟩ : syracuseStep 3343415 = 5015123) B5015123
theorem B2228943 : Blo 2227435 2228943 := bstep (se 1 (by rfl) ⟨1671707, by rfl⟩ : syracuseStep 2228943 = 3343415) B3343415
theorem B3343421 : Blo 2227435 3343421 := bbase (se 3 (by rfl) ⟨626891, by rfl⟩ : syracuseStep 3343421 = 1253783) (by norm_num)
theorem B2228947 : Blo 2227435 2228947 := bstep (se 1 (by rfl) ⟨1671710, by rfl⟩ : syracuseStep 2228947 = 3343421) B3343421
theorem B5015141 : Blo 2227435 5015141 := bbase (se 4 (by rfl) ⟨470169, by rfl⟩ : syracuseStep 5015141 = 940339) (by norm_num)
theorem B3343427 : Blo 2227435 3343427 := bstep (se 1 (by rfl) ⟨2507570, by rfl⟩ : syracuseStep 3343427 = 5015141) B5015141
theorem B2228951 : Blo 2227435 2228951 := bstep (se 1 (by rfl) ⟨1671713, by rfl⟩ : syracuseStep 2228951 = 3343427) B3343427
theorem B5642045 : Blo 2227435 5642045 := bbase (se 3 (by rfl) ⟨1057883, by rfl⟩ : syracuseStep 5642045 = 2115767) (by norm_num)
theorem B3761363 : Blo 2227435 3761363 := bstep (se 1 (by rfl) ⟨2821022, by rfl⟩ : syracuseStep 3761363 = 5642045) B5642045
theorem B2507575 : Blo 2227435 2507575 := bstep (se 1 (by rfl) ⟨1880681, by rfl⟩ : syracuseStep 2507575 = 3761363) B3761363
theorem B3343433 : Blo 2227435 3343433 := bstep (se 2 (by rfl) ⟨1253787, by rfl⟩ : syracuseStep 3343433 = 2507575) B2507575
theorem B2228955 : Blo 2227435 2228955 := bstep (se 1 (by rfl) ⟨1671716, by rfl⟩ : syracuseStep 2228955 = 3343433) B3343433
theorem B4231541 : Blo 2227435 4231541 := bbase (se 5 (by rfl) ⟨198353, by rfl⟩ : syracuseStep 4231541 = 396707) (by norm_num)
theorem B11284109 : Blo 2227435 11284109 := bstep (se 3 (by rfl) ⟨2115770, by rfl⟩ : syracuseStep 11284109 = 4231541) B4231541
theorem B7522739 : Blo 2227435 7522739 := bstep (se 1 (by rfl) ⟨5642054, by rfl⟩ : syracuseStep 7522739 = 11284109) B11284109
theorem B5015159 : Blo 2227435 5015159 := bstep (se 1 (by rfl) ⟨3761369, by rfl⟩ : syracuseStep 5015159 = 7522739) B7522739
theorem B3343439 : Blo 2227435 3343439 := bstep (se 1 (by rfl) ⟨2507579, by rfl⟩ : syracuseStep 3343439 = 5015159) B5015159
theorem B2228959 : Blo 2227435 2228959 := bstep (se 1 (by rfl) ⟨1671719, by rfl⟩ : syracuseStep 2228959 = 3343439) B3343439
theorem B3343445 : Blo 2227435 3343445 := bbase (se 8 (by rfl) ⟨19590, by rfl⟩ : syracuseStep 3343445 = 39181) (by norm_num)
theorem B2228963 : Blo 2227435 2228963 := bstep (se 1 (by rfl) ⟨1671722, by rfl⟩ : syracuseStep 2228963 = 3343445) B3343445
theorem B3389069 : Blo 2227435 3389069 := bbase (se 3 (by rfl) ⟨635450, by rfl⟩ : syracuseStep 3389069 = 1270901) (by norm_num)
theorem B2259379 : Blo 2227435 2259379 := bstep (se 1 (by rfl) ⟨1694534, by rfl⟩ : syracuseStep 2259379 = 3389069) B3389069
theorem B12050021 : Blo 2227435 12050021 := bstep (se 4 (by rfl) ⟨1129689, by rfl⟩ : syracuseStep 12050021 = 2259379) B2259379
theorem B8033347 : Blo 2227435 8033347 := bstep (se 1 (by rfl) ⟨6025010, by rfl⟩ : syracuseStep 8033347 = 12050021) B12050021
theorem B10711129 : Blo 2227435 10711129 := bstep (se 2 (by rfl) ⟨4016673, by rfl⟩ : syracuseStep 10711129 = 8033347) B8033347
theorem B14281505 : Blo 2227435 14281505 := bstep (se 2 (by rfl) ⟨5355564, by rfl⟩ : syracuseStep 14281505 = 10711129) B10711129
theorem B9521003 : Blo 2227435 9521003 := bstep (se 1 (by rfl) ⟨7140752, by rfl⟩ : syracuseStep 9521003 = 14281505) B14281505
theorem B6347335 : Blo 2227435 6347335 := bstep (se 1 (by rfl) ⟨4760501, by rfl⟩ : syracuseStep 6347335 = 9521003) B9521003
theorem B8463113 : Blo 2227435 8463113 := bstep (se 2 (by rfl) ⟨3173667, by rfl⟩ : syracuseStep 8463113 = 6347335) B6347335
theorem B5642075 : Blo 2227435 5642075 := bstep (se 1 (by rfl) ⟨4231556, by rfl⟩ : syracuseStep 5642075 = 8463113) B8463113
theorem B3761383 : Blo 2227435 3761383 := bstep (se 1 (by rfl) ⟨2821037, by rfl⟩ : syracuseStep 3761383 = 5642075) B5642075
theorem B5015177 : Blo 2227435 5015177 := bstep (se 2 (by rfl) ⟨1880691, by rfl⟩ : syracuseStep 5015177 = 3761383) B3761383
theorem B3343451 : Blo 2227435 3343451 := bstep (se 1 (by rfl) ⟨2507588, by rfl⟩ : syracuseStep 3343451 = 5015177) B5015177
theorem B2228967 : Blo 2227435 2228967 := bstep (se 1 (by rfl) ⟨1671725, by rfl⟩ : syracuseStep 2228967 = 3343451) B3343451
theorem B2507593 : Blo 2227435 2507593 := bbase (se 2 (by rfl) ⟨940347, by rfl⟩ : syracuseStep 2507593 = 1880695) (by norm_num)
theorem B3343457 : Blo 2227435 3343457 := bstep (se 2 (by rfl) ⟨1253796, by rfl⟩ : syracuseStep 3343457 = 2507593) B2507593
theorem B2228971 : Blo 2227435 2228971 := bstep (se 1 (by rfl) ⟨1671728, by rfl⟩ : syracuseStep 2228971 = 3343457) B3343457
theorem B4825469 : Blo 2227435 4825469 := bbase (se 3 (by rfl) ⟨904775, by rfl⟩ : syracuseStep 4825469 = 1809551) (by norm_num)
theorem B3216979 : Blo 2227435 3216979 := bstep (se 1 (by rfl) ⟨2412734, by rfl⟩ : syracuseStep 3216979 = 4825469) B4825469
theorem B17157221 : Blo 2227435 17157221 := bstep (se 4 (by rfl) ⟨1608489, by rfl⟩ : syracuseStep 17157221 = 3216979) B3216979
theorem B11438147 : Blo 2227435 11438147 := bstep (se 1 (by rfl) ⟨8578610, by rfl⟩ : syracuseStep 11438147 = 17157221) B17157221
theorem B7625431 : Blo 2227435 7625431 := bstep (se 1 (by rfl) ⟨5719073, by rfl⟩ : syracuseStep 7625431 = 11438147) B11438147
theorem B40668965 : Blo 2227435 40668965 := bstep (se 4 (by rfl) ⟨3812715, by rfl⟩ : syracuseStep 40668965 = 7625431) B7625431
theorem B27112643 : Blo 2227435 27112643 := bstep (se 1 (by rfl) ⟨20334482, by rfl⟩ : syracuseStep 27112643 = 40668965) B40668965
theorem B18075095 : Blo 2227435 18075095 := bstep (se 1 (by rfl) ⟨13556321, by rfl⟩ : syracuseStep 18075095 = 27112643) B27112643
theorem B12050063 : Blo 2227435 12050063 := bstep (se 1 (by rfl) ⟨9037547, by rfl⟩ : syracuseStep 12050063 = 18075095) B18075095
theorem B8033375 : Blo 2227435 8033375 := bstep (se 1 (by rfl) ⟨6025031, by rfl⟩ : syracuseStep 8033375 = 12050063) B12050063
theorem B21422333 : Blo 2227435 21422333 := bstep (se 3 (by rfl) ⟨4016687, by rfl⟩ : syracuseStep 21422333 = 8033375) B8033375
theorem B14281555 : Blo 2227435 14281555 := bstep (se 1 (by rfl) ⟨10711166, by rfl⟩ : syracuseStep 14281555 = 21422333) B21422333
theorem B19042073 : Blo 2227435 19042073 := bstep (se 2 (by rfl) ⟨7140777, by rfl⟩ : syracuseStep 19042073 = 14281555) B14281555
theorem B12694715 : Blo 2227435 12694715 := bstep (se 1 (by rfl) ⟨9521036, by rfl⟩ : syracuseStep 12694715 = 19042073) B19042073
theorem B8463143 : Blo 2227435 8463143 := bstep (se 1 (by rfl) ⟨6347357, by rfl⟩ : syracuseStep 8463143 = 12694715) B12694715
theorem B5642095 : Blo 2227435 5642095 := bstep (se 1 (by rfl) ⟨4231571, by rfl⟩ : syracuseStep 5642095 = 8463143) B8463143
theorem B7522793 : Blo 2227435 7522793 := bstep (se 2 (by rfl) ⟨2821047, by rfl⟩ : syracuseStep 7522793 = 5642095) B5642095
theorem B5015195 : Blo 2227435 5015195 := bstep (se 1 (by rfl) ⟨3761396, by rfl⟩ : syracuseStep 5015195 = 7522793) B7522793
theorem B3343463 : Blo 2227435 3343463 := bstep (se 1 (by rfl) ⟨2507597, by rfl⟩ : syracuseStep 3343463 = 5015195) B5015195
theorem B2228975 : Blo 2227435 2228975 := bstep (se 1 (by rfl) ⟨1671731, by rfl⟩ : syracuseStep 2228975 = 3343463) B3343463
theorem B3343469 : Blo 2227435 3343469 := bbase (se 3 (by rfl) ⟨626900, by rfl⟩ : syracuseStep 3343469 = 1253801) (by norm_num)
theorem B2228979 : Blo 2227435 2228979 := bstep (se 1 (by rfl) ⟨1671734, by rfl⟩ : syracuseStep 2228979 = 3343469) B3343469
theorem B5015213 : Blo 2227435 5015213 := bbase (se 3 (by rfl) ⟨940352, by rfl⟩ : syracuseStep 5015213 = 1880705) (by norm_num)
theorem B3343475 : Blo 2227435 3343475 := bstep (se 1 (by rfl) ⟨2507606, by rfl⟩ : syracuseStep 3343475 = 5015213) B5015213
theorem B2228983 : Blo 2227435 2228983 := bstep (se 1 (by rfl) ⟨1671737, by rfl⟩ : syracuseStep 2228983 = 3343475) B3343475
theorem B7625477 : Blo 2227435 7625477 := bbase (se 4 (by rfl) ⟨714888, by rfl⟩ : syracuseStep 7625477 = 1429777) (by norm_num)
theorem B5083651 : Blo 2227435 5083651 := bstep (se 1 (by rfl) ⟨3812738, by rfl⟩ : syracuseStep 5083651 = 7625477) B7625477
theorem B6778201 : Blo 2227435 6778201 := bstep (se 2 (by rfl) ⟨2541825, by rfl⟩ : syracuseStep 6778201 = 5083651) B5083651
theorem B9037601 : Blo 2227435 9037601 := bstep (se 2 (by rfl) ⟨3389100, by rfl⟩ : syracuseStep 9037601 = 6778201) B6778201
theorem B6025067 : Blo 2227435 6025067 := bstep (se 1 (by rfl) ⟨4518800, by rfl⟩ : syracuseStep 6025067 = 9037601) B9037601
theorem B4016711 : Blo 2227435 4016711 := bstep (se 1 (by rfl) ⟨3012533, by rfl⟩ : syracuseStep 4016711 = 6025067) B6025067
theorem B2677807 : Blo 2227435 2677807 := bstep (se 1 (by rfl) ⟨2008355, by rfl⟩ : syracuseStep 2677807 = 4016711) B4016711
theorem B3570409 : Blo 2227435 3570409 := bstep (se 2 (by rfl) ⟨1338903, by rfl⟩ : syracuseStep 3570409 = 2677807) B2677807
theorem B4760545 : Blo 2227435 4760545 := bstep (se 2 (by rfl) ⟨1785204, by rfl⟩ : syracuseStep 4760545 = 3570409) B3570409
theorem B6347393 : Blo 2227435 6347393 := bstep (se 2 (by rfl) ⟨2380272, by rfl⟩ : syracuseStep 6347393 = 4760545) B4760545
theorem B4231595 : Blo 2227435 4231595 := bstep (se 1 (by rfl) ⟨3173696, by rfl⟩ : syracuseStep 4231595 = 6347393) B6347393
theorem B2821063 : Blo 2227435 2821063 := bstep (se 1 (by rfl) ⟨2115797, by rfl⟩ : syracuseStep 2821063 = 4231595) B4231595
theorem B3761417 : Blo 2227435 3761417 := bstep (se 2 (by rfl) ⟨1410531, by rfl⟩ : syracuseStep 3761417 = 2821063) B2821063
theorem B2507611 : Blo 2227435 2507611 := bstep (se 1 (by rfl) ⟨1880708, by rfl⟩ : syracuseStep 2507611 = 3761417) B3761417
theorem B3343481 : Blo 2227435 3343481 := bstep (se 2 (by rfl) ⟨1253805, by rfl⟩ : syracuseStep 3343481 = 2507611) B2507611
theorem B2228987 : Blo 2227435 2228987 := bstep (se 1 (by rfl) ⟨1671740, by rfl⟩ : syracuseStep 2228987 = 3343481) B3343481
theorem B21422485 : Blo 2227435 21422485 := bbase (se 6 (by rfl) ⟨502089, by rfl⟩ : syracuseStep 21422485 = 1004179) (by norm_num)
theorem B28563313 : Blo 2227435 28563313 := bstep (se 2 (by rfl) ⟨10711242, by rfl⟩ : syracuseStep 28563313 = 21422485) B21422485
theorem B38084417 : Blo 2227435 38084417 := bstep (se 2 (by rfl) ⟨14281656, by rfl⟩ : syracuseStep 38084417 = 28563313) B28563313
theorem B25389611 : Blo 2227435 25389611 := bstep (se 1 (by rfl) ⟨19042208, by rfl⟩ : syracuseStep 25389611 = 38084417) B38084417
theorem B16926407 : Blo 2227435 16926407 := bstep (se 1 (by rfl) ⟨12694805, by rfl⟩ : syracuseStep 16926407 = 25389611) B25389611
theorem B11284271 : Blo 2227435 11284271 := bstep (se 1 (by rfl) ⟨8463203, by rfl⟩ : syracuseStep 11284271 = 16926407) B16926407
theorem B7522847 : Blo 2227435 7522847 := bstep (se 1 (by rfl) ⟨5642135, by rfl⟩ : syracuseStep 7522847 = 11284271) B11284271
theorem B5015231 : Blo 2227435 5015231 := bstep (se 1 (by rfl) ⟨3761423, by rfl⟩ : syracuseStep 5015231 = 7522847) B7522847
theorem B3343487 : Blo 2227435 3343487 := bstep (se 1 (by rfl) ⟨2507615, by rfl⟩ : syracuseStep 3343487 = 5015231) B5015231
theorem B2228991 : Blo 2227435 2228991 := bstep (se 1 (by rfl) ⟨1671743, by rfl⟩ : syracuseStep 2228991 = 3343487) B3343487
theorem B3343493 : Blo 2227435 3343493 := bbase (se 4 (by rfl) ⟨313452, by rfl⟩ : syracuseStep 3343493 = 626905) (by norm_num)
theorem B2228995 : Blo 2227435 2228995 := bstep (se 1 (by rfl) ⟨1671746, by rfl⟩ : syracuseStep 2228995 = 3343493) B3343493
theorem B3761437 : Blo 2227435 3761437 := bbase (se 3 (by rfl) ⟨705269, by rfl⟩ : syracuseStep 3761437 = 1410539) (by norm_num)
theorem B5015249 : Blo 2227435 5015249 := bstep (se 2 (by rfl) ⟨1880718, by rfl⟩ : syracuseStep 5015249 = 3761437) B3761437
theorem B3343499 : Blo 2227435 3343499 := bstep (se 1 (by rfl) ⟨2507624, by rfl⟩ : syracuseStep 3343499 = 5015249) B5015249
theorem B2228999 : Blo 2227435 2228999 := bstep (se 1 (by rfl) ⟨1671749, by rfl⟩ : syracuseStep 2228999 = 3343499) B3343499
theorem B2507629 : Blo 2227435 2507629 := bbase (se 3 (by rfl) ⟨470180, by rfl⟩ : syracuseStep 2507629 = 940361) (by norm_num)
theorem B3343505 : Blo 2227435 3343505 := bstep (se 2 (by rfl) ⟨1253814, by rfl⟩ : syracuseStep 3343505 = 2507629) B2507629
theorem B2229003 : Blo 2227435 2229003 := bstep (se 1 (by rfl) ⟨1671752, by rfl⟩ : syracuseStep 2229003 = 3343505) B3343505
theorem B7522901 : Blo 2227435 7522901 := bbase (se 8 (by rfl) ⟨44079, by rfl⟩ : syracuseStep 7522901 = 88159) (by norm_num)
theorem B5015267 : Blo 2227435 5015267 := bstep (se 1 (by rfl) ⟨3761450, by rfl⟩ : syracuseStep 5015267 = 7522901) B7522901
theorem B3343511 : Blo 2227435 3343511 := bstep (se 1 (by rfl) ⟨2507633, by rfl⟩ : syracuseStep 3343511 = 5015267) B5015267
theorem B2229007 : Blo 2227435 2229007 := bstep (se 1 (by rfl) ⟨1671755, by rfl⟩ : syracuseStep 2229007 = 3343511) B3343511
theorem B3343517 : Blo 2227435 3343517 := bbase (se 3 (by rfl) ⟨626909, by rfl⟩ : syracuseStep 3343517 = 1253819) (by norm_num)
theorem B2229011 : Blo 2227435 2229011 := bstep (se 1 (by rfl) ⟨1671758, by rfl⟩ : syracuseStep 2229011 = 3343517) B3343517
theorem B5015285 : Blo 2227435 5015285 := bbase (se 5 (by rfl) ⟨235091, by rfl⟩ : syracuseStep 5015285 = 470183) (by norm_num)
theorem B3343523 : Blo 2227435 3343523 := bstep (se 1 (by rfl) ⟨2507642, by rfl⟩ : syracuseStep 3343523 = 5015285) B5015285
theorem B2229015 : Blo 2227435 2229015 := bstep (se 1 (by rfl) ⟨1671761, by rfl⟩ : syracuseStep 2229015 = 3343523) B3343523
theorem B14476693 : Blo 2227435 14476693 := bbase (se 6 (by rfl) ⟨339297, by rfl⟩ : syracuseStep 14476693 = 678595) (by norm_num)
theorem B19302257 : Blo 2227435 19302257 := bstep (se 2 (by rfl) ⟨7238346, by rfl⟩ : syracuseStep 19302257 = 14476693) B14476693
theorem B51472685 : Blo 2227435 51472685 := bstep (se 3 (by rfl) ⟨9651128, by rfl⟩ : syracuseStep 51472685 = 19302257) B19302257
theorem B34315123 : Blo 2227435 34315123 := bstep (se 1 (by rfl) ⟨25736342, by rfl⟩ : syracuseStep 34315123 = 51472685) B51472685
theorem B45753497 : Blo 2227435 45753497 := bstep (se 2 (by rfl) ⟨17157561, by rfl⟩ : syracuseStep 45753497 = 34315123) B34315123
theorem B30502331 : Blo 2227435 30502331 := bstep (se 1 (by rfl) ⟨22876748, by rfl⟩ : syracuseStep 30502331 = 45753497) B45753497
theorem B20334887 : Blo 2227435 20334887 := bstep (se 1 (by rfl) ⟨15251165, by rfl⟩ : syracuseStep 20334887 = 30502331) B30502331
theorem B13556591 : Blo 2227435 13556591 := bstep (se 1 (by rfl) ⟨10167443, by rfl⟩ : syracuseStep 13556591 = 20334887) B20334887
theorem B9037727 : Blo 2227435 9037727 := bstep (se 1 (by rfl) ⟨6778295, by rfl⟩ : syracuseStep 9037727 = 13556591) B13556591
theorem B6025151 : Blo 2227435 6025151 := bstep (se 1 (by rfl) ⟨4518863, by rfl⟩ : syracuseStep 6025151 = 9037727) B9037727
theorem B16067069 : Blo 2227435 16067069 := bstep (se 3 (by rfl) ⟨3012575, by rfl⟩ : syracuseStep 16067069 = 6025151) B6025151
theorem B10711379 : Blo 2227435 10711379 := bstep (se 1 (by rfl) ⟨8033534, by rfl⟩ : syracuseStep 10711379 = 16067069) B16067069
theorem B28563677 : Blo 2227435 28563677 := bstep (se 3 (by rfl) ⟨5355689, by rfl⟩ : syracuseStep 28563677 = 10711379) B10711379
theorem B19042451 : Blo 2227435 19042451 := bstep (se 1 (by rfl) ⟨14281838, by rfl⟩ : syracuseStep 19042451 = 28563677) B28563677
theorem B12694967 : Blo 2227435 12694967 := bstep (se 1 (by rfl) ⟨9521225, by rfl⟩ : syracuseStep 12694967 = 19042451) B19042451
theorem B8463311 : Blo 2227435 8463311 := bstep (se 1 (by rfl) ⟨6347483, by rfl⟩ : syracuseStep 8463311 = 12694967) B12694967
theorem B5642207 : Blo 2227435 5642207 := bstep (se 1 (by rfl) ⟨4231655, by rfl⟩ : syracuseStep 5642207 = 8463311) B8463311
theorem B3761471 : Blo 2227435 3761471 := bstep (se 1 (by rfl) ⟨2821103, by rfl⟩ : syracuseStep 3761471 = 5642207) B5642207
theorem B2507647 : Blo 2227435 2507647 := bstep (se 1 (by rfl) ⟨1880735, by rfl⟩ : syracuseStep 2507647 = 3761471) B3761471
theorem B3343529 : Blo 2227435 3343529 := bstep (se 2 (by rfl) ⟨1253823, by rfl⟩ : syracuseStep 3343529 = 2507647) B2507647
theorem B2229019 : Blo 2227435 2229019 := bstep (se 1 (by rfl) ⟨1671764, by rfl⟩ : syracuseStep 2229019 = 3343529) B3343529
theorem B4760621 : Blo 2227435 4760621 := bbase (se 3 (by rfl) ⟨892616, by rfl⟩ : syracuseStep 4760621 = 1785233) (by norm_num)
theorem B3173747 : Blo 2227435 3173747 := bstep (se 1 (by rfl) ⟨2380310, by rfl⟩ : syracuseStep 3173747 = 4760621) B4760621
theorem B8463325 : Blo 2227435 8463325 := bstep (se 3 (by rfl) ⟨1586873, by rfl⟩ : syracuseStep 8463325 = 3173747) B3173747
theorem B11284433 : Blo 2227435 11284433 := bstep (se 2 (by rfl) ⟨4231662, by rfl⟩ : syracuseStep 11284433 = 8463325) B8463325
theorem B7522955 : Blo 2227435 7522955 := bstep (se 1 (by rfl) ⟨5642216, by rfl⟩ : syracuseStep 7522955 = 11284433) B11284433
theorem B5015303 : Blo 2227435 5015303 := bstep (se 1 (by rfl) ⟨3761477, by rfl⟩ : syracuseStep 5015303 = 7522955) B7522955
theorem B3343535 : Blo 2227435 3343535 := bstep (se 1 (by rfl) ⟨2507651, by rfl⟩ : syracuseStep 3343535 = 5015303) B5015303
theorem B2229023 : Blo 2227435 2229023 := bstep (se 1 (by rfl) ⟨1671767, by rfl⟩ : syracuseStep 2229023 = 3343535) B3343535
theorem B3343541 : Blo 2227435 3343541 := bbase (se 5 (by rfl) ⟨156728, by rfl⟩ : syracuseStep 3343541 = 313457) (by norm_num)
theorem B2229027 : Blo 2227435 2229027 := bstep (se 1 (by rfl) ⟨1671770, by rfl⟩ : syracuseStep 2229027 = 3343541) B3343541
theorem B5642237 : Blo 2227435 5642237 := bbase (se 3 (by rfl) ⟨1057919, by rfl⟩ : syracuseStep 5642237 = 2115839) (by norm_num)
theorem B3761491 : Blo 2227435 3761491 := bstep (se 1 (by rfl) ⟨2821118, by rfl⟩ : syracuseStep 3761491 = 5642237) B5642237
theorem B5015321 : Blo 2227435 5015321 := bstep (se 2 (by rfl) ⟨1880745, by rfl⟩ : syracuseStep 5015321 = 3761491) B3761491
theorem B3343547 : Blo 2227435 3343547 := bstep (se 1 (by rfl) ⟨2507660, by rfl⟩ : syracuseStep 3343547 = 5015321) B5015321
theorem B2229031 : Blo 2227435 2229031 := bstep (se 1 (by rfl) ⟨1671773, by rfl⟩ : syracuseStep 2229031 = 3343547) B3343547
theorem B2507665 : Blo 2227435 2507665 := bbase (se 2 (by rfl) ⟨940374, by rfl⟩ : syracuseStep 2507665 = 1880749) (by norm_num)
theorem B3343553 : Blo 2227435 3343553 := bstep (se 2 (by rfl) ⟨1253832, by rfl⟩ : syracuseStep 3343553 = 2507665) B2507665
theorem B2229035 : Blo 2227435 2229035 := bstep (se 1 (by rfl) ⟨1671776, by rfl⟩ : syracuseStep 2229035 = 3343553) B3343553
theorem B4231693 : Blo 2227435 4231693 := bbase (se 3 (by rfl) ⟨793442, by rfl⟩ : syracuseStep 4231693 = 1586885) (by norm_num)
theorem B5642257 : Blo 2227435 5642257 := bstep (se 2 (by rfl) ⟨2115846, by rfl⟩ : syracuseStep 5642257 = 4231693) B4231693
theorem B7523009 : Blo 2227435 7523009 := bstep (se 2 (by rfl) ⟨2821128, by rfl⟩ : syracuseStep 7523009 = 5642257) B5642257
theorem B5015339 : Blo 2227435 5015339 := bstep (se 1 (by rfl) ⟨3761504, by rfl⟩ : syracuseStep 5015339 = 7523009) B7523009
theorem B3343559 : Blo 2227435 3343559 := bstep (se 1 (by rfl) ⟨2507669, by rfl⟩ : syracuseStep 3343559 = 5015339) B5015339
theorem B2229039 : Blo 2227435 2229039 := bstep (se 1 (by rfl) ⟨1671779, by rfl⟩ : syracuseStep 2229039 = 3343559) B3343559
theorem B3343565 : Blo 2227435 3343565 := bbase (se 3 (by rfl) ⟨626918, by rfl⟩ : syracuseStep 3343565 = 1253837) (by norm_num)
theorem B2229043 : Blo 2227435 2229043 := bstep (se 1 (by rfl) ⟨1671782, by rfl⟩ : syracuseStep 2229043 = 3343565) B3343565
theorem B5015357 : Blo 2227435 5015357 := bbase (se 3 (by rfl) ⟨940379, by rfl⟩ : syracuseStep 5015357 = 1880759) (by norm_num)
theorem B3343571 : Blo 2227435 3343571 := bstep (se 1 (by rfl) ⟨2507678, by rfl⟩ : syracuseStep 3343571 = 5015357) B5015357
theorem B2229047 : Blo 2227435 2229047 := bstep (se 1 (by rfl) ⟨1671785, by rfl⟩ : syracuseStep 2229047 = 3343571) B3343571
theorem B3761525 : Blo 2227435 3761525 := bbase (se 5 (by rfl) ⟨176321, by rfl⟩ : syracuseStep 3761525 = 352643) (by norm_num)
theorem B2507683 : Blo 2227435 2507683 := bstep (se 1 (by rfl) ⟨1880762, by rfl⟩ : syracuseStep 2507683 = 3761525) B3761525
theorem B3343577 : Blo 2227435 3343577 := bstep (se 2 (by rfl) ⟨1253841, by rfl⟩ : syracuseStep 3343577 = 2507683) B2507683
theorem B2229051 : Blo 2227435 2229051 := bstep (se 1 (by rfl) ⟨1671788, by rfl⟩ : syracuseStep 2229051 = 3343577) B3343577
theorem B3570517 : Blo 2227435 3570517 := bbase (se 9 (by rfl) ⟨10460, by rfl⟩ : syracuseStep 3570517 = 20921) (by norm_num)
theorem B4760689 : Blo 2227435 4760689 := bstep (se 2 (by rfl) ⟨1785258, by rfl⟩ : syracuseStep 4760689 = 3570517) B3570517
theorem B6347585 : Blo 2227435 6347585 := bstep (se 2 (by rfl) ⟨2380344, by rfl⟩ : syracuseStep 6347585 = 4760689) B4760689
theorem B16926893 : Blo 2227435 16926893 := bstep (se 3 (by rfl) ⟨3173792, by rfl⟩ : syracuseStep 16926893 = 6347585) B6347585
theorem B11284595 : Blo 2227435 11284595 := bstep (se 1 (by rfl) ⟨8463446, by rfl⟩ : syracuseStep 11284595 = 16926893) B16926893
theorem B7523063 : Blo 2227435 7523063 := bstep (se 1 (by rfl) ⟨5642297, by rfl⟩ : syracuseStep 7523063 = 11284595) B11284595
theorem B5015375 : Blo 2227435 5015375 := bstep (se 1 (by rfl) ⟨3761531, by rfl⟩ : syracuseStep 5015375 = 7523063) B7523063
theorem B3343583 : Blo 2227435 3343583 := bstep (se 1 (by rfl) ⟨2507687, by rfl⟩ : syracuseStep 3343583 = 5015375) B5015375
theorem B2229055 : Blo 2227435 2229055 := bstep (se 1 (by rfl) ⟨1671791, by rfl⟩ : syracuseStep 2229055 = 3343583) B3343583
theorem B3343589 : Blo 2227435 3343589 := bbase (se 4 (by rfl) ⟨313461, by rfl⟩ : syracuseStep 3343589 = 626923) (by norm_num)
theorem B2229059 : Blo 2227435 2229059 := bstep (se 1 (by rfl) ⟨1671794, by rfl⟩ : syracuseStep 2229059 = 3343589) B3343589
theorem B7141061 : Blo 2227435 7141061 := bbase (se 4 (by rfl) ⟨669474, by rfl⟩ : syracuseStep 7141061 = 1338949) (by norm_num)
theorem B4760707 : Blo 2227435 4760707 := bstep (se 1 (by rfl) ⟨3570530, by rfl⟩ : syracuseStep 4760707 = 7141061) B7141061
theorem B6347609 : Blo 2227435 6347609 := bstep (se 2 (by rfl) ⟨2380353, by rfl⟩ : syracuseStep 6347609 = 4760707) B4760707
theorem B4231739 : Blo 2227435 4231739 := bstep (se 1 (by rfl) ⟨3173804, by rfl⟩ : syracuseStep 4231739 = 6347609) B6347609
theorem B2821159 : Blo 2227435 2821159 := bstep (se 1 (by rfl) ⟨2115869, by rfl⟩ : syracuseStep 2821159 = 4231739) B4231739
theorem B3761545 : Blo 2227435 3761545 := bstep (se 2 (by rfl) ⟨1410579, by rfl⟩ : syracuseStep 3761545 = 2821159) B2821159
theorem B5015393 : Blo 2227435 5015393 := bstep (se 2 (by rfl) ⟨1880772, by rfl⟩ : syracuseStep 5015393 = 3761545) B3761545
theorem B3343595 : Blo 2227435 3343595 := bstep (se 1 (by rfl) ⟨2507696, by rfl⟩ : syracuseStep 3343595 = 5015393) B5015393
theorem B2229063 : Blo 2227435 2229063 := bstep (se 1 (by rfl) ⟨1671797, by rfl⟩ : syracuseStep 2229063 = 3343595) B3343595
theorem B2507701 : Blo 2227435 2507701 := bbase (se 5 (by rfl) ⟨117548, by rfl⟩ : syracuseStep 2507701 = 235097) (by norm_num)
theorem B3343601 : Blo 2227435 3343601 := bstep (se 2 (by rfl) ⟨1253850, by rfl⟩ : syracuseStep 3343601 = 2507701) B2507701
theorem B2229067 : Blo 2227435 2229067 := bstep (se 1 (by rfl) ⟨1671800, by rfl⟩ : syracuseStep 2229067 = 3343601) B3343601
theorem B2821169 : Blo 2227435 2821169 := bbase (se 2 (by rfl) ⟨1057938, by rfl⟩ : syracuseStep 2821169 = 2115877) (by norm_num)
theorem B7523117 : Blo 2227435 7523117 := bstep (se 3 (by rfl) ⟨1410584, by rfl⟩ : syracuseStep 7523117 = 2821169) B2821169
theorem B5015411 : Blo 2227435 5015411 := bstep (se 1 (by rfl) ⟨3761558, by rfl⟩ : syracuseStep 5015411 = 7523117) B7523117
theorem B3343607 : Blo 2227435 3343607 := bstep (se 1 (by rfl) ⟨2507705, by rfl⟩ : syracuseStep 3343607 = 5015411) B5015411
theorem B2229071 : Blo 2227435 2229071 := bstep (se 1 (by rfl) ⟨1671803, by rfl⟩ : syracuseStep 2229071 = 3343607) B3343607
theorem B3343613 : Blo 2227435 3343613 := bbase (se 3 (by rfl) ⟨626927, by rfl⟩ : syracuseStep 3343613 = 1253855) (by norm_num)
theorem B2229075 : Blo 2227435 2229075 := bstep (se 1 (by rfl) ⟨1671806, by rfl⟩ : syracuseStep 2229075 = 3343613) B3343613
theorem B5015429 : Blo 2227435 5015429 := bbase (se 4 (by rfl) ⟨470196, by rfl⟩ : syracuseStep 5015429 = 940393) (by norm_num)
theorem B3343619 : Blo 2227435 3343619 := bstep (se 1 (by rfl) ⟨2507714, by rfl⟩ : syracuseStep 3343619 = 5015429) B5015429
theorem B2229079 : Blo 2227435 2229079 := bstep (se 1 (by rfl) ⟨1671809, by rfl⟩ : syracuseStep 2229079 = 3343619) B3343619
theorem B5355845 : Blo 2227435 5355845 := bbase (se 4 (by rfl) ⟨502110, by rfl⟩ : syracuseStep 5355845 = 1004221) (by norm_num)
theorem B3570563 : Blo 2227435 3570563 := bstep (se 1 (by rfl) ⟨2677922, by rfl⟩ : syracuseStep 3570563 = 5355845) B5355845
theorem B2380375 : Blo 2227435 2380375 := bstep (se 1 (by rfl) ⟨1785281, by rfl⟩ : syracuseStep 2380375 = 3570563) B3570563
theorem B3173833 : Blo 2227435 3173833 := bstep (se 2 (by rfl) ⟨1190187, by rfl⟩ : syracuseStep 3173833 = 2380375) B2380375
theorem B4231777 : Blo 2227435 4231777 := bstep (se 2 (by rfl) ⟨1586916, by rfl⟩ : syracuseStep 4231777 = 3173833) B3173833
theorem B5642369 : Blo 2227435 5642369 := bstep (se 2 (by rfl) ⟨2115888, by rfl⟩ : syracuseStep 5642369 = 4231777) B4231777
theorem B3761579 : Blo 2227435 3761579 := bstep (se 1 (by rfl) ⟨2821184, by rfl⟩ : syracuseStep 3761579 = 5642369) B5642369
theorem B2507719 : Blo 2227435 2507719 := bstep (se 1 (by rfl) ⟨1880789, by rfl⟩ : syracuseStep 2507719 = 3761579) B3761579
theorem B3343625 : Blo 2227435 3343625 := bstep (se 2 (by rfl) ⟨1253859, by rfl⟩ : syracuseStep 3343625 = 2507719) B2507719
theorem B2229083 : Blo 2227435 2229083 := bstep (se 1 (by rfl) ⟨1671812, by rfl⟩ : syracuseStep 2229083 = 3343625) B3343625
theorem B11284757 : Blo 2227435 11284757 := bbase (se 6 (by rfl) ⟨264486, by rfl⟩ : syracuseStep 11284757 = 528973) (by norm_num)
theorem B7523171 : Blo 2227435 7523171 := bstep (se 1 (by rfl) ⟨5642378, by rfl⟩ : syracuseStep 7523171 = 11284757) B11284757
theorem B5015447 : Blo 2227435 5015447 := bstep (se 1 (by rfl) ⟨3761585, by rfl⟩ : syracuseStep 5015447 = 7523171) B7523171
theorem B3343631 : Blo 2227435 3343631 := bstep (se 1 (by rfl) ⟨2507723, by rfl⟩ : syracuseStep 3343631 = 5015447) B5015447
theorem B2229087 : Blo 2227435 2229087 := bstep (se 1 (by rfl) ⟨1671815, by rfl⟩ : syracuseStep 2229087 = 3343631) B3343631
theorem B3343637 : Blo 2227435 3343637 := bbase (se 6 (by rfl) ⟨78366, by rfl⟩ : syracuseStep 3343637 = 156733) (by norm_num)
theorem B2229091 : Blo 2227435 2229091 := bstep (se 1 (by rfl) ⟨1671818, by rfl⟩ : syracuseStep 2229091 = 3343637) B3343637
theorem B23506037 : Blo 2227435 23506037 := bbase (se 5 (by rfl) ⟨1101845, by rfl⟩ : syracuseStep 23506037 = 2203691) (by norm_num)
theorem B15670691 : Blo 2227435 15670691 := bstep (se 1 (by rfl) ⟨11753018, by rfl⟩ : syracuseStep 15670691 = 23506037) B23506037
theorem B10447127 : Blo 2227435 10447127 := bstep (se 1 (by rfl) ⟨7835345, by rfl⟩ : syracuseStep 10447127 = 15670691) B15670691
theorem B6964751 : Blo 2227435 6964751 := bstep (se 1 (by rfl) ⟨5223563, by rfl⟩ : syracuseStep 6964751 = 10447127) B10447127
theorem B4643167 : Blo 2227435 4643167 := bstep (se 1 (by rfl) ⟨3482375, by rfl⟩ : syracuseStep 4643167 = 6964751) B6964751
theorem B6190889 : Blo 2227435 6190889 := bstep (se 2 (by rfl) ⟨2321583, by rfl⟩ : syracuseStep 6190889 = 4643167) B4643167
theorem B16509037 : Blo 2227435 16509037 := bstep (se 3 (by rfl) ⟨3095444, by rfl⟩ : syracuseStep 16509037 = 6190889) B6190889
theorem B352192789 : Blo 2227435 352192789 := bstep (se 6 (by rfl) ⟨8254518, by rfl⟩ : syracuseStep 352192789 = 16509037) B16509037
theorem B469590385 : Blo 2227435 469590385 := bstep (se 2 (by rfl) ⟨176096394, by rfl⟩ : syracuseStep 469590385 = 352192789) B352192789
theorem B626120513 : Blo 2227435 626120513 := bstep (se 2 (by rfl) ⟨234795192, by rfl⟩ : syracuseStep 626120513 = 469590385) B469590385
theorem B417413675 : Blo 2227435 417413675 := bstep (se 1 (by rfl) ⟨313060256, by rfl⟩ : syracuseStep 417413675 = 626120513) B626120513
theorem B278275783 : Blo 2227435 278275783 := bstep (se 1 (by rfl) ⟨208706837, by rfl⟩ : syracuseStep 278275783 = 417413675) B417413675
theorem B371034377 : Blo 2227435 371034377 := bstep (se 2 (by rfl) ⟨139137891, by rfl⟩ : syracuseStep 371034377 = 278275783) B278275783
theorem B247356251 : Blo 2227435 247356251 := bstep (se 1 (by rfl) ⟨185517188, by rfl⟩ : syracuseStep 247356251 = 371034377) B371034377
theorem B164904167 : Blo 2227435 164904167 := bstep (se 1 (by rfl) ⟨123678125, by rfl⟩ : syracuseStep 164904167 = 247356251) B247356251
theorem B109936111 : Blo 2227435 109936111 := bstep (se 1 (by rfl) ⟨82452083, by rfl⟩ : syracuseStep 109936111 = 164904167) B164904167
theorem B146581481 : Blo 2227435 146581481 := bstep (se 2 (by rfl) ⟨54968055, by rfl⟩ : syracuseStep 146581481 = 109936111) B109936111
theorem B97720987 : Blo 2227435 97720987 := bstep (se 1 (by rfl) ⟨73290740, by rfl⟩ : syracuseStep 97720987 = 146581481) B146581481
theorem B130294649 : Blo 2227435 130294649 := bstep (se 2 (by rfl) ⟨48860493, by rfl⟩ : syracuseStep 130294649 = 97720987) B97720987
theorem B86863099 : Blo 2227435 86863099 := bstep (se 1 (by rfl) ⟨65147324, by rfl⟩ : syracuseStep 86863099 = 130294649) B130294649
theorem B115817465 : Blo 2227435 115817465 := bstep (se 2 (by rfl) ⟨43431549, by rfl⟩ : syracuseStep 115817465 = 86863099) B86863099
theorem B77211643 : Blo 2227435 77211643 := bstep (se 1 (by rfl) ⟨57908732, by rfl⟩ : syracuseStep 77211643 = 115817465) B115817465
theorem B102948857 : Blo 2227435 102948857 := bstep (se 2 (by rfl) ⟨38605821, by rfl⟩ : syracuseStep 102948857 = 77211643) B77211643
theorem B68632571 : Blo 2227435 68632571 := bstep (se 1 (by rfl) ⟨51474428, by rfl⟩ : syracuseStep 68632571 = 102948857) B102948857
theorem B45755047 : Blo 2227435 45755047 := bstep (se 1 (by rfl) ⟨34316285, by rfl⟩ : syracuseStep 45755047 = 68632571) B68632571
theorem B244026917 : Blo 2227435 244026917 := bstep (se 4 (by rfl) ⟨22877523, by rfl⟩ : syracuseStep 244026917 = 45755047) B45755047
theorem B162684611 : Blo 2227435 162684611 := bstep (se 1 (by rfl) ⟨122013458, by rfl⟩ : syracuseStep 162684611 = 244026917) B244026917
theorem B108456407 : Blo 2227435 108456407 := bstep (se 1 (by rfl) ⟨81342305, by rfl⟩ : syracuseStep 108456407 = 162684611) B162684611
theorem B72304271 : Blo 2227435 72304271 := bstep (se 1 (by rfl) ⟨54228203, by rfl⟩ : syracuseStep 72304271 = 108456407) B108456407
theorem B48202847 : Blo 2227435 48202847 := bstep (se 1 (by rfl) ⟨36152135, by rfl⟩ : syracuseStep 48202847 = 72304271) B72304271
theorem B32135231 : Blo 2227435 32135231 := bstep (se 1 (by rfl) ⟨24101423, by rfl⟩ : syracuseStep 32135231 = 48202847) B48202847
theorem B21423487 : Blo 2227435 21423487 := bstep (se 1 (by rfl) ⟨16067615, by rfl⟩ : syracuseStep 21423487 = 32135231) B32135231
theorem B28564649 : Blo 2227435 28564649 := bstep (se 2 (by rfl) ⟨10711743, by rfl⟩ : syracuseStep 28564649 = 21423487) B21423487
theorem B19043099 : Blo 2227435 19043099 := bstep (se 1 (by rfl) ⟨14282324, by rfl⟩ : syracuseStep 19043099 = 28564649) B28564649
theorem B12695399 : Blo 2227435 12695399 := bstep (se 1 (by rfl) ⟨9521549, by rfl⟩ : syracuseStep 12695399 = 19043099) B19043099
theorem B8463599 : Blo 2227435 8463599 := bstep (se 1 (by rfl) ⟨6347699, by rfl⟩ : syracuseStep 8463599 = 12695399) B12695399
theorem B5642399 : Blo 2227435 5642399 := bstep (se 1 (by rfl) ⟨4231799, by rfl⟩ : syracuseStep 5642399 = 8463599) B8463599
theorem B3761599 : Blo 2227435 3761599 := bstep (se 1 (by rfl) ⟨2821199, by rfl⟩ : syracuseStep 3761599 = 5642399) B5642399
theorem B5015465 : Blo 2227435 5015465 := bstep (se 2 (by rfl) ⟨1880799, by rfl⟩ : syracuseStep 5015465 = 3761599) B3761599
theorem B3343643 : Blo 2227435 3343643 := bstep (se 1 (by rfl) ⟨2507732, by rfl⟩ : syracuseStep 3343643 = 5015465) B5015465
theorem B2229095 : Blo 2227435 2229095 := bstep (se 1 (by rfl) ⟨1671821, by rfl⟩ : syracuseStep 2229095 = 3343643) B3343643
theorem B2507737 : Blo 2227435 2507737 := bbase (se 2 (by rfl) ⟨940401, by rfl⟩ : syracuseStep 2507737 = 1880803) (by norm_num)
theorem B3343649 : Blo 2227435 3343649 := bstep (se 2 (by rfl) ⟨1253868, by rfl⟩ : syracuseStep 3343649 = 2507737) B2507737
theorem B2229099 : Blo 2227435 2229099 := bstep (se 1 (by rfl) ⟨1671824, by rfl⟩ : syracuseStep 2229099 = 3343649) B3343649
theorem B3173861 : Blo 2227435 3173861 := bbase (se 4 (by rfl) ⟨297549, by rfl⟩ : syracuseStep 3173861 = 595099) (by norm_num)
theorem B8463629 : Blo 2227435 8463629 := bstep (se 3 (by rfl) ⟨1586930, by rfl⟩ : syracuseStep 8463629 = 3173861) B3173861
theorem B5642419 : Blo 2227435 5642419 := bstep (se 1 (by rfl) ⟨4231814, by rfl⟩ : syracuseStep 5642419 = 8463629) B8463629
theorem B7523225 : Blo 2227435 7523225 := bstep (se 2 (by rfl) ⟨2821209, by rfl⟩ : syracuseStep 7523225 = 5642419) B5642419
theorem B5015483 : Blo 2227435 5015483 := bstep (se 1 (by rfl) ⟨3761612, by rfl⟩ : syracuseStep 5015483 = 7523225) B7523225
theorem B3343655 : Blo 2227435 3343655 := bstep (se 1 (by rfl) ⟨2507741, by rfl⟩ : syracuseStep 3343655 = 5015483) B5015483
theorem B2229103 : Blo 2227435 2229103 := bstep (se 1 (by rfl) ⟨1671827, by rfl⟩ : syracuseStep 2229103 = 3343655) B3343655
theorem B3343661 : Blo 2227435 3343661 := bbase (se 3 (by rfl) ⟨626936, by rfl⟩ : syracuseStep 3343661 = 1253873) (by norm_num)
theorem B2229107 : Blo 2227435 2229107 := bstep (se 1 (by rfl) ⟨1671830, by rfl⟩ : syracuseStep 2229107 = 3343661) B3343661
theorem B5015501 : Blo 2227435 5015501 := bbase (se 3 (by rfl) ⟨940406, by rfl⟩ : syracuseStep 5015501 = 1880813) (by norm_num)
theorem B3343667 : Blo 2227435 3343667 := bstep (se 1 (by rfl) ⟨2507750, by rfl⟩ : syracuseStep 3343667 = 5015501) B5015501
theorem B2229111 : Blo 2227435 2229111 := bstep (se 1 (by rfl) ⟨1671833, by rfl⟩ : syracuseStep 2229111 = 3343667) B3343667
theorem B2821225 : Blo 2227435 2821225 := bbase (se 2 (by rfl) ⟨1057959, by rfl⟩ : syracuseStep 2821225 = 2115919) (by norm_num)
theorem B3761633 : Blo 2227435 3761633 := bstep (se 2 (by rfl) ⟨1410612, by rfl⟩ : syracuseStep 3761633 = 2821225) B2821225
theorem B2507755 : Blo 2227435 2507755 := bstep (se 1 (by rfl) ⟨1880816, by rfl⟩ : syracuseStep 2507755 = 3761633) B3761633
theorem B3343673 : Blo 2227435 3343673 := bstep (se 2 (by rfl) ⟨1253877, by rfl⟩ : syracuseStep 3343673 = 2507755) B2507755
theorem B2229115 : Blo 2227435 2229115 := bstep (se 1 (by rfl) ⟨1671836, by rfl⟩ : syracuseStep 2229115 = 3343673) B3343673
theorem B2259533 : Blo 2227435 2259533 := bbase (se 3 (by rfl) ⟨423662, by rfl⟩ : syracuseStep 2259533 = 847325) (by norm_num)
theorem B6025421 : Blo 2227435 6025421 := bstep (se 3 (by rfl) ⟨1129766, by rfl⟩ : syracuseStep 6025421 = 2259533) B2259533
theorem B4016947 : Blo 2227435 4016947 := bstep (se 1 (by rfl) ⟨3012710, by rfl⟩ : syracuseStep 4016947 = 6025421) B6025421
theorem B5355929 : Blo 2227435 5355929 := bstep (se 2 (by rfl) ⟨2008473, by rfl⟩ : syracuseStep 5355929 = 4016947) B4016947
theorem B14282477 : Blo 2227435 14282477 := bstep (se 3 (by rfl) ⟨2677964, by rfl⟩ : syracuseStep 14282477 = 5355929) B5355929
theorem B9521651 : Blo 2227435 9521651 := bstep (se 1 (by rfl) ⟨7141238, by rfl⟩ : syracuseStep 9521651 = 14282477) B14282477
theorem B25391069 : Blo 2227435 25391069 := bstep (se 3 (by rfl) ⟨4760825, by rfl⟩ : syracuseStep 25391069 = 9521651) B9521651
theorem B16927379 : Blo 2227435 16927379 := bstep (se 1 (by rfl) ⟨12695534, by rfl⟩ : syracuseStep 16927379 = 25391069) B25391069
theorem B11284919 : Blo 2227435 11284919 := bstep (se 1 (by rfl) ⟨8463689, by rfl⟩ : syracuseStep 11284919 = 16927379) B16927379
theorem B7523279 : Blo 2227435 7523279 := bstep (se 1 (by rfl) ⟨5642459, by rfl⟩ : syracuseStep 7523279 = 11284919) B11284919
theorem B5015519 : Blo 2227435 5015519 := bstep (se 1 (by rfl) ⟨3761639, by rfl⟩ : syracuseStep 5015519 = 7523279) B7523279
theorem B3343679 : Blo 2227435 3343679 := bstep (se 1 (by rfl) ⟨2507759, by rfl⟩ : syracuseStep 3343679 = 5015519) B5015519
theorem B2229119 : Blo 2227435 2229119 := bstep (se 1 (by rfl) ⟨1671839, by rfl⟩ : syracuseStep 2229119 = 3343679) B3343679
theorem B3343685 : Blo 2227435 3343685 := bbase (se 4 (by rfl) ⟨313470, by rfl⟩ : syracuseStep 3343685 = 626941) (by norm_num)
theorem B2229123 : Blo 2227435 2229123 := bstep (se 1 (by rfl) ⟨1671842, by rfl⟩ : syracuseStep 2229123 = 3343685) B3343685
theorem B3761653 : Blo 2227435 3761653 := bbase (se 5 (by rfl) ⟨176327, by rfl⟩ : syracuseStep 3761653 = 352655) (by norm_num)
theorem B5015537 : Blo 2227435 5015537 := bstep (se 2 (by rfl) ⟨1880826, by rfl⟩ : syracuseStep 5015537 = 3761653) B3761653
theorem B3343691 : Blo 2227435 3343691 := bstep (se 1 (by rfl) ⟨2507768, by rfl⟩ : syracuseStep 3343691 = 5015537) B5015537
theorem B2229127 : Blo 2227435 2229127 := bstep (se 1 (by rfl) ⟨1671845, by rfl⟩ : syracuseStep 2229127 = 3343691) B3343691
theorem B2507773 : Blo 2227435 2507773 := bbase (se 3 (by rfl) ⟨470207, by rfl⟩ : syracuseStep 2507773 = 940415) (by norm_num)
theorem B3343697 : Blo 2227435 3343697 := bstep (se 2 (by rfl) ⟨1253886, by rfl⟩ : syracuseStep 3343697 = 2507773) B2507773
theorem B2229131 : Blo 2227435 2229131 := bstep (se 1 (by rfl) ⟨1671848, by rfl⟩ : syracuseStep 2229131 = 3343697) B3343697
theorem B7523333 : Blo 2227435 7523333 := bbase (se 4 (by rfl) ⟨705312, by rfl⟩ : syracuseStep 7523333 = 1410625) (by norm_num)
theorem B5015555 : Blo 2227435 5015555 := bstep (se 1 (by rfl) ⟨3761666, by rfl⟩ : syracuseStep 5015555 = 7523333) B7523333
theorem B3343703 : Blo 2227435 3343703 := bstep (se 1 (by rfl) ⟨2507777, by rfl⟩ : syracuseStep 3343703 = 5015555) B5015555
theorem B2229135 : Blo 2227435 2229135 := bstep (se 1 (by rfl) ⟨1671851, by rfl⟩ : syracuseStep 2229135 = 3343703) B3343703
theorem B3343709 : Blo 2227435 3343709 := bbase (se 3 (by rfl) ⟨626945, by rfl⟩ : syracuseStep 3343709 = 1253891) (by norm_num)
theorem B2229139 : Blo 2227435 2229139 := bstep (se 1 (by rfl) ⟨1671854, by rfl⟩ : syracuseStep 2229139 = 3343709) B3343709
theorem B5015573 : Blo 2227435 5015573 := bbase (se 6 (by rfl) ⟨117552, by rfl⟩ : syracuseStep 5015573 = 235105) (by norm_num)
theorem B3343715 : Blo 2227435 3343715 := bstep (se 1 (by rfl) ⟨2507786, by rfl⟩ : syracuseStep 3343715 = 5015573) B5015573
theorem B2229143 : Blo 2227435 2229143 := bstep (se 1 (by rfl) ⟨1671857, by rfl⟩ : syracuseStep 2229143 = 3343715) B3343715
theorem B8463797 : Blo 2227435 8463797 := bbase (se 5 (by rfl) ⟨396740, by rfl⟩ : syracuseStep 8463797 = 793481) (by norm_num)
theorem B5642531 : Blo 2227435 5642531 := bstep (se 1 (by rfl) ⟨4231898, by rfl⟩ : syracuseStep 5642531 = 8463797) B8463797
theorem B3761687 : Blo 2227435 3761687 := bstep (se 1 (by rfl) ⟨2821265, by rfl⟩ : syracuseStep 3761687 = 5642531) B5642531
theorem B2507791 : Blo 2227435 2507791 := bstep (se 1 (by rfl) ⟨1880843, by rfl⟩ : syracuseStep 2507791 = 3761687) B3761687
theorem B3343721 : Blo 2227435 3343721 := bstep (se 2 (by rfl) ⟨1253895, by rfl⟩ : syracuseStep 3343721 = 2507791) B2507791
theorem B2229147 : Blo 2227435 2229147 := bstep (se 1 (by rfl) ⟨1671860, by rfl⟩ : syracuseStep 2229147 = 3343721) B3343721
theorem B4289645 : Blo 2227435 4289645 := bbase (se 3 (by rfl) ⟨804308, by rfl⟩ : syracuseStep 4289645 = 1608617) (by norm_num)
theorem B11439053 : Blo 2227435 11439053 := bstep (se 3 (by rfl) ⟨2144822, by rfl⟩ : syracuseStep 11439053 = 4289645) B4289645
theorem B7626035 : Blo 2227435 7626035 := bstep (se 1 (by rfl) ⟨5719526, by rfl⟩ : syracuseStep 7626035 = 11439053) B11439053
theorem B20336093 : Blo 2227435 20336093 := bstep (se 3 (by rfl) ⟨3813017, by rfl⟩ : syracuseStep 20336093 = 7626035) B7626035
theorem B13557395 : Blo 2227435 13557395 := bstep (se 1 (by rfl) ⟨10168046, by rfl⟩ : syracuseStep 13557395 = 20336093) B20336093
theorem B9038263 : Blo 2227435 9038263 := bstep (se 1 (by rfl) ⟨6778697, by rfl⟩ : syracuseStep 9038263 = 13557395) B13557395
theorem B12051017 : Blo 2227435 12051017 := bstep (se 2 (by rfl) ⟨4519131, by rfl⟩ : syracuseStep 12051017 = 9038263) B9038263
theorem B8034011 : Blo 2227435 8034011 := bstep (se 1 (by rfl) ⟨6025508, by rfl⟩ : syracuseStep 8034011 = 12051017) B12051017
theorem B5356007 : Blo 2227435 5356007 := bstep (se 1 (by rfl) ⟨4017005, by rfl⟩ : syracuseStep 5356007 = 8034011) B8034011
theorem B3570671 : Blo 2227435 3570671 := bstep (se 1 (by rfl) ⟨2678003, by rfl⟩ : syracuseStep 3570671 = 5356007) B5356007
theorem B2380447 : Blo 2227435 2380447 := bstep (se 1 (by rfl) ⟨1785335, by rfl⟩ : syracuseStep 2380447 = 3570671) B3570671
theorem B12695717 : Blo 2227435 12695717 := bstep (se 4 (by rfl) ⟨1190223, by rfl⟩ : syracuseStep 12695717 = 2380447) B2380447
theorem B8463811 : Blo 2227435 8463811 := bstep (se 1 (by rfl) ⟨6347858, by rfl⟩ : syracuseStep 8463811 = 12695717) B12695717
theorem B11285081 : Blo 2227435 11285081 := bstep (se 2 (by rfl) ⟨4231905, by rfl⟩ : syracuseStep 11285081 = 8463811) B8463811
theorem B7523387 : Blo 2227435 7523387 := bstep (se 1 (by rfl) ⟨5642540, by rfl⟩ : syracuseStep 7523387 = 11285081) B11285081
theorem B5015591 : Blo 2227435 5015591 := bstep (se 1 (by rfl) ⟨3761693, by rfl⟩ : syracuseStep 5015591 = 7523387) B7523387
theorem B3343727 : Blo 2227435 3343727 := bstep (se 1 (by rfl) ⟨2507795, by rfl⟩ : syracuseStep 3343727 = 5015591) B5015591
theorem B2229151 : Blo 2227435 2229151 := bstep (se 1 (by rfl) ⟨1671863, by rfl⟩ : syracuseStep 2229151 = 3343727) B3343727
theorem B3343733 : Blo 2227435 3343733 := bbase (se 5 (by rfl) ⟨156737, by rfl⟩ : syracuseStep 3343733 = 313475) (by norm_num)
theorem B2229155 : Blo 2227435 2229155 := bstep (se 1 (by rfl) ⟨1671866, by rfl⟩ : syracuseStep 2229155 = 3343733) B3343733
theorem B3173941 : Blo 2227435 3173941 := bbase (se 5 (by rfl) ⟨148778, by rfl⟩ : syracuseStep 3173941 = 297557) (by norm_num)
theorem B4231921 : Blo 2227435 4231921 := bstep (se 2 (by rfl) ⟨1586970, by rfl⟩ : syracuseStep 4231921 = 3173941) B3173941
theorem B5642561 : Blo 2227435 5642561 := bstep (se 2 (by rfl) ⟨2115960, by rfl⟩ : syracuseStep 5642561 = 4231921) B4231921
theorem B3761707 : Blo 2227435 3761707 := bstep (se 1 (by rfl) ⟨2821280, by rfl⟩ : syracuseStep 3761707 = 5642561) B5642561
theorem B5015609 : Blo 2227435 5015609 := bstep (se 2 (by rfl) ⟨1880853, by rfl⟩ : syracuseStep 5015609 = 3761707) B3761707
theorem B3343739 : Blo 2227435 3343739 := bstep (se 1 (by rfl) ⟨2507804, by rfl⟩ : syracuseStep 3343739 = 5015609) B5015609
theorem B2229159 : Blo 2227435 2229159 := bstep (se 1 (by rfl) ⟨1671869, by rfl⟩ : syracuseStep 2229159 = 3343739) B3343739
theorem B2507809 : Blo 2227435 2507809 := bbase (se 2 (by rfl) ⟨940428, by rfl⟩ : syracuseStep 2507809 = 1880857) (by norm_num)
theorem B3343745 : Blo 2227435 3343745 := bstep (se 2 (by rfl) ⟨1253904, by rfl⟩ : syracuseStep 3343745 = 2507809) B2507809
theorem B2229163 : Blo 2227435 2229163 := bstep (se 1 (by rfl) ⟨1671872, by rfl⟩ : syracuseStep 2229163 = 3343745) B3343745
theorem B5642581 : Blo 2227435 5642581 := bbase (se 10 (by rfl) ⟨8265, by rfl⟩ : syracuseStep 5642581 = 16531) (by norm_num)
theorem B7523441 : Blo 2227435 7523441 := bstep (se 2 (by rfl) ⟨2821290, by rfl⟩ : syracuseStep 7523441 = 5642581) B5642581
theorem B5015627 : Blo 2227435 5015627 := bstep (se 1 (by rfl) ⟨3761720, by rfl⟩ : syracuseStep 5015627 = 7523441) B7523441
theorem B3343751 : Blo 2227435 3343751 := bstep (se 1 (by rfl) ⟨2507813, by rfl⟩ : syracuseStep 3343751 = 5015627) B5015627
theorem B2229167 : Blo 2227435 2229167 := bstep (se 1 (by rfl) ⟨1671875, by rfl⟩ : syracuseStep 2229167 = 3343751) B3343751
theorem B3343757 : Blo 2227435 3343757 := bbase (se 3 (by rfl) ⟨626954, by rfl⟩ : syracuseStep 3343757 = 1253909) (by norm_num)
theorem B2229171 : Blo 2227435 2229171 := bstep (se 1 (by rfl) ⟨1671878, by rfl⟩ : syracuseStep 2229171 = 3343757) B3343757
theorem B5015645 : Blo 2227435 5015645 := bbase (se 3 (by rfl) ⟨940433, by rfl⟩ : syracuseStep 5015645 = 1880867) (by norm_num)
theorem B3343763 : Blo 2227435 3343763 := bstep (se 1 (by rfl) ⟨2507822, by rfl⟩ : syracuseStep 3343763 = 5015645) B5015645
theorem B2229175 : Blo 2227435 2229175 := bstep (se 1 (by rfl) ⟨1671881, by rfl⟩ : syracuseStep 2229175 = 3343763) B3343763
theorem B3761741 : Blo 2227435 3761741 := bbase (se 3 (by rfl) ⟨705326, by rfl⟩ : syracuseStep 3761741 = 1410653) (by norm_num)
theorem B2507827 : Blo 2227435 2507827 := bstep (se 1 (by rfl) ⟨1880870, by rfl⟩ : syracuseStep 2507827 = 3761741) B3761741
theorem B3343769 : Blo 2227435 3343769 := bstep (se 2 (by rfl) ⟨1253913, by rfl⟩ : syracuseStep 3343769 = 2507827) B2507827
theorem B2229179 : Blo 2227435 2229179 := bstep (se 1 (by rfl) ⟨1671884, by rfl⟩ : syracuseStep 2229179 = 3343769) B3343769
theorem B94027861 : Blo 2227435 94027861 := bbase (se 8 (by rfl) ⟨550944, by rfl⟩ : syracuseStep 94027861 = 1101889) (by norm_num)
theorem B501481925 : Blo 2227435 501481925 := bstep (se 4 (by rfl) ⟨47013930, by rfl⟩ : syracuseStep 501481925 = 94027861) B94027861
theorem B334321283 : Blo 2227435 334321283 := bstep (se 1 (by rfl) ⟨250740962, by rfl⟩ : syracuseStep 334321283 = 501481925) B501481925
theorem B891523421 : Blo 2227435 891523421 := bstep (se 3 (by rfl) ⟨167160641, by rfl⟩ : syracuseStep 891523421 = 334321283) B334321283
theorem B594348947 : Blo 2227435 594348947 := bstep (se 1 (by rfl) ⟨445761710, by rfl⟩ : syracuseStep 594348947 = 891523421) B891523421
theorem B396232631 : Blo 2227435 396232631 := bstep (se 1 (by rfl) ⟨297174473, by rfl⟩ : syracuseStep 396232631 = 594348947) B594348947
theorem B264155087 : Blo 2227435 264155087 := bstep (se 1 (by rfl) ⟨198116315, by rfl⟩ : syracuseStep 264155087 = 396232631) B396232631
theorem B176103391 : Blo 2227435 176103391 := bstep (se 1 (by rfl) ⟨132077543, by rfl⟩ : syracuseStep 176103391 = 264155087) B264155087
theorem B234804521 : Blo 2227435 234804521 := bstep (se 2 (by rfl) ⟨88051695, by rfl⟩ : syracuseStep 234804521 = 176103391) B176103391
theorem B156536347 : Blo 2227435 156536347 := bstep (se 1 (by rfl) ⟨117402260, by rfl⟩ : syracuseStep 156536347 = 234804521) B234804521
theorem B208715129 : Blo 2227435 208715129 := bstep (se 2 (by rfl) ⟨78268173, by rfl⟩ : syracuseStep 208715129 = 156536347) B156536347
theorem B139143419 : Blo 2227435 139143419 := bstep (se 1 (by rfl) ⟨104357564, by rfl⟩ : syracuseStep 139143419 = 208715129) B208715129
theorem B92762279 : Blo 2227435 92762279 := bstep (se 1 (by rfl) ⟨69571709, by rfl⟩ : syracuseStep 92762279 = 139143419) B139143419
theorem B61841519 : Blo 2227435 61841519 := bstep (se 1 (by rfl) ⟨46381139, by rfl⟩ : syracuseStep 61841519 = 92762279) B92762279
theorem B41227679 : Blo 2227435 41227679 := bstep (se 1 (by rfl) ⟨30920759, by rfl⟩ : syracuseStep 41227679 = 61841519) B61841519
theorem B27485119 : Blo 2227435 27485119 := bstep (se 1 (by rfl) ⟨20613839, by rfl⟩ : syracuseStep 27485119 = 41227679) B41227679
theorem B36646825 : Blo 2227435 36646825 := bstep (se 2 (by rfl) ⟨13742559, by rfl⟩ : syracuseStep 36646825 = 27485119) B27485119
theorem B48862433 : Blo 2227435 48862433 := bstep (se 2 (by rfl) ⟨18323412, by rfl⟩ : syracuseStep 48862433 = 36646825) B36646825
theorem B32574955 : Blo 2227435 32574955 := bstep (se 1 (by rfl) ⟨24431216, by rfl⟩ : syracuseStep 32574955 = 48862433) B48862433
theorem B43433273 : Blo 2227435 43433273 := bstep (se 2 (by rfl) ⟨16287477, by rfl⟩ : syracuseStep 43433273 = 32574955) B32574955
theorem B28955515 : Blo 2227435 28955515 := bstep (se 1 (by rfl) ⟨21716636, by rfl⟩ : syracuseStep 28955515 = 43433273) B43433273
theorem B38607353 : Blo 2227435 38607353 := bstep (se 2 (by rfl) ⟨14477757, by rfl⟩ : syracuseStep 38607353 = 28955515) B28955515
theorem B25738235 : Blo 2227435 25738235 := bstep (se 1 (by rfl) ⟨19303676, by rfl⟩ : syracuseStep 25738235 = 38607353) B38607353
theorem B17158823 : Blo 2227435 17158823 := bstep (se 1 (by rfl) ⟨12869117, by rfl⟩ : syracuseStep 17158823 = 25738235) B25738235
theorem B11439215 : Blo 2227435 11439215 := bstep (se 1 (by rfl) ⟨8579411, by rfl⟩ : syracuseStep 11439215 = 17158823) B17158823
theorem B7626143 : Blo 2227435 7626143 := bstep (se 1 (by rfl) ⟨5719607, by rfl⟩ : syracuseStep 7626143 = 11439215) B11439215
theorem B5084095 : Blo 2227435 5084095 := bstep (se 1 (by rfl) ⟨3813071, by rfl⟩ : syracuseStep 5084095 = 7626143) B7626143
theorem B6778793 : Blo 2227435 6778793 := bstep (se 2 (by rfl) ⟨2542047, by rfl⟩ : syracuseStep 6778793 = 5084095) B5084095
theorem B4519195 : Blo 2227435 4519195 := bstep (se 1 (by rfl) ⟨3389396, by rfl⟩ : syracuseStep 4519195 = 6778793) B6778793
theorem B24102373 : Blo 2227435 24102373 := bstep (se 4 (by rfl) ⟨2259597, by rfl⟩ : syracuseStep 24102373 = 4519195) B4519195
theorem B32136497 : Blo 2227435 32136497 := bstep (se 2 (by rfl) ⟨12051186, by rfl⟩ : syracuseStep 32136497 = 24102373) B24102373
theorem B21424331 : Blo 2227435 21424331 := bstep (se 1 (by rfl) ⟨16068248, by rfl⟩ : syracuseStep 21424331 = 32136497) B32136497
theorem B14282887 : Blo 2227435 14282887 := bstep (se 1 (by rfl) ⟨10712165, by rfl⟩ : syracuseStep 14282887 = 21424331) B21424331
theorem B19043849 : Blo 2227435 19043849 := bstep (se 2 (by rfl) ⟨7141443, by rfl⟩ : syracuseStep 19043849 = 14282887) B14282887
theorem B12695899 : Blo 2227435 12695899 := bstep (se 1 (by rfl) ⟨9521924, by rfl⟩ : syracuseStep 12695899 = 19043849) B19043849
theorem B16927865 : Blo 2227435 16927865 := bstep (se 2 (by rfl) ⟨6347949, by rfl⟩ : syracuseStep 16927865 = 12695899) B12695899
theorem B11285243 : Blo 2227435 11285243 := bstep (se 1 (by rfl) ⟨8463932, by rfl⟩ : syracuseStep 11285243 = 16927865) B16927865
theorem B7523495 : Blo 2227435 7523495 := bstep (se 1 (by rfl) ⟨5642621, by rfl⟩ : syracuseStep 7523495 = 11285243) B11285243
theorem B5015663 : Blo 2227435 5015663 := bstep (se 1 (by rfl) ⟨3761747, by rfl⟩ : syracuseStep 5015663 = 7523495) B7523495
theorem B3343775 : Blo 2227435 3343775 := bstep (se 1 (by rfl) ⟨2507831, by rfl⟩ : syracuseStep 3343775 = 5015663) B5015663
theorem B2229183 : Blo 2227435 2229183 := bstep (se 1 (by rfl) ⟨1671887, by rfl⟩ : syracuseStep 2229183 = 3343775) B3343775
theorem B3343781 : Blo 2227435 3343781 := bbase (se 4 (by rfl) ⟨313479, by rfl⟩ : syracuseStep 3343781 = 626959) (by norm_num)
theorem B2229187 : Blo 2227435 2229187 := bstep (se 1 (by rfl) ⟨1671890, by rfl⟩ : syracuseStep 2229187 = 3343781) B3343781
theorem B2821321 : Blo 2227435 2821321 := bbase (se 2 (by rfl) ⟨1057995, by rfl⟩ : syracuseStep 2821321 = 2115991) (by norm_num)
theorem B3761761 : Blo 2227435 3761761 := bstep (se 2 (by rfl) ⟨1410660, by rfl⟩ : syracuseStep 3761761 = 2821321) B2821321
theorem B5015681 : Blo 2227435 5015681 := bstep (se 2 (by rfl) ⟨1880880, by rfl⟩ : syracuseStep 5015681 = 3761761) B3761761
theorem B3343787 : Blo 2227435 3343787 := bstep (se 1 (by rfl) ⟨2507840, by rfl⟩ : syracuseStep 3343787 = 5015681) B5015681
theorem B2229191 : Blo 2227435 2229191 := bstep (se 1 (by rfl) ⟨1671893, by rfl⟩ : syracuseStep 2229191 = 3343787) B3343787
theorem B2507845 : Blo 2227435 2507845 := bbase (se 4 (by rfl) ⟨235110, by rfl⟩ : syracuseStep 2507845 = 470221) (by norm_num)
theorem B3343793 : Blo 2227435 3343793 := bstep (se 2 (by rfl) ⟨1253922, by rfl⟩ : syracuseStep 3343793 = 2507845) B2507845
theorem B2229195 : Blo 2227435 2229195 := bstep (se 1 (by rfl) ⟨1671896, by rfl⟩ : syracuseStep 2229195 = 3343793) B3343793
theorem B4231997 : Blo 2227435 4231997 := bbase (se 3 (by rfl) ⟨793499, by rfl⟩ : syracuseStep 4231997 = 1586999) (by norm_num)
theorem B2821331 : Blo 2227435 2821331 := bstep (se 1 (by rfl) ⟨2115998, by rfl⟩ : syracuseStep 2821331 = 4231997) B4231997
theorem B7523549 : Blo 2227435 7523549 := bstep (se 3 (by rfl) ⟨1410665, by rfl⟩ : syracuseStep 7523549 = 2821331) B2821331
theorem B5015699 : Blo 2227435 5015699 := bstep (se 1 (by rfl) ⟨3761774, by rfl⟩ : syracuseStep 5015699 = 7523549) B7523549
theorem B3343799 : Blo 2227435 3343799 := bstep (se 1 (by rfl) ⟨2507849, by rfl⟩ : syracuseStep 3343799 = 5015699) B5015699
theorem B2229199 : Blo 2227435 2229199 := bstep (se 1 (by rfl) ⟨1671899, by rfl⟩ : syracuseStep 2229199 = 3343799) B3343799
theorem B3343805 : Blo 2227435 3343805 := bbase (se 3 (by rfl) ⟨626963, by rfl⟩ : syracuseStep 3343805 = 1253927) (by norm_num)
theorem B2229203 : Blo 2227435 2229203 := bstep (se 1 (by rfl) ⟨1671902, by rfl⟩ : syracuseStep 2229203 = 3343805) B3343805
theorem B5015717 : Blo 2227435 5015717 := bbase (se 4 (by rfl) ⟨470223, by rfl⟩ : syracuseStep 5015717 = 940447) (by norm_num)
theorem B3343811 : Blo 2227435 3343811 := bstep (se 1 (by rfl) ⟨2507858, by rfl⟩ : syracuseStep 3343811 = 5015717) B5015717
theorem B2229207 : Blo 2227435 2229207 := bstep (se 1 (by rfl) ⟨1671905, by rfl⟩ : syracuseStep 2229207 = 3343811) B3343811
theorem B5642693 : Blo 2227435 5642693 := bbase (se 4 (by rfl) ⟨529002, by rfl⟩ : syracuseStep 5642693 = 1058005) (by norm_num)
theorem B3761795 : Blo 2227435 3761795 := bstep (se 1 (by rfl) ⟨2821346, by rfl⟩ : syracuseStep 3761795 = 5642693) B5642693
theorem B2507863 : Blo 2227435 2507863 := bstep (se 1 (by rfl) ⟨1880897, by rfl⟩ : syracuseStep 2507863 = 3761795) B3761795
theorem B3343817 : Blo 2227435 3343817 := bstep (se 2 (by rfl) ⟨1253931, by rfl⟩ : syracuseStep 3343817 = 2507863) B2507863
theorem B2229211 : Blo 2227435 2229211 := bstep (se 1 (by rfl) ⟨1671908, by rfl⟩ : syracuseStep 2229211 = 3343817) B3343817
theorem B4519261 : Blo 2227435 4519261 := bbase (se 3 (by rfl) ⟨847361, by rfl⟩ : syracuseStep 4519261 = 1694723) (by norm_num)
theorem B6025681 : Blo 2227435 6025681 := bstep (se 2 (by rfl) ⟨2259630, by rfl⟩ : syracuseStep 6025681 = 4519261) B4519261
theorem B8034241 : Blo 2227435 8034241 := bstep (se 2 (by rfl) ⟨3012840, by rfl⟩ : syracuseStep 8034241 = 6025681) B6025681
theorem B10712321 : Blo 2227435 10712321 := bstep (se 2 (by rfl) ⟨4017120, by rfl⟩ : syracuseStep 10712321 = 8034241) B8034241
theorem B7141547 : Blo 2227435 7141547 := bstep (se 1 (by rfl) ⟨5356160, by rfl⟩ : syracuseStep 7141547 = 10712321) B10712321
theorem B4761031 : Blo 2227435 4761031 := bstep (se 1 (by rfl) ⟨3570773, by rfl⟩ : syracuseStep 4761031 = 7141547) B7141547
theorem B6348041 : Blo 2227435 6348041 := bstep (se 2 (by rfl) ⟨2380515, by rfl⟩ : syracuseStep 6348041 = 4761031) B4761031
theorem B4232027 : Blo 2227435 4232027 := bstep (se 1 (by rfl) ⟨3174020, by rfl⟩ : syracuseStep 4232027 = 6348041) B6348041
theorem B11285405 : Blo 2227435 11285405 := bstep (se 3 (by rfl) ⟨2116013, by rfl⟩ : syracuseStep 11285405 = 4232027) B4232027
theorem B7523603 : Blo 2227435 7523603 := bstep (se 1 (by rfl) ⟨5642702, by rfl⟩ : syracuseStep 7523603 = 11285405) B11285405
theorem B5015735 : Blo 2227435 5015735 := bstep (se 1 (by rfl) ⟨3761801, by rfl⟩ : syracuseStep 5015735 = 7523603) B7523603
theorem B3343823 : Blo 2227435 3343823 := bstep (se 1 (by rfl) ⟨2507867, by rfl⟩ : syracuseStep 3343823 = 5015735) B5015735
theorem B2229215 : Blo 2227435 2229215 := bstep (se 1 (by rfl) ⟨1671911, by rfl⟩ : syracuseStep 2229215 = 3343823) B3343823
theorem B3343829 : Blo 2227435 3343829 := bbase (se 7 (by rfl) ⟨39185, by rfl⟩ : syracuseStep 3343829 = 78371) (by norm_num)
theorem B2229219 : Blo 2227435 2229219 := bstep (se 1 (by rfl) ⟨1671914, by rfl⟩ : syracuseStep 2229219 = 3343829) B3343829
theorem B8464085 : Blo 2227435 8464085 := bbase (se 7 (by rfl) ⟨99188, by rfl⟩ : syracuseStep 8464085 = 198377) (by norm_num)
theorem B5642723 : Blo 2227435 5642723 := bstep (se 1 (by rfl) ⟨4232042, by rfl⟩ : syracuseStep 5642723 = 8464085) B8464085
theorem B3761815 : Blo 2227435 3761815 := bstep (se 1 (by rfl) ⟨2821361, by rfl⟩ : syracuseStep 3761815 = 5642723) B5642723
theorem B5015753 : Blo 2227435 5015753 := bstep (se 2 (by rfl) ⟨1880907, by rfl⟩ : syracuseStep 5015753 = 3761815) B3761815
theorem B3343835 : Blo 2227435 3343835 := bstep (se 1 (by rfl) ⟨2507876, by rfl⟩ : syracuseStep 3343835 = 5015753) B5015753
theorem B2229223 : Blo 2227435 2229223 := bstep (se 1 (by rfl) ⟨1671917, by rfl⟩ : syracuseStep 2229223 = 3343835) B3343835
theorem B2507881 : Blo 2227435 2507881 := bbase (se 2 (by rfl) ⟨940455, by rfl⟩ : syracuseStep 2507881 = 1880911) (by norm_num)
theorem B3343841 : Blo 2227435 3343841 := bstep (se 2 (by rfl) ⟨1253940, by rfl⟩ : syracuseStep 3343841 = 2507881) B2507881
theorem B2229227 : Blo 2227435 2229227 := bstep (se 1 (by rfl) ⟨1671920, by rfl⟩ : syracuseStep 2229227 = 3343841) B3343841
theorem B123685717 : Blo 2227435 123685717 := bbase (se 9 (by rfl) ⟨362360, by rfl⟩ : syracuseStep 123685717 = 724721) (by norm_num)
theorem B164914289 : Blo 2227435 164914289 := bstep (se 2 (by rfl) ⟨61842858, by rfl⟩ : syracuseStep 164914289 = 123685717) B123685717
theorem B109942859 : Blo 2227435 109942859 := bstep (se 1 (by rfl) ⟨82457144, by rfl⟩ : syracuseStep 109942859 = 164914289) B164914289
theorem B73295239 : Blo 2227435 73295239 := bstep (se 1 (by rfl) ⟨54971429, by rfl⟩ : syracuseStep 73295239 = 109942859) B109942859
theorem B97726985 : Blo 2227435 97726985 := bstep (se 2 (by rfl) ⟨36647619, by rfl⟩ : syracuseStep 97726985 = 73295239) B73295239
theorem B65151323 : Blo 2227435 65151323 := bstep (se 1 (by rfl) ⟨48863492, by rfl⟩ : syracuseStep 65151323 = 97726985) B97726985
theorem B43434215 : Blo 2227435 43434215 := bstep (se 1 (by rfl) ⟨32575661, by rfl⟩ : syracuseStep 43434215 = 65151323) B65151323
theorem B28956143 : Blo 2227435 28956143 := bstep (se 1 (by rfl) ⟨21717107, by rfl⟩ : syracuseStep 28956143 = 43434215) B43434215
theorem B19304095 : Blo 2227435 19304095 := bstep (se 1 (by rfl) ⟨14478071, by rfl⟩ : syracuseStep 19304095 = 28956143) B28956143
theorem B25738793 : Blo 2227435 25738793 := bstep (se 2 (by rfl) ⟨9652047, by rfl⟩ : syracuseStep 25738793 = 19304095) B19304095
theorem B17159195 : Blo 2227435 17159195 := bstep (se 1 (by rfl) ⟨12869396, by rfl⟩ : syracuseStep 17159195 = 25738793) B25738793
theorem B11439463 : Blo 2227435 11439463 := bstep (se 1 (by rfl) ⟨8579597, by rfl⟩ : syracuseStep 11439463 = 17159195) B17159195
theorem B15252617 : Blo 2227435 15252617 := bstep (se 2 (by rfl) ⟨5719731, by rfl⟩ : syracuseStep 15252617 = 11439463) B11439463
theorem B10168411 : Blo 2227435 10168411 := bstep (se 1 (by rfl) ⟨7626308, by rfl⟩ : syracuseStep 10168411 = 15252617) B15252617
theorem B13557881 : Blo 2227435 13557881 := bstep (se 2 (by rfl) ⟨5084205, by rfl⟩ : syracuseStep 13557881 = 10168411) B10168411
theorem B9038587 : Blo 2227435 9038587 := bstep (se 1 (by rfl) ⟨6778940, by rfl⟩ : syracuseStep 9038587 = 13557881) B13557881
theorem B12051449 : Blo 2227435 12051449 := bstep (se 2 (by rfl) ⟨4519293, by rfl⟩ : syracuseStep 12051449 = 9038587) B9038587
theorem B8034299 : Blo 2227435 8034299 := bstep (se 1 (by rfl) ⟨6025724, by rfl⟩ : syracuseStep 8034299 = 12051449) B12051449
theorem B5356199 : Blo 2227435 5356199 := bstep (se 1 (by rfl) ⟨4017149, by rfl⟩ : syracuseStep 5356199 = 8034299) B8034299
theorem B3570799 : Blo 2227435 3570799 := bstep (se 1 (by rfl) ⟨2678099, by rfl⟩ : syracuseStep 3570799 = 5356199) B5356199
theorem B4761065 : Blo 2227435 4761065 := bstep (se 2 (by rfl) ⟨1785399, by rfl⟩ : syracuseStep 4761065 = 3570799) B3570799
theorem B12696173 : Blo 2227435 12696173 := bstep (se 3 (by rfl) ⟨2380532, by rfl⟩ : syracuseStep 12696173 = 4761065) B4761065
theorem B8464115 : Blo 2227435 8464115 := bstep (se 1 (by rfl) ⟨6348086, by rfl⟩ : syracuseStep 8464115 = 12696173) B12696173
theorem B5642743 : Blo 2227435 5642743 := bstep (se 1 (by rfl) ⟨4232057, by rfl⟩ : syracuseStep 5642743 = 8464115) B8464115
theorem B7523657 : Blo 2227435 7523657 := bstep (se 2 (by rfl) ⟨2821371, by rfl⟩ : syracuseStep 7523657 = 5642743) B5642743
theorem B5015771 : Blo 2227435 5015771 := bstep (se 1 (by rfl) ⟨3761828, by rfl⟩ : syracuseStep 5015771 = 7523657) B7523657
theorem B3343847 : Blo 2227435 3343847 := bstep (se 1 (by rfl) ⟨2507885, by rfl⟩ : syracuseStep 3343847 = 5015771) B5015771
theorem B2229231 : Blo 2227435 2229231 := bstep (se 1 (by rfl) ⟨1671923, by rfl⟩ : syracuseStep 2229231 = 3343847) B3343847
theorem B3343853 : Blo 2227435 3343853 := bbase (se 3 (by rfl) ⟨626972, by rfl⟩ : syracuseStep 3343853 = 1253945) (by norm_num)
theorem B2229235 : Blo 2227435 2229235 := bstep (se 1 (by rfl) ⟨1671926, by rfl⟩ : syracuseStep 2229235 = 3343853) B3343853
theorem B5015789 : Blo 2227435 5015789 := bbase (se 3 (by rfl) ⟨940460, by rfl⟩ : syracuseStep 5015789 = 1880921) (by norm_num)
theorem B3343859 : Blo 2227435 3343859 := bstep (se 1 (by rfl) ⟨2507894, by rfl⟩ : syracuseStep 3343859 = 5015789) B5015789
theorem B2229239 : Blo 2227435 2229239 := bstep (se 1 (by rfl) ⟨1671929, by rfl⟩ : syracuseStep 2229239 = 3343859) B3343859
theorem B3174061 : Blo 2227435 3174061 := bbase (se 3 (by rfl) ⟨595136, by rfl⟩ : syracuseStep 3174061 = 1190273) (by norm_num)
theorem B4232081 : Blo 2227435 4232081 := bstep (se 2 (by rfl) ⟨1587030, by rfl⟩ : syracuseStep 4232081 = 3174061) B3174061
theorem B2821387 : Blo 2227435 2821387 := bstep (se 1 (by rfl) ⟨2116040, by rfl⟩ : syracuseStep 2821387 = 4232081) B4232081
theorem B3761849 : Blo 2227435 3761849 := bstep (se 2 (by rfl) ⟨1410693, by rfl⟩ : syracuseStep 3761849 = 2821387) B2821387
theorem B2507899 : Blo 2227435 2507899 := bstep (se 1 (by rfl) ⟨1880924, by rfl⟩ : syracuseStep 2507899 = 3761849) B3761849
theorem B3343865 : Blo 2227435 3343865 := bstep (se 2 (by rfl) ⟨1253949, by rfl⟩ : syracuseStep 3343865 = 2507899) B2507899
theorem B2229243 : Blo 2227435 2229243 := bstep (se 1 (by rfl) ⟨1671932, by rfl⟩ : syracuseStep 2229243 = 3343865) B3343865
theorem B4519325 : Blo 2227435 4519325 := bbase (se 3 (by rfl) ⟨847373, by rfl⟩ : syracuseStep 4519325 = 1694747) (by norm_num)
theorem B3012883 : Blo 2227435 3012883 := bstep (se 1 (by rfl) ⟨2259662, by rfl⟩ : syracuseStep 3012883 = 4519325) B4519325
theorem B16068709 : Blo 2227435 16068709 := bstep (se 4 (by rfl) ⟨1506441, by rfl⟩ : syracuseStep 16068709 = 3012883) B3012883
theorem B85699781 : Blo 2227435 85699781 := bstep (se 4 (by rfl) ⟨8034354, by rfl⟩ : syracuseStep 85699781 = 16068709) B16068709
theorem B57133187 : Blo 2227435 57133187 := bstep (se 1 (by rfl) ⟨42849890, by rfl⟩ : syracuseStep 57133187 = 85699781) B85699781
theorem B38088791 : Blo 2227435 38088791 := bstep (se 1 (by rfl) ⟨28566593, by rfl⟩ : syracuseStep 38088791 = 57133187) B57133187
theorem B25392527 : Blo 2227435 25392527 := bstep (se 1 (by rfl) ⟨19044395, by rfl⟩ : syracuseStep 25392527 = 38088791) B38088791
theorem B16928351 : Blo 2227435 16928351 := bstep (se 1 (by rfl) ⟨12696263, by rfl⟩ : syracuseStep 16928351 = 25392527) B25392527
theorem B11285567 : Blo 2227435 11285567 := bstep (se 1 (by rfl) ⟨8464175, by rfl⟩ : syracuseStep 11285567 = 16928351) B16928351
theorem B7523711 : Blo 2227435 7523711 := bstep (se 1 (by rfl) ⟨5642783, by rfl⟩ : syracuseStep 7523711 = 11285567) B11285567
theorem B5015807 : Blo 2227435 5015807 := bstep (se 1 (by rfl) ⟨3761855, by rfl⟩ : syracuseStep 5015807 = 7523711) B7523711
theorem B3343871 : Blo 2227435 3343871 := bstep (se 1 (by rfl) ⟨2507903, by rfl⟩ : syracuseStep 3343871 = 5015807) B5015807
theorem B2229247 : Blo 2227435 2229247 := bstep (se 1 (by rfl) ⟨1671935, by rfl⟩ : syracuseStep 2229247 = 3343871) B3343871
theorem B3343877 : Blo 2227435 3343877 := bbase (se 4 (by rfl) ⟨313488, by rfl⟩ : syracuseStep 3343877 = 626977) (by norm_num)
theorem B2229251 : Blo 2227435 2229251 := bstep (se 1 (by rfl) ⟨1671938, by rfl⟩ : syracuseStep 2229251 = 3343877) B3343877
theorem B3761869 : Blo 2227435 3761869 := bbase (se 3 (by rfl) ⟨705350, by rfl⟩ : syracuseStep 3761869 = 1410701) (by norm_num)
theorem B5015825 : Blo 2227435 5015825 := bstep (se 2 (by rfl) ⟨1880934, by rfl⟩ : syracuseStep 5015825 = 3761869) B3761869
theorem B3343883 : Blo 2227435 3343883 := bstep (se 1 (by rfl) ⟨2507912, by rfl⟩ : syracuseStep 3343883 = 5015825) B5015825
theorem B2229255 : Blo 2227435 2229255 := bstep (se 1 (by rfl) ⟨1671941, by rfl⟩ : syracuseStep 2229255 = 3343883) B3343883
theorem B2507917 : Blo 2227435 2507917 := bbase (se 3 (by rfl) ⟨470234, by rfl⟩ : syracuseStep 2507917 = 940469) (by norm_num)
theorem B3343889 : Blo 2227435 3343889 := bstep (se 2 (by rfl) ⟨1253958, by rfl⟩ : syracuseStep 3343889 = 2507917) B2507917
theorem B2229259 : Blo 2227435 2229259 := bstep (se 1 (by rfl) ⟨1671944, by rfl⟩ : syracuseStep 2229259 = 3343889) B3343889
theorem B7523765 : Blo 2227435 7523765 := bbase (se 5 (by rfl) ⟨352676, by rfl⟩ : syracuseStep 7523765 = 705353) (by norm_num)
theorem B5015843 : Blo 2227435 5015843 := bstep (se 1 (by rfl) ⟨3761882, by rfl⟩ : syracuseStep 5015843 = 7523765) B7523765
theorem B3343895 : Blo 2227435 3343895 := bstep (se 1 (by rfl) ⟨2507921, by rfl⟩ : syracuseStep 3343895 = 5015843) B5015843
theorem B2229263 : Blo 2227435 2229263 := bstep (se 1 (by rfl) ⟨1671947, by rfl⟩ : syracuseStep 2229263 = 3343895) B3343895
theorem B3343901 : Blo 2227435 3343901 := bbase (se 3 (by rfl) ⟨626981, by rfl⟩ : syracuseStep 3343901 = 1253963) (by norm_num)
theorem B2229267 : Blo 2227435 2229267 := bstep (se 1 (by rfl) ⟨1671950, by rfl⟩ : syracuseStep 2229267 = 3343901) B3343901
theorem B5015861 : Blo 2227435 5015861 := bbase (se 5 (by rfl) ⟨235118, by rfl⟩ : syracuseStep 5015861 = 470237) (by norm_num)
theorem B3343907 : Blo 2227435 3343907 := bstep (se 1 (by rfl) ⟨2507930, by rfl⟩ : syracuseStep 3343907 = 5015861) B5015861
theorem B2229271 : Blo 2227435 2229271 := bstep (se 1 (by rfl) ⟨1671953, by rfl⟩ : syracuseStep 2229271 = 3343907) B3343907
theorem B2542153 : Blo 2227435 2542153 := bbase (se 2 (by rfl) ⟨953307, by rfl⟩ : syracuseStep 2542153 = 1906615) (by norm_num)
theorem B3389537 : Blo 2227435 3389537 := bstep (se 2 (by rfl) ⟨1271076, by rfl⟩ : syracuseStep 3389537 = 2542153) B2542153
theorem B9038765 : Blo 2227435 9038765 := bstep (se 3 (by rfl) ⟨1694768, by rfl⟩ : syracuseStep 9038765 = 3389537) B3389537
theorem B6025843 : Blo 2227435 6025843 := bstep (se 1 (by rfl) ⟨4519382, by rfl⟩ : syracuseStep 6025843 = 9038765) B9038765
theorem B32137829 : Blo 2227435 32137829 := bstep (se 4 (by rfl) ⟨3012921, by rfl⟩ : syracuseStep 32137829 = 6025843) B6025843
theorem B21425219 : Blo 2227435 21425219 := bstep (se 1 (by rfl) ⟨16068914, by rfl⟩ : syracuseStep 21425219 = 32137829) B32137829
theorem B14283479 : Blo 2227435 14283479 := bstep (se 1 (by rfl) ⟨10712609, by rfl⟩ : syracuseStep 14283479 = 21425219) B21425219
theorem B9522319 : Blo 2227435 9522319 := bstep (se 1 (by rfl) ⟨7141739, by rfl⟩ : syracuseStep 9522319 = 14283479) B14283479
theorem B12696425 : Blo 2227435 12696425 := bstep (se 2 (by rfl) ⟨4761159, by rfl⟩ : syracuseStep 12696425 = 9522319) B9522319
theorem B8464283 : Blo 2227435 8464283 := bstep (se 1 (by rfl) ⟨6348212, by rfl⟩ : syracuseStep 8464283 = 12696425) B12696425
theorem B5642855 : Blo 2227435 5642855 := bstep (se 1 (by rfl) ⟨4232141, by rfl⟩ : syracuseStep 5642855 = 8464283) B8464283
theorem B3761903 : Blo 2227435 3761903 := bstep (se 1 (by rfl) ⟨2821427, by rfl⟩ : syracuseStep 3761903 = 5642855) B5642855
theorem B2507935 : Blo 2227435 2507935 := bstep (se 1 (by rfl) ⟨1880951, by rfl⟩ : syracuseStep 2507935 = 3761903) B3761903
theorem B3343913 : Blo 2227435 3343913 := bstep (se 2 (by rfl) ⟨1253967, by rfl⟩ : syracuseStep 3343913 = 2507935) B2507935
theorem B2229275 : Blo 2227435 2229275 := bstep (se 1 (by rfl) ⟨1671956, by rfl⟩ : syracuseStep 2229275 = 3343913) B3343913
theorem B11006933 : Blo 2227435 11006933 := bbase (se 7 (by rfl) ⟨128987, by rfl⟩ : syracuseStep 11006933 = 257975) (by norm_num)
theorem B117407285 : Blo 2227435 117407285 := bstep (se 5 (by rfl) ⟨5503466, by rfl⟩ : syracuseStep 117407285 = 11006933) B11006933
theorem B78271523 : Blo 2227435 78271523 := bstep (se 1 (by rfl) ⟨58703642, by rfl⟩ : syracuseStep 78271523 = 117407285) B117407285
theorem B52181015 : Blo 2227435 52181015 := bstep (se 1 (by rfl) ⟨39135761, by rfl⟩ : syracuseStep 52181015 = 78271523) B78271523
theorem B556597493 : Blo 2227435 556597493 := bstep (se 5 (by rfl) ⟨26090507, by rfl⟩ : syracuseStep 556597493 = 52181015) B52181015
theorem B371064995 : Blo 2227435 371064995 := bstep (se 1 (by rfl) ⟨278298746, by rfl⟩ : syracuseStep 371064995 = 556597493) B556597493
theorem B247376663 : Blo 2227435 247376663 := bstep (se 1 (by rfl) ⟨185532497, by rfl⟩ : syracuseStep 247376663 = 371064995) B371064995
theorem B164917775 : Blo 2227435 164917775 := bstep (se 1 (by rfl) ⟨123688331, by rfl⟩ : syracuseStep 164917775 = 247376663) B247376663
theorem B109945183 : Blo 2227435 109945183 := bstep (se 1 (by rfl) ⟨82458887, by rfl⟩ : syracuseStep 109945183 = 164917775) B164917775
theorem B146593577 : Blo 2227435 146593577 := bstep (se 2 (by rfl) ⟨54972591, by rfl⟩ : syracuseStep 146593577 = 109945183) B109945183
theorem B390916205 : Blo 2227435 390916205 := bstep (se 3 (by rfl) ⟨73296788, by rfl⟩ : syracuseStep 390916205 = 146593577) B146593577
theorem B260610803 : Blo 2227435 260610803 := bstep (se 1 (by rfl) ⟨195458102, by rfl⟩ : syracuseStep 260610803 = 390916205) B390916205
theorem B173740535 : Blo 2227435 173740535 := bstep (se 1 (by rfl) ⟨130305401, by rfl⟩ : syracuseStep 173740535 = 260610803) B260610803
theorem B115827023 : Blo 2227435 115827023 := bstep (se 1 (by rfl) ⟨86870267, by rfl⟩ : syracuseStep 115827023 = 173740535) B173740535
theorem B308872061 : Blo 2227435 308872061 := bstep (se 3 (by rfl) ⟨57913511, by rfl⟩ : syracuseStep 308872061 = 115827023) B115827023
theorem B205914707 : Blo 2227435 205914707 := bstep (se 1 (by rfl) ⟨154436030, by rfl⟩ : syracuseStep 205914707 = 308872061) B308872061
theorem B137276471 : Blo 2227435 137276471 := bstep (se 1 (by rfl) ⟨102957353, by rfl⟩ : syracuseStep 137276471 = 205914707) B205914707
theorem B91517647 : Blo 2227435 91517647 := bstep (se 1 (by rfl) ⟨68638235, by rfl⟩ : syracuseStep 91517647 = 137276471) B137276471
theorem B122023529 : Blo 2227435 122023529 := bstep (se 2 (by rfl) ⟨45758823, by rfl⟩ : syracuseStep 122023529 = 91517647) B91517647
theorem B81349019 : Blo 2227435 81349019 := bstep (se 1 (by rfl) ⟨61011764, by rfl⟩ : syracuseStep 81349019 = 122023529) B122023529
theorem B54232679 : Blo 2227435 54232679 := bstep (se 1 (by rfl) ⟨40674509, by rfl⟩ : syracuseStep 54232679 = 81349019) B81349019
theorem B36155119 : Blo 2227435 36155119 := bstep (se 1 (by rfl) ⟨27116339, by rfl⟩ : syracuseStep 36155119 = 54232679) B54232679
theorem B48206825 : Blo 2227435 48206825 := bstep (se 2 (by rfl) ⟨18077559, by rfl⟩ : syracuseStep 48206825 = 36155119) B36155119
theorem B32137883 : Blo 2227435 32137883 := bstep (se 1 (by rfl) ⟨24103412, by rfl⟩ : syracuseStep 32137883 = 48206825) B48206825
theorem B21425255 : Blo 2227435 21425255 := bstep (se 1 (by rfl) ⟨16068941, by rfl⟩ : syracuseStep 21425255 = 32137883) B32137883
theorem B14283503 : Blo 2227435 14283503 := bstep (se 1 (by rfl) ⟨10712627, by rfl⟩ : syracuseStep 14283503 = 21425255) B21425255
theorem B9522335 : Blo 2227435 9522335 := bstep (se 1 (by rfl) ⟨7141751, by rfl⟩ : syracuseStep 9522335 = 14283503) B14283503
theorem B6348223 : Blo 2227435 6348223 := bstep (se 1 (by rfl) ⟨4761167, by rfl⟩ : syracuseStep 6348223 = 9522335) B9522335
theorem B8464297 : Blo 2227435 8464297 := bstep (se 2 (by rfl) ⟨3174111, by rfl⟩ : syracuseStep 8464297 = 6348223) B6348223
theorem B11285729 : Blo 2227435 11285729 := bstep (se 2 (by rfl) ⟨4232148, by rfl⟩ : syracuseStep 11285729 = 8464297) B8464297
theorem B7523819 : Blo 2227435 7523819 := bstep (se 1 (by rfl) ⟨5642864, by rfl⟩ : syracuseStep 7523819 = 11285729) B11285729
theorem B5015879 : Blo 2227435 5015879 := bstep (se 1 (by rfl) ⟨3761909, by rfl⟩ : syracuseStep 5015879 = 7523819) B7523819
theorem B3343919 : Blo 2227435 3343919 := bstep (se 1 (by rfl) ⟨2507939, by rfl⟩ : syracuseStep 3343919 = 5015879) B5015879
theorem B2229279 : Blo 2227435 2229279 := bstep (se 1 (by rfl) ⟨1671959, by rfl⟩ : syracuseStep 2229279 = 3343919) B3343919
theorem B3343925 : Blo 2227435 3343925 := bbase (se 5 (by rfl) ⟨156746, by rfl⟩ : syracuseStep 3343925 = 313493) (by norm_num)
theorem B2229283 : Blo 2227435 2229283 := bstep (se 1 (by rfl) ⟨1671962, by rfl⟩ : syracuseStep 2229283 = 3343925) B3343925
theorem B5642885 : Blo 2227435 5642885 := bbase (se 4 (by rfl) ⟨529020, by rfl⟩ : syracuseStep 5642885 = 1058041) (by norm_num)
theorem B3761923 : Blo 2227435 3761923 := bstep (se 1 (by rfl) ⟨2821442, by rfl⟩ : syracuseStep 3761923 = 5642885) B5642885
theorem B5015897 : Blo 2227435 5015897 := bstep (se 2 (by rfl) ⟨1880961, by rfl⟩ : syracuseStep 5015897 = 3761923) B3761923
theorem B3343931 : Blo 2227435 3343931 := bstep (se 1 (by rfl) ⟨2507948, by rfl⟩ : syracuseStep 3343931 = 5015897) B5015897
theorem B2229287 : Blo 2227435 2229287 := bstep (se 1 (by rfl) ⟨1671965, by rfl⟩ : syracuseStep 2229287 = 3343931) B3343931
theorem B2507953 : Blo 2227435 2507953 := bbase (se 2 (by rfl) ⟨940482, by rfl⟩ : syracuseStep 2507953 = 1880965) (by norm_num)
theorem B3343937 : Blo 2227435 3343937 := bstep (se 2 (by rfl) ⟨1253976, by rfl⟩ : syracuseStep 3343937 = 2507953) B2507953
theorem B2229291 : Blo 2227435 2229291 := bstep (se 1 (by rfl) ⟨1671968, by rfl⟩ : syracuseStep 2229291 = 3343937) B3343937
theorem B2380601 : Blo 2227435 2380601 := bbase (se 2 (by rfl) ⟨892725, by rfl⟩ : syracuseStep 2380601 = 1785451) (by norm_num)
theorem B6348269 : Blo 2227435 6348269 := bstep (se 3 (by rfl) ⟨1190300, by rfl⟩ : syracuseStep 6348269 = 2380601) B2380601
theorem B4232179 : Blo 2227435 4232179 := bstep (se 1 (by rfl) ⟨3174134, by rfl⟩ : syracuseStep 4232179 = 6348269) B6348269
theorem B5642905 : Blo 2227435 5642905 := bstep (se 2 (by rfl) ⟨2116089, by rfl⟩ : syracuseStep 5642905 = 4232179) B4232179
theorem B7523873 : Blo 2227435 7523873 := bstep (se 2 (by rfl) ⟨2821452, by rfl⟩ : syracuseStep 7523873 = 5642905) B5642905
theorem B5015915 : Blo 2227435 5015915 := bstep (se 1 (by rfl) ⟨3761936, by rfl⟩ : syracuseStep 5015915 = 7523873) B7523873
theorem B3343943 : Blo 2227435 3343943 := bstep (se 1 (by rfl) ⟨2507957, by rfl⟩ : syracuseStep 3343943 = 5015915) B5015915
theorem B2229295 : Blo 2227435 2229295 := bstep (se 1 (by rfl) ⟨1671971, by rfl⟩ : syracuseStep 2229295 = 3343943) B3343943
theorem B3343949 : Blo 2227435 3343949 := bbase (se 3 (by rfl) ⟨626990, by rfl⟩ : syracuseStep 3343949 = 1253981) (by norm_num)
theorem B2229299 : Blo 2227435 2229299 := bstep (se 1 (by rfl) ⟨1671974, by rfl⟩ : syracuseStep 2229299 = 3343949) B3343949
theorem B5015933 : Blo 2227435 5015933 := bbase (se 3 (by rfl) ⟨940487, by rfl⟩ : syracuseStep 5015933 = 1880975) (by norm_num)
theorem B3343955 : Blo 2227435 3343955 := bstep (se 1 (by rfl) ⟨2507966, by rfl⟩ : syracuseStep 3343955 = 5015933) B5015933
theorem B2229303 : Blo 2227435 2229303 := bstep (se 1 (by rfl) ⟨1671977, by rfl⟩ : syracuseStep 2229303 = 3343955) B3343955
theorem B3761957 : Blo 2227435 3761957 := bbase (se 4 (by rfl) ⟨352683, by rfl⟩ : syracuseStep 3761957 = 705367) (by norm_num)
theorem B2507971 : Blo 2227435 2507971 := bstep (se 1 (by rfl) ⟨1880978, by rfl⟩ : syracuseStep 2507971 = 3761957) B3761957
theorem B3343961 : Blo 2227435 3343961 := bstep (se 2 (by rfl) ⟨1253985, by rfl⟩ : syracuseStep 3343961 = 2507971) B2507971
theorem B2229307 : Blo 2227435 2229307 := bstep (se 1 (by rfl) ⟨1671980, by rfl⟩ : syracuseStep 2229307 = 3343961) B3343961
theorem B3174157 : Blo 2227435 3174157 := bbase (se 3 (by rfl) ⟨595154, by rfl⟩ : syracuseStep 3174157 = 1190309) (by norm_num)
theorem B16928837 : Blo 2227435 16928837 := bstep (se 4 (by rfl) ⟨1587078, by rfl⟩ : syracuseStep 16928837 = 3174157) B3174157
theorem B11285891 : Blo 2227435 11285891 := bstep (se 1 (by rfl) ⟨8464418, by rfl⟩ : syracuseStep 11285891 = 16928837) B16928837
theorem B7523927 : Blo 2227435 7523927 := bstep (se 1 (by rfl) ⟨5642945, by rfl⟩ : syracuseStep 7523927 = 11285891) B11285891
theorem B5015951 : Blo 2227435 5015951 := bstep (se 1 (by rfl) ⟨3761963, by rfl⟩ : syracuseStep 5015951 = 7523927) B7523927
theorem B3343967 : Blo 2227435 3343967 := bstep (se 1 (by rfl) ⟨2507975, by rfl⟩ : syracuseStep 3343967 = 5015951) B5015951
theorem B2229311 : Blo 2227435 2229311 := bstep (se 1 (by rfl) ⟨1671983, by rfl⟩ : syracuseStep 2229311 = 3343967) B3343967
theorem B3343973 : Blo 2227435 3343973 := bbase (se 4 (by rfl) ⟨313497, by rfl⟩ : syracuseStep 3343973 = 626995) (by norm_num)
theorem B2229315 : Blo 2227435 2229315 := bstep (se 1 (by rfl) ⟨1671986, by rfl⟩ : syracuseStep 2229315 = 3343973) B3343973
theorem B3570941 : Blo 2227435 3570941 := bbase (se 3 (by rfl) ⟨669551, by rfl⟩ : syracuseStep 3570941 = 1339103) (by norm_num)
theorem B2380627 : Blo 2227435 2380627 := bstep (se 1 (by rfl) ⟨1785470, by rfl⟩ : syracuseStep 2380627 = 3570941) B3570941
theorem B3174169 : Blo 2227435 3174169 := bstep (se 2 (by rfl) ⟨1190313, by rfl⟩ : syracuseStep 3174169 = 2380627) B2380627
theorem B4232225 : Blo 2227435 4232225 := bstep (se 2 (by rfl) ⟨1587084, by rfl⟩ : syracuseStep 4232225 = 3174169) B3174169
theorem B2821483 : Blo 2227435 2821483 := bstep (se 1 (by rfl) ⟨2116112, by rfl⟩ : syracuseStep 2821483 = 4232225) B4232225
theorem B3761977 : Blo 2227435 3761977 := bstep (se 2 (by rfl) ⟨1410741, by rfl⟩ : syracuseStep 3761977 = 2821483) B2821483
theorem B5015969 : Blo 2227435 5015969 := bstep (se 2 (by rfl) ⟨1880988, by rfl⟩ : syracuseStep 5015969 = 3761977) B3761977
theorem B3343979 : Blo 2227435 3343979 := bstep (se 1 (by rfl) ⟨2507984, by rfl⟩ : syracuseStep 3343979 = 5015969) B5015969
theorem B2229319 : Blo 2227435 2229319 := bstep (se 1 (by rfl) ⟨1671989, by rfl⟩ : syracuseStep 2229319 = 3343979) B3343979
theorem B2507989 : Blo 2227435 2507989 := bbase (se 7 (by rfl) ⟨29390, by rfl⟩ : syracuseStep 2507989 = 58781) (by norm_num)
theorem B3343985 : Blo 2227435 3343985 := bstep (se 2 (by rfl) ⟨1253994, by rfl⟩ : syracuseStep 3343985 = 2507989) B2507989
theorem B2229323 : Blo 2227435 2229323 := bstep (se 1 (by rfl) ⟨1671992, by rfl⟩ : syracuseStep 2229323 = 3343985) B3343985
theorem B2821493 : Blo 2227435 2821493 := bbase (se 5 (by rfl) ⟨132257, by rfl⟩ : syracuseStep 2821493 = 264515) (by norm_num)
theorem B7523981 : Blo 2227435 7523981 := bstep (se 3 (by rfl) ⟨1410746, by rfl⟩ : syracuseStep 7523981 = 2821493) B2821493
theorem B5015987 : Blo 2227435 5015987 := bstep (se 1 (by rfl) ⟨3761990, by rfl⟩ : syracuseStep 5015987 = 7523981) B7523981
theorem B3343991 : Blo 2227435 3343991 := bstep (se 1 (by rfl) ⟨2507993, by rfl⟩ : syracuseStep 3343991 = 5015987) B5015987
theorem B2229327 : Blo 2227435 2229327 := bstep (se 1 (by rfl) ⟨1671995, by rfl⟩ : syracuseStep 2229327 = 3343991) B3343991
theorem B3343997 : Blo 2227435 3343997 := bbase (se 3 (by rfl) ⟨626999, by rfl⟩ : syracuseStep 3343997 = 1253999) (by norm_num)
theorem B2229331 : Blo 2227435 2229331 := bstep (se 1 (by rfl) ⟨1671998, by rfl⟩ : syracuseStep 2229331 = 3343997) B3343997
theorem B5016005 : Blo 2227435 5016005 := bbase (se 4 (by rfl) ⟨470250, by rfl⟩ : syracuseStep 5016005 = 940501) (by norm_num)
theorem B3344003 : Blo 2227435 3344003 := bstep (se 1 (by rfl) ⟨2508002, by rfl⟩ : syracuseStep 3344003 = 5016005) B5016005
theorem B2229335 : Blo 2227435 2229335 := bstep (se 1 (by rfl) ⟨1672001, by rfl⟩ : syracuseStep 2229335 = 3344003) B3344003
theorem B5084453 : Blo 2227435 5084453 := bbase (se 4 (by rfl) ⟨476667, by rfl⟩ : syracuseStep 5084453 = 953335) (by norm_num)
theorem B3389635 : Blo 2227435 3389635 := bstep (se 1 (by rfl) ⟨2542226, by rfl⟩ : syracuseStep 3389635 = 5084453) B5084453
theorem B4519513 : Blo 2227435 4519513 := bstep (se 2 (by rfl) ⟨1694817, by rfl⟩ : syracuseStep 4519513 = 3389635) B3389635
theorem B6026017 : Blo 2227435 6026017 := bstep (se 2 (by rfl) ⟨2259756, by rfl⟩ : syracuseStep 6026017 = 4519513) B4519513
theorem B8034689 : Blo 2227435 8034689 := bstep (se 2 (by rfl) ⟨3013008, by rfl⟩ : syracuseStep 8034689 = 6026017) B6026017
theorem B5356459 : Blo 2227435 5356459 := bstep (se 1 (by rfl) ⟨4017344, by rfl⟩ : syracuseStep 5356459 = 8034689) B8034689
theorem B7141945 : Blo 2227435 7141945 := bstep (se 2 (by rfl) ⟨2678229, by rfl⟩ : syracuseStep 7141945 = 5356459) B5356459
theorem B9522593 : Blo 2227435 9522593 := bstep (se 2 (by rfl) ⟨3570972, by rfl⟩ : syracuseStep 9522593 = 7141945) B7141945
theorem B6348395 : Blo 2227435 6348395 := bstep (se 1 (by rfl) ⟨4761296, by rfl⟩ : syracuseStep 6348395 = 9522593) B9522593
theorem B4232263 : Blo 2227435 4232263 := bstep (se 1 (by rfl) ⟨3174197, by rfl⟩ : syracuseStep 4232263 = 6348395) B6348395
theorem B5643017 : Blo 2227435 5643017 := bstep (se 2 (by rfl) ⟨2116131, by rfl⟩ : syracuseStep 5643017 = 4232263) B4232263
theorem B3762011 : Blo 2227435 3762011 := bstep (se 1 (by rfl) ⟨2821508, by rfl⟩ : syracuseStep 3762011 = 5643017) B5643017
theorem B2508007 : Blo 2227435 2508007 := bstep (se 1 (by rfl) ⟨1881005, by rfl⟩ : syracuseStep 2508007 = 3762011) B3762011
theorem B3344009 : Blo 2227435 3344009 := bstep (se 2 (by rfl) ⟨1254003, by rfl⟩ : syracuseStep 3344009 = 2508007) B2508007
theorem B2229339 : Blo 2227435 2229339 := bstep (se 1 (by rfl) ⟨1672004, by rfl⟩ : syracuseStep 2229339 = 3344009) B3344009
theorem B11286053 : Blo 2227435 11286053 := bbase (se 4 (by rfl) ⟨1058067, by rfl⟩ : syracuseStep 11286053 = 2116135) (by norm_num)
theorem B7524035 : Blo 2227435 7524035 := bstep (se 1 (by rfl) ⟨5643026, by rfl⟩ : syracuseStep 7524035 = 11286053) B11286053
theorem B5016023 : Blo 2227435 5016023 := bstep (se 1 (by rfl) ⟨3762017, by rfl⟩ : syracuseStep 5016023 = 7524035) B7524035
theorem B3344015 : Blo 2227435 3344015 := bstep (se 1 (by rfl) ⟨2508011, by rfl⟩ : syracuseStep 3344015 = 5016023) B5016023
theorem B2229343 : Blo 2227435 2229343 := bstep (se 1 (by rfl) ⟨1672007, by rfl⟩ : syracuseStep 2229343 = 3344015) B3344015
theorem B3344021 : Blo 2227435 3344021 := bbase (se 6 (by rfl) ⟨78375, by rfl⟩ : syracuseStep 3344021 = 156751) (by norm_num)
theorem B2229347 : Blo 2227435 2229347 := bstep (se 1 (by rfl) ⟨1672010, by rfl⟩ : syracuseStep 2229347 = 3344021) B3344021
theorem B3054133 : Blo 2227435 3054133 := bbase (se 5 (by rfl) ⟨143162, by rfl⟩ : syracuseStep 3054133 = 286325) (by norm_num)
theorem B4072177 : Blo 2227435 4072177 := bstep (se 2 (by rfl) ⟨1527066, by rfl⟩ : syracuseStep 4072177 = 3054133) B3054133
theorem B21718277 : Blo 2227435 21718277 := bstep (se 4 (by rfl) ⟨2036088, by rfl⟩ : syracuseStep 21718277 = 4072177) B4072177
theorem B14478851 : Blo 2227435 14478851 := bstep (se 1 (by rfl) ⟨10859138, by rfl⟩ : syracuseStep 14478851 = 21718277) B21718277
theorem B38610269 : Blo 2227435 38610269 := bstep (se 3 (by rfl) ⟨7239425, by rfl⟩ : syracuseStep 38610269 = 14478851) B14478851
theorem B25740179 : Blo 2227435 25740179 := bstep (se 1 (by rfl) ⟨19305134, by rfl⟩ : syracuseStep 25740179 = 38610269) B38610269
theorem B17160119 : Blo 2227435 17160119 := bstep (se 1 (by rfl) ⟨12870089, by rfl⟩ : syracuseStep 17160119 = 25740179) B25740179
theorem B11440079 : Blo 2227435 11440079 := bstep (se 1 (by rfl) ⟨8580059, by rfl⟩ : syracuseStep 11440079 = 17160119) B17160119
theorem B7626719 : Blo 2227435 7626719 := bstep (se 1 (by rfl) ⟨5720039, by rfl⟩ : syracuseStep 7626719 = 11440079) B11440079
theorem B5084479 : Blo 2227435 5084479 := bstep (se 1 (by rfl) ⟨3813359, by rfl⟩ : syracuseStep 5084479 = 7626719) B7626719
theorem B6779305 : Blo 2227435 6779305 := bstep (se 2 (by rfl) ⟨2542239, by rfl⟩ : syracuseStep 6779305 = 5084479) B5084479
theorem B9039073 : Blo 2227435 9039073 := bstep (se 2 (by rfl) ⟨3389652, by rfl⟩ : syracuseStep 9039073 = 6779305) B6779305
theorem B12052097 : Blo 2227435 12052097 := bstep (se 2 (by rfl) ⟨4519536, by rfl⟩ : syracuseStep 12052097 = 9039073) B9039073
theorem B8034731 : Blo 2227435 8034731 := bstep (se 1 (by rfl) ⟨6026048, by rfl⟩ : syracuseStep 8034731 = 12052097) B12052097
theorem B5356487 : Blo 2227435 5356487 := bstep (se 1 (by rfl) ⟨4017365, by rfl⟩ : syracuseStep 5356487 = 8034731) B8034731
theorem B14283965 : Blo 2227435 14283965 := bstep (se 3 (by rfl) ⟨2678243, by rfl⟩ : syracuseStep 14283965 = 5356487) B5356487
theorem B9522643 : Blo 2227435 9522643 := bstep (se 1 (by rfl) ⟨7141982, by rfl⟩ : syracuseStep 9522643 = 14283965) B14283965
theorem B12696857 : Blo 2227435 12696857 := bstep (se 2 (by rfl) ⟨4761321, by rfl⟩ : syracuseStep 12696857 = 9522643) B9522643
theorem B8464571 : Blo 2227435 8464571 := bstep (se 1 (by rfl) ⟨6348428, by rfl⟩ : syracuseStep 8464571 = 12696857) B12696857
theorem B5643047 : Blo 2227435 5643047 := bstep (se 1 (by rfl) ⟨4232285, by rfl⟩ : syracuseStep 5643047 = 8464571) B8464571
theorem B3762031 : Blo 2227435 3762031 := bstep (se 1 (by rfl) ⟨2821523, by rfl⟩ : syracuseStep 3762031 = 5643047) B5643047
theorem B5016041 : Blo 2227435 5016041 := bstep (se 2 (by rfl) ⟨1881015, by rfl⟩ : syracuseStep 5016041 = 3762031) B3762031
theorem B3344027 : Blo 2227435 3344027 := bstep (se 1 (by rfl) ⟨2508020, by rfl⟩ : syracuseStep 3344027 = 5016041) B5016041
theorem B2229351 : Blo 2227435 2229351 := bstep (se 1 (by rfl) ⟨1672013, by rfl⟩ : syracuseStep 2229351 = 3344027) B3344027
theorem B2508025 : Blo 2227435 2508025 := bbase (se 2 (by rfl) ⟨940509, by rfl⟩ : syracuseStep 2508025 = 1881019) (by norm_num)
theorem B3344033 : Blo 2227435 3344033 := bstep (se 2 (by rfl) ⟨1254012, by rfl⟩ : syracuseStep 3344033 = 2508025) B2508025
theorem B2229355 : Blo 2227435 2229355 := bstep (se 1 (by rfl) ⟨1672016, by rfl⟩ : syracuseStep 2229355 = 3344033) B3344033
theorem B9522677 : Blo 2227435 9522677 := bbase (se 5 (by rfl) ⟨446375, by rfl⟩ : syracuseStep 9522677 = 892751) (by norm_num)
theorem B6348451 : Blo 2227435 6348451 := bstep (se 1 (by rfl) ⟨4761338, by rfl⟩ : syracuseStep 6348451 = 9522677) B9522677
theorem B8464601 : Blo 2227435 8464601 := bstep (se 2 (by rfl) ⟨3174225, by rfl⟩ : syracuseStep 8464601 = 6348451) B6348451
theorem B5643067 : Blo 2227435 5643067 := bstep (se 1 (by rfl) ⟨4232300, by rfl⟩ : syracuseStep 5643067 = 8464601) B8464601
theorem B7524089 : Blo 2227435 7524089 := bstep (se 2 (by rfl) ⟨2821533, by rfl⟩ : syracuseStep 7524089 = 5643067) B5643067
theorem B5016059 : Blo 2227435 5016059 := bstep (se 1 (by rfl) ⟨3762044, by rfl⟩ : syracuseStep 5016059 = 7524089) B7524089
theorem B3344039 : Blo 2227435 3344039 := bstep (se 1 (by rfl) ⟨2508029, by rfl⟩ : syracuseStep 3344039 = 5016059) B5016059
theorem B2229359 : Blo 2227435 2229359 := bstep (se 1 (by rfl) ⟨1672019, by rfl⟩ : syracuseStep 2229359 = 3344039) B3344039
theorem B3344045 : Blo 2227435 3344045 := bbase (se 3 (by rfl) ⟨627008, by rfl⟩ : syracuseStep 3344045 = 1254017) (by norm_num)
theorem B2229363 : Blo 2227435 2229363 := bstep (se 1 (by rfl) ⟨1672022, by rfl⟩ : syracuseStep 2229363 = 3344045) B3344045
theorem B5016077 : Blo 2227435 5016077 := bbase (se 3 (by rfl) ⟨940514, by rfl⟩ : syracuseStep 5016077 = 1881029) (by norm_num)
theorem B3344051 : Blo 2227435 3344051 := bstep (se 1 (by rfl) ⟨2508038, by rfl⟩ : syracuseStep 3344051 = 5016077) B5016077
theorem B2229367 : Blo 2227435 2229367 := bstep (se 1 (by rfl) ⟨1672025, by rfl⟩ : syracuseStep 2229367 = 3344051) B3344051
theorem B2821549 : Blo 2227435 2821549 := bbase (se 3 (by rfl) ⟨529040, by rfl⟩ : syracuseStep 2821549 = 1058081) (by norm_num)
theorem B3762065 : Blo 2227435 3762065 := bstep (se 2 (by rfl) ⟨1410774, by rfl⟩ : syracuseStep 3762065 = 2821549) B2821549
theorem B2508043 : Blo 2227435 2508043 := bstep (se 1 (by rfl) ⟨1881032, by rfl⟩ : syracuseStep 2508043 = 3762065) B3762065
theorem B3344057 : Blo 2227435 3344057 := bstep (se 2 (by rfl) ⟨1254021, by rfl⟩ : syracuseStep 3344057 = 2508043) B2508043
theorem B2229371 : Blo 2227435 2229371 := bstep (se 1 (by rfl) ⟨1672028, by rfl⟩ : syracuseStep 2229371 = 3344057) B3344057
theorem B14284117 : Blo 2227435 14284117 := bbase (se 13 (by rfl) ⟨2615, by rfl⟩ : syracuseStep 14284117 = 5231) (by norm_num)
theorem B19045489 : Blo 2227435 19045489 := bstep (se 2 (by rfl) ⟨7142058, by rfl⟩ : syracuseStep 19045489 = 14284117) B14284117
theorem B25393985 : Blo 2227435 25393985 := bstep (se 2 (by rfl) ⟨9522744, by rfl⟩ : syracuseStep 25393985 = 19045489) B19045489
theorem B16929323 : Blo 2227435 16929323 := bstep (se 1 (by rfl) ⟨12696992, by rfl⟩ : syracuseStep 16929323 = 25393985) B25393985
theorem B11286215 : Blo 2227435 11286215 := bstep (se 1 (by rfl) ⟨8464661, by rfl⟩ : syracuseStep 11286215 = 16929323) B16929323
theorem B7524143 : Blo 2227435 7524143 := bstep (se 1 (by rfl) ⟨5643107, by rfl⟩ : syracuseStep 7524143 = 11286215) B11286215
theorem B5016095 : Blo 2227435 5016095 := bstep (se 1 (by rfl) ⟨3762071, by rfl⟩ : syracuseStep 5016095 = 7524143) B7524143
theorem B3344063 : Blo 2227435 3344063 := bstep (se 1 (by rfl) ⟨2508047, by rfl⟩ : syracuseStep 3344063 = 5016095) B5016095
theorem B2229375 : Blo 2227435 2229375 := bstep (se 1 (by rfl) ⟨1672031, by rfl⟩ : syracuseStep 2229375 = 3344063) B3344063
theorem B3344069 : Blo 2227435 3344069 := bbase (se 4 (by rfl) ⟨313506, by rfl⟩ : syracuseStep 3344069 = 627013) (by norm_num)
theorem B2229379 : Blo 2227435 2229379 := bstep (se 1 (by rfl) ⟨1672034, by rfl⟩ : syracuseStep 2229379 = 3344069) B3344069
theorem B3762085 : Blo 2227435 3762085 := bbase (se 4 (by rfl) ⟨352695, by rfl⟩ : syracuseStep 3762085 = 705391) (by norm_num)
theorem B5016113 : Blo 2227435 5016113 := bstep (se 2 (by rfl) ⟨1881042, by rfl⟩ : syracuseStep 5016113 = 3762085) B3762085
theorem B3344075 : Blo 2227435 3344075 := bstep (se 1 (by rfl) ⟨2508056, by rfl⟩ : syracuseStep 3344075 = 5016113) B5016113
theorem B2229383 : Blo 2227435 2229383 := bstep (se 1 (by rfl) ⟨1672037, by rfl⟩ : syracuseStep 2229383 = 3344075) B3344075
theorem B2508061 : Blo 2227435 2508061 := bbase (se 3 (by rfl) ⟨470261, by rfl⟩ : syracuseStep 2508061 = 940523) (by norm_num)
theorem B3344081 : Blo 2227435 3344081 := bstep (se 2 (by rfl) ⟨1254030, by rfl⟩ : syracuseStep 3344081 = 2508061) B2508061
theorem B2229387 : Blo 2227435 2229387 := bstep (se 1 (by rfl) ⟨1672040, by rfl⟩ : syracuseStep 2229387 = 3344081) B3344081
theorem B7524197 : Blo 2227435 7524197 := bbase (se 4 (by rfl) ⟨705393, by rfl⟩ : syracuseStep 7524197 = 1410787) (by norm_num)
theorem B5016131 : Blo 2227435 5016131 := bstep (se 1 (by rfl) ⟨3762098, by rfl⟩ : syracuseStep 5016131 = 7524197) B7524197
theorem B3344087 : Blo 2227435 3344087 := bstep (se 1 (by rfl) ⟨2508065, by rfl⟩ : syracuseStep 3344087 = 5016131) B5016131
theorem B2229391 : Blo 2227435 2229391 := bstep (se 1 (by rfl) ⟨1672043, by rfl⟩ : syracuseStep 2229391 = 3344087) B3344087
theorem B3344093 : Blo 2227435 3344093 := bbase (se 3 (by rfl) ⟨627017, by rfl⟩ : syracuseStep 3344093 = 1254035) (by norm_num)
theorem B2229395 : Blo 2227435 2229395 := bstep (se 1 (by rfl) ⟨1672046, by rfl⟩ : syracuseStep 2229395 = 3344093) B3344093
theorem B5016149 : Blo 2227435 5016149 := bbase (se 8 (by rfl) ⟨29391, by rfl⟩ : syracuseStep 5016149 = 58783) (by norm_num)
theorem B3344099 : Blo 2227435 3344099 := bstep (se 1 (by rfl) ⟨2508074, by rfl⟩ : syracuseStep 3344099 = 5016149) B5016149
theorem B2229399 : Blo 2227435 2229399 := bstep (se 1 (by rfl) ⟨1672049, by rfl⟩ : syracuseStep 2229399 = 3344099) B3344099
theorem B5356613 : Blo 2227435 5356613 := bbase (se 4 (by rfl) ⟨502182, by rfl⟩ : syracuseStep 5356613 = 1004365) (by norm_num)
theorem B3571075 : Blo 2227435 3571075 := bstep (se 1 (by rfl) ⟨2678306, by rfl⟩ : syracuseStep 3571075 = 5356613) B5356613
theorem B4761433 : Blo 2227435 4761433 := bstep (se 2 (by rfl) ⟨1785537, by rfl⟩ : syracuseStep 4761433 = 3571075) B3571075
theorem B6348577 : Blo 2227435 6348577 := bstep (se 2 (by rfl) ⟨2380716, by rfl⟩ : syracuseStep 6348577 = 4761433) B4761433
theorem B8464769 : Blo 2227435 8464769 := bstep (se 2 (by rfl) ⟨3174288, by rfl⟩ : syracuseStep 8464769 = 6348577) B6348577
theorem B5643179 : Blo 2227435 5643179 := bstep (se 1 (by rfl) ⟨4232384, by rfl⟩ : syracuseStep 5643179 = 8464769) B8464769
theorem B3762119 : Blo 2227435 3762119 := bstep (se 1 (by rfl) ⟨2821589, by rfl⟩ : syracuseStep 3762119 = 5643179) B5643179
theorem B2508079 : Blo 2227435 2508079 := bstep (se 1 (by rfl) ⟨1881059, by rfl⟩ : syracuseStep 2508079 = 3762119) B3762119
theorem B3344105 : Blo 2227435 3344105 := bstep (se 2 (by rfl) ⟨1254039, by rfl⟩ : syracuseStep 3344105 = 2508079) B2508079
theorem B2229403 : Blo 2227435 2229403 := bstep (se 1 (by rfl) ⟨1672052, by rfl⟩ : syracuseStep 2229403 = 3344105) B3344105
theorem B5356621 : Blo 2227435 5356621 := bbase (se 3 (by rfl) ⟨1004366, by rfl⟩ : syracuseStep 5356621 = 2008733) (by norm_num)
theorem B28568645 : Blo 2227435 28568645 := bstep (se 4 (by rfl) ⟨2678310, by rfl⟩ : syracuseStep 28568645 = 5356621) B5356621
theorem B19045763 : Blo 2227435 19045763 := bstep (se 1 (by rfl) ⟨14284322, by rfl⟩ : syracuseStep 19045763 = 28568645) B28568645
theorem B12697175 : Blo 2227435 12697175 := bstep (se 1 (by rfl) ⟨9522881, by rfl⟩ : syracuseStep 12697175 = 19045763) B19045763
theorem B8464783 : Blo 2227435 8464783 := bstep (se 1 (by rfl) ⟨6348587, by rfl⟩ : syracuseStep 8464783 = 12697175) B12697175
theorem B11286377 : Blo 2227435 11286377 := bstep (se 2 (by rfl) ⟨4232391, by rfl⟩ : syracuseStep 11286377 = 8464783) B8464783
theorem B7524251 : Blo 2227435 7524251 := bstep (se 1 (by rfl) ⟨5643188, by rfl⟩ : syracuseStep 7524251 = 11286377) B11286377
theorem B5016167 : Blo 2227435 5016167 := bstep (se 1 (by rfl) ⟨3762125, by rfl⟩ : syracuseStep 5016167 = 7524251) B7524251
theorem B3344111 : Blo 2227435 3344111 := bstep (se 1 (by rfl) ⟨2508083, by rfl⟩ : syracuseStep 3344111 = 5016167) B5016167
theorem B2229407 : Blo 2227435 2229407 := bstep (se 1 (by rfl) ⟨1672055, by rfl⟩ : syracuseStep 2229407 = 3344111) B3344111
theorem B3344117 : Blo 2227435 3344117 := bbase (se 5 (by rfl) ⟨156755, by rfl⟩ : syracuseStep 3344117 = 313511) (by norm_num)
theorem B2229411 : Blo 2227435 2229411 := bstep (se 1 (by rfl) ⟨1672058, by rfl⟩ : syracuseStep 2229411 = 3344117) B3344117
theorem B9522917 : Blo 2227435 9522917 := bbase (se 4 (by rfl) ⟨892773, by rfl⟩ : syracuseStep 9522917 = 1785547) (by norm_num)
theorem B6348611 : Blo 2227435 6348611 := bstep (se 1 (by rfl) ⟨4761458, by rfl⟩ : syracuseStep 6348611 = 9522917) B9522917
theorem B4232407 : Blo 2227435 4232407 := bstep (se 1 (by rfl) ⟨3174305, by rfl⟩ : syracuseStep 4232407 = 6348611) B6348611
theorem B5643209 : Blo 2227435 5643209 := bstep (se 2 (by rfl) ⟨2116203, by rfl⟩ : syracuseStep 5643209 = 4232407) B4232407
theorem B3762139 : Blo 2227435 3762139 := bstep (se 1 (by rfl) ⟨2821604, by rfl⟩ : syracuseStep 3762139 = 5643209) B5643209
theorem B5016185 : Blo 2227435 5016185 := bstep (se 2 (by rfl) ⟨1881069, by rfl⟩ : syracuseStep 5016185 = 3762139) B3762139
theorem B3344123 : Blo 2227435 3344123 := bstep (se 1 (by rfl) ⟨2508092, by rfl⟩ : syracuseStep 3344123 = 5016185) B5016185
theorem B2229415 : Blo 2227435 2229415 := bstep (se 1 (by rfl) ⟨1672061, by rfl⟩ : syracuseStep 2229415 = 3344123) B3344123
theorem B2508097 : Blo 2227435 2508097 := bbase (se 2 (by rfl) ⟨940536, by rfl⟩ : syracuseStep 2508097 = 1881073) (by norm_num)
theorem B3344129 : Blo 2227435 3344129 := bstep (se 2 (by rfl) ⟨1254048, by rfl⟩ : syracuseStep 3344129 = 2508097) B2508097
theorem B2229419 : Blo 2227435 2229419 := bstep (se 1 (by rfl) ⟨1672064, by rfl⟩ : syracuseStep 2229419 = 3344129) B3344129
theorem B5643229 : Blo 2227435 5643229 := bbase (se 3 (by rfl) ⟨1058105, by rfl⟩ : syracuseStep 5643229 = 2116211) (by norm_num)
theorem B7524305 : Blo 2227435 7524305 := bstep (se 2 (by rfl) ⟨2821614, by rfl⟩ : syracuseStep 7524305 = 5643229) B5643229
theorem B5016203 : Blo 2227435 5016203 := bstep (se 1 (by rfl) ⟨3762152, by rfl⟩ : syracuseStep 5016203 = 7524305) B7524305
theorem B3344135 : Blo 2227435 3344135 := bstep (se 1 (by rfl) ⟨2508101, by rfl⟩ : syracuseStep 3344135 = 5016203) B5016203
theorem B2229423 : Blo 2227435 2229423 := bstep (se 1 (by rfl) ⟨1672067, by rfl⟩ : syracuseStep 2229423 = 3344135) B3344135
theorem B3344141 : Blo 2227435 3344141 := bbase (se 3 (by rfl) ⟨627026, by rfl⟩ : syracuseStep 3344141 = 1254053) (by norm_num)
theorem B2229427 : Blo 2227435 2229427 := bstep (se 1 (by rfl) ⟨1672070, by rfl⟩ : syracuseStep 2229427 = 3344141) B3344141
theorem B5016221 : Blo 2227435 5016221 := bbase (se 3 (by rfl) ⟨940541, by rfl⟩ : syracuseStep 5016221 = 1881083) (by norm_num)
theorem B3344147 : Blo 2227435 3344147 := bstep (se 1 (by rfl) ⟨2508110, by rfl⟩ : syracuseStep 3344147 = 5016221) B5016221
theorem B2229431 : Blo 2227435 2229431 := bstep (se 1 (by rfl) ⟨1672073, by rfl⟩ : syracuseStep 2229431 = 3344147) B3344147
theorem B3762173 : Blo 2227435 3762173 := bbase (se 3 (by rfl) ⟨705407, by rfl⟩ : syracuseStep 3762173 = 1410815) (by norm_num)
theorem B2508115 : Blo 2227435 2508115 := bstep (se 1 (by rfl) ⟨1881086, by rfl⟩ : syracuseStep 2508115 = 3762173) B3762173
theorem B3344153 : Blo 2227435 3344153 := bstep (se 2 (by rfl) ⟨1254057, by rfl⟩ : syracuseStep 3344153 = 2508115) B2508115
theorem B2229435 : Blo 2227435 2229435 := bstep (se 1 (by rfl) ⟨1672076, by rfl⟩ : syracuseStep 2229435 = 3344153) B3344153
theorem C0 (j : ℕ) (h1 : 556858 ≤ j) (h2 : j ≤ 557358) : Blo 2227435 (4 * j + 3) := by
  interval_cases j
  · exact B2227435
  · exact B2227439
  · exact B2227443
  · exact B2227447
  · exact B2227451
  · exact B2227455
  · exact B2227459
  · exact B2227463
  · exact B2227467
  · exact B2227471
  · exact B2227475
  · exact B2227479
  · exact B2227483
  · exact B2227487
  · exact B2227491
  · exact B2227495
  · exact B2227499
  · exact B2227503
  · exact B2227507
  · exact B2227511
  · exact B2227515
  · exact B2227519
  · exact B2227523
  · exact B2227527
  · exact B2227531
  · exact B2227535
  · exact B2227539
  · exact B2227543
  · exact B2227547
  · exact B2227551
  · exact B2227555
  · exact B2227559
  · exact B2227563
  · exact B2227567
  · exact B2227571
  · exact B2227575
  · exact B2227579
  · exact B2227583
  · exact B2227587
  · exact B2227591
  · exact B2227595
  · exact B2227599
  · exact B2227603
  · exact B2227607
  · exact B2227611
  · exact B2227615
  · exact B2227619
  · exact B2227623
  · exact B2227627
  · exact B2227631
  · exact B2227635
  · exact B2227639
  · exact B2227643
  · exact B2227647
  · exact B2227651
  · exact B2227655
  · exact B2227659
  · exact B2227663
  · exact B2227667
  · exact B2227671
  · exact B2227675
  · exact B2227679
  · exact B2227683
  · exact B2227687
  · exact B2227691
  · exact B2227695
  · exact B2227699
  · exact B2227703
  · exact B2227707
  · exact B2227711
  · exact B2227715
  · exact B2227719
  · exact B2227723
  · exact B2227727
  · exact B2227731
  · exact B2227735
  · exact B2227739
  · exact B2227743
  · exact B2227747
  · exact B2227751
  · exact B2227755
  · exact B2227759
  · exact B2227763
  · exact B2227767
  · exact B2227771
  · exact B2227775
  · exact B2227779
  · exact B2227783
  · exact B2227787
  · exact B2227791
  · exact B2227795
  · exact B2227799
  · exact B2227803
  · exact B2227807
  · exact B2227811
  · exact B2227815
  · exact B2227819
  · exact B2227823
  · exact B2227827
  · exact B2227831
  · exact B2227835
  · exact B2227839
  · exact B2227843
  · exact B2227847
  · exact B2227851
  · exact B2227855
  · exact B2227859
  · exact B2227863
  · exact B2227867
  · exact B2227871
  · exact B2227875
  · exact B2227879
  · exact B2227883
  · exact B2227887
  · exact B2227891
  · exact B2227895
  · exact B2227899
  · exact B2227903
  · exact B2227907
  · exact B2227911
  · exact B2227915
  · exact B2227919
  · exact B2227923
  · exact B2227927
  · exact B2227931
  · exact B2227935
  · exact B2227939
  · exact B2227943
  · exact B2227947
  · exact B2227951
  · exact B2227955
  · exact B2227959
  · exact B2227963
  · exact B2227967
  · exact B2227971
  · exact B2227975
  · exact B2227979
  · exact B2227983
  · exact B2227987
  · exact B2227991
  · exact B2227995
  · exact B2227999
  · exact B2228003
  · exact B2228007
  · exact B2228011
  · exact B2228015
  · exact B2228019
  · exact B2228023
  · exact B2228027
  · exact B2228031
  · exact B2228035
  · exact B2228039
  · exact B2228043
  · exact B2228047
  · exact B2228051
  · exact B2228055
  · exact B2228059
  · exact B2228063
  · exact B2228067
  · exact B2228071
  · exact B2228075
  · exact B2228079
  · exact B2228083
  · exact B2228087
  · exact B2228091
  · exact B2228095
  · exact B2228099
  · exact B2228103
  · exact B2228107
  · exact B2228111
  · exact B2228115
  · exact B2228119
  · exact B2228123
  · exact B2228127
  · exact B2228131
  · exact B2228135
  · exact B2228139
  · exact B2228143
  · exact B2228147
  · exact B2228151
  · exact B2228155
  · exact B2228159
  · exact B2228163
  · exact B2228167
  · exact B2228171
  · exact B2228175
  · exact B2228179
  · exact B2228183
  · exact B2228187
  · exact B2228191
  · exact B2228195
  · exact B2228199
  · exact B2228203
  · exact B2228207
  · exact B2228211
  · exact B2228215
  · exact B2228219
  · exact B2228223
  · exact B2228227
  · exact B2228231
  · exact B2228235
  · exact B2228239
  · exact B2228243
  · exact B2228247
  · exact B2228251
  · exact B2228255
  · exact B2228259
  · exact B2228263
  · exact B2228267
  · exact B2228271
  · exact B2228275
  · exact B2228279
  · exact B2228283
  · exact B2228287
  · exact B2228291
  · exact B2228295
  · exact B2228299
  · exact B2228303
  · exact B2228307
  · exact B2228311
  · exact B2228315
  · exact B2228319
  · exact B2228323
  · exact B2228327
  · exact B2228331
  · exact B2228335
  · exact B2228339
  · exact B2228343
  · exact B2228347
  · exact B2228351
  · exact B2228355
  · exact B2228359
  · exact B2228363
  · exact B2228367
  · exact B2228371
  · exact B2228375
  · exact B2228379
  · exact B2228383
  · exact B2228387
  · exact B2228391
  · exact B2228395
  · exact B2228399
  · exact B2228403
  · exact B2228407
  · exact B2228411
  · exact B2228415
  · exact B2228419
  · exact B2228423
  · exact B2228427
  · exact B2228431
  · exact B2228435
  · exact B2228439
  · exact B2228443
  · exact B2228447
  · exact B2228451
  · exact B2228455
  · exact B2228459
  · exact B2228463
  · exact B2228467
  · exact B2228471
  · exact B2228475
  · exact B2228479
  · exact B2228483
  · exact B2228487
  · exact B2228491
  · exact B2228495
  · exact B2228499
  · exact B2228503
  · exact B2228507
  · exact B2228511
  · exact B2228515
  · exact B2228519
  · exact B2228523
  · exact B2228527
  · exact B2228531
  · exact B2228535
  · exact B2228539
  · exact B2228543
  · exact B2228547
  · exact B2228551
  · exact B2228555
  · exact B2228559
  · exact B2228563
  · exact B2228567
  · exact B2228571
  · exact B2228575
  · exact B2228579
  · exact B2228583
  · exact B2228587
  · exact B2228591
  · exact B2228595
  · exact B2228599
  · exact B2228603
  · exact B2228607
  · exact B2228611
  · exact B2228615
  · exact B2228619
  · exact B2228623
  · exact B2228627
  · exact B2228631
  · exact B2228635
  · exact B2228639
  · exact B2228643
  · exact B2228647
  · exact B2228651
  · exact B2228655
  · exact B2228659
  · exact B2228663
  · exact B2228667
  · exact B2228671
  · exact B2228675
  · exact B2228679
  · exact B2228683
  · exact B2228687
  · exact B2228691
  · exact B2228695
  · exact B2228699
  · exact B2228703
  · exact B2228707
  · exact B2228711
  · exact B2228715
  · exact B2228719
  · exact B2228723
  · exact B2228727
  · exact B2228731
  · exact B2228735
  · exact B2228739
  · exact B2228743
  · exact B2228747
  · exact B2228751
  · exact B2228755
  · exact B2228759
  · exact B2228763
  · exact B2228767
  · exact B2228771
  · exact B2228775
  · exact B2228779
  · exact B2228783
  · exact B2228787
  · exact B2228791
  · exact B2228795
  · exact B2228799
  · exact B2228803
  · exact B2228807
  · exact B2228811
  · exact B2228815
  · exact B2228819
  · exact B2228823
  · exact B2228827
  · exact B2228831
  · exact B2228835
  · exact B2228839
  · exact B2228843
  · exact B2228847
  · exact B2228851
  · exact B2228855
  · exact B2228859
  · exact B2228863
  · exact B2228867
  · exact B2228871
  · exact B2228875
  · exact B2228879
  · exact B2228883
  · exact B2228887
  · exact B2228891
  · exact B2228895
  · exact B2228899
  · exact B2228903
  · exact B2228907
  · exact B2228911
  · exact B2228915
  · exact B2228919
  · exact B2228923
  · exact B2228927
  · exact B2228931
  · exact B2228935
  · exact B2228939
  · exact B2228943
  · exact B2228947
  · exact B2228951
  · exact B2228955
  · exact B2228959
  · exact B2228963
  · exact B2228967
  · exact B2228971
  · exact B2228975
  · exact B2228979
  · exact B2228983
  · exact B2228987
  · exact B2228991
  · exact B2228995
  · exact B2228999
  · exact B2229003
  · exact B2229007
  · exact B2229011
  · exact B2229015
  · exact B2229019
  · exact B2229023
  · exact B2229027
  · exact B2229031
  · exact B2229035
  · exact B2229039
  · exact B2229043
  · exact B2229047
  · exact B2229051
  · exact B2229055
  · exact B2229059
  · exact B2229063
  · exact B2229067
  · exact B2229071
  · exact B2229075
  · exact B2229079
  · exact B2229083
  · exact B2229087
  · exact B2229091
  · exact B2229095
  · exact B2229099
  · exact B2229103
  · exact B2229107
  · exact B2229111
  · exact B2229115
  · exact B2229119
  · exact B2229123
  · exact B2229127
  · exact B2229131
  · exact B2229135
  · exact B2229139
  · exact B2229143
  · exact B2229147
  · exact B2229151
  · exact B2229155
  · exact B2229159
  · exact B2229163
  · exact B2229167
  · exact B2229171
  · exact B2229175
  · exact B2229179
  · exact B2229183
  · exact B2229187
  · exact B2229191
  · exact B2229195
  · exact B2229199
  · exact B2229203
  · exact B2229207
  · exact B2229211
  · exact B2229215
  · exact B2229219
  · exact B2229223
  · exact B2229227
  · exact B2229231
  · exact B2229235
  · exact B2229239
  · exact B2229243
  · exact B2229247
  · exact B2229251
  · exact B2229255
  · exact B2229259
  · exact B2229263
  · exact B2229267
  · exact B2229271
  · exact B2229275
  · exact B2229279
  · exact B2229283
  · exact B2229287
  · exact B2229291
  · exact B2229295
  · exact B2229299
  · exact B2229303
  · exact B2229307
  · exact B2229311
  · exact B2229315
  · exact B2229319
  · exact B2229323
  · exact B2229327
  · exact B2229331
  · exact B2229335
  · exact B2229339
  · exact B2229343
  · exact B2229347
  · exact B2229351
  · exact B2229355
  · exact B2229359
  · exact B2229363
  · exact B2229367
  · exact B2229371
  · exact B2229375
  · exact B2229379
  · exact B2229383
  · exact B2229387
  · exact B2229391
  · exact B2229395
  · exact B2229399
  · exact B2229403
  · exact B2229407
  · exact B2229411
  · exact B2229415
  · exact B2229419
  · exact B2229423
  · exact B2229427
  · exact B2229431
  · exact B2229435
theorem solution (m : ℕ) (hlo : 2227435 ≤ m) (hhi : m ≤ 2229435) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 556858 ≤ j := by omega
    have hj2 : j ≤ 557358 := by omega
    have hb : Blo 2227435 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
