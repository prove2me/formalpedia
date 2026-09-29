-- Prove2me | solution 1 for syracuse_descends_range_385764_389764
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:47:44.274721+00:00
-- url     : https://prove2.me/submissions/35f905f9-c065-4b67-9d90-97661a3f4994

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


theorem B1310741 : Blo 385764 1310741 := bbase (se 6 (by rfl) ⟨30720, by rfl⟩ : syracuseStep 1310741 = 61441) (by norm_num)
theorem B983117 : Blo 385764 983117 := bbase (se 3 (by rfl) ⟨184334, by rfl⟩ : syracuseStep 983117 = 368669) (by norm_num)
theorem B1572949 : Blo 385764 1572949 := bbase (se 8 (by rfl) ⟨9216, by rfl⟩ : syracuseStep 1572949 = 18433) (by norm_num)
theorem B1474645 : Blo 385764 1474645 := bbase (se 8 (by rfl) ⟨8640, by rfl⟩ : syracuseStep 1474645 = 17281) (by norm_num)
theorem B655445 : Blo 385764 655445 := bbase (se 8 (by rfl) ⟨3840, by rfl⟩ : syracuseStep 655445 = 7681) (by norm_num)
theorem B491609 : Blo 385764 491609 := bbase (se 2 (by rfl) ⟨184353, by rfl⟩ : syracuseStep 491609 = 368707) (by norm_num)
theorem B491665 : Blo 385764 491665 := bbase (se 2 (by rfl) ⟨184374, by rfl⟩ : syracuseStep 491665 = 368749) (by norm_num)
theorem B655573 : Blo 385764 655573 := bbase (se 7 (by rfl) ⟨7682, by rfl⟩ : syracuseStep 655573 = 15365) (by norm_num)
theorem B786653 : Blo 385764 786653 := bbase (se 3 (by rfl) ⟨147497, by rfl⟩ : syracuseStep 786653 = 294995) (by norm_num)
theorem B491761 : Blo 385764 491761 := bbase (se 2 (by rfl) ⟨184410, by rfl⟩ : syracuseStep 491761 = 368821) (by norm_num)
theorem B655661 : Blo 385764 655661 := bbase (se 3 (by rfl) ⟨122936, by rfl⟩ : syracuseStep 655661 = 245873) (by norm_num)
theorem B1474949 : Blo 385764 1474949 := bbase (se 4 (by rfl) ⟨138276, by rfl⟩ : syracuseStep 1474949 = 276553) (by norm_num)
theorem B491933 : Blo 385764 491933 := bbase (se 3 (by rfl) ⟨92237, by rfl⟩ : syracuseStep 491933 = 184475) (by norm_num)
theorem B983461 : Blo 385764 983461 := bbase (se 4 (by rfl) ⟨92199, by rfl⟩ : syracuseStep 983461 = 184399) (by norm_num)
theorem B655789 : Blo 385764 655789 := bbase (se 3 (by rfl) ⟨122960, by rfl⟩ : syracuseStep 655789 = 245921) (by norm_num)
theorem B1966517 : Blo 385764 1966517 := bbase (se 5 (by rfl) ⟨92180, by rfl⟩ : syracuseStep 1966517 = 184361) (by norm_num)
theorem B1311173 : Blo 385764 1311173 := bbase (se 4 (by rfl) ⟨122922, by rfl⟩ : syracuseStep 1311173 = 245845) (by norm_num)
theorem B1671637 : Blo 385764 1671637 := bbase (se 7 (by rfl) ⟨19589, by rfl⟩ : syracuseStep 1671637 = 39179) (by norm_num)
theorem B491989 : Blo 385764 491989 := bbase (se 7 (by rfl) ⟨5765, by rfl⟩ : syracuseStep 491989 = 11531) (by norm_num)
theorem B655877 : Blo 385764 655877 := bbase (se 4 (by rfl) ⟨61488, by rfl⟩ : syracuseStep 655877 = 122977) (by norm_num)
theorem B983573 : Blo 385764 983573 := bbase (se 6 (by rfl) ⟨23052, by rfl⟩ : syracuseStep 983573 = 46105) (by norm_num)
theorem B492085 : Blo 385764 492085 := bbase (se 5 (by rfl) ⟨23066, by rfl⟩ : syracuseStep 492085 = 46133) (by norm_num)
theorem B656005 : Blo 385764 656005 := bbase (se 4 (by rfl) ⟨61500, by rfl⟩ : syracuseStep 656005 = 123001) (by norm_num)
theorem B6292181 : Blo 385764 6292181 := bbase (se 7 (by rfl) ⟨73736, by rfl⟩ : syracuseStep 6292181 = 147473) (by norm_num)
theorem B983765 : Blo 385764 983765 := bbase (se 7 (by rfl) ⟨11528, by rfl⟩ : syracuseStep 983765 = 23057) (by norm_num)
theorem B656093 : Blo 385764 656093 := bbase (se 3 (by rfl) ⟨123017, by rfl⟩ : syracuseStep 656093 = 246035) (by norm_num)
theorem B492257 : Blo 385764 492257 := bbase (se 2 (by rfl) ⟨184596, by rfl⟩ : syracuseStep 492257 = 369193) (by norm_num)
theorem B7144213 : Blo 385764 7144213 := bbase (se 6 (by rfl) ⟨167442, by rfl⟩ : syracuseStep 7144213 = 334885) (by norm_num)
theorem B492313 : Blo 385764 492313 := bbase (se 2 (by rfl) ⟨184617, by rfl⟩ : syracuseStep 492313 = 369235) (by norm_num)
theorem B394069 : Blo 385764 394069 := bbase (se 9 (by rfl) ⟨1154, by rfl⟩ : syracuseStep 394069 = 2309) (by norm_num)
theorem B656221 : Blo 385764 656221 := bbase (se 3 (by rfl) ⟨123041, by rfl⟩ : syracuseStep 656221 = 246083) (by norm_num)
theorem B1311605 : Blo 385764 1311605 := bbase (se 5 (by rfl) ⟨61481, by rfl⟩ : syracuseStep 1311605 = 122963) (by norm_num)
theorem B492409 : Blo 385764 492409 := bbase (se 2 (by rfl) ⟨184653, by rfl⟩ : syracuseStep 492409 = 369307) (by norm_num)
theorem B656309 : Blo 385764 656309 := bbase (se 5 (by rfl) ⟨30764, by rfl⟩ : syracuseStep 656309 = 61529) (by norm_num)
theorem B623629 : Blo 385764 623629 := bbase (se 3 (by rfl) ⟨116930, by rfl⟩ : syracuseStep 623629 = 233861) (by norm_num)
theorem B492581 : Blo 385764 492581 := bbase (se 4 (by rfl) ⟨46179, by rfl⟩ : syracuseStep 492581 = 92359) (by norm_num)
theorem B984109 : Blo 385764 984109 := bbase (se 3 (by rfl) ⟨184520, by rfl⟩ : syracuseStep 984109 = 369041) (by norm_num)
theorem B656437 : Blo 385764 656437 := bbase (se 5 (by rfl) ⟨30770, by rfl⟩ : syracuseStep 656437 = 61541) (by norm_num)
theorem B492637 : Blo 385764 492637 := bbase (se 3 (by rfl) ⟨92369, by rfl⟩ : syracuseStep 492637 = 184739) (by norm_num)
theorem B656525 : Blo 385764 656525 := bbase (se 3 (by rfl) ⟨123098, by rfl⟩ : syracuseStep 656525 = 246197) (by norm_num)
theorem B984221 : Blo 385764 984221 := bbase (se 3 (by rfl) ⟨184541, by rfl⟩ : syracuseStep 984221 = 369083) (by norm_num)
theorem B492733 : Blo 385764 492733 := bbase (se 3 (by rfl) ⟨92387, by rfl⟩ : syracuseStep 492733 = 184775) (by norm_num)
theorem B656653 : Blo 385764 656653 := bbase (se 3 (by rfl) ⟨123122, by rfl⟩ : syracuseStep 656653 = 246245) (by norm_num)
theorem B3736853 : Blo 385764 3736853 := bbase (se 6 (by rfl) ⟨87582, by rfl⟩ : syracuseStep 3736853 = 175165) (by norm_num)
theorem B1312037 : Blo 385764 1312037 := bbase (se 4 (by rfl) ⟨123003, by rfl⟩ : syracuseStep 1312037 = 246007) (by norm_num)
theorem B1574213 : Blo 385764 1574213 := bbase (se 4 (by rfl) ⟨147582, by rfl⟩ : syracuseStep 1574213 = 295165) (by norm_num)
theorem B984413 : Blo 385764 984413 := bbase (se 3 (by rfl) ⟨184577, by rfl⟩ : syracuseStep 984413 = 369155) (by norm_num)
theorem B656741 : Blo 385764 656741 := bbase (se 4 (by rfl) ⟨61569, by rfl⟩ : syracuseStep 656741 = 123139) (by norm_num)
theorem B492905 : Blo 385764 492905 := bbase (se 2 (by rfl) ⟨184839, by rfl⟩ : syracuseStep 492905 = 369679) (by norm_num)
theorem B525685 : Blo 385764 525685 := bbase (se 5 (by rfl) ⟨24641, by rfl⟩ : syracuseStep 525685 = 49283) (by norm_num)
theorem B492961 : Blo 385764 492961 := bbase (se 2 (by rfl) ⟨184860, by rfl⟩ : syracuseStep 492961 = 369721) (by norm_num)
theorem B1246693 : Blo 385764 1246693 := bbase (se 4 (by rfl) ⟨116877, by rfl⟩ : syracuseStep 1246693 = 233755) (by norm_num)
theorem B656869 : Blo 385764 656869 := bbase (se 4 (by rfl) ⟨61581, by rfl⟩ : syracuseStep 656869 = 123163) (by norm_num)
theorem B493057 : Blo 385764 493057 := bbase (se 2 (by rfl) ⟨184896, by rfl⟩ : syracuseStep 493057 = 369793) (by norm_num)
theorem B656957 : Blo 385764 656957 := bbase (se 3 (by rfl) ⟨123179, by rfl⟩ : syracuseStep 656957 = 246359) (by norm_num)
theorem B886373 : Blo 385764 886373 := bbase (se 4 (by rfl) ⟨83097, by rfl⟩ : syracuseStep 886373 = 166195) (by norm_num)
theorem B2360981 : Blo 385764 2360981 := bbase (se 6 (by rfl) ⟨55335, by rfl⟩ : syracuseStep 2360981 = 110671) (by norm_num)
theorem B493229 : Blo 385764 493229 := bbase (se 3 (by rfl) ⟨92480, by rfl⟩ : syracuseStep 493229 = 184961) (by norm_num)
theorem B984757 : Blo 385764 984757 := bbase (se 5 (by rfl) ⟨46160, by rfl⟩ : syracuseStep 984757 = 92321) (by norm_num)
theorem B657085 : Blo 385764 657085 := bbase (se 3 (by rfl) ⟨123203, by rfl⟩ : syracuseStep 657085 = 246407) (by norm_num)
theorem B1967813 : Blo 385764 1967813 := bbase (se 4 (by rfl) ⟨184482, by rfl⟩ : syracuseStep 1967813 = 368965) (by norm_num)
theorem B1312469 : Blo 385764 1312469 := bbase (se 7 (by rfl) ⟨15380, by rfl⟩ : syracuseStep 1312469 = 30761) (by norm_num)
theorem B493285 : Blo 385764 493285 := bbase (se 4 (by rfl) ⟨46245, by rfl⟩ : syracuseStep 493285 = 92491) (by norm_num)
theorem B657173 : Blo 385764 657173 := bbase (se 6 (by rfl) ⟨15402, by rfl⟩ : syracuseStep 657173 = 30805) (by norm_num)
theorem B984869 : Blo 385764 984869 := bbase (se 4 (by rfl) ⟨92331, by rfl⟩ : syracuseStep 984869 = 184663) (by norm_num)
theorem B2098997 : Blo 385764 2098997 := bbase (se 5 (by rfl) ⟨98390, by rfl⟩ : syracuseStep 2098997 = 196781) (by norm_num)
theorem B526133 : Blo 385764 526133 := bbase (se 5 (by rfl) ⟨24662, by rfl⟩ : syracuseStep 526133 = 49325) (by norm_num)
theorem B657301 : Blo 385764 657301 := bbase (se 6 (by rfl) ⟨15405, by rfl⟩ : syracuseStep 657301 = 30811) (by norm_num)
theorem B1771429 : Blo 385764 1771429 := bbase (se 4 (by rfl) ⟨166071, by rfl⟩ : syracuseStep 1771429 = 332143) (by norm_num)
theorem B985061 : Blo 385764 985061 := bbase (se 4 (by rfl) ⟨92349, by rfl⟩ : syracuseStep 985061 = 184699) (by norm_num)
theorem B657389 : Blo 385764 657389 := bbase (se 3 (by rfl) ⟨123260, by rfl⟩ : syracuseStep 657389 = 246521) (by norm_num)
theorem B657517 : Blo 385764 657517 := bbase (se 3 (by rfl) ⟨123284, by rfl⟩ : syracuseStep 657517 = 246569) (by norm_num)
theorem B1312901 : Blo 385764 1312901 := bbase (se 4 (by rfl) ⟨123084, by rfl⟩ : syracuseStep 1312901 = 246169) (by norm_num)
theorem B1411253 : Blo 385764 1411253 := bbase (se 5 (by rfl) ⟨66152, by rfl⟩ : syracuseStep 1411253 = 132305) (by norm_num)
theorem B657605 : Blo 385764 657605 := bbase (se 4 (by rfl) ⟨61650, by rfl⟩ : syracuseStep 657605 = 123301) (by norm_num)
theorem B2951477 : Blo 385764 2951477 := bbase (se 5 (by rfl) ⟨138350, by rfl⟩ : syracuseStep 2951477 = 276701) (by norm_num)
theorem B985405 : Blo 385764 985405 := bbase (se 3 (by rfl) ⟨184763, by rfl⟩ : syracuseStep 985405 = 369527) (by norm_num)
theorem B985517 : Blo 385764 985517 := bbase (se 3 (by rfl) ⟨184784, by rfl⟩ : syracuseStep 985517 = 369569) (by norm_num)
theorem B1477061 : Blo 385764 1477061 := bbase (se 4 (by rfl) ⟨138474, by rfl⟩ : syracuseStep 1477061 = 276949) (by norm_num)
theorem B788957 : Blo 385764 788957 := bbase (se 3 (by rfl) ⟨147929, by rfl⟩ : syracuseStep 788957 = 295859) (by norm_num)
theorem B1313333 : Blo 385764 1313333 := bbase (se 5 (by rfl) ⟨61562, by rfl⟩ : syracuseStep 1313333 = 123125) (by norm_num)
theorem B985709 : Blo 385764 985709 := bbase (se 3 (by rfl) ⟨184820, by rfl⟩ : syracuseStep 985709 = 369641) (by norm_num)
theorem B1477349 : Blo 385764 1477349 := bbase (se 4 (by rfl) ⟨138501, by rfl⟩ : syracuseStep 1477349 = 277003) (by norm_num)
theorem B986053 : Blo 385764 986053 := bbase (se 4 (by rfl) ⟨92442, by rfl⟩ : syracuseStep 986053 = 184885) (by norm_num)
theorem B1969109 : Blo 385764 1969109 := bbase (se 7 (by rfl) ⟨23075, by rfl⟩ : syracuseStep 1969109 = 46151) (by norm_num)
theorem B1313765 : Blo 385764 1313765 := bbase (se 4 (by rfl) ⟨123165, by rfl⟩ : syracuseStep 1313765 = 246331) (by norm_num)
theorem B986165 : Blo 385764 986165 := bbase (se 5 (by rfl) ⟨46226, by rfl⟩ : syracuseStep 986165 = 92453) (by norm_num)
theorem B986357 : Blo 385764 986357 := bbase (se 5 (by rfl) ⟨46235, by rfl⟩ : syracuseStep 986357 = 92471) (by norm_num)
theorem B757021 : Blo 385764 757021 := bbase (se 3 (by rfl) ⟨141941, by rfl⟩ : syracuseStep 757021 = 283883) (by norm_num)
theorem B1314197 : Blo 385764 1314197 := bbase (se 6 (by rfl) ⟨30801, by rfl⟩ : syracuseStep 1314197 = 61603) (by norm_num)
theorem B1576421 : Blo 385764 1576421 := bbase (se 4 (by rfl) ⟨147789, by rfl⟩ : syracuseStep 1576421 = 295579) (by norm_num)
theorem B2100853 : Blo 385764 2100853 := bbase (se 5 (by rfl) ⟨98477, by rfl⟩ : syracuseStep 2100853 = 196955) (by norm_num)
theorem B495353 : Blo 385764 495353 := bbase (se 2 (by rfl) ⟨185757, by rfl⟩ : syracuseStep 495353 = 371515) (by norm_num)
theorem B1314629 : Blo 385764 1314629 := bbase (se 4 (by rfl) ⟨123246, by rfl⟩ : syracuseStep 1314629 = 246493) (by norm_num)
theorem B397181 : Blo 385764 397181 := bbase (se 3 (by rfl) ⟨74471, by rfl⟩ : syracuseStep 397181 = 148943) (by norm_num)
theorem B1478533 : Blo 385764 1478533 := bbase (se 4 (by rfl) ⟨138612, by rfl⟩ : syracuseStep 1478533 = 277225) (by norm_num)
theorem B1478837 : Blo 385764 1478837 := bbase (se 5 (by rfl) ⟨69320, by rfl⟩ : syracuseStep 1478837 = 138641) (by norm_num)
theorem B1970405 : Blo 385764 1970405 := bbase (se 4 (by rfl) ⟨184725, by rfl⟩ : syracuseStep 1970405 = 369451) (by norm_num)
theorem B1315061 : Blo 385764 1315061 := bbase (se 5 (by rfl) ⟨61643, by rfl⟩ : syracuseStep 1315061 = 123287) (by norm_num)
theorem B1773893 : Blo 385764 1773893 := bbase (se 4 (by rfl) ⟨166302, by rfl⟩ : syracuseStep 1773893 = 332605) (by norm_num)
theorem B1053109 : Blo 385764 1053109 := bbase (se 5 (by rfl) ⟨49364, by rfl⟩ : syracuseStep 1053109 = 98729) (by norm_num)
theorem B824021 : Blo 385764 824021 := bbase (se 7 (by rfl) ⟨9656, by rfl⟩ : syracuseStep 824021 = 19313) (by norm_num)
theorem B463585 : Blo 385764 463585 := bbase (se 2 (by rfl) ⟨173844, by rfl⟩ : syracuseStep 463585 = 347689) (by norm_num)
theorem B2495285 : Blo 385764 2495285 := bbase (se 5 (by rfl) ⟨116966, by rfl⟩ : syracuseStep 2495285 = 233933) (by norm_num)
theorem B398233 : Blo 385764 398233 := bbase (se 2 (by rfl) ⟨149337, by rfl⟩ : syracuseStep 398233 = 298675) (by norm_num)
theorem B463969 : Blo 385764 463969 := bbase (se 2 (by rfl) ⟨173988, by rfl⟩ : syracuseStep 463969 = 347977) (by norm_num)
theorem B463973 : Blo 385764 463973 := bbase (se 4 (by rfl) ⟨43497, by rfl⟩ : syracuseStep 463973 = 86995) (by norm_num)
theorem B595421 : Blo 385764 595421 := bbase (se 3 (by rfl) ⟨111641, by rfl⟩ : syracuseStep 595421 = 223283) (by norm_num)
theorem B1971701 : Blo 385764 1971701 := bbase (se 5 (by rfl) ⟨92423, by rfl⟩ : syracuseStep 1971701 = 184847) (by norm_num)
theorem B464377 : Blo 385764 464377 := bbase (se 2 (by rfl) ⟨174141, by rfl⟩ : syracuseStep 464377 = 348283) (by norm_num)
theorem B1676837 : Blo 385764 1676837 := bbase (se 4 (by rfl) ⟨157203, by rfl⟩ : syracuseStep 1676837 = 314407) (by norm_num)
theorem B824909 : Blo 385764 824909 := bbase (se 3 (by rfl) ⟨154670, by rfl⟩ : syracuseStep 824909 = 309341) (by norm_num)
theorem B825149 : Blo 385764 825149 := bbase (se 3 (by rfl) ⟨154715, by rfl⟩ : syracuseStep 825149 = 309431) (by norm_num)
theorem B825653 : Blo 385764 825653 := bbase (se 5 (by rfl) ⟨38702, by rfl⟩ : syracuseStep 825653 = 77405) (by norm_num)
theorem B825661 : Blo 385764 825661 := bbase (se 3 (by rfl) ⟨154811, by rfl⟩ : syracuseStep 825661 = 309623) (by norm_num)
theorem B1972997 : Blo 385764 1972997 := bbase (se 4 (by rfl) ⟨184968, by rfl⟩ : syracuseStep 1972997 = 369937) (by norm_num)
theorem B465761 : Blo 385764 465761 := bbase (se 2 (by rfl) ⟨174660, by rfl⟩ : syracuseStep 465761 = 349321) (by norm_num)
theorem B1579925 : Blo 385764 1579925 := bbase (se 6 (by rfl) ⟨37029, by rfl⟩ : syracuseStep 1579925 = 74059) (by norm_num)
theorem B695261 : Blo 385764 695261 := bbase (se 3 (by rfl) ⟨130361, by rfl⟩ : syracuseStep 695261 = 260723) (by norm_num)
theorem B695341 : Blo 385764 695341 := bbase (se 3 (by rfl) ⟨130376, by rfl⟩ : syracuseStep 695341 = 260753) (by norm_num)
theorem B466021 : Blo 385764 466021 := bbase (se 4 (by rfl) ⟨43689, by rfl⟩ : syracuseStep 466021 = 87379) (by norm_num)
theorem B466069 : Blo 385764 466069 := bbase (se 6 (by rfl) ⟨10923, by rfl⟩ : syracuseStep 466069 = 21847) (by norm_num)
theorem B498841 : Blo 385764 498841 := bbase (se 2 (by rfl) ⟨187065, by rfl⟩ : syracuseStep 498841 = 374131) (by norm_num)
theorem B466273 : Blo 385764 466273 := bbase (se 2 (by rfl) ⟨174852, by rfl⟩ : syracuseStep 466273 = 349705) (by norm_num)
theorem B826789 : Blo 385764 826789 := bbase (se 4 (by rfl) ⟨77511, by rfl⟩ : syracuseStep 826789 = 155023) (by norm_num)
theorem B1121861 : Blo 385764 1121861 := bbase (se 4 (by rfl) ⟨105174, by rfl⟩ : syracuseStep 1121861 = 210349) (by norm_num)
theorem B2989781 : Blo 385764 2989781 := bbase (se 7 (by rfl) ⟨35036, by rfl⟩ : syracuseStep 2989781 = 70073) (by norm_num)
theorem B827165 : Blo 385764 827165 := bbase (se 3 (by rfl) ⟨155093, by rfl⟩ : syracuseStep 827165 = 310187) (by norm_num)
theorem B466741 : Blo 385764 466741 := bbase (se 5 (by rfl) ⟨21878, by rfl⟩ : syracuseStep 466741 = 43757) (by norm_num)
theorem B433993 : Blo 385764 433993 := bbase (se 2 (by rfl) ⟨162747, by rfl⟩ : syracuseStep 433993 = 325495) (by norm_num)
theorem B794461 : Blo 385764 794461 := bbase (se 3 (by rfl) ⟨148961, by rfl⟩ : syracuseStep 794461 = 297923) (by norm_num)
theorem B434029 : Blo 385764 434029 := bbase (se 3 (by rfl) ⟨81380, by rfl⟩ : syracuseStep 434029 = 162761) (by norm_num)
theorem B434065 : Blo 385764 434065 := bbase (se 2 (by rfl) ⟨162774, by rfl⟩ : syracuseStep 434065 = 325549) (by norm_num)
theorem B434101 : Blo 385764 434101 := bbase (se 5 (by rfl) ⟨20348, by rfl⟩ : syracuseStep 434101 = 40697) (by norm_num)
theorem B434137 : Blo 385764 434137 := bbase (se 2 (by rfl) ⟨162801, by rfl⟩ : syracuseStep 434137 = 325603) (by norm_num)
theorem B434173 : Blo 385764 434173 := bbase (se 3 (by rfl) ⟨81407, by rfl⟩ : syracuseStep 434173 = 162815) (by norm_num)
theorem B434209 : Blo 385764 434209 := bbase (se 2 (by rfl) ⟨162828, by rfl⟩ : syracuseStep 434209 = 325657) (by norm_num)
theorem B1450037 : Blo 385764 1450037 := bbase (se 5 (by rfl) ⟨67970, by rfl⟩ : syracuseStep 1450037 = 135941) (by norm_num)
theorem B434245 : Blo 385764 434245 := bbase (se 4 (by rfl) ⟨40710, by rfl⟩ : syracuseStep 434245 = 81421) (by norm_num)
theorem B696421 : Blo 385764 696421 := bbase (se 4 (by rfl) ⟨65289, by rfl⟩ : syracuseStep 696421 = 130579) (by norm_num)
theorem B434281 : Blo 385764 434281 := bbase (se 2 (by rfl) ⟨162855, by rfl⟩ : syracuseStep 434281 = 325711) (by norm_num)
theorem B1777781 : Blo 385764 1777781 := bbase (se 5 (by rfl) ⟨83333, by rfl⟩ : syracuseStep 1777781 = 166667) (by norm_num)
theorem B434317 : Blo 385764 434317 := bbase (se 3 (by rfl) ⟨81434, by rfl⟩ : syracuseStep 434317 = 162869) (by norm_num)
theorem B434353 : Blo 385764 434353 := bbase (se 2 (by rfl) ⟨162882, by rfl⟩ : syracuseStep 434353 = 325765) (by norm_num)
theorem B696509 : Blo 385764 696509 := bbase (se 3 (by rfl) ⟨130595, by rfl⟩ : syracuseStep 696509 = 261191) (by norm_num)
theorem B434389 : Blo 385764 434389 := bbase (se 7 (by rfl) ⟨5090, by rfl⟩ : syracuseStep 434389 = 10181) (by norm_num)
theorem B434425 : Blo 385764 434425 := bbase (se 2 (by rfl) ⟨162909, by rfl⟩ : syracuseStep 434425 = 325819) (by norm_num)
theorem B434461 : Blo 385764 434461 := bbase (se 3 (by rfl) ⟨81461, by rfl⟩ : syracuseStep 434461 = 162923) (by norm_num)
theorem B434497 : Blo 385764 434497 := bbase (se 2 (by rfl) ⟨162936, by rfl⟩ : syracuseStep 434497 = 325873) (by norm_num)
theorem B434533 : Blo 385764 434533 := bbase (se 4 (by rfl) ⟨40737, by rfl⟩ : syracuseStep 434533 = 81475) (by norm_num)
theorem B434569 : Blo 385764 434569 := bbase (se 2 (by rfl) ⟨162963, by rfl⟩ : syracuseStep 434569 = 325927) (by norm_num)
theorem B434605 : Blo 385764 434605 := bbase (se 3 (by rfl) ⟨81488, by rfl⟩ : syracuseStep 434605 = 162977) (by norm_num)
theorem B434641 : Blo 385764 434641 := bbase (se 2 (by rfl) ⟨162990, by rfl⟩ : syracuseStep 434641 = 325981) (by norm_num)
theorem B434677 : Blo 385764 434677 := bbase (se 5 (by rfl) ⟨20375, by rfl⟩ : syracuseStep 434677 = 40751) (by norm_num)
theorem B434713 : Blo 385764 434713 := bbase (se 2 (by rfl) ⟨163017, by rfl⟩ : syracuseStep 434713 = 326035) (by norm_num)
theorem B3875381 : Blo 385764 3875381 := bbase (se 5 (by rfl) ⟨181658, by rfl⟩ : syracuseStep 3875381 = 363317) (by norm_num)
theorem B434749 : Blo 385764 434749 := bbase (se 3 (by rfl) ⟨81515, by rfl⟩ : syracuseStep 434749 = 163031) (by norm_num)
theorem B434785 : Blo 385764 434785 := bbase (se 2 (by rfl) ⟨163044, by rfl⟩ : syracuseStep 434785 = 326089) (by norm_num)
theorem B434821 : Blo 385764 434821 := bbase (se 4 (by rfl) ⟨40764, by rfl⟩ : syracuseStep 434821 = 81529) (by norm_num)
theorem B434857 : Blo 385764 434857 := bbase (se 2 (by rfl) ⟨163071, by rfl⟩ : syracuseStep 434857 = 326143) (by norm_num)
theorem B697013 : Blo 385764 697013 := bbase (se 5 (by rfl) ⟨32672, by rfl⟩ : syracuseStep 697013 = 65345) (by norm_num)
theorem B434893 : Blo 385764 434893 := bbase (se 3 (by rfl) ⟨81542, by rfl⟩ : syracuseStep 434893 = 163085) (by norm_num)
theorem B434929 : Blo 385764 434929 := bbase (se 2 (by rfl) ⟨163098, by rfl⟩ : syracuseStep 434929 = 326197) (by norm_num)
theorem B2204405 : Blo 385764 2204405 := bbase (se 5 (by rfl) ⟨103331, by rfl⟩ : syracuseStep 2204405 = 206663) (by norm_num)
theorem B434965 : Blo 385764 434965 := bbase (se 6 (by rfl) ⟨10194, by rfl⟩ : syracuseStep 434965 = 20389) (by norm_num)
theorem B795413 : Blo 385764 795413 := bbase (se 6 (by rfl) ⟨18642, by rfl⟩ : syracuseStep 795413 = 37285) (by norm_num)
theorem B467741 : Blo 385764 467741 := bbase (se 3 (by rfl) ⟨87701, by rfl⟩ : syracuseStep 467741 = 175403) (by norm_num)
theorem B435001 : Blo 385764 435001 := bbase (se 2 (by rfl) ⟨163125, by rfl⟩ : syracuseStep 435001 = 326251) (by norm_num)
theorem B435037 : Blo 385764 435037 := bbase (se 3 (by rfl) ⟨81569, by rfl⟩ : syracuseStep 435037 = 163139) (by norm_num)
theorem B467813 : Blo 385764 467813 := bbase (se 4 (by rfl) ⟨43857, by rfl⟩ : syracuseStep 467813 = 87715) (by norm_num)
theorem B435073 : Blo 385764 435073 := bbase (se 2 (by rfl) ⟨163152, by rfl⟩ : syracuseStep 435073 = 326305) (by norm_num)
theorem B435109 : Blo 385764 435109 := bbase (se 4 (by rfl) ⟨40791, by rfl⟩ : syracuseStep 435109 = 81583) (by norm_num)
theorem B435145 : Blo 385764 435145 := bbase (se 2 (by rfl) ⟨163179, by rfl⟩ : syracuseStep 435145 = 326359) (by norm_num)
theorem B435181 : Blo 385764 435181 := bbase (se 3 (by rfl) ⟨81596, by rfl⟩ : syracuseStep 435181 = 163193) (by norm_num)
theorem B435217 : Blo 385764 435217 := bbase (se 2 (by rfl) ⟨163206, by rfl⟩ : syracuseStep 435217 = 326413) (by norm_num)
theorem B2106389 : Blo 385764 2106389 := bbase (se 6 (by rfl) ⟨49368, by rfl⟩ : syracuseStep 2106389 = 98737) (by norm_num)
theorem B435253 : Blo 385764 435253 := bbase (se 5 (by rfl) ⟨20402, by rfl⟩ : syracuseStep 435253 = 40805) (by norm_num)
theorem B5022805 : Blo 385764 5022805 := bbase (se 8 (by rfl) ⟨29430, by rfl⟩ : syracuseStep 5022805 = 58861) (by norm_num)
theorem B435289 : Blo 385764 435289 := bbase (se 2 (by rfl) ⟨163233, by rfl⟩ : syracuseStep 435289 = 326467) (by norm_num)
theorem B435325 : Blo 385764 435325 := bbase (se 3 (by rfl) ⟨81623, by rfl⟩ : syracuseStep 435325 = 163247) (by norm_num)
theorem B468121 : Blo 385764 468121 := bbase (se 2 (by rfl) ⟨175545, by rfl⟩ : syracuseStep 468121 = 351091) (by norm_num)
theorem B435361 : Blo 385764 435361 := bbase (se 2 (by rfl) ⟨163260, by rfl⟩ : syracuseStep 435361 = 326521) (by norm_num)
theorem B435397 : Blo 385764 435397 := bbase (se 4 (by rfl) ⟨40818, by rfl⟩ : syracuseStep 435397 = 81637) (by norm_num)
theorem B435433 : Blo 385764 435433 := bbase (se 2 (by rfl) ⟨163287, by rfl⟩ : syracuseStep 435433 = 326575) (by norm_num)
theorem B435469 : Blo 385764 435469 := bbase (se 3 (by rfl) ⟨81650, by rfl⟩ : syracuseStep 435469 = 163301) (by norm_num)
theorem B435505 : Blo 385764 435505 := bbase (se 2 (by rfl) ⟨163314, by rfl⟩ : syracuseStep 435505 = 326629) (by norm_num)
theorem B435541 : Blo 385764 435541 := bbase (se 12 (by rfl) ⟨159, by rfl⟩ : syracuseStep 435541 = 319) (by norm_num)
theorem B435577 : Blo 385764 435577 := bbase (se 2 (by rfl) ⟨163341, by rfl⟩ : syracuseStep 435577 = 326683) (by norm_num)
theorem B927101 : Blo 385764 927101 := bbase (se 3 (by rfl) ⟨173831, by rfl⟩ : syracuseStep 927101 = 347663) (by norm_num)
theorem B828805 : Blo 385764 828805 := bbase (se 4 (by rfl) ⟨77700, by rfl⟩ : syracuseStep 828805 = 155401) (by norm_num)
theorem B435613 : Blo 385764 435613 := bbase (se 3 (by rfl) ⟨81677, by rfl⟩ : syracuseStep 435613 = 163355) (by norm_num)
theorem B435649 : Blo 385764 435649 := bbase (se 2 (by rfl) ⟨163368, by rfl⟩ : syracuseStep 435649 = 326737) (by norm_num)
theorem B435685 : Blo 385764 435685 := bbase (se 4 (by rfl) ⟨40845, by rfl⟩ : syracuseStep 435685 = 81691) (by norm_num)
theorem B435721 : Blo 385764 435721 := bbase (se 2 (by rfl) ⟨163395, by rfl⟩ : syracuseStep 435721 = 326791) (by norm_num)
theorem B435757 : Blo 385764 435757 := bbase (se 3 (by rfl) ⟨81704, by rfl⟩ : syracuseStep 435757 = 163409) (by norm_num)
theorem B435793 : Blo 385764 435793 := bbase (se 2 (by rfl) ⟨163422, by rfl⟩ : syracuseStep 435793 = 326845) (by norm_num)
theorem B435829 : Blo 385764 435829 := bbase (se 5 (by rfl) ⟨20429, by rfl⟩ : syracuseStep 435829 = 40859) (by norm_num)
theorem B1320581 : Blo 385764 1320581 := bbase (se 4 (by rfl) ⟨123804, by rfl⟩ : syracuseStep 1320581 = 247609) (by norm_num)
theorem B435865 : Blo 385764 435865 := bbase (se 2 (by rfl) ⟨163449, by rfl⟩ : syracuseStep 435865 = 326899) (by norm_num)
theorem B435901 : Blo 385764 435901 := bbase (se 3 (by rfl) ⟨81731, by rfl⟩ : syracuseStep 435901 = 163463) (by norm_num)
theorem B435937 : Blo 385764 435937 := bbase (se 2 (by rfl) ⟨163476, by rfl⟩ : syracuseStep 435937 = 326953) (by norm_num)
theorem B435973 : Blo 385764 435973 := bbase (se 4 (by rfl) ⟨40872, by rfl⟩ : syracuseStep 435973 = 81745) (by norm_num)
theorem B436009 : Blo 385764 436009 := bbase (se 2 (by rfl) ⟨163503, by rfl⟩ : syracuseStep 436009 = 327007) (by norm_num)
theorem B436045 : Blo 385764 436045 := bbase (se 3 (by rfl) ⟨81758, by rfl⟩ : syracuseStep 436045 = 163517) (by norm_num)
theorem B436081 : Blo 385764 436081 := bbase (se 2 (by rfl) ⟨163530, by rfl⟩ : syracuseStep 436081 = 327061) (by norm_num)
theorem B501653 : Blo 385764 501653 := bbase (se 6 (by rfl) ⟨11757, by rfl⟩ : syracuseStep 501653 = 23515) (by norm_num)
theorem B2205589 : Blo 385764 2205589 := bbase (se 6 (by rfl) ⟨51693, by rfl⟩ : syracuseStep 2205589 = 103387) (by norm_num)
theorem B436117 : Blo 385764 436117 := bbase (se 6 (by rfl) ⟨10221, by rfl⟩ : syracuseStep 436117 = 20443) (by norm_num)
theorem B2959253 : Blo 385764 2959253 := bbase (se 6 (by rfl) ⟨69357, by rfl⟩ : syracuseStep 2959253 = 138715) (by norm_num)
theorem B436153 : Blo 385764 436153 := bbase (se 2 (by rfl) ⟨163557, by rfl⟩ : syracuseStep 436153 = 327115) (by norm_num)
theorem B436189 : Blo 385764 436189 := bbase (se 3 (by rfl) ⟨81785, by rfl⟩ : syracuseStep 436189 = 163571) (by norm_num)
theorem B436225 : Blo 385764 436225 := bbase (se 2 (by rfl) ⟨163584, by rfl⟩ : syracuseStep 436225 = 327169) (by norm_num)
theorem B436261 : Blo 385764 436261 := bbase (se 4 (by rfl) ⟨40899, by rfl⟩ : syracuseStep 436261 = 81799) (by norm_num)
theorem B436297 : Blo 385764 436297 := bbase (se 2 (by rfl) ⟨163611, by rfl⟩ : syracuseStep 436297 = 327223) (by norm_num)
theorem B436333 : Blo 385764 436333 := bbase (se 3 (by rfl) ⟨81812, by rfl⟩ : syracuseStep 436333 = 163625) (by norm_num)
theorem B927869 : Blo 385764 927869 := bbase (se 3 (by rfl) ⟨173975, by rfl⟩ : syracuseStep 927869 = 347951) (by norm_num)
theorem B436369 : Blo 385764 436369 := bbase (se 2 (by rfl) ⟨163638, by rfl⟩ : syracuseStep 436369 = 327277) (by norm_num)
theorem B436405 : Blo 385764 436405 := bbase (se 5 (by rfl) ⟨20456, by rfl⟩ : syracuseStep 436405 = 40913) (by norm_num)
theorem B436441 : Blo 385764 436441 := bbase (se 2 (by rfl) ⟨163665, by rfl⟩ : syracuseStep 436441 = 327331) (by norm_num)
theorem B436477 : Blo 385764 436477 := bbase (se 3 (by rfl) ⟨81839, by rfl⟩ : syracuseStep 436477 = 163679) (by norm_num)
theorem B829693 : Blo 385764 829693 := bbase (se 3 (by rfl) ⟨155567, by rfl⟩ : syracuseStep 829693 = 311135) (by norm_num)
theorem B436513 : Blo 385764 436513 := bbase (se 2 (by rfl) ⟨163692, by rfl⟩ : syracuseStep 436513 = 327385) (by norm_num)
theorem B436549 : Blo 385764 436549 := bbase (se 4 (by rfl) ⟨40926, by rfl⟩ : syracuseStep 436549 = 81853) (by norm_num)
theorem B436585 : Blo 385764 436585 := bbase (se 2 (by rfl) ⟨163719, by rfl⟩ : syracuseStep 436585 = 327439) (by norm_num)
theorem B436621 : Blo 385764 436621 := bbase (se 3 (by rfl) ⟨81866, by rfl⟩ : syracuseStep 436621 = 163733) (by norm_num)
theorem B436657 : Blo 385764 436657 := bbase (se 2 (by rfl) ⟨163746, by rfl⟩ : syracuseStep 436657 = 327493) (by norm_num)
theorem B436693 : Blo 385764 436693 := bbase (se 7 (by rfl) ⟨5117, by rfl⟩ : syracuseStep 436693 = 10235) (by norm_num)
theorem B436729 : Blo 385764 436729 := bbase (se 2 (by rfl) ⟨163773, by rfl⟩ : syracuseStep 436729 = 327547) (by norm_num)
theorem B436765 : Blo 385764 436765 := bbase (se 3 (by rfl) ⟨81893, by rfl⟩ : syracuseStep 436765 = 163787) (by norm_num)
theorem B436801 : Blo 385764 436801 := bbase (se 2 (by rfl) ⟨163800, by rfl⟩ : syracuseStep 436801 = 327601) (by norm_num)
theorem B436837 : Blo 385764 436837 := bbase (se 4 (by rfl) ⟨40953, by rfl⟩ : syracuseStep 436837 = 81907) (by norm_num)
theorem B436873 : Blo 385764 436873 := bbase (se 2 (by rfl) ⟨163827, by rfl⟩ : syracuseStep 436873 = 327655) (by norm_num)
theorem B436909 : Blo 385764 436909 := bbase (se 3 (by rfl) ⟨81920, by rfl⟩ : syracuseStep 436909 = 163841) (by norm_num)
theorem B436945 : Blo 385764 436945 := bbase (se 2 (by rfl) ⟨163854, by rfl⟩ : syracuseStep 436945 = 327709) (by norm_num)
theorem B830189 : Blo 385764 830189 := bbase (se 3 (by rfl) ⟨155660, by rfl⟩ : syracuseStep 830189 = 311321) (by norm_num)
theorem B436981 : Blo 385764 436981 := bbase (se 5 (by rfl) ⟨20483, by rfl⟩ : syracuseStep 436981 = 40967) (by norm_num)
theorem B994069 : Blo 385764 994069 := bbase (se 6 (by rfl) ⟨23298, by rfl⟩ : syracuseStep 994069 = 46597) (by norm_num)
theorem B437017 : Blo 385764 437017 := bbase (se 2 (by rfl) ⟨163881, by rfl⟩ : syracuseStep 437017 = 327763) (by norm_num)
theorem B437053 : Blo 385764 437053 := bbase (se 3 (by rfl) ⟨81947, by rfl⟩ : syracuseStep 437053 = 163895) (by norm_num)
theorem B1649477 : Blo 385764 1649477 := bbase (se 4 (by rfl) ⟨154638, by rfl⟩ : syracuseStep 1649477 = 309277) (by norm_num)
theorem B699205 : Blo 385764 699205 := bbase (se 4 (by rfl) ⟨65550, by rfl⟩ : syracuseStep 699205 = 131101) (by norm_num)
theorem B437089 : Blo 385764 437089 := bbase (se 2 (by rfl) ⟨163908, by rfl⟩ : syracuseStep 437089 = 327817) (by norm_num)
theorem B1682309 : Blo 385764 1682309 := bbase (se 4 (by rfl) ⟨157716, by rfl⟩ : syracuseStep 1682309 = 315433) (by norm_num)
theorem B437125 : Blo 385764 437125 := bbase (se 4 (by rfl) ⟨40980, by rfl⟩ : syracuseStep 437125 = 81961) (by norm_num)
theorem B437161 : Blo 385764 437161 := bbase (se 2 (by rfl) ⟨163935, by rfl⟩ : syracuseStep 437161 = 327871) (by norm_num)
theorem B437197 : Blo 385764 437197 := bbase (se 3 (by rfl) ⟨81974, by rfl⟩ : syracuseStep 437197 = 163949) (by norm_num)
theorem B437233 : Blo 385764 437233 := bbase (se 2 (by rfl) ⟨163962, by rfl⟩ : syracuseStep 437233 = 327925) (by norm_num)
theorem B699413 : Blo 385764 699413 := bbase (se 6 (by rfl) ⟨16392, by rfl⟩ : syracuseStep 699413 = 32785) (by norm_num)
theorem B437269 : Blo 385764 437269 := bbase (se 6 (by rfl) ⟨10248, by rfl⟩ : syracuseStep 437269 = 20497) (by norm_num)
theorem B1649717 : Blo 385764 1649717 := bbase (se 5 (by rfl) ⟨77330, by rfl⟩ : syracuseStep 1649717 = 154661) (by norm_num)
theorem B437305 : Blo 385764 437305 := bbase (se 2 (by rfl) ⟨163989, by rfl⟩ : syracuseStep 437305 = 327979) (by norm_num)
theorem B437341 : Blo 385764 437341 := bbase (se 3 (by rfl) ⟨82001, by rfl⟩ : syracuseStep 437341 = 164003) (by norm_num)
theorem B437377 : Blo 385764 437377 := bbase (se 2 (by rfl) ⟨164016, by rfl⟩ : syracuseStep 437377 = 328033) (by norm_num)
theorem B437413 : Blo 385764 437413 := bbase (se 4 (by rfl) ⟨41007, by rfl⟩ : syracuseStep 437413 = 82015) (by norm_num)
theorem B437449 : Blo 385764 437449 := bbase (se 2 (by rfl) ⟨164043, by rfl⟩ : syracuseStep 437449 = 328087) (by norm_num)
theorem B437485 : Blo 385764 437485 := bbase (se 3 (by rfl) ⟨82028, by rfl⟩ : syracuseStep 437485 = 164057) (by norm_num)
theorem B437521 : Blo 385764 437521 := bbase (se 2 (by rfl) ⟨164070, by rfl⟩ : syracuseStep 437521 = 328141) (by norm_num)
theorem B437557 : Blo 385764 437557 := bbase (se 5 (by rfl) ⟨20510, by rfl⟩ : syracuseStep 437557 = 41021) (by norm_num)
theorem B732493 : Blo 385764 732493 := bbase (se 3 (by rfl) ⟨137342, by rfl⟩ : syracuseStep 732493 = 274685) (by norm_num)
theorem B437593 : Blo 385764 437593 := bbase (se 2 (by rfl) ⟨164097, by rfl⟩ : syracuseStep 437593 = 328195) (by norm_num)
theorem B437629 : Blo 385764 437629 := bbase (se 3 (by rfl) ⟨82055, by rfl⟩ : syracuseStep 437629 = 164111) (by norm_num)
theorem B699781 : Blo 385764 699781 := bbase (se 4 (by rfl) ⟨65604, by rfl⟩ : syracuseStep 699781 = 131209) (by norm_num)
theorem B437665 : Blo 385764 437665 := bbase (se 2 (by rfl) ⟨164124, by rfl⟩ : syracuseStep 437665 = 328249) (by norm_num)
theorem B437701 : Blo 385764 437701 := bbase (se 4 (by rfl) ⟨41034, by rfl⟩ : syracuseStep 437701 = 82069) (by norm_num)
theorem B437737 : Blo 385764 437737 := bbase (se 2 (by rfl) ⟨164151, by rfl⟩ : syracuseStep 437737 = 328303) (by norm_num)
theorem B437773 : Blo 385764 437773 := bbase (se 3 (by rfl) ⟨82082, by rfl⟩ : syracuseStep 437773 = 164165) (by norm_num)
theorem B437809 : Blo 385764 437809 := bbase (se 2 (by rfl) ⟨164178, by rfl⟩ : syracuseStep 437809 = 328357) (by norm_num)
theorem B831053 : Blo 385764 831053 := bbase (se 3 (by rfl) ⟨155822, by rfl⟩ : syracuseStep 831053 = 311645) (by norm_num)
theorem B437845 : Blo 385764 437845 := bbase (se 8 (by rfl) ⟨2565, by rfl⟩ : syracuseStep 437845 = 5131) (by norm_num)
theorem B437881 : Blo 385764 437881 := bbase (se 2 (by rfl) ⟨164205, by rfl⟩ : syracuseStep 437881 = 328411) (by norm_num)
theorem B732797 : Blo 385764 732797 := bbase (se 3 (by rfl) ⟨137399, by rfl⟩ : syracuseStep 732797 = 274799) (by norm_num)
theorem B437917 : Blo 385764 437917 := bbase (se 3 (by rfl) ⟨82109, by rfl⟩ : syracuseStep 437917 = 164219) (by norm_num)
theorem B437953 : Blo 385764 437953 := bbase (se 2 (by rfl) ⟨164232, by rfl⟩ : syracuseStep 437953 = 328465) (by norm_num)
theorem B831197 : Blo 385764 831197 := bbase (se 3 (by rfl) ⟨155849, by rfl⟩ : syracuseStep 831197 = 311699) (by norm_num)
theorem B437989 : Blo 385764 437989 := bbase (se 4 (by rfl) ⟨41061, by rfl⟩ : syracuseStep 437989 = 82123) (by norm_num)
theorem B438025 : Blo 385764 438025 := bbase (se 2 (by rfl) ⟨164259, by rfl⟩ : syracuseStep 438025 = 328519) (by norm_num)
theorem B438061 : Blo 385764 438061 := bbase (se 3 (by rfl) ⟨82136, by rfl⟩ : syracuseStep 438061 = 164273) (by norm_num)
theorem B438097 : Blo 385764 438097 := bbase (se 2 (by rfl) ⟨164286, by rfl⟩ : syracuseStep 438097 = 328573) (by norm_num)
theorem B2207573 : Blo 385764 2207573 := bbase (se 9 (by rfl) ⟨6467, by rfl⟩ : syracuseStep 2207573 = 12935) (by norm_num)
theorem B438133 : Blo 385764 438133 := bbase (se 5 (by rfl) ⟨20537, by rfl⟩ : syracuseStep 438133 = 41075) (by norm_num)
theorem B929677 : Blo 385764 929677 := bbase (se 3 (by rfl) ⟨174314, by rfl⟩ : syracuseStep 929677 = 348629) (by norm_num)
theorem B438169 : Blo 385764 438169 := bbase (se 2 (by rfl) ⟨164313, by rfl⟩ : syracuseStep 438169 = 328627) (by norm_num)
theorem B438205 : Blo 385764 438205 := bbase (se 3 (by rfl) ⟨82163, by rfl⟩ : syracuseStep 438205 = 164327) (by norm_num)
theorem B438241 : Blo 385764 438241 := bbase (se 2 (by rfl) ⟨164340, by rfl⟩ : syracuseStep 438241 = 328681) (by norm_num)
theorem B438277 : Blo 385764 438277 := bbase (se 4 (by rfl) ⟨41088, by rfl⟩ : syracuseStep 438277 = 82177) (by norm_num)
theorem B438313 : Blo 385764 438313 := bbase (se 2 (by rfl) ⟨164367, by rfl⟩ : syracuseStep 438313 = 328735) (by norm_num)
theorem B438349 : Blo 385764 438349 := bbase (se 3 (by rfl) ⟨82190, by rfl⟩ : syracuseStep 438349 = 164381) (by norm_num)
theorem B438385 : Blo 385764 438385 := bbase (se 2 (by rfl) ⟨164394, by rfl⟩ : syracuseStep 438385 = 328789) (by norm_num)
theorem B897173 : Blo 385764 897173 := bbase (se 6 (by rfl) ⟨21027, by rfl⟩ : syracuseStep 897173 = 42055) (by norm_num)
theorem B438421 : Blo 385764 438421 := bbase (se 6 (by rfl) ⟨10275, by rfl⟩ : syracuseStep 438421 = 20551) (by norm_num)
theorem B700573 : Blo 385764 700573 := bbase (se 3 (by rfl) ⟨131357, by rfl⟩ : syracuseStep 700573 = 262715) (by norm_num)
theorem B700589 : Blo 385764 700589 := bbase (se 3 (by rfl) ⟨131360, by rfl⟩ : syracuseStep 700589 = 262721) (by norm_num)
theorem B438457 : Blo 385764 438457 := bbase (se 2 (by rfl) ⟨164421, by rfl⟩ : syracuseStep 438457 = 328843) (by norm_num)
theorem B1323317 : Blo 385764 1323317 := bbase (se 5 (by rfl) ⟨62030, by rfl⟩ : syracuseStep 1323317 = 124061) (by norm_num)
theorem B733549 : Blo 385764 733549 := bbase (se 3 (by rfl) ⟨137540, by rfl⟩ : syracuseStep 733549 = 275081) (by norm_num)
theorem B700805 : Blo 385764 700805 := bbase (se 4 (by rfl) ⟨65700, by rfl⟩ : syracuseStep 700805 = 131401) (by norm_num)
theorem B930197 : Blo 385764 930197 := bbase (se 6 (by rfl) ⟨21801, by rfl⟩ : syracuseStep 930197 = 43603) (by norm_num)
theorem B831941 : Blo 385764 831941 := bbase (se 4 (by rfl) ⟨77994, by rfl⟩ : syracuseStep 831941 = 155989) (by norm_num)
theorem B1192421 : Blo 385764 1192421 := bbase (se 4 (by rfl) ⟨111789, by rfl⟩ : syracuseStep 1192421 = 223579) (by norm_num)
theorem B733693 : Blo 385764 733693 := bbase (se 3 (by rfl) ⟨137567, by rfl⟩ : syracuseStep 733693 = 275135) (by norm_num)
theorem B700949 : Blo 385764 700949 := bbase (se 6 (by rfl) ⟨16428, by rfl⟩ : syracuseStep 700949 = 32857) (by norm_num)
theorem B733853 : Blo 385764 733853 := bbase (se 3 (by rfl) ⟨137597, by rfl⟩ : syracuseStep 733853 = 275195) (by norm_num)
theorem B4436693 : Blo 385764 4436693 := bbase (se 7 (by rfl) ⟨51992, by rfl⟩ : syracuseStep 4436693 = 103985) (by norm_num)
theorem B996101 : Blo 385764 996101 := bbase (se 4 (by rfl) ⟨93384, by rfl⟩ : syracuseStep 996101 = 186769) (by norm_num)
theorem B930581 : Blo 385764 930581 := bbase (se 6 (by rfl) ⟨21810, by rfl⟩ : syracuseStep 930581 = 43621) (by norm_num)
theorem B733997 : Blo 385764 733997 := bbase (se 3 (by rfl) ⟨137624, by rfl⟩ : syracuseStep 733997 = 275249) (by norm_num)
theorem B930629 : Blo 385764 930629 := bbase (se 4 (by rfl) ⟨87246, by rfl⟩ : syracuseStep 930629 = 174493) (by norm_num)
theorem B930637 : Blo 385764 930637 := bbase (se 3 (by rfl) ⟨174494, by rfl⟩ : syracuseStep 930637 = 348989) (by norm_num)
theorem B734285 : Blo 385764 734285 := bbase (se 3 (by rfl) ⟨137678, by rfl⟩ : syracuseStep 734285 = 275357) (by norm_num)
theorem B734437 : Blo 385764 734437 := bbase (se 4 (by rfl) ⟨68853, by rfl⟩ : syracuseStep 734437 = 137707) (by norm_num)
theorem B701669 : Blo 385764 701669 := bbase (se 4 (by rfl) ⟨65781, by rfl⟩ : syracuseStep 701669 = 131563) (by norm_num)
theorem B1652005 : Blo 385764 1652005 := bbase (se 4 (by rfl) ⟨154875, by rfl⟩ : syracuseStep 1652005 = 309751) (by norm_num)
theorem B701957 : Blo 385764 701957 := bbase (se 4 (by rfl) ⟨65808, by rfl⟩ : syracuseStep 701957 = 131617) (by norm_num)
theorem B734741 : Blo 385764 734741 := bbase (se 6 (by rfl) ⟨17220, by rfl⟩ : syracuseStep 734741 = 34441) (by norm_num)
theorem B996965 : Blo 385764 996965 := bbase (se 4 (by rfl) ⟨93465, by rfl⟩ : syracuseStep 996965 = 186931) (by norm_num)
theorem B472717 : Blo 385764 472717 := bbase (se 3 (by rfl) ⟨88634, by rfl⟩ : syracuseStep 472717 = 177269) (by norm_num)
theorem B931637 : Blo 385764 931637 := bbase (se 5 (by rfl) ⟨43670, by rfl⟩ : syracuseStep 931637 = 87341) (by norm_num)
theorem B407485 : Blo 385764 407485 := bbase (se 3 (by rfl) ⟨76403, by rfl⟩ : syracuseStep 407485 = 152807) (by norm_num)
theorem B931829 : Blo 385764 931829 := bbase (se 5 (by rfl) ⟨43679, by rfl⟩ : syracuseStep 931829 = 87359) (by norm_num)
theorem B2209781 : Blo 385764 2209781 := bbase (se 5 (by rfl) ⟨103583, by rfl⟩ : syracuseStep 2209781 = 207167) (by norm_num)
theorem B1325317 : Blo 385764 1325317 := bbase (se 4 (by rfl) ⟨124248, by rfl⟩ : syracuseStep 1325317 = 248497) (by norm_num)
theorem B735493 : Blo 385764 735493 := bbase (se 4 (by rfl) ⟨68952, by rfl⟩ : syracuseStep 735493 = 137905) (by norm_num)
theorem B440641 : Blo 385764 440641 := bbase (se 2 (by rfl) ⟨165240, by rfl⟩ : syracuseStep 440641 = 330481) (by norm_num)
theorem B1849717 : Blo 385764 1849717 := bbase (se 5 (by rfl) ⟨86705, by rfl⟩ : syracuseStep 1849717 = 173411) (by norm_num)
theorem B735637 : Blo 385764 735637 := bbase (se 6 (by rfl) ⟨17241, by rfl⟩ : syracuseStep 735637 = 34483) (by norm_num)
theorem B1325605 : Blo 385764 1325605 := bbase (se 4 (by rfl) ⟨124275, by rfl⟩ : syracuseStep 1325605 = 248551) (by norm_num)
theorem B735797 : Blo 385764 735797 := bbase (se 5 (by rfl) ⟨34490, by rfl⟩ : syracuseStep 735797 = 68981) (by norm_num)
theorem B735941 : Blo 385764 735941 := bbase (se 4 (by rfl) ⟨68994, by rfl⟩ : syracuseStep 735941 = 137989) (by norm_num)
theorem B1653493 : Blo 385764 1653493 := bbase (se 5 (by rfl) ⟨77507, by rfl⟩ : syracuseStep 1653493 = 155015) (by norm_num)
theorem B1653509 : Blo 385764 1653509 := bbase (se 4 (by rfl) ⟨155016, by rfl⟩ : syracuseStep 1653509 = 310033) (by norm_num)
theorem B506741 : Blo 385764 506741 := bbase (se 5 (by rfl) ⟨23753, by rfl⟩ : syracuseStep 506741 = 47507) (by norm_num)
theorem B736229 : Blo 385764 736229 := bbase (se 4 (by rfl) ⟨69021, by rfl⟩ : syracuseStep 736229 = 138043) (by norm_num)
theorem B1621061 : Blo 385764 1621061 := bbase (se 4 (by rfl) ⟨151974, by rfl⟩ : syracuseStep 1621061 = 303949) (by norm_num)
theorem B1719413 : Blo 385764 1719413 := bbase (se 5 (by rfl) ⟨80597, by rfl⟩ : syracuseStep 1719413 = 161195) (by norm_num)
theorem B736381 : Blo 385764 736381 := bbase (se 3 (by rfl) ⟨138071, by rfl⟩ : syracuseStep 736381 = 276143) (by norm_num)
theorem B441517 : Blo 385764 441517 := bbase (se 3 (by rfl) ⟨82784, by rfl⟩ : syracuseStep 441517 = 165569) (by norm_num)
theorem B1785077 : Blo 385764 1785077 := bbase (se 5 (by rfl) ⟨83675, by rfl⟩ : syracuseStep 1785077 = 167351) (by norm_num)
theorem B933125 : Blo 385764 933125 := bbase (se 4 (by rfl) ⟨87480, by rfl⟩ : syracuseStep 933125 = 174961) (by norm_num)
theorem B638237 : Blo 385764 638237 := bbase (se 3 (by rfl) ⟨119669, by rfl⟩ : syracuseStep 638237 = 239339) (by norm_num)
theorem B3325333 : Blo 385764 3325333 := bbase (se 6 (by rfl) ⟨77937, by rfl⟩ : syracuseStep 3325333 = 155875) (by norm_num)
theorem B736685 : Blo 385764 736685 := bbase (se 3 (by rfl) ⟨138128, by rfl⟩ : syracuseStep 736685 = 276257) (by norm_num)
theorem B769517 : Blo 385764 769517 := bbase (se 3 (by rfl) ⟨144284, by rfl⟩ : syracuseStep 769517 = 288569) (by norm_num)
theorem B868013 : Blo 385764 868013 := bbase (se 3 (by rfl) ⟨162752, by rfl⟩ : syracuseStep 868013 = 325505) (by norm_num)
theorem B868085 : Blo 385764 868085 := bbase (se 5 (by rfl) ⟨40691, by rfl⟩ : syracuseStep 868085 = 81383) (by norm_num)
theorem B868157 : Blo 385764 868157 := bbase (se 3 (by rfl) ⟨162779, by rfl⟩ : syracuseStep 868157 = 325559) (by norm_num)
theorem B1326917 : Blo 385764 1326917 := bbase (se 4 (by rfl) ⟨124398, by rfl⟩ : syracuseStep 1326917 = 248797) (by norm_num)
theorem B442201 : Blo 385764 442201 := bbase (se 2 (by rfl) ⟨165825, by rfl⟩ : syracuseStep 442201 = 331651) (by norm_num)
theorem B868229 : Blo 385764 868229 := bbase (se 4 (by rfl) ⟨81396, by rfl⟩ : syracuseStep 868229 = 162793) (by norm_num)
theorem B933781 : Blo 385764 933781 := bbase (se 6 (by rfl) ⟨21885, by rfl⟩ : syracuseStep 933781 = 43771) (by norm_num)
theorem B868301 : Blo 385764 868301 := bbase (se 3 (by rfl) ⟨162806, by rfl⟩ : syracuseStep 868301 = 325613) (by norm_num)
theorem B868373 : Blo 385764 868373 := bbase (se 6 (by rfl) ⟨20352, by rfl⟩ : syracuseStep 868373 = 40705) (by norm_num)
theorem B868445 : Blo 385764 868445 := bbase (se 3 (by rfl) ⟨162833, by rfl⟩ : syracuseStep 868445 = 325667) (by norm_num)
theorem B737437 : Blo 385764 737437 := bbase (se 3 (by rfl) ⟨138269, by rfl⟩ : syracuseStep 737437 = 276539) (by norm_num)
theorem B868517 : Blo 385764 868517 := bbase (se 4 (by rfl) ⟨81423, by rfl⟩ : syracuseStep 868517 = 162847) (by norm_num)
theorem B2474165 : Blo 385764 2474165 := bbase (se 5 (by rfl) ⟨115976, by rfl⟩ : syracuseStep 2474165 = 231953) (by norm_num)
theorem B868589 : Blo 385764 868589 := bbase (se 3 (by rfl) ⟨162860, by rfl⟩ : syracuseStep 868589 = 325721) (by norm_num)
theorem B737581 : Blo 385764 737581 := bbase (se 3 (by rfl) ⟨138296, by rfl⟩ : syracuseStep 737581 = 276593) (by norm_num)
theorem B868661 : Blo 385764 868661 := bbase (se 5 (by rfl) ⟨40718, by rfl⟩ : syracuseStep 868661 = 81437) (by norm_num)
theorem B409969 : Blo 385764 409969 := bbase (se 2 (by rfl) ⟨153738, by rfl⟩ : syracuseStep 409969 = 307477) (by norm_num)
theorem B3555701 : Blo 385764 3555701 := bbase (se 5 (by rfl) ⟨166673, by rfl⟩ : syracuseStep 3555701 = 333347) (by norm_num)
theorem B868733 : Blo 385764 868733 := bbase (se 3 (by rfl) ⟨162887, by rfl⟩ : syracuseStep 868733 = 325775) (by norm_num)
theorem B868805 : Blo 385764 868805 := bbase (se 4 (by rfl) ⟨81450, by rfl⟩ : syracuseStep 868805 = 162901) (by norm_num)
theorem B737741 : Blo 385764 737741 := bbase (se 3 (by rfl) ⟨138326, by rfl⟩ : syracuseStep 737741 = 276653) (by norm_num)
theorem B868877 : Blo 385764 868877 := bbase (se 3 (by rfl) ⟨162914, by rfl⟩ : syracuseStep 868877 = 325829) (by norm_num)
theorem B442913 : Blo 385764 442913 := bbase (se 2 (by rfl) ⟨166092, by rfl⟩ : syracuseStep 442913 = 332185) (by norm_num)
theorem B868949 : Blo 385764 868949 := bbase (se 8 (by rfl) ⟨5091, by rfl⟩ : syracuseStep 868949 = 10183) (by norm_num)
theorem B737885 : Blo 385764 737885 := bbase (se 3 (by rfl) ⟨138353, by rfl⟩ : syracuseStep 737885 = 276707) (by norm_num)
theorem B508529 : Blo 385764 508529 := bbase (se 2 (by rfl) ⟨190698, by rfl⟩ : syracuseStep 508529 = 381397) (by norm_num)
theorem B869021 : Blo 385764 869021 := bbase (se 3 (by rfl) ⟨162941, by rfl⟩ : syracuseStep 869021 = 325883) (by norm_num)
theorem B869093 : Blo 385764 869093 := bbase (se 4 (by rfl) ⟨81477, by rfl⟩ : syracuseStep 869093 = 162955) (by norm_num)
theorem B869165 : Blo 385764 869165 := bbase (se 3 (by rfl) ⟨162968, by rfl⟩ : syracuseStep 869165 = 325937) (by norm_num)
theorem B934733 : Blo 385764 934733 := bbase (se 3 (by rfl) ⟨175262, by rfl⟩ : syracuseStep 934733 = 350525) (by norm_num)
theorem B869237 : Blo 385764 869237 := bbase (se 5 (by rfl) ⟨40745, by rfl⟩ : syracuseStep 869237 = 81491) (by norm_num)
theorem B738173 : Blo 385764 738173 := bbase (se 3 (by rfl) ⟨138407, by rfl⟩ : syracuseStep 738173 = 276815) (by norm_num)
theorem B934789 : Blo 385764 934789 := bbase (se 4 (by rfl) ⟨87636, by rfl⟩ : syracuseStep 934789 = 175273) (by norm_num)
theorem B869309 : Blo 385764 869309 := bbase (se 3 (by rfl) ⟨162995, by rfl⟩ : syracuseStep 869309 = 325991) (by norm_num)
theorem B1655765 : Blo 385764 1655765 := bbase (se 7 (by rfl) ⟨19403, by rfl⟩ : syracuseStep 1655765 = 38807) (by norm_num)
theorem B869381 : Blo 385764 869381 := bbase (se 4 (by rfl) ⟨81504, by rfl⟩ : syracuseStep 869381 = 163009) (by norm_num)
theorem B738325 : Blo 385764 738325 := bbase (se 6 (by rfl) ⟨17304, by rfl⟩ : syracuseStep 738325 = 34609) (by norm_num)
theorem B869453 : Blo 385764 869453 := bbase (se 3 (by rfl) ⟨163022, by rfl⟩ : syracuseStep 869453 = 326045) (by norm_num)
theorem B869525 : Blo 385764 869525 := bbase (se 6 (by rfl) ⟨20379, by rfl⟩ : syracuseStep 869525 = 40759) (by norm_num)
theorem B2802869 : Blo 385764 2802869 := bbase (se 5 (by rfl) ⟨131384, by rfl⟩ : syracuseStep 2802869 = 262769) (by norm_num)
theorem B869597 : Blo 385764 869597 := bbase (se 3 (by rfl) ⟨163049, by rfl⟩ : syracuseStep 869597 = 326099) (by norm_num)
theorem B935165 : Blo 385764 935165 := bbase (se 3 (by rfl) ⟨175343, by rfl⟩ : syracuseStep 935165 = 350687) (by norm_num)
theorem B4179221 : Blo 385764 4179221 := bbase (se 6 (by rfl) ⟨97950, by rfl⟩ : syracuseStep 4179221 = 195901) (by norm_num)
theorem B869669 : Blo 385764 869669 := bbase (se 4 (by rfl) ⟨81531, by rfl⟩ : syracuseStep 869669 = 163063) (by norm_num)
theorem B738629 : Blo 385764 738629 := bbase (se 4 (by rfl) ⟨69246, by rfl⟩ : syracuseStep 738629 = 138493) (by norm_num)
theorem B3327317 : Blo 385764 3327317 := bbase (se 12 (by rfl) ⟨1218, by rfl⟩ : syracuseStep 3327317 = 2437) (by norm_num)
theorem B869741 : Blo 385764 869741 := bbase (se 3 (by rfl) ⟨163076, by rfl⟩ : syracuseStep 869741 = 326153) (by norm_num)
theorem B869813 : Blo 385764 869813 := bbase (se 5 (by rfl) ⟨40772, by rfl⟩ : syracuseStep 869813 = 81545) (by norm_num)
theorem B935405 : Blo 385764 935405 := bbase (se 3 (by rfl) ⟨175388, by rfl⟩ : syracuseStep 935405 = 350777) (by norm_num)
theorem B869885 : Blo 385764 869885 := bbase (se 3 (by rfl) ⟨163103, by rfl⟩ : syracuseStep 869885 = 326207) (by norm_num)
theorem B869957 : Blo 385764 869957 := bbase (se 4 (by rfl) ⟨81558, by rfl⟩ : syracuseStep 869957 = 163117) (by norm_num)
theorem B870029 : Blo 385764 870029 := bbase (se 3 (by rfl) ⟨163130, by rfl⟩ : syracuseStep 870029 = 326261) (by norm_num)
theorem B1492661 : Blo 385764 1492661 := bbase (se 5 (by rfl) ⟨69968, by rfl⟩ : syracuseStep 1492661 = 139937) (by norm_num)
theorem B870101 : Blo 385764 870101 := bbase (se 7 (by rfl) ⟨10196, by rfl⟩ : syracuseStep 870101 = 20393) (by norm_num)
theorem B4703957 : Blo 385764 4703957 := bbase (se 7 (by rfl) ⟨55124, by rfl⟩ : syracuseStep 4703957 = 110249) (by norm_num)
theorem B870173 : Blo 385764 870173 := bbase (se 3 (by rfl) ⟨163157, by rfl⟩ : syracuseStep 870173 = 326315) (by norm_num)
theorem B870245 : Blo 385764 870245 := bbase (se 4 (by rfl) ⟨81585, by rfl⟩ : syracuseStep 870245 = 163171) (by norm_num)
theorem B870317 : Blo 385764 870317 := bbase (se 3 (by rfl) ⟨163184, by rfl⟩ : syracuseStep 870317 = 326369) (by norm_num)
theorem B870389 : Blo 385764 870389 := bbase (se 5 (by rfl) ⟨40799, by rfl⟩ : syracuseStep 870389 = 81599) (by norm_num)
theorem B739381 : Blo 385764 739381 := bbase (se 5 (by rfl) ⟨34658, by rfl⟩ : syracuseStep 739381 = 69317) (by norm_num)
theorem B870461 : Blo 385764 870461 := bbase (se 3 (by rfl) ⟨163211, by rfl⟩ : syracuseStep 870461 = 326423) (by norm_num)
theorem B870533 : Blo 385764 870533 := bbase (se 4 (by rfl) ⟨81612, by rfl⟩ : syracuseStep 870533 = 163225) (by norm_num)
theorem B1099925 : Blo 385764 1099925 := bbase (se 6 (by rfl) ⟨25779, by rfl⟩ : syracuseStep 1099925 = 51559) (by norm_num)
theorem B739525 : Blo 385764 739525 := bbase (se 4 (by rfl) ⟨69330, by rfl⟩ : syracuseStep 739525 = 138661) (by norm_num)
theorem B870605 : Blo 385764 870605 := bbase (se 3 (by rfl) ⟨163238, by rfl⟩ : syracuseStep 870605 = 326477) (by norm_num)
theorem B870677 : Blo 385764 870677 := bbase (se 6 (by rfl) ⟨20406, by rfl⟩ : syracuseStep 870677 = 40813) (by norm_num)
theorem B870749 : Blo 385764 870749 := bbase (se 3 (by rfl) ⟨163265, by rfl⟩ : syracuseStep 870749 = 326531) (by norm_num)
theorem B739685 : Blo 385764 739685 := bbase (se 4 (by rfl) ⟨69345, by rfl⟩ : syracuseStep 739685 = 138691) (by norm_num)
theorem B870821 : Blo 385764 870821 := bbase (se 4 (by rfl) ⟨81639, by rfl⟩ : syracuseStep 870821 = 163279) (by norm_num)
theorem B870893 : Blo 385764 870893 := bbase (se 3 (by rfl) ⟨163292, by rfl⟩ : syracuseStep 870893 = 326585) (by norm_num)
theorem B739829 : Blo 385764 739829 := bbase (se 5 (by rfl) ⟨34679, by rfl⟩ : syracuseStep 739829 = 69359) (by norm_num)
theorem B870965 : Blo 385764 870965 := bbase (se 5 (by rfl) ⟨40826, by rfl⟩ : syracuseStep 870965 = 81653) (by norm_num)
theorem B871037 : Blo 385764 871037 := bbase (se 3 (by rfl) ⟨163319, by rfl⟩ : syracuseStep 871037 = 326639) (by norm_num)
theorem B412301 : Blo 385764 412301 := bbase (se 3 (by rfl) ⟨77306, by rfl⟩ : syracuseStep 412301 = 154613) (by norm_num)
theorem B871109 : Blo 385764 871109 := bbase (se 4 (by rfl) ⟨81666, by rfl⟩ : syracuseStep 871109 = 163333) (by norm_num)
theorem B871181 : Blo 385764 871181 := bbase (se 3 (by rfl) ⟨163346, by rfl⟩ : syracuseStep 871181 = 326693) (by norm_num)
theorem B412489 : Blo 385764 412489 := bbase (se 2 (by rfl) ⟨154683, by rfl⟩ : syracuseStep 412489 = 309367) (by norm_num)
theorem B7064405 : Blo 385764 7064405 := bbase (se 9 (by rfl) ⟨20696, by rfl⟩ : syracuseStep 7064405 = 41393) (by norm_num)
theorem B871253 : Blo 385764 871253 := bbase (se 9 (by rfl) ⟨2552, by rfl⟩ : syracuseStep 871253 = 5105) (by norm_num)
theorem B871325 : Blo 385764 871325 := bbase (se 3 (by rfl) ⟨163373, by rfl⟩ : syracuseStep 871325 = 326747) (by norm_num)
theorem B576437 : Blo 385764 576437 := bbase (se 5 (by rfl) ⟨27020, by rfl⟩ : syracuseStep 576437 = 54041) (by norm_num)
theorem B1985509 : Blo 385764 1985509 := bbase (se 4 (by rfl) ⟨186141, by rfl⟩ : syracuseStep 1985509 = 372283) (by norm_num)
theorem B871397 : Blo 385764 871397 := bbase (se 4 (by rfl) ⟨81693, by rfl⟩ : syracuseStep 871397 = 163387) (by norm_num)
theorem B4213781 : Blo 385764 4213781 := bbase (se 6 (by rfl) ⟨98760, by rfl⟩ : syracuseStep 4213781 = 197521) (by norm_num)
theorem B871469 : Blo 385764 871469 := bbase (se 3 (by rfl) ⟨163400, by rfl⟩ : syracuseStep 871469 = 326801) (by norm_num)
theorem B2935925 : Blo 385764 2935925 := bbase (se 5 (by rfl) ⟨137621, by rfl⟩ : syracuseStep 2935925 = 275243) (by norm_num)
theorem B871541 : Blo 385764 871541 := bbase (se 5 (by rfl) ⟨40853, by rfl⟩ : syracuseStep 871541 = 81707) (by norm_num)
theorem B871613 : Blo 385764 871613 := bbase (se 3 (by rfl) ⟨163427, by rfl⟩ : syracuseStep 871613 = 326855) (by norm_num)
theorem B871685 : Blo 385764 871685 := bbase (se 4 (by rfl) ⟨81720, by rfl⟩ : syracuseStep 871685 = 163441) (by norm_num)
theorem B1101109 : Blo 385764 1101109 := bbase (se 5 (by rfl) ⟨51614, by rfl⟩ : syracuseStep 1101109 = 103229) (by norm_num)
theorem B871757 : Blo 385764 871757 := bbase (se 3 (by rfl) ⟨163454, by rfl⟩ : syracuseStep 871757 = 326909) (by norm_num)
theorem B871829 : Blo 385764 871829 := bbase (se 6 (by rfl) ⟨20433, by rfl⟩ : syracuseStep 871829 = 40867) (by norm_num)
theorem B1101269 : Blo 385764 1101269 := bbase (se 7 (by rfl) ⟨12905, by rfl⟩ : syracuseStep 1101269 = 25811) (by norm_num)
theorem B871901 : Blo 385764 871901 := bbase (se 3 (by rfl) ⟨163481, by rfl⟩ : syracuseStep 871901 = 326963) (by norm_num)
theorem B871973 : Blo 385764 871973 := bbase (se 4 (by rfl) ⟨81747, by rfl⟩ : syracuseStep 871973 = 163495) (by norm_num)
theorem B872045 : Blo 385764 872045 := bbase (se 3 (by rfl) ⟨163508, by rfl⟩ : syracuseStep 872045 = 327017) (by norm_num)
theorem B413309 : Blo 385764 413309 := bbase (se 3 (by rfl) ⟨77495, by rfl⟩ : syracuseStep 413309 = 154991) (by norm_num)
theorem B675461 : Blo 385764 675461 := bbase (se 4 (by rfl) ⟨63324, by rfl⟩ : syracuseStep 675461 = 126649) (by norm_num)
theorem B872117 : Blo 385764 872117 := bbase (se 5 (by rfl) ⟨40880, by rfl⟩ : syracuseStep 872117 = 81761) (by norm_num)
theorem B1101509 : Blo 385764 1101509 := bbase (se 4 (by rfl) ⟨103266, by rfl⟩ : syracuseStep 1101509 = 206533) (by norm_num)
theorem B675541 : Blo 385764 675541 := bbase (se 7 (by rfl) ⟨7916, by rfl⟩ : syracuseStep 675541 = 15833) (by norm_num)
theorem B872189 : Blo 385764 872189 := bbase (se 3 (by rfl) ⟨163535, by rfl⟩ : syracuseStep 872189 = 327071) (by norm_num)
theorem B1953557 : Blo 385764 1953557 := bbase (se 6 (by rfl) ⟨45786, by rfl⟩ : syracuseStep 1953557 = 91573) (by norm_num)
theorem B872261 : Blo 385764 872261 := bbase (se 4 (by rfl) ⟨81774, by rfl⟩ : syracuseStep 872261 = 163549) (by norm_num)
theorem B1101701 : Blo 385764 1101701 := bbase (se 4 (by rfl) ⟨103284, by rfl⟩ : syracuseStep 1101701 = 206569) (by norm_num)
theorem B872333 : Blo 385764 872333 := bbase (se 3 (by rfl) ⟨163562, by rfl⟩ : syracuseStep 872333 = 327125) (by norm_num)
theorem B839629 : Blo 385764 839629 := bbase (se 3 (by rfl) ⟨157430, by rfl⟩ : syracuseStep 839629 = 314861) (by norm_num)
theorem B872405 : Blo 385764 872405 := bbase (se 7 (by rfl) ⟨10223, by rfl⟩ : syracuseStep 872405 = 20447) (by norm_num)
theorem B1396709 : Blo 385764 1396709 := bbase (se 4 (by rfl) ⟨130941, by rfl⟩ : syracuseStep 1396709 = 261883) (by norm_num)
theorem B4739093 : Blo 385764 4739093 := bbase (se 6 (by rfl) ⟨111072, by rfl⟩ : syracuseStep 4739093 = 222145) (by norm_num)
theorem B872477 : Blo 385764 872477 := bbase (se 3 (by rfl) ⟨163589, by rfl⟩ : syracuseStep 872477 = 327179) (by norm_num)
theorem B413753 : Blo 385764 413753 := bbase (se 2 (by rfl) ⟨155157, by rfl⟩ : syracuseStep 413753 = 310315) (by norm_num)
theorem B872549 : Blo 385764 872549 := bbase (se 4 (by rfl) ⟨81801, by rfl⟩ : syracuseStep 872549 = 163603) (by norm_num)
theorem B872621 : Blo 385764 872621 := bbase (se 3 (by rfl) ⟨163616, by rfl⟩ : syracuseStep 872621 = 327233) (by norm_num)
theorem B872693 : Blo 385764 872693 := bbase (se 5 (by rfl) ⟨40907, by rfl⟩ : syracuseStep 872693 = 81815) (by norm_num)
theorem B3985685 : Blo 385764 3985685 := bbase (se 6 (by rfl) ⟨93414, by rfl⟩ : syracuseStep 3985685 = 186829) (by norm_num)
theorem B414001 : Blo 385764 414001 := bbase (se 2 (by rfl) ⟨155250, by rfl⟩ : syracuseStep 414001 = 310501) (by norm_num)
theorem B872765 : Blo 385764 872765 := bbase (se 3 (by rfl) ⟨163643, by rfl⟩ : syracuseStep 872765 = 327287) (by norm_num)
theorem B872837 : Blo 385764 872837 := bbase (se 4 (by rfl) ⟨81828, by rfl⟩ : syracuseStep 872837 = 163657) (by norm_num)
theorem B872909 : Blo 385764 872909 := bbase (se 3 (by rfl) ⟨163670, by rfl⟩ : syracuseStep 872909 = 327341) (by norm_num)
theorem B872981 : Blo 385764 872981 := bbase (se 6 (by rfl) ⟨20460, by rfl⟩ : syracuseStep 872981 = 40921) (by norm_num)
theorem B3986005 : Blo 385764 3986005 := bbase (se 8 (by rfl) ⟨23355, by rfl⟩ : syracuseStep 3986005 = 46711) (by norm_num)
theorem B873053 : Blo 385764 873053 := bbase (se 3 (by rfl) ⟨163697, by rfl⟩ : syracuseStep 873053 = 327395) (by norm_num)
theorem B873125 : Blo 385764 873125 := bbase (se 4 (by rfl) ⟨81855, by rfl⟩ : syracuseStep 873125 = 163711) (by norm_num)
theorem B414433 : Blo 385764 414433 := bbase (se 2 (by rfl) ⟨155412, by rfl⟩ : syracuseStep 414433 = 310825) (by norm_num)
theorem B873197 : Blo 385764 873197 := bbase (se 3 (by rfl) ⟨163724, by rfl⟩ : syracuseStep 873197 = 327449) (by norm_num)
theorem B414505 : Blo 385764 414505 := bbase (se 2 (by rfl) ⟨155439, by rfl⟩ : syracuseStep 414505 = 310879) (by norm_num)
theorem B873269 : Blo 385764 873269 := bbase (se 5 (by rfl) ⟨40934, by rfl⟩ : syracuseStep 873269 = 81869) (by norm_num)
theorem B1102693 : Blo 385764 1102693 := bbase (se 4 (by rfl) ⟨103377, by rfl⟩ : syracuseStep 1102693 = 206755) (by norm_num)
theorem B873341 : Blo 385764 873341 := bbase (se 3 (by rfl) ⟨163751, by rfl⟩ : syracuseStep 873341 = 327503) (by norm_num)
theorem B1659797 : Blo 385764 1659797 := bbase (se 6 (by rfl) ⟨38901, by rfl⟩ : syracuseStep 1659797 = 77803) (by norm_num)
theorem B873413 : Blo 385764 873413 := bbase (se 4 (by rfl) ⟨81882, by rfl⟩ : syracuseStep 873413 = 163765) (by norm_num)
theorem B873485 : Blo 385764 873485 := bbase (se 3 (by rfl) ⟨163778, by rfl⟩ : syracuseStep 873485 = 327557) (by norm_num)
theorem B1954853 : Blo 385764 1954853 := bbase (se 4 (by rfl) ⟨183267, by rfl⟩ : syracuseStep 1954853 = 366535) (by norm_num)
theorem B873557 : Blo 385764 873557 := bbase (se 8 (by rfl) ⟨5118, by rfl⟩ : syracuseStep 873557 = 10237) (by norm_num)
theorem B578669 : Blo 385764 578669 := bbase (se 3 (by rfl) ⟨108500, by rfl⟩ : syracuseStep 578669 = 217001) (by norm_num)
theorem B578693 : Blo 385764 578693 := bbase (se 4 (by rfl) ⟨54252, by rfl⟩ : syracuseStep 578693 = 108505) (by norm_num)
theorem B578717 : Blo 385764 578717 := bbase (se 3 (by rfl) ⟨108509, by rfl⟩ : syracuseStep 578717 = 217019) (by norm_num)
theorem B873629 : Blo 385764 873629 := bbase (se 3 (by rfl) ⟨163805, by rfl⟩ : syracuseStep 873629 = 327611) (by norm_num)
theorem B414877 : Blo 385764 414877 := bbase (se 3 (by rfl) ⟨77789, by rfl⟩ : syracuseStep 414877 = 155579) (by norm_num)
theorem B578741 : Blo 385764 578741 := bbase (se 5 (by rfl) ⟨27128, by rfl⟩ : syracuseStep 578741 = 54257) (by norm_num)
theorem B578765 : Blo 385764 578765 := bbase (se 3 (by rfl) ⟨108518, by rfl⟩ : syracuseStep 578765 = 217037) (by norm_num)
theorem B578789 : Blo 385764 578789 := bbase (se 4 (by rfl) ⟨54261, by rfl⟩ : syracuseStep 578789 = 108523) (by norm_num)
theorem B873701 : Blo 385764 873701 := bbase (se 4 (by rfl) ⟨81909, by rfl⟩ : syracuseStep 873701 = 163819) (by norm_num)
theorem B578813 : Blo 385764 578813 := bbase (se 3 (by rfl) ⟨108527, by rfl⟩ : syracuseStep 578813 = 217055) (by norm_num)
theorem B578837 : Blo 385764 578837 := bbase (se 6 (by rfl) ⟨13566, by rfl⟩ : syracuseStep 578837 = 27133) (by norm_num)
theorem B578861 : Blo 385764 578861 := bbase (se 3 (by rfl) ⟨108536, by rfl⟩ : syracuseStep 578861 = 217073) (by norm_num)
theorem B873773 : Blo 385764 873773 := bbase (se 3 (by rfl) ⟨163832, by rfl⟩ : syracuseStep 873773 = 327665) (by norm_num)
theorem B578885 : Blo 385764 578885 := bbase (se 4 (by rfl) ⟨54270, by rfl⟩ : syracuseStep 578885 = 108541) (by norm_num)
theorem B578909 : Blo 385764 578909 := bbase (se 3 (by rfl) ⟨108545, by rfl⟩ : syracuseStep 578909 = 217091) (by norm_num)
theorem B578933 : Blo 385764 578933 := bbase (se 5 (by rfl) ⟨27137, by rfl⟩ : syracuseStep 578933 = 54275) (by norm_num)
theorem B873845 : Blo 385764 873845 := bbase (se 5 (by rfl) ⟨40961, by rfl⟩ : syracuseStep 873845 = 81923) (by norm_num)
theorem B578957 : Blo 385764 578957 := bbase (se 3 (by rfl) ⟨108554, by rfl⟩ : syracuseStep 578957 = 217109) (by norm_num)
theorem B578981 : Blo 385764 578981 := bbase (se 4 (by rfl) ⟨54279, by rfl⟩ : syracuseStep 578981 = 108559) (by norm_num)
theorem B579005 : Blo 385764 579005 := bbase (se 3 (by rfl) ⟨108563, by rfl⟩ : syracuseStep 579005 = 217127) (by norm_num)
theorem B873917 : Blo 385764 873917 := bbase (se 3 (by rfl) ⟨163859, by rfl⟩ : syracuseStep 873917 = 327719) (by norm_num)
theorem B579029 : Blo 385764 579029 := bbase (se 7 (by rfl) ⟨6785, by rfl⟩ : syracuseStep 579029 = 13571) (by norm_num)
theorem B579053 : Blo 385764 579053 := bbase (se 3 (by rfl) ⟨108572, by rfl⟩ : syracuseStep 579053 = 217145) (by norm_num)
theorem B579077 : Blo 385764 579077 := bbase (se 4 (by rfl) ⟨54288, by rfl⟩ : syracuseStep 579077 = 108577) (by norm_num)
theorem B873989 : Blo 385764 873989 := bbase (se 4 (by rfl) ⟨81936, by rfl⟩ : syracuseStep 873989 = 163873) (by norm_num)
theorem B415253 : Blo 385764 415253 := bbase (se 6 (by rfl) ⟨9732, by rfl⟩ : syracuseStep 415253 = 19465) (by norm_num)
theorem B579101 : Blo 385764 579101 := bbase (se 3 (by rfl) ⟨108581, by rfl⟩ : syracuseStep 579101 = 217163) (by norm_num)
theorem B579125 : Blo 385764 579125 := bbase (se 5 (by rfl) ⟨27146, by rfl⟩ : syracuseStep 579125 = 54293) (by norm_num)
theorem B579149 : Blo 385764 579149 := bbase (se 3 (by rfl) ⟨108590, by rfl⟩ : syracuseStep 579149 = 217181) (by norm_num)
theorem B874061 : Blo 385764 874061 := bbase (se 3 (by rfl) ⟨163886, by rfl⟩ : syracuseStep 874061 = 327773) (by norm_num)
theorem B415325 : Blo 385764 415325 := bbase (se 3 (by rfl) ⟨77873, by rfl⟩ : syracuseStep 415325 = 155747) (by norm_num)
theorem B579173 : Blo 385764 579173 := bbase (se 4 (by rfl) ⟨54297, by rfl⟩ : syracuseStep 579173 = 108595) (by norm_num)
theorem B579197 : Blo 385764 579197 := bbase (se 3 (by rfl) ⟨108599, by rfl⟩ : syracuseStep 579197 = 217199) (by norm_num)
theorem B579221 : Blo 385764 579221 := bbase (se 6 (by rfl) ⟨13575, by rfl⟩ : syracuseStep 579221 = 27151) (by norm_num)
theorem B874133 : Blo 385764 874133 := bbase (se 6 (by rfl) ⟨20487, by rfl⟩ : syracuseStep 874133 = 40975) (by norm_num)
theorem B710309 : Blo 385764 710309 := bbase (se 4 (by rfl) ⟨66591, by rfl⟩ : syracuseStep 710309 = 133183) (by norm_num)
theorem B579245 : Blo 385764 579245 := bbase (se 3 (by rfl) ⟨108608, by rfl⟩ : syracuseStep 579245 = 217217) (by norm_num)
theorem B579269 : Blo 385764 579269 := bbase (se 4 (by rfl) ⟨54306, by rfl⟩ : syracuseStep 579269 = 108613) (by norm_num)
theorem B579293 : Blo 385764 579293 := bbase (se 3 (by rfl) ⟨108617, by rfl⟩ : syracuseStep 579293 = 217235) (by norm_num)
theorem B874205 : Blo 385764 874205 := bbase (se 3 (by rfl) ⟨163913, by rfl⟩ : syracuseStep 874205 = 327827) (by norm_num)
theorem B579317 : Blo 385764 579317 := bbase (se 5 (by rfl) ⟨27155, by rfl⟩ : syracuseStep 579317 = 54311) (by norm_num)
theorem B579341 : Blo 385764 579341 := bbase (se 3 (by rfl) ⟨108626, by rfl⟩ : syracuseStep 579341 = 217253) (by norm_num)
theorem B2119445 : Blo 385764 2119445 := bbase (se 6 (by rfl) ⟨49674, by rfl⟩ : syracuseStep 2119445 = 99349) (by norm_num)
theorem B415513 : Blo 385764 415513 := bbase (se 2 (by rfl) ⟨155817, by rfl⟩ : syracuseStep 415513 = 311635) (by norm_num)
theorem B579365 : Blo 385764 579365 := bbase (se 4 (by rfl) ⟨54315, by rfl⟩ : syracuseStep 579365 = 108631) (by norm_num)
theorem B874277 : Blo 385764 874277 := bbase (se 4 (by rfl) ⟨81963, by rfl⟩ : syracuseStep 874277 = 163927) (by norm_num)
theorem B579389 : Blo 385764 579389 := bbase (se 3 (by rfl) ⟨108635, by rfl⟩ : syracuseStep 579389 = 217271) (by norm_num)
theorem B579413 : Blo 385764 579413 := bbase (se 9 (by rfl) ⟨1697, by rfl⟩ : syracuseStep 579413 = 3395) (by norm_num)
theorem B579437 : Blo 385764 579437 := bbase (se 3 (by rfl) ⟨108644, by rfl⟩ : syracuseStep 579437 = 217289) (by norm_num)
theorem B874349 : Blo 385764 874349 := bbase (se 3 (by rfl) ⟨163940, by rfl⟩ : syracuseStep 874349 = 327881) (by norm_num)
theorem B579461 : Blo 385764 579461 := bbase (se 4 (by rfl) ⟨54324, by rfl⟩ : syracuseStep 579461 = 108649) (by norm_num)
theorem B579485 : Blo 385764 579485 := bbase (se 3 (by rfl) ⟨108653, by rfl⟩ : syracuseStep 579485 = 217307) (by norm_num)
theorem B579509 : Blo 385764 579509 := bbase (se 5 (by rfl) ⟨27164, by rfl⟩ : syracuseStep 579509 = 54329) (by norm_num)
theorem B1103797 : Blo 385764 1103797 := bbase (se 5 (by rfl) ⟨51740, by rfl⟩ : syracuseStep 1103797 = 103481) (by norm_num)
theorem B874421 : Blo 385764 874421 := bbase (se 5 (by rfl) ⟨40988, by rfl⟩ : syracuseStep 874421 = 81977) (by norm_num)
theorem B579533 : Blo 385764 579533 := bbase (se 3 (by rfl) ⟨108662, by rfl⟩ : syracuseStep 579533 = 217325) (by norm_num)
theorem B415697 : Blo 385764 415697 := bbase (se 2 (by rfl) ⟨155886, by rfl⟩ : syracuseStep 415697 = 311773) (by norm_num)
theorem B579557 : Blo 385764 579557 := bbase (se 4 (by rfl) ⟨54333, by rfl⟩ : syracuseStep 579557 = 108667) (by norm_num)
theorem B579581 : Blo 385764 579581 := bbase (se 3 (by rfl) ⟨108671, by rfl⟩ : syracuseStep 579581 = 217343) (by norm_num)
theorem B874493 : Blo 385764 874493 := bbase (se 3 (by rfl) ⟨163967, by rfl⟩ : syracuseStep 874493 = 327935) (by norm_num)
theorem B579605 : Blo 385764 579605 := bbase (se 6 (by rfl) ⟨13584, by rfl⟩ : syracuseStep 579605 = 27169) (by norm_num)
theorem B579629 : Blo 385764 579629 := bbase (se 3 (by rfl) ⟨108680, by rfl⟩ : syracuseStep 579629 = 217361) (by norm_num)
theorem B579653 : Blo 385764 579653 := bbase (se 4 (by rfl) ⟨54342, by rfl⟩ : syracuseStep 579653 = 108685) (by norm_num)
theorem B874565 : Blo 385764 874565 := bbase (se 4 (by rfl) ⟨81990, by rfl⟩ : syracuseStep 874565 = 163981) (by norm_num)
theorem B579677 : Blo 385764 579677 := bbase (se 3 (by rfl) ⟨108689, by rfl⟩ : syracuseStep 579677 = 217379) (by norm_num)
theorem B579701 : Blo 385764 579701 := bbase (se 5 (by rfl) ⟨27173, by rfl⟩ : syracuseStep 579701 = 54347) (by norm_num)
theorem B579725 : Blo 385764 579725 := bbase (se 3 (by rfl) ⟨108698, by rfl⟩ : syracuseStep 579725 = 217397) (by norm_num)
theorem B874637 : Blo 385764 874637 := bbase (se 3 (by rfl) ⟨163994, by rfl⟩ : syracuseStep 874637 = 327989) (by norm_num)
theorem B579749 : Blo 385764 579749 := bbase (se 4 (by rfl) ⟨54351, by rfl⟩ : syracuseStep 579749 = 108703) (by norm_num)
theorem B579773 : Blo 385764 579773 := bbase (se 3 (by rfl) ⟨108707, by rfl⟩ : syracuseStep 579773 = 217415) (by norm_num)
theorem B579797 : Blo 385764 579797 := bbase (se 7 (by rfl) ⟨6794, by rfl⟩ : syracuseStep 579797 = 13589) (by norm_num)
theorem B874709 : Blo 385764 874709 := bbase (se 7 (by rfl) ⟨10250, by rfl⟩ : syracuseStep 874709 = 20501) (by norm_num)
theorem B579821 : Blo 385764 579821 := bbase (se 3 (by rfl) ⟨108716, by rfl⟩ : syracuseStep 579821 = 217433) (by norm_num)
theorem B579845 : Blo 385764 579845 := bbase (se 4 (by rfl) ⟨54360, by rfl⟩ : syracuseStep 579845 = 108721) (by norm_num)
theorem B579869 : Blo 385764 579869 := bbase (se 3 (by rfl) ⟨108725, by rfl⟩ : syracuseStep 579869 = 217451) (by norm_num)
theorem B874781 : Blo 385764 874781 := bbase (se 3 (by rfl) ⟨164021, by rfl⟩ : syracuseStep 874781 = 328043) (by norm_num)
theorem B1956149 : Blo 385764 1956149 := bbase (se 5 (by rfl) ⟨91694, by rfl⟩ : syracuseStep 1956149 = 183389) (by norm_num)
theorem B579893 : Blo 385764 579893 := bbase (se 5 (by rfl) ⟨27182, by rfl⟩ : syracuseStep 579893 = 54365) (by norm_num)
theorem B579917 : Blo 385764 579917 := bbase (se 3 (by rfl) ⟨108734, by rfl⟩ : syracuseStep 579917 = 217469) (by norm_num)
theorem B579941 : Blo 385764 579941 := bbase (se 4 (by rfl) ⟨54369, by rfl⟩ : syracuseStep 579941 = 108739) (by norm_num)
theorem B874853 : Blo 385764 874853 := bbase (se 4 (by rfl) ⟨82017, by rfl⟩ : syracuseStep 874853 = 164035) (by norm_num)
theorem B579965 : Blo 385764 579965 := bbase (se 3 (by rfl) ⟨108743, by rfl⟩ : syracuseStep 579965 = 217487) (by norm_num)
theorem B579989 : Blo 385764 579989 := bbase (se 6 (by rfl) ⟨13593, by rfl⟩ : syracuseStep 579989 = 27187) (by norm_num)
theorem B580013 : Blo 385764 580013 := bbase (se 3 (by rfl) ⟨108752, by rfl⟩ : syracuseStep 580013 = 217505) (by norm_num)
theorem B874925 : Blo 385764 874925 := bbase (se 3 (by rfl) ⟨164048, by rfl⟩ : syracuseStep 874925 = 328097) (by norm_num)
theorem B580037 : Blo 385764 580037 := bbase (se 4 (by rfl) ⟨54378, by rfl⟩ : syracuseStep 580037 = 108757) (by norm_num)
theorem B580061 : Blo 385764 580061 := bbase (se 3 (by rfl) ⟨108761, by rfl⟩ : syracuseStep 580061 = 217523) (by norm_num)
theorem B580085 : Blo 385764 580085 := bbase (se 5 (by rfl) ⟨27191, by rfl⟩ : syracuseStep 580085 = 54383) (by norm_num)
theorem B874997 : Blo 385764 874997 := bbase (se 5 (by rfl) ⟨41015, by rfl⟩ : syracuseStep 874997 = 82031) (by norm_num)
theorem B580109 : Blo 385764 580109 := bbase (se 3 (by rfl) ⟨108770, by rfl⟩ : syracuseStep 580109 = 217541) (by norm_num)
theorem B1858085 : Blo 385764 1858085 := bbase (se 4 (by rfl) ⟨174195, by rfl⟩ : syracuseStep 1858085 = 348391) (by norm_num)
theorem B580133 : Blo 385764 580133 := bbase (se 4 (by rfl) ⟨54387, by rfl⟩ : syracuseStep 580133 = 108775) (by norm_num)
theorem B580157 : Blo 385764 580157 := bbase (se 3 (by rfl) ⟨108779, by rfl⟩ : syracuseStep 580157 = 217559) (by norm_num)
theorem B875069 : Blo 385764 875069 := bbase (se 3 (by rfl) ⟨164075, by rfl⟩ : syracuseStep 875069 = 328151) (by norm_num)
theorem B580181 : Blo 385764 580181 := bbase (se 8 (by rfl) ⟨3399, by rfl⟩ : syracuseStep 580181 = 6799) (by norm_num)
theorem B580205 : Blo 385764 580205 := bbase (se 3 (by rfl) ⟨108788, by rfl⟩ : syracuseStep 580205 = 217577) (by norm_num)
theorem B580229 : Blo 385764 580229 := bbase (se 4 (by rfl) ⟨54396, by rfl⟩ : syracuseStep 580229 = 108793) (by norm_num)
theorem B875141 : Blo 385764 875141 := bbase (se 4 (by rfl) ⟨82044, by rfl⟩ : syracuseStep 875141 = 164089) (by norm_num)
theorem B1661573 : Blo 385764 1661573 := bbase (se 4 (by rfl) ⟨155772, by rfl⟩ : syracuseStep 1661573 = 311545) (by norm_num)
theorem B580253 : Blo 385764 580253 := bbase (se 3 (by rfl) ⟨108797, by rfl⟩ : syracuseStep 580253 = 217595) (by norm_num)
theorem B580277 : Blo 385764 580277 := bbase (se 5 (by rfl) ⟨27200, by rfl⟩ : syracuseStep 580277 = 54401) (by norm_num)
theorem B580301 : Blo 385764 580301 := bbase (se 3 (by rfl) ⟨108806, by rfl⟩ : syracuseStep 580301 = 217613) (by norm_num)
theorem B875213 : Blo 385764 875213 := bbase (se 3 (by rfl) ⟨164102, by rfl⟩ : syracuseStep 875213 = 328205) (by norm_num)
theorem B580325 : Blo 385764 580325 := bbase (se 4 (by rfl) ⟨54405, by rfl⟩ : syracuseStep 580325 = 108811) (by norm_num)
theorem B580349 : Blo 385764 580349 := bbase (se 3 (by rfl) ⟨108815, by rfl⟩ : syracuseStep 580349 = 217631) (by norm_num)
theorem B580373 : Blo 385764 580373 := bbase (se 6 (by rfl) ⟨13602, by rfl⟩ : syracuseStep 580373 = 27205) (by norm_num)
theorem B875285 : Blo 385764 875285 := bbase (se 6 (by rfl) ⟨20514, by rfl⟩ : syracuseStep 875285 = 41029) (by norm_num)
theorem B580397 : Blo 385764 580397 := bbase (se 3 (by rfl) ⟨108824, by rfl⟩ : syracuseStep 580397 = 217649) (by norm_num)
theorem B580421 : Blo 385764 580421 := bbase (se 4 (by rfl) ⟨54414, by rfl⟩ : syracuseStep 580421 = 108829) (by norm_num)
theorem B908101 : Blo 385764 908101 := bbase (se 4 (by rfl) ⟨85134, by rfl⟩ : syracuseStep 908101 = 170269) (by norm_num)
theorem B580445 : Blo 385764 580445 := bbase (se 3 (by rfl) ⟨108833, by rfl⟩ : syracuseStep 580445 = 217667) (by norm_num)
theorem B875357 : Blo 385764 875357 := bbase (se 3 (by rfl) ⟨164129, by rfl⟩ : syracuseStep 875357 = 328259) (by norm_num)
theorem B580469 : Blo 385764 580469 := bbase (se 5 (by rfl) ⟨27209, by rfl⟩ : syracuseStep 580469 = 54419) (by norm_num)
theorem B580493 : Blo 385764 580493 := bbase (se 3 (by rfl) ⟨108842, by rfl⟩ : syracuseStep 580493 = 217685) (by norm_num)
theorem B842645 : Blo 385764 842645 := bbase (se 6 (by rfl) ⟨19749, by rfl⟩ : syracuseStep 842645 = 39499) (by norm_num)
theorem B580517 : Blo 385764 580517 := bbase (se 4 (by rfl) ⟨54423, by rfl⟩ : syracuseStep 580517 = 108847) (by norm_num)
theorem B875429 : Blo 385764 875429 := bbase (se 4 (by rfl) ⟨82071, by rfl⟩ : syracuseStep 875429 = 164143) (by norm_num)
theorem B580541 : Blo 385764 580541 := bbase (se 3 (by rfl) ⟨108851, by rfl⟩ : syracuseStep 580541 = 217703) (by norm_num)
theorem B580565 : Blo 385764 580565 := bbase (se 7 (by rfl) ⟨6803, by rfl⟩ : syracuseStep 580565 = 13607) (by norm_num)
theorem B941021 : Blo 385764 941021 := bbase (se 3 (by rfl) ⟨176441, by rfl⟩ : syracuseStep 941021 = 352883) (by norm_num)
theorem B580589 : Blo 385764 580589 := bbase (se 3 (by rfl) ⟨108860, by rfl⟩ : syracuseStep 580589 = 217721) (by norm_num)
theorem B875501 : Blo 385764 875501 := bbase (se 3 (by rfl) ⟨164156, by rfl⟩ : syracuseStep 875501 = 328313) (by norm_num)
theorem B580613 : Blo 385764 580613 := bbase (se 4 (by rfl) ⟨54432, by rfl⟩ : syracuseStep 580613 = 108865) (by norm_num)
theorem B580637 : Blo 385764 580637 := bbase (se 3 (by rfl) ⟨108869, by rfl⟩ : syracuseStep 580637 = 217739) (by norm_num)
theorem B1465397 : Blo 385764 1465397 := bbase (se 5 (by rfl) ⟨68690, by rfl⟩ : syracuseStep 1465397 = 137381) (by norm_num)
theorem B580661 : Blo 385764 580661 := bbase (se 5 (by rfl) ⟨27218, by rfl⟩ : syracuseStep 580661 = 54437) (by norm_num)
theorem B875573 : Blo 385764 875573 := bbase (se 5 (by rfl) ⟨41042, by rfl⟩ : syracuseStep 875573 = 82085) (by norm_num)
theorem B580685 : Blo 385764 580685 := bbase (se 3 (by rfl) ⟨108878, by rfl⟩ : syracuseStep 580685 = 217757) (by norm_num)
theorem B580709 : Blo 385764 580709 := bbase (se 4 (by rfl) ⟨54441, by rfl⟩ : syracuseStep 580709 = 108883) (by norm_num)
theorem B580733 : Blo 385764 580733 := bbase (se 3 (by rfl) ⟨108887, by rfl⟩ : syracuseStep 580733 = 217775) (by norm_num)
theorem B875645 : Blo 385764 875645 := bbase (se 3 (by rfl) ⟨164183, by rfl⟩ : syracuseStep 875645 = 328367) (by norm_num)
theorem B580757 : Blo 385764 580757 := bbase (se 6 (by rfl) ⟨13611, by rfl⟩ : syracuseStep 580757 = 27223) (by norm_num)
theorem B580781 : Blo 385764 580781 := bbase (se 3 (by rfl) ⟨108896, by rfl⟩ : syracuseStep 580781 = 217793) (by norm_num)
theorem B580805 : Blo 385764 580805 := bbase (se 4 (by rfl) ⟨54450, by rfl⟩ : syracuseStep 580805 = 108901) (by norm_num)
theorem B875717 : Blo 385764 875717 := bbase (se 4 (by rfl) ⟨82098, by rfl⟩ : syracuseStep 875717 = 164197) (by norm_num)
theorem B580829 : Blo 385764 580829 := bbase (se 3 (by rfl) ⟨108905, by rfl⟩ : syracuseStep 580829 = 217811) (by norm_num)
theorem B580853 : Blo 385764 580853 := bbase (se 5 (by rfl) ⟨27227, by rfl⟩ : syracuseStep 580853 = 54455) (by norm_num)
theorem B580877 : Blo 385764 580877 := bbase (se 3 (by rfl) ⟨108914, by rfl⟩ : syracuseStep 580877 = 217829) (by norm_num)
theorem B875789 : Blo 385764 875789 := bbase (se 3 (by rfl) ⟨164210, by rfl⟩ : syracuseStep 875789 = 328421) (by norm_num)
theorem B580901 : Blo 385764 580901 := bbase (se 4 (by rfl) ⟨54459, by rfl⟩ : syracuseStep 580901 = 108919) (by norm_num)
theorem B843061 : Blo 385764 843061 := bbase (se 5 (by rfl) ⟨39518, by rfl⟩ : syracuseStep 843061 = 79037) (by norm_num)
theorem B580925 : Blo 385764 580925 := bbase (se 3 (by rfl) ⟨108923, by rfl⟩ : syracuseStep 580925 = 217847) (by norm_num)
theorem B1465685 : Blo 385764 1465685 := bbase (se 11 (by rfl) ⟨1073, by rfl⟩ : syracuseStep 1465685 = 2147) (by norm_num)
theorem B580949 : Blo 385764 580949 := bbase (se 11 (by rfl) ⟨425, by rfl⟩ : syracuseStep 580949 = 851) (by norm_num)
theorem B875861 : Blo 385764 875861 := bbase (se 11 (by rfl) ⟨641, by rfl⟩ : syracuseStep 875861 = 1283) (by norm_num)
theorem B580973 : Blo 385764 580973 := bbase (se 3 (by rfl) ⟨108932, by rfl⟩ : syracuseStep 580973 = 217865) (by norm_num)
theorem B580997 : Blo 385764 580997 := bbase (se 4 (by rfl) ⟨54468, by rfl⟩ : syracuseStep 580997 = 108937) (by norm_num)
theorem B5037461 : Blo 385764 5037461 := bbase (se 6 (by rfl) ⟨118065, by rfl⟩ : syracuseStep 5037461 = 236131) (by norm_num)
theorem B1105301 : Blo 385764 1105301 := bbase (se 6 (by rfl) ⟨25905, by rfl⟩ : syracuseStep 1105301 = 51811) (by norm_num)
theorem B581021 : Blo 385764 581021 := bbase (se 3 (by rfl) ⟨108941, by rfl⟩ : syracuseStep 581021 = 217883) (by norm_num)
theorem B875933 : Blo 385764 875933 := bbase (se 3 (by rfl) ⟨164237, by rfl⟩ : syracuseStep 875933 = 328475) (by norm_num)
theorem B581045 : Blo 385764 581045 := bbase (se 5 (by rfl) ⟨27236, by rfl⟩ : syracuseStep 581045 = 54473) (by norm_num)
theorem B581069 : Blo 385764 581069 := bbase (se 3 (by rfl) ⟨108950, by rfl⟩ : syracuseStep 581069 = 217901) (by norm_num)
theorem B581093 : Blo 385764 581093 := bbase (se 4 (by rfl) ⟨54477, by rfl⟩ : syracuseStep 581093 = 108955) (by norm_num)
theorem B876005 : Blo 385764 876005 := bbase (se 4 (by rfl) ⟨82125, by rfl⟩ : syracuseStep 876005 = 164251) (by norm_num)
theorem B581117 : Blo 385764 581117 := bbase (se 3 (by rfl) ⟨108959, by rfl⟩ : syracuseStep 581117 = 217919) (by norm_num)
theorem B581141 : Blo 385764 581141 := bbase (se 6 (by rfl) ⟨13620, by rfl⟩ : syracuseStep 581141 = 27241) (by norm_num)
theorem B581165 : Blo 385764 581165 := bbase (se 3 (by rfl) ⟨108968, by rfl⟩ : syracuseStep 581165 = 217937) (by norm_num)
theorem B876077 : Blo 385764 876077 := bbase (se 3 (by rfl) ⟨164264, by rfl⟩ : syracuseStep 876077 = 328529) (by norm_num)
theorem B1957445 : Blo 385764 1957445 := bbase (se 4 (by rfl) ⟨183510, by rfl⟩ : syracuseStep 1957445 = 367021) (by norm_num)
theorem B581189 : Blo 385764 581189 := bbase (se 4 (by rfl) ⟨54486, by rfl⟩ : syracuseStep 581189 = 108973) (by norm_num)
theorem B1302101 : Blo 385764 1302101 := bbase (se 8 (by rfl) ⟨7629, by rfl⟩ : syracuseStep 1302101 = 15259) (by norm_num)
theorem B581213 : Blo 385764 581213 := bbase (se 3 (by rfl) ⟨108977, by rfl⟩ : syracuseStep 581213 = 217955) (by norm_num)
theorem B1662565 : Blo 385764 1662565 := bbase (se 4 (by rfl) ⟨155865, by rfl⟩ : syracuseStep 1662565 = 311731) (by norm_num)
theorem B581237 : Blo 385764 581237 := bbase (se 5 (by rfl) ⟨27245, by rfl⟩ : syracuseStep 581237 = 54491) (by norm_num)
theorem B876149 : Blo 385764 876149 := bbase (se 5 (by rfl) ⟨41069, by rfl⟩ : syracuseStep 876149 = 82139) (by norm_num)
theorem B581261 : Blo 385764 581261 := bbase (se 3 (by rfl) ⟨108986, by rfl⟩ : syracuseStep 581261 = 217973) (by norm_num)
theorem B2219669 : Blo 385764 2219669 := bbase (se 6 (by rfl) ⟨52023, by rfl⟩ : syracuseStep 2219669 = 104047) (by norm_num)
theorem B581285 : Blo 385764 581285 := bbase (se 4 (by rfl) ⟨54495, by rfl⟩ : syracuseStep 581285 = 108991) (by norm_num)
theorem B581309 : Blo 385764 581309 := bbase (se 3 (by rfl) ⟨108995, by rfl⟩ : syracuseStep 581309 = 217991) (by norm_num)
theorem B876221 : Blo 385764 876221 := bbase (se 3 (by rfl) ⟨164291, by rfl⟩ : syracuseStep 876221 = 328583) (by norm_num)
theorem B581333 : Blo 385764 581333 := bbase (se 7 (by rfl) ⟨6812, by rfl⟩ : syracuseStep 581333 = 13625) (by norm_num)
theorem B581357 : Blo 385764 581357 := bbase (se 3 (by rfl) ⟨109004, by rfl⟩ : syracuseStep 581357 = 218009) (by norm_num)
theorem B581381 : Blo 385764 581381 := bbase (se 4 (by rfl) ⟨54504, by rfl⟩ : syracuseStep 581381 = 109009) (by norm_num)
theorem B876293 : Blo 385764 876293 := bbase (se 4 (by rfl) ⟨82152, by rfl⟩ : syracuseStep 876293 = 164305) (by norm_num)
theorem B581405 : Blo 385764 581405 := bbase (se 3 (by rfl) ⟨109013, by rfl⟩ : syracuseStep 581405 = 218027) (by norm_num)
theorem B581429 : Blo 385764 581429 := bbase (se 5 (by rfl) ⟨27254, by rfl⟩ : syracuseStep 581429 = 54509) (by norm_num)
theorem B1892165 : Blo 385764 1892165 := bbase (se 4 (by rfl) ⟨177390, by rfl⟩ : syracuseStep 1892165 = 354781) (by norm_num)
theorem B581453 : Blo 385764 581453 := bbase (se 3 (by rfl) ⟨109022, by rfl⟩ : syracuseStep 581453 = 218045) (by norm_num)
theorem B876365 : Blo 385764 876365 := bbase (se 3 (by rfl) ⟨164318, by rfl⟩ : syracuseStep 876365 = 328637) (by norm_num)
theorem B1859429 : Blo 385764 1859429 := bbase (se 4 (by rfl) ⟨174321, by rfl⟩ : syracuseStep 1859429 = 348643) (by norm_num)
theorem B581477 : Blo 385764 581477 := bbase (se 4 (by rfl) ⟨54513, by rfl⟩ : syracuseStep 581477 = 109027) (by norm_num)
theorem B581501 : Blo 385764 581501 := bbase (se 3 (by rfl) ⟨109031, by rfl⟩ : syracuseStep 581501 = 218063) (by norm_num)
theorem B581525 : Blo 385764 581525 := bbase (se 6 (by rfl) ⟨13629, by rfl⟩ : syracuseStep 581525 = 27259) (by norm_num)
theorem B876437 : Blo 385764 876437 := bbase (se 6 (by rfl) ⟨20541, by rfl⟩ : syracuseStep 876437 = 41083) (by norm_num)
theorem B581549 : Blo 385764 581549 := bbase (se 3 (by rfl) ⟨109040, by rfl⟩ : syracuseStep 581549 = 218081) (by norm_num)
theorem B581573 : Blo 385764 581573 := bbase (se 4 (by rfl) ⟨54522, by rfl⟩ : syracuseStep 581573 = 109045) (by norm_num)
theorem B581597 : Blo 385764 581597 := bbase (se 3 (by rfl) ⟨109049, by rfl⟩ : syracuseStep 581597 = 218099) (by norm_num)
theorem B876509 : Blo 385764 876509 := bbase (se 3 (by rfl) ⟨164345, by rfl⟩ : syracuseStep 876509 = 328691) (by norm_num)
theorem B1564645 : Blo 385764 1564645 := bbase (se 4 (by rfl) ⟨146685, by rfl⟩ : syracuseStep 1564645 = 293371) (by norm_num)
theorem B581621 : Blo 385764 581621 := bbase (se 5 (by rfl) ⟨27263, by rfl⟩ : syracuseStep 581621 = 54527) (by norm_num)
theorem B1302533 : Blo 385764 1302533 := bbase (se 4 (by rfl) ⟨122112, by rfl⟩ : syracuseStep 1302533 = 244225) (by norm_num)
theorem B581645 : Blo 385764 581645 := bbase (se 3 (by rfl) ⟨109058, by rfl⟩ : syracuseStep 581645 = 218117) (by norm_num)
theorem B581669 : Blo 385764 581669 := bbase (se 4 (by rfl) ⟨54531, by rfl⟩ : syracuseStep 581669 = 109063) (by norm_num)
theorem B876581 : Blo 385764 876581 := bbase (se 4 (by rfl) ⟨82179, by rfl⟩ : syracuseStep 876581 = 164359) (by norm_num)
theorem B1237045 : Blo 385764 1237045 := bbase (se 5 (by rfl) ⟨57986, by rfl⟩ : syracuseStep 1237045 = 115973) (by norm_num)
theorem B581693 : Blo 385764 581693 := bbase (se 3 (by rfl) ⟨109067, by rfl⟩ : syracuseStep 581693 = 218135) (by norm_num)
theorem B581717 : Blo 385764 581717 := bbase (se 8 (by rfl) ⟨3408, by rfl⟩ : syracuseStep 581717 = 6817) (by norm_num)
theorem B581741 : Blo 385764 581741 := bbase (se 3 (by rfl) ⟨109076, by rfl⟩ : syracuseStep 581741 = 218153) (by norm_num)
theorem B876653 : Blo 385764 876653 := bbase (se 3 (by rfl) ⟨164372, by rfl⟩ : syracuseStep 876653 = 328745) (by norm_num)
theorem B581765 : Blo 385764 581765 := bbase (se 4 (by rfl) ⟨54540, by rfl⟩ : syracuseStep 581765 = 109081) (by norm_num)
theorem B581789 : Blo 385764 581789 := bbase (se 3 (by rfl) ⟨109085, by rfl⟩ : syracuseStep 581789 = 218171) (by norm_num)
theorem B581813 : Blo 385764 581813 := bbase (se 5 (by rfl) ⟨27272, by rfl⟩ : syracuseStep 581813 = 54545) (by norm_num)
theorem B876725 : Blo 385764 876725 := bbase (se 5 (by rfl) ⟨41096, by rfl⟩ : syracuseStep 876725 = 82193) (by norm_num)
theorem B745661 : Blo 385764 745661 := bbase (se 3 (by rfl) ⟨139811, by rfl⟩ : syracuseStep 745661 = 279623) (by norm_num)
theorem B581837 : Blo 385764 581837 := bbase (se 3 (by rfl) ⟨109094, by rfl⟩ : syracuseStep 581837 = 218189) (by norm_num)
theorem B581861 : Blo 385764 581861 := bbase (se 4 (by rfl) ⟨54549, by rfl⟩ : syracuseStep 581861 = 109099) (by norm_num)
theorem B581885 : Blo 385764 581885 := bbase (se 3 (by rfl) ⟨109103, by rfl⟩ : syracuseStep 581885 = 218207) (by norm_num)
theorem B876797 : Blo 385764 876797 := bbase (se 3 (by rfl) ⟨164399, by rfl⟩ : syracuseStep 876797 = 328799) (by norm_num)
theorem B581909 : Blo 385764 581909 := bbase (se 6 (by rfl) ⟨13638, by rfl⟩ : syracuseStep 581909 = 27277) (by norm_num)
theorem B581933 : Blo 385764 581933 := bbase (se 3 (by rfl) ⟨109112, by rfl⟩ : syracuseStep 581933 = 218225) (by norm_num)
theorem B581957 : Blo 385764 581957 := bbase (se 4 (by rfl) ⟨54558, by rfl⟩ : syracuseStep 581957 = 109117) (by norm_num)
theorem B876869 : Blo 385764 876869 := bbase (se 4 (by rfl) ⟨82206, by rfl⟩ : syracuseStep 876869 = 164413) (by norm_num)
theorem B581981 : Blo 385764 581981 := bbase (se 3 (by rfl) ⟨109121, by rfl⟩ : syracuseStep 581981 = 218243) (by norm_num)
theorem B582005 : Blo 385764 582005 := bbase (se 5 (by rfl) ⟨27281, by rfl⟩ : syracuseStep 582005 = 54563) (by norm_num)
theorem B582029 : Blo 385764 582029 := bbase (se 3 (by rfl) ⟨109130, by rfl⟩ : syracuseStep 582029 = 218261) (by norm_num)
theorem B876941 : Blo 385764 876941 := bbase (se 3 (by rfl) ⟨164426, by rfl⟩ : syracuseStep 876941 = 328853) (by norm_num)
theorem B582053 : Blo 385764 582053 := bbase (se 4 (by rfl) ⟨54567, by rfl⟩ : syracuseStep 582053 = 109135) (by norm_num)
theorem B1302965 : Blo 385764 1302965 := bbase (se 5 (by rfl) ⟨61076, by rfl⟩ : syracuseStep 1302965 = 122153) (by norm_num)
theorem B582077 : Blo 385764 582077 := bbase (se 3 (by rfl) ⟨109139, by rfl⟩ : syracuseStep 582077 = 218279) (by norm_num)
theorem B582101 : Blo 385764 582101 := bbase (se 7 (by rfl) ⟨6821, by rfl⟩ : syracuseStep 582101 = 13643) (by norm_num)
theorem B582125 : Blo 385764 582125 := bbase (se 3 (by rfl) ⟨109148, by rfl⟩ : syracuseStep 582125 = 218297) (by norm_num)
theorem B1237493 : Blo 385764 1237493 := bbase (se 5 (by rfl) ⟨58007, by rfl⟩ : syracuseStep 1237493 = 116015) (by norm_num)
theorem B1466869 : Blo 385764 1466869 := bbase (se 5 (by rfl) ⟨68759, by rfl⟩ : syracuseStep 1466869 = 137519) (by norm_num)
theorem B582149 : Blo 385764 582149 := bbase (se 4 (by rfl) ⟨54576, by rfl⟩ : syracuseStep 582149 = 109153) (by norm_num)
theorem B582173 : Blo 385764 582173 := bbase (se 3 (by rfl) ⟨109157, by rfl⟩ : syracuseStep 582173 = 218315) (by norm_num)
theorem B582197 : Blo 385764 582197 := bbase (se 5 (by rfl) ⟨27290, by rfl⟩ : syracuseStep 582197 = 54581) (by norm_num)
theorem B582221 : Blo 385764 582221 := bbase (se 3 (by rfl) ⟨109166, by rfl⟩ : syracuseStep 582221 = 218333) (by norm_num)
theorem B549461 : Blo 385764 549461 := bbase (se 8 (by rfl) ⟨3219, by rfl⟩ : syracuseStep 549461 = 6439) (by norm_num)
theorem B582245 : Blo 385764 582245 := bbase (se 4 (by rfl) ⟨54585, by rfl⟩ : syracuseStep 582245 = 109171) (by norm_num)
theorem B582269 : Blo 385764 582269 := bbase (se 3 (by rfl) ⟨109175, by rfl⟩ : syracuseStep 582269 = 218351) (by norm_num)
theorem B582293 : Blo 385764 582293 := bbase (se 6 (by rfl) ⟨13647, by rfl⟩ : syracuseStep 582293 = 27295) (by norm_num)
theorem B549541 : Blo 385764 549541 := bbase (se 4 (by rfl) ⟨51519, by rfl⟩ : syracuseStep 549541 = 103039) (by norm_num)
theorem B582317 : Blo 385764 582317 := bbase (se 3 (by rfl) ⟨109184, by rfl⟩ : syracuseStep 582317 = 218369) (by norm_num)
theorem B582341 : Blo 385764 582341 := bbase (se 4 (by rfl) ⟨54594, by rfl⟩ : syracuseStep 582341 = 109189) (by norm_num)
theorem B582365 : Blo 385764 582365 := bbase (se 3 (by rfl) ⟨109193, by rfl⟩ : syracuseStep 582365 = 218387) (by norm_num)
theorem B582389 : Blo 385764 582389 := bbase (se 5 (by rfl) ⟨27299, by rfl⟩ : syracuseStep 582389 = 54599) (by norm_num)
theorem B582413 : Blo 385764 582413 := bbase (se 3 (by rfl) ⟨109202, by rfl⟩ : syracuseStep 582413 = 218405) (by norm_num)
theorem B549661 : Blo 385764 549661 := bbase (se 3 (by rfl) ⟨103061, by rfl⟩ : syracuseStep 549661 = 206123) (by norm_num)
theorem B1467173 : Blo 385764 1467173 := bbase (se 4 (by rfl) ⟨137547, by rfl⟩ : syracuseStep 1467173 = 275095) (by norm_num)
theorem B582437 : Blo 385764 582437 := bbase (se 4 (by rfl) ⟨54603, by rfl⟩ : syracuseStep 582437 = 109207) (by norm_num)
theorem B582461 : Blo 385764 582461 := bbase (se 3 (by rfl) ⟨109211, by rfl⟩ : syracuseStep 582461 = 218423) (by norm_num)
theorem B1958741 : Blo 385764 1958741 := bbase (se 9 (by rfl) ⟨5738, by rfl⟩ : syracuseStep 1958741 = 11477) (by norm_num)
theorem B582485 : Blo 385764 582485 := bbase (se 9 (by rfl) ⟨1706, by rfl⟩ : syracuseStep 582485 = 3413) (by norm_num)
theorem B1303397 : Blo 385764 1303397 := bbase (se 4 (by rfl) ⟨122193, by rfl⟩ : syracuseStep 1303397 = 244387) (by norm_num)
theorem B582509 : Blo 385764 582509 := bbase (se 3 (by rfl) ⟨109220, by rfl⟩ : syracuseStep 582509 = 218441) (by norm_num)
theorem B549757 : Blo 385764 549757 := bbase (se 3 (by rfl) ⟨103079, by rfl⟩ : syracuseStep 549757 = 206159) (by norm_num)
theorem B582533 : Blo 385764 582533 := bbase (se 4 (by rfl) ⟨54612, by rfl⟩ : syracuseStep 582533 = 109225) (by norm_num)
theorem B582557 : Blo 385764 582557 := bbase (se 3 (by rfl) ⟨109229, by rfl⟩ : syracuseStep 582557 = 218459) (by norm_num)
theorem B582581 : Blo 385764 582581 := bbase (se 5 (by rfl) ⟨27308, by rfl⟩ : syracuseStep 582581 = 54617) (by norm_num)
theorem B1106885 : Blo 385764 1106885 := bbase (se 4 (by rfl) ⟨103770, by rfl⟩ : syracuseStep 1106885 = 207541) (by norm_num)
theorem B582605 : Blo 385764 582605 := bbase (se 3 (by rfl) ⟨109238, by rfl⟩ : syracuseStep 582605 = 218477) (by norm_num)
theorem B582629 : Blo 385764 582629 := bbase (se 4 (by rfl) ⟨54621, by rfl⟩ : syracuseStep 582629 = 109243) (by norm_num)
theorem B582653 : Blo 385764 582653 := bbase (se 3 (by rfl) ⟨109247, by rfl⟩ : syracuseStep 582653 = 218495) (by norm_num)
theorem B582677 : Blo 385764 582677 := bbase (se 6 (by rfl) ⟨13656, by rfl⟩ : syracuseStep 582677 = 27313) (by norm_num)
theorem B582701 : Blo 385764 582701 := bbase (se 3 (by rfl) ⟨109256, by rfl⟩ : syracuseStep 582701 = 218513) (by norm_num)
theorem B582725 : Blo 385764 582725 := bbase (se 4 (by rfl) ⟨54630, by rfl⟩ : syracuseStep 582725 = 109261) (by norm_num)
theorem B582749 : Blo 385764 582749 := bbase (se 3 (by rfl) ⟨109265, by rfl⟩ : syracuseStep 582749 = 218531) (by norm_num)
theorem B582773 : Blo 385764 582773 := bbase (se 5 (by rfl) ⟨27317, by rfl⟩ : syracuseStep 582773 = 54635) (by norm_num)
theorem B582797 : Blo 385764 582797 := bbase (se 3 (by rfl) ⟨109274, by rfl⟩ : syracuseStep 582797 = 218549) (by norm_num)
theorem B582821 : Blo 385764 582821 := bbase (se 4 (by rfl) ⟨54639, by rfl⟩ : syracuseStep 582821 = 109279) (by norm_num)
theorem B582845 : Blo 385764 582845 := bbase (se 3 (by rfl) ⟨109283, by rfl⟩ : syracuseStep 582845 = 218567) (by norm_num)
theorem B582869 : Blo 385764 582869 := bbase (se 7 (by rfl) ⟨6830, by rfl⟩ : syracuseStep 582869 = 13661) (by norm_num)
theorem B1402069 : Blo 385764 1402069 := bbase (se 7 (by rfl) ⟨16430, by rfl⟩ : syracuseStep 1402069 = 32861) (by norm_num)
theorem B582893 : Blo 385764 582893 := bbase (se 3 (by rfl) ⟨109292, by rfl⟩ : syracuseStep 582893 = 218585) (by norm_num)
theorem B1860853 : Blo 385764 1860853 := bbase (se 5 (by rfl) ⟨87227, by rfl⟩ : syracuseStep 1860853 = 174455) (by norm_num)
theorem B582917 : Blo 385764 582917 := bbase (se 4 (by rfl) ⟨54648, by rfl⟩ : syracuseStep 582917 = 109297) (by norm_num)
theorem B1303829 : Blo 385764 1303829 := bbase (se 6 (by rfl) ⟨30558, by rfl⟩ : syracuseStep 1303829 = 61117) (by norm_num)
theorem B582941 : Blo 385764 582941 := bbase (se 3 (by rfl) ⟨109301, by rfl⟩ : syracuseStep 582941 = 218603) (by norm_num)
theorem B582965 : Blo 385764 582965 := bbase (se 5 (by rfl) ⟨27326, by rfl⟩ : syracuseStep 582965 = 54653) (by norm_num)
theorem B582989 : Blo 385764 582989 := bbase (se 3 (by rfl) ⟨109310, by rfl⟩ : syracuseStep 582989 = 218621) (by norm_num)
theorem B583013 : Blo 385764 583013 := bbase (se 4 (by rfl) ⟨54657, by rfl⟩ : syracuseStep 583013 = 109315) (by norm_num)
theorem B550253 : Blo 385764 550253 := bbase (se 3 (by rfl) ⟨103172, by rfl⟩ : syracuseStep 550253 = 206345) (by norm_num)
theorem B583037 : Blo 385764 583037 := bbase (se 3 (by rfl) ⟨109319, by rfl⟩ : syracuseStep 583037 = 218639) (by norm_num)
theorem B583061 : Blo 385764 583061 := bbase (se 6 (by rfl) ⟨13665, by rfl⟩ : syracuseStep 583061 = 27331) (by norm_num)
theorem B583085 : Blo 385764 583085 := bbase (se 3 (by rfl) ⟨109328, by rfl⟩ : syracuseStep 583085 = 218657) (by norm_num)
theorem B583109 : Blo 385764 583109 := bbase (se 4 (by rfl) ⟨54666, by rfl⟩ : syracuseStep 583109 = 109333) (by norm_num)
theorem B583133 : Blo 385764 583133 := bbase (se 3 (by rfl) ⟨109337, by rfl⟩ : syracuseStep 583133 = 218675) (by norm_num)
theorem B583157 : Blo 385764 583157 := bbase (se 5 (by rfl) ⟨27335, by rfl⟩ : syracuseStep 583157 = 54671) (by norm_num)
theorem B583181 : Blo 385764 583181 := bbase (se 3 (by rfl) ⟨109346, by rfl⟩ : syracuseStep 583181 = 218693) (by norm_num)
theorem B583205 : Blo 385764 583205 := bbase (se 4 (by rfl) ⟨54675, by rfl⟩ : syracuseStep 583205 = 109351) (by norm_num)
theorem B583229 : Blo 385764 583229 := bbase (se 3 (by rfl) ⟨109355, by rfl⟩ : syracuseStep 583229 = 218711) (by norm_num)
theorem B583253 : Blo 385764 583253 := bbase (se 8 (by rfl) ⟨3417, by rfl⟩ : syracuseStep 583253 = 6835) (by norm_num)
theorem B1107557 : Blo 385764 1107557 := bbase (se 4 (by rfl) ⟨103833, by rfl⟩ : syracuseStep 1107557 = 207667) (by norm_num)
theorem B583277 : Blo 385764 583277 := bbase (se 3 (by rfl) ⟨109364, by rfl⟩ : syracuseStep 583277 = 218729) (by norm_num)
theorem B583301 : Blo 385764 583301 := bbase (se 4 (by rfl) ⟨54684, by rfl⟩ : syracuseStep 583301 = 109369) (by norm_num)
theorem B1402517 : Blo 385764 1402517 := bbase (se 6 (by rfl) ⟨32871, by rfl⟩ : syracuseStep 1402517 = 65743) (by norm_num)
theorem B583325 : Blo 385764 583325 := bbase (se 3 (by rfl) ⟨109373, by rfl⟩ : syracuseStep 583325 = 218747) (by norm_num)
theorem B583349 : Blo 385764 583349 := bbase (se 5 (by rfl) ⟨27344, by rfl⟩ : syracuseStep 583349 = 54689) (by norm_num)
theorem B1304261 : Blo 385764 1304261 := bbase (se 4 (by rfl) ⟨122274, by rfl⟩ : syracuseStep 1304261 = 244549) (by norm_num)
theorem B583373 : Blo 385764 583373 := bbase (se 3 (by rfl) ⟨109382, by rfl⟩ : syracuseStep 583373 = 218765) (by norm_num)
theorem B583397 : Blo 385764 583397 := bbase (se 4 (by rfl) ⟨54693, by rfl⟩ : syracuseStep 583397 = 109387) (by norm_num)
theorem B976637 : Blo 385764 976637 := bbase (se 3 (by rfl) ⟨183119, by rfl⟩ : syracuseStep 976637 = 366239) (by norm_num)
theorem B583421 : Blo 385764 583421 := bbase (se 3 (by rfl) ⟨109391, by rfl⟩ : syracuseStep 583421 = 218783) (by norm_num)
theorem B583445 : Blo 385764 583445 := bbase (se 6 (by rfl) ⟨13674, by rfl⟩ : syracuseStep 583445 = 27349) (by norm_num)
theorem B583469 : Blo 385764 583469 := bbase (se 3 (by rfl) ⟨109400, by rfl⟩ : syracuseStep 583469 = 218801) (by norm_num)
theorem B583493 : Blo 385764 583493 := bbase (se 4 (by rfl) ⟨54702, by rfl⟩ : syracuseStep 583493 = 109405) (by norm_num)
theorem B583517 : Blo 385764 583517 := bbase (se 3 (by rfl) ⟨109409, by rfl⟩ : syracuseStep 583517 = 218819) (by norm_num)
theorem B583541 : Blo 385764 583541 := bbase (se 5 (by rfl) ⟨27353, by rfl⟩ : syracuseStep 583541 = 54707) (by norm_num)
theorem B583565 : Blo 385764 583565 := bbase (se 3 (by rfl) ⟨109418, by rfl⟩ : syracuseStep 583565 = 218837) (by norm_num)
theorem B550805 : Blo 385764 550805 := bbase (se 6 (by rfl) ⟨12909, by rfl⟩ : syracuseStep 550805 = 25819) (by norm_num)
theorem B583589 : Blo 385764 583589 := bbase (se 4 (by rfl) ⟨54711, by rfl⟩ : syracuseStep 583589 = 109423) (by norm_num)
theorem B583613 : Blo 385764 583613 := bbase (se 3 (by rfl) ⟨109427, by rfl⟩ : syracuseStep 583613 = 218855) (by norm_num)
theorem B14378965 : Blo 385764 14378965 := bbase (se 7 (by rfl) ⟨168503, by rfl⟩ : syracuseStep 14378965 = 337007) (by norm_num)
theorem B583637 : Blo 385764 583637 := bbase (se 7 (by rfl) ⟨6839, by rfl⟩ : syracuseStep 583637 = 13679) (by norm_num)
theorem B583661 : Blo 385764 583661 := bbase (se 3 (by rfl) ⟨109436, by rfl⟩ : syracuseStep 583661 = 218873) (by norm_num)
theorem B583685 : Blo 385764 583685 := bbase (se 4 (by rfl) ⟨54720, by rfl⟩ : syracuseStep 583685 = 109441) (by norm_num)
theorem B1107989 : Blo 385764 1107989 := bbase (se 6 (by rfl) ⟨25968, by rfl⟩ : syracuseStep 1107989 = 51937) (by norm_num)
theorem B583709 : Blo 385764 583709 := bbase (se 3 (by rfl) ⟨109445, by rfl⟩ : syracuseStep 583709 = 218891) (by norm_num)
theorem B583733 : Blo 385764 583733 := bbase (se 5 (by rfl) ⟨27362, by rfl⟩ : syracuseStep 583733 = 54725) (by norm_num)
theorem B583757 : Blo 385764 583757 := bbase (se 3 (by rfl) ⟨109454, by rfl⟩ : syracuseStep 583757 = 218909) (by norm_num)
theorem B976981 : Blo 385764 976981 := bbase (se 8 (by rfl) ⟨5724, by rfl⟩ : syracuseStep 976981 = 11449) (by norm_num)
theorem B1960037 : Blo 385764 1960037 := bbase (se 4 (by rfl) ⟨183753, by rfl⟩ : syracuseStep 1960037 = 367507) (by norm_num)
theorem B583781 : Blo 385764 583781 := bbase (se 4 (by rfl) ⟨54729, by rfl⟩ : syracuseStep 583781 = 109459) (by norm_num)
theorem B1304693 : Blo 385764 1304693 := bbase (se 5 (by rfl) ⟨61157, by rfl⟩ : syracuseStep 1304693 = 122315) (by norm_num)
theorem B2484341 : Blo 385764 2484341 := bbase (se 5 (by rfl) ⟨116453, by rfl⟩ : syracuseStep 2484341 = 232907) (by norm_num)
theorem B583805 : Blo 385764 583805 := bbase (se 3 (by rfl) ⟨109463, by rfl⟩ : syracuseStep 583805 = 218927) (by norm_num)
theorem B583829 : Blo 385764 583829 := bbase (se 6 (by rfl) ⟨13683, by rfl⟩ : syracuseStep 583829 = 27367) (by norm_num)
theorem B583853 : Blo 385764 583853 := bbase (se 3 (by rfl) ⟨109472, by rfl⟩ : syracuseStep 583853 = 218945) (by norm_num)
theorem B977093 : Blo 385764 977093 := bbase (se 4 (by rfl) ⟨91602, by rfl⟩ : syracuseStep 977093 = 183205) (by norm_num)
theorem B583877 : Blo 385764 583877 := bbase (se 4 (by rfl) ⟨54738, by rfl⟩ : syracuseStep 583877 = 109477) (by norm_num)
theorem B583901 : Blo 385764 583901 := bbase (se 3 (by rfl) ⟨109481, by rfl⟩ : syracuseStep 583901 = 218963) (by norm_num)
theorem B583925 : Blo 385764 583925 := bbase (se 5 (by rfl) ⟨27371, by rfl⟩ : syracuseStep 583925 = 54743) (by norm_num)
theorem B1894661 : Blo 385764 1894661 := bbase (se 4 (by rfl) ⟨177624, by rfl⟩ : syracuseStep 1894661 = 355249) (by norm_num)
theorem B583949 : Blo 385764 583949 := bbase (se 3 (by rfl) ⟨109490, by rfl⟩ : syracuseStep 583949 = 218981) (by norm_num)
theorem B583973 : Blo 385764 583973 := bbase (se 4 (by rfl) ⟨54747, by rfl⟩ : syracuseStep 583973 = 109495) (by norm_num)
theorem B583997 : Blo 385764 583997 := bbase (se 3 (by rfl) ⟨109499, by rfl⟩ : syracuseStep 583997 = 218999) (by norm_num)
theorem B584021 : Blo 385764 584021 := bbase (se 10 (by rfl) ⟨855, by rfl⟩ : syracuseStep 584021 = 1711) (by norm_num)
theorem B584045 : Blo 385764 584045 := bbase (se 3 (by rfl) ⟨109508, by rfl⟩ : syracuseStep 584045 = 219017) (by norm_num)
theorem B977285 : Blo 385764 977285 := bbase (se 4 (by rfl) ⟨91620, by rfl⟩ : syracuseStep 977285 = 183241) (by norm_num)
theorem B584069 : Blo 385764 584069 := bbase (se 4 (by rfl) ⟨54756, by rfl⟩ : syracuseStep 584069 = 109513) (by norm_num)
theorem B584093 : Blo 385764 584093 := bbase (se 3 (by rfl) ⟨109517, by rfl⟩ : syracuseStep 584093 = 219035) (by norm_num)
theorem B584117 : Blo 385764 584117 := bbase (se 5 (by rfl) ⟨27380, by rfl⟩ : syracuseStep 584117 = 54761) (by norm_num)
theorem B584141 : Blo 385764 584141 := bbase (se 3 (by rfl) ⟨109526, by rfl⟩ : syracuseStep 584141 = 219053) (by norm_num)
theorem B584165 : Blo 385764 584165 := bbase (se 4 (by rfl) ⟨54765, by rfl⟩ : syracuseStep 584165 = 109531) (by norm_num)
theorem B584189 : Blo 385764 584189 := bbase (se 3 (by rfl) ⟨109535, by rfl⟩ : syracuseStep 584189 = 219071) (by norm_num)
theorem B584213 : Blo 385764 584213 := bbase (se 6 (by rfl) ⟨13692, by rfl⟩ : syracuseStep 584213 = 27385) (by norm_num)
theorem B1305125 : Blo 385764 1305125 := bbase (se 4 (by rfl) ⟨122355, by rfl⟩ : syracuseStep 1305125 = 244711) (by norm_num)
theorem B584237 : Blo 385764 584237 := bbase (se 3 (by rfl) ⟨109544, by rfl⟩ : syracuseStep 584237 = 219089) (by norm_num)
theorem B584261 : Blo 385764 584261 := bbase (se 4 (by rfl) ⟨54774, by rfl⟩ : syracuseStep 584261 = 109549) (by norm_num)
theorem B584285 : Blo 385764 584285 := bbase (se 3 (by rfl) ⟨109553, by rfl⟩ : syracuseStep 584285 = 219107) (by norm_num)
theorem B584309 : Blo 385764 584309 := bbase (se 5 (by rfl) ⟨27389, by rfl⟩ : syracuseStep 584309 = 54779) (by norm_num)
theorem B551557 : Blo 385764 551557 := bbase (se 4 (by rfl) ⟨51708, by rfl⟩ : syracuseStep 551557 = 103417) (by norm_num)
theorem B584333 : Blo 385764 584333 := bbase (se 3 (by rfl) ⟨109562, by rfl⟩ : syracuseStep 584333 = 219125) (by norm_num)
theorem B584357 : Blo 385764 584357 := bbase (se 4 (by rfl) ⟨54783, by rfl⟩ : syracuseStep 584357 = 109567) (by norm_num)
theorem B584381 : Blo 385764 584381 := bbase (se 3 (by rfl) ⟨109571, by rfl⟩ : syracuseStep 584381 = 219143) (by norm_num)
theorem B1239749 : Blo 385764 1239749 := bbase (se 4 (by rfl) ⟨116226, by rfl⟩ : syracuseStep 1239749 = 232453) (by norm_num)
theorem B2943701 : Blo 385764 2943701 := bbase (se 7 (by rfl) ⟨34496, by rfl⟩ : syracuseStep 2943701 = 68993) (by norm_num)
theorem B584405 : Blo 385764 584405 := bbase (se 7 (by rfl) ⟨6848, by rfl⟩ : syracuseStep 584405 = 13697) (by norm_num)
theorem B977629 : Blo 385764 977629 := bbase (se 3 (by rfl) ⟨183305, by rfl⟩ : syracuseStep 977629 = 366611) (by norm_num)
theorem B584429 : Blo 385764 584429 := bbase (se 3 (by rfl) ⟨109580, by rfl⟩ : syracuseStep 584429 = 219161) (by norm_num)
theorem B1108741 : Blo 385764 1108741 := bbase (se 4 (by rfl) ⟨103944, by rfl⟩ : syracuseStep 1108741 = 207889) (by norm_num)
theorem B584453 : Blo 385764 584453 := bbase (se 4 (by rfl) ⟨54792, by rfl⟩ : syracuseStep 584453 = 109585) (by norm_num)
theorem B584477 : Blo 385764 584477 := bbase (se 3 (by rfl) ⟨109589, by rfl⟩ : syracuseStep 584477 = 219179) (by norm_num)
theorem B584501 : Blo 385764 584501 := bbase (se 5 (by rfl) ⟨27398, by rfl⟩ : syracuseStep 584501 = 54797) (by norm_num)
theorem B977741 : Blo 385764 977741 := bbase (se 3 (by rfl) ⟨183326, by rfl⟩ : syracuseStep 977741 = 366653) (by norm_num)
theorem B584525 : Blo 385764 584525 := bbase (se 3 (by rfl) ⟨109598, by rfl⟩ : syracuseStep 584525 = 219197) (by norm_num)
theorem B1469285 : Blo 385764 1469285 := bbase (se 4 (by rfl) ⟨137745, by rfl⟩ : syracuseStep 1469285 = 275491) (by norm_num)
theorem B584549 : Blo 385764 584549 := bbase (se 4 (by rfl) ⟨54801, by rfl⟩ : syracuseStep 584549 = 109603) (by norm_num)
theorem B584573 : Blo 385764 584573 := bbase (se 3 (by rfl) ⟨109607, by rfl⟩ : syracuseStep 584573 = 219215) (by norm_num)
theorem B584597 : Blo 385764 584597 := bbase (se 6 (by rfl) ⟨13701, by rfl⟩ : syracuseStep 584597 = 27403) (by norm_num)
theorem B584621 : Blo 385764 584621 := bbase (se 3 (by rfl) ⟨109616, by rfl⟩ : syracuseStep 584621 = 219233) (by norm_num)
theorem B584645 : Blo 385764 584645 := bbase (se 4 (by rfl) ⟨54810, by rfl⟩ : syracuseStep 584645 = 109621) (by norm_num)
theorem B1305557 : Blo 385764 1305557 := bbase (se 7 (by rfl) ⟨15299, by rfl⟩ : syracuseStep 1305557 = 30599) (by norm_num)
theorem B977933 : Blo 385764 977933 := bbase (se 3 (by rfl) ⟨183362, by rfl⟩ : syracuseStep 977933 = 366725) (by norm_num)
theorem B1469573 : Blo 385764 1469573 := bbase (se 4 (by rfl) ⟨137772, by rfl⟩ : syracuseStep 1469573 = 275545) (by norm_num)
theorem B879869 : Blo 385764 879869 := bbase (se 3 (by rfl) ⟨164975, by rfl⟩ : syracuseStep 879869 = 329951) (by norm_num)
theorem B3534101 : Blo 385764 3534101 := bbase (se 6 (by rfl) ⟨82830, by rfl⟩ : syracuseStep 3534101 = 165661) (by norm_num)
theorem B978277 : Blo 385764 978277 := bbase (se 4 (by rfl) ⟨91713, by rfl⟩ : syracuseStep 978277 = 183427) (by norm_num)
theorem B1961333 : Blo 385764 1961333 := bbase (se 5 (by rfl) ⟨91937, by rfl⟩ : syracuseStep 1961333 = 183875) (by norm_num)
theorem B1305989 : Blo 385764 1305989 := bbase (se 4 (by rfl) ⟨122436, by rfl⟩ : syracuseStep 1305989 = 244873) (by norm_num)
theorem B552349 : Blo 385764 552349 := bbase (se 3 (by rfl) ⟨103565, by rfl⟩ : syracuseStep 552349 = 207131) (by norm_num)
theorem B978389 : Blo 385764 978389 := bbase (se 7 (by rfl) ⟨11465, by rfl⟩ : syracuseStep 978389 = 22931) (by norm_num)
theorem B421373 : Blo 385764 421373 := bbase (se 3 (by rfl) ⟨79007, by rfl⟩ : syracuseStep 421373 = 158015) (by norm_num)
theorem B2780725 : Blo 385764 2780725 := bbase (se 5 (by rfl) ⟨130346, by rfl⟩ : syracuseStep 2780725 = 260693) (by norm_num)
theorem B978581 : Blo 385764 978581 := bbase (se 6 (by rfl) ⟨22935, by rfl⟩ : syracuseStep 978581 = 45871) (by norm_num)
theorem B618221 : Blo 385764 618221 := bbase (se 3 (by rfl) ⟨115916, by rfl⟩ : syracuseStep 618221 = 231833) (by norm_num)
theorem B552685 : Blo 385764 552685 := bbase (se 3 (by rfl) ⟨103628, by rfl⟩ : syracuseStep 552685 = 207257) (by norm_num)
theorem B651037 : Blo 385764 651037 := bbase (se 3 (by rfl) ⟨122069, by rfl⟩ : syracuseStep 651037 = 244139) (by norm_num)
theorem B1306421 : Blo 385764 1306421 := bbase (se 5 (by rfl) ⟨61238, by rfl⟩ : syracuseStep 1306421 = 122477) (by norm_num)
theorem B618349 : Blo 385764 618349 := bbase (se 3 (by rfl) ⟨115940, by rfl⟩ : syracuseStep 618349 = 231881) (by norm_num)
theorem B651125 : Blo 385764 651125 := bbase (se 5 (by rfl) ⟨30521, by rfl⟩ : syracuseStep 651125 = 61043) (by norm_num)
theorem B1044373 : Blo 385764 1044373 := bbase (se 6 (by rfl) ⟨24477, by rfl⟩ : syracuseStep 1044373 = 48955) (by norm_num)
theorem B552901 : Blo 385764 552901 := bbase (se 4 (by rfl) ⟨51834, by rfl⟩ : syracuseStep 552901 = 103669) (by norm_num)
theorem B978925 : Blo 385764 978925 := bbase (se 3 (by rfl) ⟨183548, by rfl⟩ : syracuseStep 978925 = 367097) (by norm_num)
theorem B651253 : Blo 385764 651253 := bbase (se 5 (by rfl) ⟨30527, by rfl⟩ : syracuseStep 651253 = 61055) (by norm_num)
theorem B651341 : Blo 385764 651341 := bbase (se 3 (by rfl) ⟨122126, by rfl⟩ : syracuseStep 651341 = 244253) (by norm_num)
theorem B979037 : Blo 385764 979037 := bbase (se 3 (by rfl) ⟨183569, by rfl⟩ : syracuseStep 979037 = 367139) (by norm_num)
theorem B1896629 : Blo 385764 1896629 := bbase (se 5 (by rfl) ⟨88904, by rfl⟩ : syracuseStep 1896629 = 177809) (by norm_num)
theorem B651469 : Blo 385764 651469 := bbase (se 3 (by rfl) ⟨122150, by rfl⟩ : syracuseStep 651469 = 244301) (by norm_num)
theorem B1306853 : Blo 385764 1306853 := bbase (se 4 (by rfl) ⟨122517, by rfl⟩ : syracuseStep 1306853 = 245035) (by norm_num)
theorem B979229 : Blo 385764 979229 := bbase (se 3 (by rfl) ⟨183605, by rfl⟩ : syracuseStep 979229 = 367211) (by norm_num)
theorem B651557 : Blo 385764 651557 := bbase (se 4 (by rfl) ⟨61083, by rfl⟩ : syracuseStep 651557 = 122167) (by norm_num)
theorem B1470757 : Blo 385764 1470757 := bbase (se 4 (by rfl) ⟨137883, by rfl⟩ : syracuseStep 1470757 = 275767) (by norm_num)
theorem B553277 : Blo 385764 553277 := bbase (se 3 (by rfl) ⟨103739, by rfl⟩ : syracuseStep 553277 = 207479) (by norm_num)
theorem B651685 : Blo 385764 651685 := bbase (se 4 (by rfl) ⟨61095, by rfl⟩ : syracuseStep 651685 = 122191) (by norm_num)
theorem B651773 : Blo 385764 651773 := bbase (se 3 (by rfl) ⟨122207, by rfl⟩ : syracuseStep 651773 = 244415) (by norm_num)
theorem B1471061 : Blo 385764 1471061 := bbase (se 8 (by rfl) ⟨8619, by rfl⟩ : syracuseStep 1471061 = 17239) (by norm_num)
theorem B979573 : Blo 385764 979573 := bbase (se 5 (by rfl) ⟨45917, by rfl⟩ : syracuseStep 979573 = 91835) (by norm_num)
theorem B651901 : Blo 385764 651901 := bbase (se 3 (by rfl) ⟨122231, by rfl⟩ : syracuseStep 651901 = 244463) (by norm_num)
theorem B1962629 : Blo 385764 1962629 := bbase (se 4 (by rfl) ⟨183996, by rfl⟩ : syracuseStep 1962629 = 367993) (by norm_num)
theorem B619157 : Blo 385764 619157 := bbase (se 6 (by rfl) ⟨14511, by rfl⟩ : syracuseStep 619157 = 29023) (by norm_num)
theorem B1307285 : Blo 385764 1307285 := bbase (se 6 (by rfl) ⟨30639, by rfl⟩ : syracuseStep 1307285 = 61279) (by norm_num)
theorem B651989 : Blo 385764 651989 := bbase (se 7 (by rfl) ⟨7640, by rfl⟩ : syracuseStep 651989 = 15281) (by norm_num)
theorem B3306197 : Blo 385764 3306197 := bbase (se 7 (by rfl) ⟨38744, by rfl⟩ : syracuseStep 3306197 = 77489) (by norm_num)
theorem B979685 : Blo 385764 979685 := bbase (se 4 (by rfl) ⟨91845, by rfl⟩ : syracuseStep 979685 = 183691) (by norm_num)
theorem B652117 : Blo 385764 652117 := bbase (se 9 (by rfl) ⟨1910, by rfl⟩ : syracuseStep 652117 = 3821) (by norm_num)
theorem B5665621 : Blo 385764 5665621 := bbase (se 9 (by rfl) ⟨16598, by rfl⟩ : syracuseStep 5665621 = 33197) (by norm_num)
theorem B979877 : Blo 385764 979877 := bbase (se 4 (by rfl) ⟨91863, by rfl⟩ : syracuseStep 979877 = 183727) (by norm_num)
theorem B652205 : Blo 385764 652205 := bbase (se 3 (by rfl) ⟨122288, by rfl⟩ : syracuseStep 652205 = 244577) (by norm_num)
theorem B488369 : Blo 385764 488369 := bbase (se 2 (by rfl) ⟨183138, by rfl⟩ : syracuseStep 488369 = 366277) (by norm_num)
theorem B619445 : Blo 385764 619445 := bbase (se 5 (by rfl) ⟨29036, by rfl⟩ : syracuseStep 619445 = 58073) (by norm_num)
theorem B488425 : Blo 385764 488425 := bbase (se 2 (by rfl) ⟨183159, by rfl⟩ : syracuseStep 488425 = 366319) (by norm_num)
theorem B1176565 : Blo 385764 1176565 := bbase (se 5 (by rfl) ⟨55151, by rfl⟩ : syracuseStep 1176565 = 110303) (by norm_num)
theorem B1045541 : Blo 385764 1045541 := bbase (se 4 (by rfl) ⟨98019, by rfl⟩ : syracuseStep 1045541 = 196039) (by norm_num)
theorem B652333 : Blo 385764 652333 := bbase (se 3 (by rfl) ⟨122312, by rfl⟩ : syracuseStep 652333 = 244625) (by norm_num)
theorem B1307717 : Blo 385764 1307717 := bbase (se 4 (by rfl) ⟨122598, by rfl⟩ : syracuseStep 1307717 = 245197) (by norm_num)
theorem B488521 : Blo 385764 488521 := bbase (se 2 (by rfl) ⟨183195, by rfl⟩ : syracuseStep 488521 = 366391) (by norm_num)
theorem B652421 : Blo 385764 652421 := bbase (se 4 (by rfl) ⟨61164, by rfl⟩ : syracuseStep 652421 = 122329) (by norm_num)
theorem B586973 : Blo 385764 586973 := bbase (se 3 (by rfl) ⟨110057, by rfl⟩ : syracuseStep 586973 = 220115) (by norm_num)
theorem B488693 : Blo 385764 488693 := bbase (se 5 (by rfl) ⟨22907, by rfl⟩ : syracuseStep 488693 = 45815) (by norm_num)
theorem B980221 : Blo 385764 980221 := bbase (se 3 (by rfl) ⟨183791, by rfl⟩ : syracuseStep 980221 = 367583) (by norm_num)
theorem B652549 : Blo 385764 652549 := bbase (se 4 (by rfl) ⟨61176, by rfl⟩ : syracuseStep 652549 = 122353) (by norm_num)
theorem B1045781 : Blo 385764 1045781 := bbase (se 6 (by rfl) ⟨24510, by rfl⟩ : syracuseStep 1045781 = 49021) (by norm_num)
theorem B488749 : Blo 385764 488749 := bbase (se 3 (by rfl) ⟨91640, by rfl⟩ : syracuseStep 488749 = 183281) (by norm_num)
theorem B619861 : Blo 385764 619861 := bbase (se 13 (by rfl) ⟨113, by rfl⟩ : syracuseStep 619861 = 227) (by norm_num)
theorem B652637 : Blo 385764 652637 := bbase (se 3 (by rfl) ⟨122369, by rfl⟩ : syracuseStep 652637 = 244739) (by norm_num)
theorem B521581 : Blo 385764 521581 := bbase (se 3 (by rfl) ⟨97796, by rfl⟩ : syracuseStep 521581 = 195593) (by norm_num)
theorem B980333 : Blo 385764 980333 := bbase (se 3 (by rfl) ⟨183812, by rfl⟩ : syracuseStep 980333 = 367625) (by norm_num)
theorem B488845 : Blo 385764 488845 := bbase (se 3 (by rfl) ⟨91658, by rfl⟩ : syracuseStep 488845 = 183317) (by norm_num)
theorem B652765 : Blo 385764 652765 := bbase (se 3 (by rfl) ⟨122393, by rfl⟩ : syracuseStep 652765 = 244787) (by norm_num)
theorem B1308149 : Blo 385764 1308149 := bbase (se 5 (by rfl) ⟨61319, by rfl⟩ : syracuseStep 1308149 = 122639) (by norm_num)
theorem B980525 : Blo 385764 980525 := bbase (se 3 (by rfl) ⟨183848, by rfl⟩ : syracuseStep 980525 = 367697) (by norm_num)
theorem B652853 : Blo 385764 652853 := bbase (se 5 (by rfl) ⟨30602, by rfl⟩ : syracuseStep 652853 = 61205) (by norm_num)
theorem B489017 : Blo 385764 489017 := bbase (se 2 (by rfl) ⟨183381, by rfl⟩ : syracuseStep 489017 = 366763) (by norm_num)
theorem B2979413 : Blo 385764 2979413 := bbase (se 8 (by rfl) ⟨17457, by rfl⟩ : syracuseStep 2979413 = 34915) (by norm_num)
theorem B489073 : Blo 385764 489073 := bbase (se 2 (by rfl) ⟨183402, by rfl⟩ : syracuseStep 489073 = 366805) (by norm_num)
theorem B652981 : Blo 385764 652981 := bbase (se 5 (by rfl) ⟨30608, by rfl⟩ : syracuseStep 652981 = 61217) (by norm_num)
theorem B554701 : Blo 385764 554701 := bbase (se 3 (by rfl) ⟨104006, by rfl⟩ : syracuseStep 554701 = 208013) (by norm_num)
theorem B489169 : Blo 385764 489169 := bbase (se 2 (by rfl) ⟨183438, by rfl⟩ : syracuseStep 489169 = 366877) (by norm_num)
theorem B653069 : Blo 385764 653069 := bbase (se 3 (by rfl) ⟨122450, by rfl⟩ : syracuseStep 653069 = 244901) (by norm_num)
theorem B587557 : Blo 385764 587557 := bbase (se 4 (by rfl) ⟨55083, by rfl⟩ : syracuseStep 587557 = 110167) (by norm_num)
theorem B489341 : Blo 385764 489341 := bbase (se 3 (by rfl) ⟨91751, by rfl⟩ : syracuseStep 489341 = 183503) (by norm_num)
theorem B980869 : Blo 385764 980869 := bbase (se 4 (by rfl) ⟨91956, by rfl⟩ : syracuseStep 980869 = 183913) (by norm_num)
theorem B653197 : Blo 385764 653197 := bbase (se 3 (by rfl) ⟨122474, by rfl⟩ : syracuseStep 653197 = 244949) (by norm_num)
theorem B1963925 : Blo 385764 1963925 := bbase (se 6 (by rfl) ⟨46029, by rfl⟩ : syracuseStep 1963925 = 92059) (by norm_num)
theorem B1308581 : Blo 385764 1308581 := bbase (se 4 (by rfl) ⟨122679, by rfl⟩ : syracuseStep 1308581 = 245359) (by norm_num)
theorem B489397 : Blo 385764 489397 := bbase (se 5 (by rfl) ⟨22940, by rfl⟩ : syracuseStep 489397 = 45881) (by norm_num)
theorem B653285 : Blo 385764 653285 := bbase (se 4 (by rfl) ⟨61245, by rfl⟩ : syracuseStep 653285 = 122491) (by norm_num)
theorem B980981 : Blo 385764 980981 := bbase (se 5 (by rfl) ⟨45983, by rfl⟩ : syracuseStep 980981 = 91967) (by norm_num)
theorem B1865717 : Blo 385764 1865717 := bbase (se 5 (by rfl) ⟨87455, by rfl⟩ : syracuseStep 1865717 = 174911) (by norm_num)
theorem B489493 : Blo 385764 489493 := bbase (se 6 (by rfl) ⟨11472, by rfl⟩ : syracuseStep 489493 = 22945) (by norm_num)
theorem B653413 : Blo 385764 653413 := bbase (se 4 (by rfl) ⟨61257, by rfl⟩ : syracuseStep 653413 = 122515) (by norm_num)
theorem B587893 : Blo 385764 587893 := bbase (se 5 (by rfl) ⟨27557, by rfl⟩ : syracuseStep 587893 = 55115) (by norm_num)
theorem B981173 : Blo 385764 981173 := bbase (se 5 (by rfl) ⟨45992, by rfl⟩ : syracuseStep 981173 = 91985) (by norm_num)
theorem B653501 : Blo 385764 653501 := bbase (se 3 (by rfl) ⟨122531, by rfl⟩ : syracuseStep 653501 = 245063) (by norm_num)
theorem B489665 : Blo 385764 489665 := bbase (se 2 (by rfl) ⟨183624, by rfl⟩ : syracuseStep 489665 = 367249) (by norm_num)
theorem B489721 : Blo 385764 489721 := bbase (se 2 (by rfl) ⟨183645, by rfl⟩ : syracuseStep 489721 = 367291) (by norm_num)
theorem B620797 : Blo 385764 620797 := bbase (se 3 (by rfl) ⟨116399, by rfl⟩ : syracuseStep 620797 = 232799) (by norm_num)
theorem B653629 : Blo 385764 653629 := bbase (se 3 (by rfl) ⟨122555, by rfl⟩ : syracuseStep 653629 = 245111) (by norm_num)
theorem B1309013 : Blo 385764 1309013 := bbase (se 10 (by rfl) ⟨1917, by rfl⟩ : syracuseStep 1309013 = 3835) (by norm_num)
theorem B489817 : Blo 385764 489817 := bbase (se 2 (by rfl) ⟨183681, by rfl⟩ : syracuseStep 489817 = 367363) (by norm_num)
theorem B653717 : Blo 385764 653717 := bbase (se 6 (by rfl) ⟨15321, by rfl⟩ : syracuseStep 653717 = 30643) (by norm_num)
theorem B1800629 : Blo 385764 1800629 := bbase (se 5 (by rfl) ⟨84404, by rfl⟩ : syracuseStep 1800629 = 168809) (by norm_num)
theorem B784837 : Blo 385764 784837 := bbase (se 4 (by rfl) ⟨73578, by rfl⟩ : syracuseStep 784837 = 147157) (by norm_num)
theorem B489989 : Blo 385764 489989 := bbase (se 4 (by rfl) ⟨45936, by rfl⟩ : syracuseStep 489989 = 91873) (by norm_num)
theorem B981517 : Blo 385764 981517 := bbase (se 3 (by rfl) ⟨184034, by rfl⟩ : syracuseStep 981517 = 368069) (by norm_num)
theorem B653845 : Blo 385764 653845 := bbase (se 6 (by rfl) ⟨15324, by rfl⟩ : syracuseStep 653845 = 30649) (by norm_num)
theorem B1243669 : Blo 385764 1243669 := bbase (se 6 (by rfl) ⟨29148, by rfl⟩ : syracuseStep 1243669 = 58297) (by norm_num)
theorem B490045 : Blo 385764 490045 := bbase (se 3 (by rfl) ⟨91883, by rfl⟩ : syracuseStep 490045 = 183767) (by norm_num)
theorem B653933 : Blo 385764 653933 := bbase (se 3 (by rfl) ⟨122612, by rfl⟩ : syracuseStep 653933 = 245225) (by norm_num)
theorem B981629 : Blo 385764 981629 := bbase (se 3 (by rfl) ⟨184055, by rfl⟩ : syracuseStep 981629 = 368111) (by norm_num)
theorem B1473173 : Blo 385764 1473173 := bbase (se 6 (by rfl) ⟨34527, by rfl⟩ : syracuseStep 1473173 = 69055) (by norm_num)
theorem B490141 : Blo 385764 490141 := bbase (se 3 (by rfl) ⟨91901, by rfl⟩ : syracuseStep 490141 = 183803) (by norm_num)
theorem B654061 : Blo 385764 654061 := bbase (se 3 (by rfl) ⟨122636, by rfl⟩ : syracuseStep 654061 = 245273) (by norm_num)
theorem B1309445 : Blo 385764 1309445 := bbase (se 4 (by rfl) ⟨122760, by rfl⟩ : syracuseStep 1309445 = 245521) (by norm_num)
theorem B1243925 : Blo 385764 1243925 := bbase (se 6 (by rfl) ⟨29154, by rfl⟩ : syracuseStep 1243925 = 58309) (by norm_num)
theorem B981821 : Blo 385764 981821 := bbase (se 3 (by rfl) ⟨184091, by rfl⟩ : syracuseStep 981821 = 368183) (by norm_num)
theorem B654149 : Blo 385764 654149 := bbase (se 4 (by rfl) ⟨61326, by rfl⟩ : syracuseStep 654149 = 122653) (by norm_num)
theorem B490313 : Blo 385764 490313 := bbase (se 2 (by rfl) ⟨183867, by rfl⟩ : syracuseStep 490313 = 367735) (by norm_num)
theorem B490369 : Blo 385764 490369 := bbase (se 2 (by rfl) ⟨183888, by rfl⟩ : syracuseStep 490369 = 367777) (by norm_num)
theorem B588725 : Blo 385764 588725 := bbase (se 5 (by rfl) ⟨27596, by rfl⟩ : syracuseStep 588725 = 55193) (by norm_num)
theorem B1473461 : Blo 385764 1473461 := bbase (se 5 (by rfl) ⟨69068, by rfl⟩ : syracuseStep 1473461 = 138137) (by norm_num)
theorem B654277 : Blo 385764 654277 := bbase (se 4 (by rfl) ⟨61338, by rfl⟩ : syracuseStep 654277 = 122677) (by norm_num)
theorem B490465 : Blo 385764 490465 := bbase (se 2 (by rfl) ⟨183924, by rfl⟩ : syracuseStep 490465 = 367849) (by norm_num)
theorem B588773 : Blo 385764 588773 := bbase (se 4 (by rfl) ⟨55197, by rfl⟩ : syracuseStep 588773 = 110395) (by norm_num)
theorem B654365 : Blo 385764 654365 := bbase (se 3 (by rfl) ⟨122693, by rfl⟩ : syracuseStep 654365 = 245387) (by norm_num)
theorem B490637 : Blo 385764 490637 := bbase (se 3 (by rfl) ⟨91994, by rfl⟩ : syracuseStep 490637 = 183989) (by norm_num)
theorem B982165 : Blo 385764 982165 := bbase (se 6 (by rfl) ⟨23019, by rfl⟩ : syracuseStep 982165 = 46039) (by norm_num)
theorem B654493 : Blo 385764 654493 := bbase (se 3 (by rfl) ⟨122717, by rfl⟩ : syracuseStep 654493 = 245435) (by norm_num)
theorem B1965221 : Blo 385764 1965221 := bbase (se 4 (by rfl) ⟨184239, by rfl⟩ : syracuseStep 1965221 = 368479) (by norm_num)
theorem B1309877 : Blo 385764 1309877 := bbase (se 5 (by rfl) ⟨61400, by rfl⟩ : syracuseStep 1309877 = 122801) (by norm_num)
theorem B490693 : Blo 385764 490693 := bbase (se 4 (by rfl) ⟨46002, by rfl⟩ : syracuseStep 490693 = 92005) (by norm_num)
theorem B654581 : Blo 385764 654581 := bbase (se 5 (by rfl) ⟨30683, by rfl⟩ : syracuseStep 654581 = 61367) (by norm_num)
theorem B982277 : Blo 385764 982277 := bbase (se 4 (by rfl) ⟨92088, by rfl⟩ : syracuseStep 982277 = 184177) (by norm_num)
theorem B490789 : Blo 385764 490789 := bbase (se 4 (by rfl) ⟨46011, by rfl⟩ : syracuseStep 490789 = 92023) (by norm_num)
theorem B654709 : Blo 385764 654709 := bbase (se 5 (by rfl) ⟨30689, by rfl⟩ : syracuseStep 654709 = 61379) (by norm_num)
theorem B621989 : Blo 385764 621989 := bbase (se 4 (by rfl) ⟨58311, by rfl⟩ : syracuseStep 621989 = 116623) (by norm_num)
theorem B982469 : Blo 385764 982469 := bbase (se 4 (by rfl) ⟨92106, by rfl⟩ : syracuseStep 982469 = 184213) (by norm_num)
theorem B654797 : Blo 385764 654797 := bbase (se 3 (by rfl) ⟨122774, by rfl⟩ : syracuseStep 654797 = 245549) (by norm_num)
theorem B490961 : Blo 385764 490961 := bbase (se 2 (by rfl) ⟨184110, by rfl⟩ : syracuseStep 490961 = 368221) (by norm_num)
theorem B589285 : Blo 385764 589285 := bbase (se 4 (by rfl) ⟨55245, by rfl⟩ : syracuseStep 589285 = 110491) (by norm_num)
theorem B491017 : Blo 385764 491017 := bbase (se 2 (by rfl) ⟨184131, by rfl⟩ : syracuseStep 491017 = 368263) (by norm_num)
theorem B785933 : Blo 385764 785933 := bbase (se 3 (by rfl) ⟨147362, by rfl⟩ : syracuseStep 785933 = 294725) (by norm_num)
theorem B654925 : Blo 385764 654925 := bbase (se 3 (by rfl) ⟨122798, by rfl⟩ : syracuseStep 654925 = 245597) (by norm_num)
theorem B1867349 : Blo 385764 1867349 := bbase (se 8 (by rfl) ⟨10941, by rfl⟩ : syracuseStep 1867349 = 21883) (by norm_num)
theorem B1310309 : Blo 385764 1310309 := bbase (se 4 (by rfl) ⟨122841, by rfl⟩ : syracuseStep 1310309 = 245683) (by norm_num)
theorem B622181 : Blo 385764 622181 := bbase (se 4 (by rfl) ⟨58329, by rfl⟩ : syracuseStep 622181 = 116659) (by norm_num)
theorem B491113 : Blo 385764 491113 := bbase (se 2 (by rfl) ⟨184167, by rfl⟩ : syracuseStep 491113 = 368335) (by norm_num)
theorem B3309173 : Blo 385764 3309173 := bbase (se 5 (by rfl) ⟨155117, by rfl⟩ : syracuseStep 3309173 = 310235) (by norm_num)
theorem B655013 : Blo 385764 655013 := bbase (se 4 (by rfl) ⟨61407, by rfl⟩ : syracuseStep 655013 = 122815) (by norm_num)
theorem B589565 : Blo 385764 589565 := bbase (se 3 (by rfl) ⟨110543, by rfl⟩ : syracuseStep 589565 = 221087) (by norm_num)
theorem B851717 : Blo 385764 851717 := bbase (se 4 (by rfl) ⟨79848, by rfl⟩ : syracuseStep 851717 = 159697) (by norm_num)
theorem B491285 : Blo 385764 491285 := bbase (se 6 (by rfl) ⟨11514, by rfl⟩ : syracuseStep 491285 = 23029) (by norm_num)
theorem B982813 : Blo 385764 982813 := bbase (se 3 (by rfl) ⟨184277, by rfl⟩ : syracuseStep 982813 = 368555) (by norm_num)
theorem B655141 : Blo 385764 655141 := bbase (se 4 (by rfl) ⟨61419, by rfl⟩ : syracuseStep 655141 = 122839) (by norm_num)
theorem B491341 : Blo 385764 491341 := bbase (se 3 (by rfl) ⟨92126, by rfl⟩ : syracuseStep 491341 = 184253) (by norm_num)
theorem B655229 : Blo 385764 655229 := bbase (se 3 (by rfl) ⟨122855, by rfl⟩ : syracuseStep 655229 = 245711) (by norm_num)
theorem B884621 : Blo 385764 884621 := bbase (se 3 (by rfl) ⟨165866, by rfl⟩ : syracuseStep 884621 = 331733) (by norm_num)
theorem B982925 : Blo 385764 982925 := bbase (se 3 (by rfl) ⟨184298, by rfl⟩ : syracuseStep 982925 = 368597) (by norm_num)
theorem B491437 : Blo 385764 491437 := bbase (se 3 (by rfl) ⟨92144, by rfl⟩ : syracuseStep 491437 = 184289) (by norm_num)
theorem B884693 : Blo 385764 884693 := bbase (se 7 (by rfl) ⟨10367, by rfl⟩ : syracuseStep 884693 = 20735) (by norm_num)
theorem B655357 : Blo 385764 655357 := bbase (se 3 (by rfl) ⟨122879, by rfl⟩ : syracuseStep 655357 = 245759) (by norm_num)
theorem B655411 : Blo 385764 655411 := bstep (se 1 (by rfl) ⟨491558, by rfl⟩ : syracuseStep 655411 = 983117) B983117
theorem B2097265 : Blo 385764 2097265 := bstep (se 2 (by rfl) ⟨786474, by rfl⟩ : syracuseStep 2097265 = 1572949) B1572949
theorem B1966193 : Blo 385764 1966193 := bstep (se 2 (by rfl) ⟨737322, by rfl⟩ : syracuseStep 1966193 = 1474645) B1474645
theorem B524435 : Blo 385764 524435 := bstep (se 1 (by rfl) ⟨393326, by rfl⟩ : syracuseStep 524435 = 786653) B786653
theorem B655553 : Blo 385764 655553 := bstep (se 2 (by rfl) ⟨245832, by rfl⟩ : syracuseStep 655553 = 491665) B491665
theorem B983249 : Blo 385764 983249 := bstep (se 2 (by rfl) ⟨368718, by rfl⟩ : syracuseStep 983249 = 737437) B737437
theorem B1310957 : Blo 385764 1310957 := bstep (se 3 (by rfl) ⟨245804, by rfl⟩ : syracuseStep 1310957 = 491609) B491609
theorem B983299 : Blo 385764 983299 := bstep (se 1 (by rfl) ⟨737474, by rfl⟩ : syracuseStep 983299 = 1474949) B1474949
theorem B1311011 : Blo 385764 1311011 := bstep (se 1 (by rfl) ⟨983258, by rfl⟩ : syracuseStep 1311011 = 1966517) B1966517
theorem B491827 : Blo 385764 491827 := bstep (se 1 (by rfl) ⟨368870, by rfl⟩ : syracuseStep 491827 = 737741) B737741
theorem B655681 : Blo 385764 655681 := bstep (se 2 (by rfl) ⟨245880, by rfl⟩ : syracuseStep 655681 = 491761) B491761
theorem B655715 : Blo 385764 655715 := bstep (se 1 (by rfl) ⟨491786, by rfl⟩ : syracuseStep 655715 = 983573) B983573
theorem B983441 : Blo 385764 983441 := bstep (se 2 (by rfl) ⟨368790, by rfl⟩ : syracuseStep 983441 = 737581) B737581
theorem B491923 : Blo 385764 491923 := bstep (se 1 (by rfl) ⟨368942, by rfl⟩ : syracuseStep 491923 = 737885) B737885
theorem B4194787 : Blo 385764 4194787 := bstep (se 1 (by rfl) ⟨3146090, by rfl⟩ : syracuseStep 4194787 = 6292181) B6292181
theorem B655843 : Blo 385764 655843 := bstep (se 1 (by rfl) ⟨491882, by rfl⟩ : syracuseStep 655843 = 983765) B983765
theorem B1311281 : Blo 385764 1311281 := bstep (se 2 (by rfl) ⟨491730, by rfl⟩ : syracuseStep 1311281 = 983461) B983461
theorem B623155 : Blo 385764 623155 := bstep (se 1 (by rfl) ⟨467366, by rfl⟩ : syracuseStep 623155 = 934733) B934733
theorem B2228849 : Blo 385764 2228849 := bstep (se 2 (by rfl) ⟨835818, by rfl⟩ : syracuseStep 2228849 = 1671637) B1671637
theorem B655985 : Blo 385764 655985 := bstep (se 2 (by rfl) ⟨245994, by rfl⟩ : syracuseStep 655985 = 491989) B491989
theorem B656113 : Blo 385764 656113 := bstep (se 2 (by rfl) ⟨246042, by rfl⟩ : syracuseStep 656113 = 492085) B492085
theorem B656147 : Blo 385764 656147 := bstep (se 1 (by rfl) ⟨492110, by rfl⟩ : syracuseStep 656147 = 984221) B984221
theorem B1868579 : Blo 385764 1868579 := bstep (se 1 (by rfl) ⟨1401434, by rfl⟩ : syracuseStep 1868579 = 2802869) B2802869
theorem B1475405 : Blo 385764 1475405 := bstep (se 3 (by rfl) ⟨276638, by rfl⟩ : syracuseStep 1475405 = 553277) B553277
theorem B2786147 : Blo 385764 2786147 := bstep (se 1 (by rfl) ⟨2089610, by rfl⟩ : syracuseStep 2786147 = 4179221) B4179221
theorem B2491235 : Blo 385764 2491235 := bstep (se 1 (by rfl) ⟨1868426, by rfl⟩ : syracuseStep 2491235 = 3736853) B3736853
theorem B492419 : Blo 385764 492419 := bstep (se 1 (by rfl) ⟨369314, by rfl⟩ : syracuseStep 492419 = 738629) B738629
theorem B656275 : Blo 385764 656275 := bstep (se 1 (by rfl) ⟨492206, by rfl⟩ : syracuseStep 656275 = 984413) B984413
theorem B623603 : Blo 385764 623603 := bstep (se 1 (by rfl) ⟨467702, by rfl⟩ : syracuseStep 623603 = 935405) B935405
theorem B656417 : Blo 385764 656417 := bstep (se 2 (by rfl) ⟨246156, by rfl⟩ : syracuseStep 656417 = 492313) B492313
theorem B4949045 : Blo 385764 4949045 := bstep (se 5 (by rfl) ⟨231986, by rfl⟩ : syracuseStep 4949045 = 463973) B463973
theorem B590915 : Blo 385764 590915 := bstep (se 1 (by rfl) ⟨443186, by rfl⟩ : syracuseStep 590915 = 886373) B886373
theorem B1311821 : Blo 385764 1311821 := bstep (se 3 (by rfl) ⟨245966, by rfl⟩ : syracuseStep 1311821 = 491933) B491933
theorem B1573987 : Blo 385764 1573987 := bstep (se 1 (by rfl) ⟨1180490, by rfl⟩ : syracuseStep 1573987 = 2360981) B2360981
theorem B525425 : Blo 385764 525425 := bstep (se 2 (by rfl) ⟨197034, by rfl⟩ : syracuseStep 525425 = 394069) B394069
theorem B1311875 : Blo 385764 1311875 := bstep (se 1 (by rfl) ⟨983906, by rfl⟩ : syracuseStep 1311875 = 1967813) B1967813
theorem B656545 : Blo 385764 656545 := bstep (se 2 (by rfl) ⟨246204, by rfl⟩ : syracuseStep 656545 = 492409) B492409
theorem B1246385 : Blo 385764 1246385 := bstep (se 2 (by rfl) ⟨467394, by rfl⟩ : syracuseStep 1246385 = 934789) B934789
theorem B656579 : Blo 385764 656579 := bstep (se 1 (by rfl) ⟨492434, by rfl⟩ : syracuseStep 656579 = 984869) B984869
theorem B656707 : Blo 385764 656707 := bstep (se 1 (by rfl) ⟨492530, by rfl⟩ : syracuseStep 656707 = 985061) B985061
theorem B4425029 : Blo 385764 4425029 := bstep (se 4 (by rfl) ⟨414846, by rfl⟩ : syracuseStep 4425029 = 829693) B829693
theorem B984433 : Blo 385764 984433 := bstep (se 2 (by rfl) ⟨369162, by rfl⟩ : syracuseStep 984433 = 738325) B738325
theorem B1312145 : Blo 385764 1312145 := bstep (se 2 (by rfl) ⟨492054, by rfl⟩ : syracuseStep 1312145 = 984109) B984109
theorem B1181101 : Blo 385764 1181101 := bstep (se 3 (by rfl) ⟨221456, by rfl⟩ : syracuseStep 1181101 = 442913) B442913
theorem B656849 : Blo 385764 656849 := bstep (se 2 (by rfl) ⟨246318, by rfl⟩ : syracuseStep 656849 = 492637) B492637
theorem B624161 : Blo 385764 624161 := bstep (se 2 (by rfl) ⟨234060, by rfl⟩ : syracuseStep 624161 = 468121) B468121
theorem B1967651 : Blo 385764 1967651 := bstep (se 1 (by rfl) ⟨1475738, by rfl⟩ : syracuseStep 1967651 = 2951477) B2951477
theorem B493123 : Blo 385764 493123 := bstep (se 1 (by rfl) ⟨369842, by rfl⟩ : syracuseStep 493123 = 739685) B739685
theorem B656977 : Blo 385764 656977 := bstep (se 2 (by rfl) ⟨246366, by rfl⟩ : syracuseStep 656977 = 492733) B492733
theorem B1869425 : Blo 385764 1869425 := bstep (se 2 (by rfl) ⟨701034, by rfl⟩ : syracuseStep 1869425 = 1402069) B1402069
theorem B657011 : Blo 385764 657011 := bstep (se 1 (by rfl) ⟨492758, by rfl⟩ : syracuseStep 657011 = 985517) B985517
theorem B984707 : Blo 385764 984707 := bstep (se 1 (by rfl) ⟨738530, by rfl⟩ : syracuseStep 984707 = 1477061) B1477061
theorem B525971 : Blo 385764 525971 := bstep (se 1 (by rfl) ⟨394478, by rfl⟩ : syracuseStep 525971 = 788957) B788957
theorem B493219 : Blo 385764 493219 := bstep (se 1 (by rfl) ⟨369914, by rfl⟩ : syracuseStep 493219 = 739829) B739829
theorem B657139 : Blo 385764 657139 := bstep (se 1 (by rfl) ⟨492854, by rfl⟩ : syracuseStep 657139 = 985709) B985709
theorem B984899 : Blo 385764 984899 := bstep (se 1 (by rfl) ⟨738674, by rfl⟩ : syracuseStep 984899 = 1477349) B1477349
theorem B657281 : Blo 385764 657281 := bstep (se 2 (by rfl) ⟨246480, by rfl⟩ : syracuseStep 657281 = 492961) B492961
theorem B1312685 : Blo 385764 1312685 := bstep (se 3 (by rfl) ⟨246128, by rfl⟩ : syracuseStep 1312685 = 492257) B492257
theorem B1312739 : Blo 385764 1312739 := bstep (se 1 (by rfl) ⟨984554, by rfl⟩ : syracuseStep 1312739 = 1969109) B1969109
theorem B657409 : Blo 385764 657409 := bstep (se 2 (by rfl) ⟨246528, by rfl⟩ : syracuseStep 657409 = 493057) B493057
theorem B657443 : Blo 385764 657443 := bstep (se 1 (by rfl) ⟨493082, by rfl⟩ : syracuseStep 657443 = 986165) B986165
theorem B1247309 : Blo 385764 1247309 := bstep (se 3 (by rfl) ⟨233870, by rfl⟩ : syracuseStep 1247309 = 467741) B467741
theorem B657571 : Blo 385764 657571 := bstep (se 1 (by rfl) ⟨493178, by rfl⟩ : syracuseStep 657571 = 986357) B986357
theorem B1313009 : Blo 385764 1313009 := bstep (se 2 (by rfl) ⟨492378, by rfl⟩ : syracuseStep 1313009 = 984757) B984757
theorem B1247501 : Blo 385764 1247501 := bstep (se 3 (by rfl) ⟨233906, by rfl⟩ : syracuseStep 1247501 = 467813) B467813
theorem B657713 : Blo 385764 657713 := bstep (se 2 (by rfl) ⟨246642, by rfl⟩ : syracuseStep 657713 = 493285) B493285
theorem B1050947 : Blo 385764 1050947 := bstep (se 1 (by rfl) ⟨788210, by rfl⟩ : syracuseStep 1050947 = 1576421) B1576421
theorem B1968461 : Blo 385764 1968461 := bstep (se 3 (by rfl) ⟨369086, by rfl⟩ : syracuseStep 1968461 = 738173) B738173
theorem B2361905 : Blo 385764 2361905 := bstep (se 2 (by rfl) ⟨885714, by rfl⟩ : syracuseStep 2361905 = 1771429) B1771429
theorem B985841 : Blo 385764 985841 := bstep (se 2 (by rfl) ⟨369690, by rfl⟩ : syracuseStep 985841 = 739381) B739381
theorem B1313549 : Blo 385764 1313549 := bstep (se 3 (by rfl) ⟨246290, by rfl⟩ : syracuseStep 1313549 = 492581) B492581
theorem B985891 : Blo 385764 985891 := bstep (se 1 (by rfl) ⟨739418, by rfl⟩ : syracuseStep 985891 = 1478837) B1478837
theorem B1313603 : Blo 385764 1313603 := bstep (se 1 (by rfl) ⟨985202, by rfl⟩ : syracuseStep 1313603 = 1970405) B1970405
theorem B2657123 : Blo 385764 2657123 := bstep (se 1 (by rfl) ⟨1992842, by rfl⟩ : syracuseStep 2657123 = 3985685) B3985685
theorem B1182595 : Blo 385764 1182595 := bstep (se 1 (by rfl) ⟨886946, by rfl⟩ : syracuseStep 1182595 = 1773893) B1773893
theorem B986033 : Blo 385764 986033 := bstep (se 2 (by rfl) ⟨369762, by rfl⟩ : syracuseStep 986033 = 739525) B739525
theorem B1313873 : Blo 385764 1313873 := bstep (se 2 (by rfl) ⟨492702, by rfl⟩ : syracuseStep 1313873 = 985405) B985405
theorem B2493773 : Blo 385764 2493773 := bstep (se 3 (by rfl) ⟨467582, by rfl⟩ : syracuseStep 2493773 = 935165) B935165
theorem B4197901 : Blo 385764 4197901 := bstep (se 3 (by rfl) ⟨787106, by rfl⟩ : syracuseStep 4197901 = 1574213) B1574213
theorem B1314413 : Blo 385764 1314413 := bstep (se 3 (by rfl) ⟨246452, by rfl⟩ : syracuseStep 1314413 = 492905) B492905
theorem B396947 : Blo 385764 396947 := bstep (se 1 (by rfl) ⟨297710, by rfl⟩ : syracuseStep 396947 = 595421) B595421
theorem B1314467 : Blo 385764 1314467 := bstep (se 1 (by rfl) ⟨985850, by rfl⟩ : syracuseStep 1314467 = 1971701) B1971701
theorem B1478321 : Blo 385764 1478321 := bstep (se 2 (by rfl) ⟨554370, by rfl⟩ : syracuseStep 1478321 = 1108741) B1108741
theorem B1117891 : Blo 385764 1117891 := bstep (se 1 (by rfl) ⟨838418, by rfl⟩ : syracuseStep 1117891 = 1676837) B1676837
theorem B1412963 : Blo 385764 1412963 := bstep (se 1 (by rfl) ⟨1059722, by rfl⟩ : syracuseStep 1412963 = 2119445) B2119445
theorem B1314737 : Blo 385764 1314737 := bstep (se 2 (by rfl) ⟨493026, by rfl⟩ : syracuseStep 1314737 = 986053) B986053
theorem B1871885 : Blo 385764 1871885 := bstep (se 3 (by rfl) ⟨350978, by rfl⟩ : syracuseStep 1871885 = 701957) B701957
theorem B2199757 : Blo 385764 2199757 := bstep (se 3 (by rfl) ⟨412454, by rfl⟩ : syracuseStep 2199757 = 824909) B824909
theorem B1315277 : Blo 385764 1315277 := bstep (se 3 (by rfl) ⟨246614, by rfl⟩ : syracuseStep 1315277 = 493229) B493229
theorem B1315331 : Blo 385764 1315331 := bstep (se 1 (by rfl) ⟨986498, by rfl⟩ : syracuseStep 1315331 = 1972997) B1972997
theorem B561763 : Blo 385764 561763 := bstep (se 1 (by rfl) ⟨421322, by rfl⟩ : syracuseStep 561763 = 842645) B842645
theorem B1053283 : Blo 385764 1053283 := bstep (se 1 (by rfl) ⟨789962, by rfl⟩ : syracuseStep 1053283 = 1579925) B1579925
theorem B627347 : Blo 385764 627347 := bstep (se 1 (by rfl) ⟨470510, by rfl⟩ : syracuseStep 627347 = 941021) B941021
theorem B3707633 : Blo 385764 3707633 := bstep (se 2 (by rfl) ⟨1390362, by rfl⟩ : syracuseStep 3707633 = 2780725) B2780725
theorem B1479779 : Blo 385764 1479779 := bstep (se 1 (by rfl) ⟨1109834, by rfl⟩ : syracuseStep 1479779 = 2219669) B2219669
theorem B824465 : Blo 385764 824465 := bstep (se 2 (by rfl) ⟨309174, by rfl⟩ : syracuseStep 824465 = 618349) B618349
theorem B1971377 : Blo 385764 1971377 := bstep (se 2 (by rfl) ⟨739266, by rfl⟩ : syracuseStep 1971377 = 1478533) B1478533
theorem B1119505 : Blo 385764 1119505 := bstep (se 2 (by rfl) ⟨419814, by rfl⟩ : syracuseStep 1119505 = 839629) B839629
theorem B1185187 : Blo 385764 1185187 := bstep (se 1 (by rfl) ⟨888890, by rfl⟩ : syracuseStep 1185187 = 1777781) B1777781
theorem B464339 : Blo 385764 464339 := bstep (se 1 (by rfl) ⟨348254, by rfl⟩ : syracuseStep 464339 = 696509) B696509
theorem B497107 : Blo 385764 497107 := bstep (se 1 (by rfl) ⟨372830, by rfl⟩ : syracuseStep 497107 = 745661) B745661
theorem B824995 : Blo 385764 824995 := bstep (se 1 (by rfl) ⟨618746, by rfl⟩ : syracuseStep 824995 = 1237493) B1237493
theorem B464675 : Blo 385764 464675 := bstep (se 1 (by rfl) ⟨348506, by rfl⟩ : syracuseStep 464675 = 697013) B697013
theorem B530275 : Blo 385764 530275 := bstep (se 1 (by rfl) ⟨397706, by rfl⟩ : syracuseStep 530275 = 795413) B795413
theorem B5314673 : Blo 385764 5314673 := bstep (se 2 (by rfl) ⟨1993002, by rfl⟩ : syracuseStep 5314673 = 3986005) B3986005
theorem B2201741 : Blo 385764 2201741 := bstep (se 3 (by rfl) ⟨412826, by rfl⟩ : syracuseStep 2201741 = 825653) B825653
theorem B530977 : Blo 385764 530977 := bstep (se 2 (by rfl) ⟨199116, by rfl⟩ : syracuseStep 530977 = 398233) B398233
theorem B1972835 : Blo 385764 1972835 := bstep (se 1 (by rfl) ⟨1479626, by rfl⟩ : syracuseStep 1972835 = 2959253) B2959253
theorem B4430861 : Blo 385764 4430861 := bstep (se 3 (by rfl) ⟨830786, by rfl⟩ : syracuseStep 4430861 = 1661573) B1661573
theorem B2202673 : Blo 385764 2202673 := bstep (se 2 (by rfl) ⟨826002, by rfl⟩ : syracuseStep 2202673 = 1652005) B1652005
theorem B826481 : Blo 385764 826481 := bstep (se 2 (by rfl) ⟨309930, by rfl⟩ : syracuseStep 826481 = 619861) B619861
theorem B826499 : Blo 385764 826499 := bstep (se 1 (by rfl) ⟨619874, by rfl⟩ : syracuseStep 826499 = 1239749) B1239749
theorem B695441 : Blo 385764 695441 := bstep (se 2 (by rfl) ⟨260790, by rfl⟩ : syracuseStep 695441 = 521581) B521581
theorem B1121539 : Blo 385764 1121539 := bstep (se 1 (by rfl) ⟨841154, by rfl⟩ : syracuseStep 1121539 = 1682309) B1682309
theorem B630289 : Blo 385764 630289 := bstep (se 2 (by rfl) ⟨236358, by rfl⟩ : syracuseStep 630289 = 472717) B472717
theorem B1351309 : Blo 385764 1351309 := bstep (se 3 (by rfl) ⟨253370, by rfl⟩ : syracuseStep 1351309 = 506741) B506741
theorem B434083 : Blo 385764 434083 := bstep (se 1 (by rfl) ⟨325562, by rfl⟩ : syracuseStep 434083 = 651125) B651125
theorem B434227 : Blo 385764 434227 := bstep (se 1 (by rfl) ⟨325670, by rfl⟩ : syracuseStep 434227 = 651341) B651341
theorem B598115 : Blo 385764 598115 := bstep (se 1 (by rfl) ⟨448586, by rfl⟩ : syracuseStep 598115 = 897173) B897173
theorem B467059 : Blo 385764 467059 := bstep (se 1 (by rfl) ⟨350294, by rfl⟩ : syracuseStep 467059 = 700589) B700589
theorem B434371 : Blo 385764 434371 := bstep (se 1 (by rfl) ⟨325778, by rfl⟩ : syracuseStep 434371 = 651557) B651557
theorem B467203 : Blo 385764 467203 := bstep (se 1 (by rfl) ⟨350402, by rfl⟩ : syracuseStep 467203 = 700805) B700805
theorem B794947 : Blo 385764 794947 := bstep (se 1 (by rfl) ⟨596210, by rfl⟩ : syracuseStep 794947 = 1192421) B1192421
theorem B827729 : Blo 385764 827729 := bstep (se 2 (by rfl) ⟨310398, by rfl⟩ : syracuseStep 827729 = 620797) B620797
theorem B434515 : Blo 385764 434515 := bstep (se 1 (by rfl) ⟨325886, by rfl⟩ : syracuseStep 434515 = 651773) B651773
theorem B467299 : Blo 385764 467299 := bstep (se 1 (by rfl) ⟨350474, by rfl⟩ : syracuseStep 467299 = 700949) B700949
theorem B434659 : Blo 385764 434659 := bstep (se 1 (by rfl) ⟨325994, by rfl⟩ : syracuseStep 434659 = 651989) B651989
theorem B2204131 : Blo 385764 2204131 := bstep (se 1 (by rfl) ⟨1653098, by rfl⟩ : syracuseStep 2204131 = 3306197) B3306197
theorem B2957795 : Blo 385764 2957795 := bstep (se 1 (by rfl) ⟨2218346, by rfl⟩ : syracuseStep 2957795 = 4436693) B4436693
theorem B2466289 : Blo 385764 2466289 := bstep (se 2 (by rfl) ⟨924858, by rfl⟩ : syracuseStep 2466289 = 1849717) B1849717
theorem B664067 : Blo 385764 664067 := bstep (se 1 (by rfl) ⟨498050, by rfl⟩ : syracuseStep 664067 = 996101) B996101
theorem B434803 : Blo 385764 434803 := bstep (se 1 (by rfl) ⟨326102, by rfl⟩ : syracuseStep 434803 = 652205) B652205
theorem B697027 : Blo 385764 697027 := bstep (se 1 (by rfl) ⟨522770, by rfl⟩ : syracuseStep 697027 = 1045541) B1045541
theorem B434947 : Blo 385764 434947 := bstep (se 1 (by rfl) ⟨326210, by rfl⟩ : syracuseStep 434947 = 652421) B652421
theorem B467779 : Blo 385764 467779 := bstep (se 1 (by rfl) ⟨350834, by rfl⟩ : syracuseStep 467779 = 701669) B701669
theorem B697187 : Blo 385764 697187 := bstep (se 1 (by rfl) ⟨522890, by rfl⟩ : syracuseStep 697187 = 1045781) B1045781
theorem B435091 : Blo 385764 435091 := bstep (se 1 (by rfl) ⟨326318, by rfl⟩ : syracuseStep 435091 = 652637) B652637
theorem B2204657 : Blo 385764 2204657 := bstep (se 2 (by rfl) ⟨826746, by rfl⟩ : syracuseStep 2204657 = 1653493) B1653493
theorem B435235 : Blo 385764 435235 := bstep (se 1 (by rfl) ⟨326426, by rfl⟩ : syracuseStep 435235 = 652853) B652853
theorem B664643 : Blo 385764 664643 := bstep (se 1 (by rfl) ⟨498482, by rfl⟩ : syracuseStep 664643 = 996965) B996965
theorem B435379 : Blo 385764 435379 := bstep (se 1 (by rfl) ⟨326534, by rfl⟩ : syracuseStep 435379 = 653069) B653069
theorem B435523 : Blo 385764 435523 := bstep (se 1 (by rfl) ⟨326642, by rfl⟩ : syracuseStep 435523 = 653285) B653285
theorem B1123661 : Blo 385764 1123661 := bstep (se 3 (by rfl) ⟨210686, by rfl⟩ : syracuseStep 1123661 = 421373) B421373
theorem B927121 : Blo 385764 927121 := bstep (se 2 (by rfl) ⟨347670, by rfl⟩ : syracuseStep 927121 = 695341) B695341
theorem B435667 : Blo 385764 435667 := bstep (se 1 (by rfl) ⟨326750, by rfl⟩ : syracuseStep 435667 = 653501) B653501
theorem B2991629 : Blo 385764 2991629 := bstep (se 3 (by rfl) ⟨560930, by rfl⟩ : syracuseStep 2991629 = 1121861) B1121861
theorem B435811 : Blo 385764 435811 := bstep (se 1 (by rfl) ⟨326858, by rfl⟩ : syracuseStep 435811 = 653717) B653717
theorem B1124081 : Blo 385764 1124081 := bstep (se 2 (by rfl) ⟨421530, by rfl⟩ : syracuseStep 1124081 = 843061) B843061
theorem B435955 : Blo 385764 435955 := bstep (se 1 (by rfl) ⟨326966, by rfl⟩ : syracuseStep 435955 = 653933) B653933
theorem B829283 : Blo 385764 829283 := bstep (se 1 (by rfl) ⟨621962, by rfl⟩ : syracuseStep 829283 = 1243925) B1243925
theorem B4433777 : Blo 385764 4433777 := bstep (se 2 (by rfl) ⟨1662666, by rfl⟩ : syracuseStep 4433777 = 3325333) B3325333
theorem B436099 : Blo 385764 436099 := bstep (se 1 (by rfl) ⟨327074, by rfl⟩ : syracuseStep 436099 = 654149) B654149
theorem B1320941 : Blo 385764 1320941 := bstep (se 3 (by rfl) ⟨247676, by rfl⟩ : syracuseStep 1320941 = 495353) B495353
theorem B436243 : Blo 385764 436243 := bstep (se 1 (by rfl) ⟨327182, by rfl⟩ : syracuseStep 436243 = 654365) B654365
theorem B1190051 : Blo 385764 1190051 := bstep (se 1 (by rfl) ⟨892538, by rfl⟩ : syracuseStep 1190051 = 1785077) B1785077
theorem B436387 : Blo 385764 436387 := bstep (se 1 (by rfl) ⟨327290, by rfl⟩ : syracuseStep 436387 = 654581) B654581
theorem B436531 : Blo 385764 436531 := bstep (se 1 (by rfl) ⟨327398, by rfl⟩ : syracuseStep 436531 = 654797) B654797
theorem B1059149 : Blo 385764 1059149 := bstep (se 3 (by rfl) ⟨198590, by rfl⟩ : syracuseStep 1059149 = 397181) B397181
theorem B2206115 : Blo 385764 2206115 := bstep (se 1 (by rfl) ⟨1654586, by rfl⟩ : syracuseStep 2206115 = 3309173) B3309173
theorem B436675 : Blo 385764 436675 := bstep (se 1 (by rfl) ⟨327506, by rfl⟩ : syracuseStep 436675 = 655013) B655013
theorem B76687813 : Blo 385764 76687813 := bstep (se 4 (by rfl) ⟨7189482, by rfl⟩ : syracuseStep 76687813 = 14378965) B14378965
theorem B1059281 : Blo 385764 1059281 := bstep (se 2 (by rfl) ⟨397230, by rfl⟩ : syracuseStep 1059281 = 794461) B794461
theorem B567811 : Blo 385764 567811 := bstep (se 1 (by rfl) ⟨425858, by rfl⟩ : syracuseStep 567811 = 851717) B851717
theorem B436819 : Blo 385764 436819 := bstep (se 1 (by rfl) ⟨327614, by rfl⟩ : syracuseStep 436819 = 655229) B655229
theorem B436963 : Blo 385764 436963 := bstep (se 1 (by rfl) ⟨327722, by rfl⟩ : syracuseStep 436963 = 655445) B655445
theorem B1649393 : Blo 385764 1649393 := bstep (se 2 (by rfl) ⟨618522, by rfl⟩ : syracuseStep 1649393 = 1237045) B1237045
theorem B1649443 : Blo 385764 1649443 := bstep (se 1 (by rfl) ⟨1237082, by rfl⟩ : syracuseStep 1649443 = 2474165) B2474165
theorem B437107 : Blo 385764 437107 := bstep (se 1 (by rfl) ⟨327830, by rfl⟩ : syracuseStep 437107 = 655661) B655661
theorem B2370467 : Blo 385764 2370467 := bstep (se 1 (by rfl) ⟨1777850, by rfl⟩ : syracuseStep 2370467 = 3555701) B3555701
theorem B437251 : Blo 385764 437251 := bstep (se 1 (by rfl) ⟨327938, by rfl⟩ : syracuseStep 437251 = 655877) B655877
theorem B5057677 : Blo 385764 5057677 := bstep (se 3 (by rfl) ⟨948314, by rfl⟩ : syracuseStep 5057677 = 1896629) B1896629
theorem B437395 : Blo 385764 437395 := bstep (se 1 (by rfl) ⟨328046, by rfl⟩ : syracuseStep 437395 = 656093) B656093
theorem B3714245 : Blo 385764 3714245 := bstep (se 4 (by rfl) ⟨348210, by rfl⟩ : syracuseStep 3714245 = 696421) B696421
theorem B437539 : Blo 385764 437539 := bstep (se 1 (by rfl) ⟨328154, by rfl⟩ : syracuseStep 437539 = 656309) B656309
theorem B437683 : Blo 385764 437683 := bstep (se 1 (by rfl) ⟨328262, by rfl⟩ : syracuseStep 437683 = 656525) B656525
theorem B732721 : Blo 385764 732721 := bstep (se 2 (by rfl) ⟨274770, by rfl⟩ : syracuseStep 732721 = 549541) B549541
theorem B437827 : Blo 385764 437827 := bstep (se 1 (by rfl) ⟨328370, by rfl⟩ : syracuseStep 437827 = 656741) B656741
theorem B732881 : Blo 385764 732881 := bstep (se 2 (by rfl) ⟨274830, by rfl⟩ : syracuseStep 732881 = 549661) B549661
theorem B437971 : Blo 385764 437971 := bstep (se 1 (by rfl) ⟨328478, by rfl⟩ : syracuseStep 437971 = 656957) B656957
theorem B995107 : Blo 385764 995107 := bstep (se 1 (by rfl) ⟨746330, by rfl⟩ : syracuseStep 995107 = 1492661) B1492661
theorem B438115 : Blo 385764 438115 := bstep (se 1 (by rfl) ⟨328586, by rfl⟩ : syracuseStep 438115 = 657173) B657173
theorem B438259 : Blo 385764 438259 := bstep (se 1 (by rfl) ⟨328694, by rfl⟩ : syracuseStep 438259 = 657389) B657389
theorem B831505 : Blo 385764 831505 := bstep (se 2 (by rfl) ⟨311814, by rfl⟩ : syracuseStep 831505 = 623629) B623629
theorem B733283 : Blo 385764 733283 := bstep (se 1 (by rfl) ⟨549962, by rfl⟩ : syracuseStep 733283 = 1099925) B1099925
theorem B6697073 : Blo 385764 6697073 := bstep (se 2 (by rfl) ⟨2511402, by rfl⟩ : syracuseStep 6697073 = 5022805) B5022805
theorem B438403 : Blo 385764 438403 := bstep (se 1 (by rfl) ⟨328802, by rfl⟩ : syracuseStep 438403 = 657605) B657605
theorem B2208005 : Blo 385764 2208005 := bstep (se 4 (by rfl) ⟨207000, by rfl⟩ : syracuseStep 2208005 = 414001) B414001
theorem B1356077 : Blo 385764 1356077 := bstep (se 3 (by rfl) ⟨254264, by rfl⟩ : syracuseStep 1356077 = 508529) B508529
theorem B700913 : Blo 385764 700913 := bstep (se 2 (by rfl) ⟨262842, by rfl⟩ : syracuseStep 700913 = 525685) B525685
theorem B734179 : Blo 385764 734179 := bstep (se 1 (by rfl) ⟨550634, by rfl⟩ : syracuseStep 734179 = 1101269) B1101269
theorem B734339 : Blo 385764 734339 := bstep (se 1 (by rfl) ⟨550754, by rfl⟩ : syracuseStep 734339 = 1101509) B1101509
theorem B1651853 : Blo 385764 1651853 := bstep (se 3 (by rfl) ⟨309722, by rfl⟩ : syracuseStep 1651853 = 619445) B619445
theorem B931139 : Blo 385764 931139 := bstep (se 1 (by rfl) ⟨698354, by rfl⟩ : syracuseStep 931139 = 1396709) B1396709
theorem B3159395 : Blo 385764 3159395 := bstep (se 1 (by rfl) ⟨2369546, by rfl⟩ : syracuseStep 3159395 = 4739093) B4739093
theorem B735409 : Blo 385764 735409 := bstep (se 2 (by rfl) ⟨275778, by rfl⟩ : syracuseStep 735409 = 551557) B551557
theorem B1325425 : Blo 385764 1325425 := bstep (se 2 (by rfl) ⟨497034, by rfl⟩ : syracuseStep 1325425 = 994069) B994069
theorem B932273 : Blo 385764 932273 := bstep (se 2 (by rfl) ⟨349602, by rfl⟩ : syracuseStep 932273 = 699205) B699205
theorem B473539 : Blo 385764 473539 := bstep (se 1 (by rfl) ⟨355154, by rfl⟩ : syracuseStep 473539 = 710309) B710309
theorem B3521549 : Blo 385764 3521549 := bstep (se 3 (by rfl) ⟨660290, by rfl⟩ : syracuseStep 3521549 = 1320581) B1320581
theorem B933041 : Blo 385764 933041 := bstep (se 2 (by rfl) ⟨349890, by rfl⟩ : syracuseStep 933041 = 699781) B699781
theorem B736465 : Blo 385764 736465 := bstep (se 2 (by rfl) ⟨276174, by rfl⟩ : syracuseStep 736465 = 552349) B552349
theorem B2932037 : Blo 385764 2932037 := bstep (se 4 (by rfl) ⟨274878, by rfl⟩ : syracuseStep 2932037 = 549757) B549757
theorem B2801137 : Blo 385764 2801137 := bstep (se 2 (by rfl) ⟨1050426, by rfl⟩ : syracuseStep 2801137 = 2100853) B2100853
theorem B3358307 : Blo 385764 3358307 := bstep (se 1 (by rfl) ⟨2518730, by rfl⟩ : syracuseStep 3358307 = 5037461) B5037461
theorem B736867 : Blo 385764 736867 := bstep (se 1 (by rfl) ⟨552650, by rfl⟩ : syracuseStep 736867 = 1105301) B1105301
theorem B900721 : Blo 385764 900721 := bstep (se 2 (by rfl) ⟨337770, by rfl⟩ : syracuseStep 900721 = 675541) B675541
theorem B736913 : Blo 385764 736913 := bstep (se 2 (by rfl) ⟨276342, by rfl⟩ : syracuseStep 736913 = 552685) B552685
theorem B868049 : Blo 385764 868049 := bstep (se 2 (by rfl) ⟨325518, by rfl⟩ : syracuseStep 868049 = 651037) B651037
theorem B868067 : Blo 385764 868067 := bstep (se 1 (by rfl) ⟨651050, by rfl⟩ : syracuseStep 868067 = 1302101) B1302101
theorem B1392497 : Blo 385764 1392497 := bstep (se 2 (by rfl) ⟨522186, by rfl⟩ : syracuseStep 1392497 = 1044373) B1044373
theorem B737201 : Blo 385764 737201 := bstep (se 2 (by rfl) ⟨276450, by rfl⟩ : syracuseStep 737201 = 552901) B552901
theorem B868337 : Blo 385764 868337 := bstep (se 2 (by rfl) ⟨325626, by rfl⟩ : syracuseStep 868337 = 651253) B651253
theorem B868355 : Blo 385764 868355 := bstep (se 1 (by rfl) ⟨651266, by rfl⟩ : syracuseStep 868355 = 1302533) B1302533
theorem B966691 : Blo 385764 966691 := bstep (se 1 (by rfl) ⟨725018, by rfl⟩ : syracuseStep 966691 = 1450037) B1450037
theorem B934097 : Blo 385764 934097 := bstep (se 2 (by rfl) ⟨350286, by rfl⟩ : syracuseStep 934097 = 700573) B700573
theorem B868625 : Blo 385764 868625 := bstep (se 2 (by rfl) ⟨325734, by rfl⟩ : syracuseStep 868625 = 651469) B651469
theorem B868643 : Blo 385764 868643 := bstep (se 1 (by rfl) ⟨651482, by rfl⟩ : syracuseStep 868643 = 1302965) B1302965
theorem B2474317 : Blo 385764 2474317 := bstep (se 3 (by rfl) ⟨463934, by rfl⟩ : syracuseStep 2474317 = 927869) B927869
theorem B868913 : Blo 385764 868913 := bstep (se 2 (by rfl) ⟨325842, by rfl⟩ : syracuseStep 868913 = 651685) B651685
theorem B868931 : Blo 385764 868931 := bstep (se 1 (by rfl) ⟨651698, by rfl⟩ : syracuseStep 868931 = 1303397) B1303397
theorem B737923 : Blo 385764 737923 := bstep (se 1 (by rfl) ⟨553442, by rfl⟩ : syracuseStep 737923 = 1106885) B1106885
theorem B869201 : Blo 385764 869201 := bstep (se 2 (by rfl) ⟨325950, by rfl⟩ : syracuseStep 869201 = 651901) B651901
theorem B869219 : Blo 385764 869219 := bstep (se 1 (by rfl) ⟨651914, by rfl⟩ : syracuseStep 869219 = 1303829) B1303829
theorem B738371 : Blo 385764 738371 := bstep (se 1 (by rfl) ⟨553778, by rfl⟩ : syracuseStep 738371 = 1107557) B1107557
theorem B935011 : Blo 385764 935011 := bstep (se 1 (by rfl) ⟨701258, by rfl⟩ : syracuseStep 935011 = 1402517) B1402517
theorem B869489 : Blo 385764 869489 := bstep (se 2 (by rfl) ⟨326058, by rfl⟩ : syracuseStep 869489 = 652117) B652117
theorem B7554161 : Blo 385764 7554161 := bstep (se 2 (by rfl) ⟨2832810, by rfl⟩ : syracuseStep 7554161 = 5665621) B5665621
theorem B869507 : Blo 385764 869507 := bstep (se 1 (by rfl) ⟨652130, by rfl⟩ : syracuseStep 869507 = 1304261) B1304261
theorem B738659 : Blo 385764 738659 := bstep (se 1 (by rfl) ⟨553994, by rfl⟩ : syracuseStep 738659 = 1107989) B1107989
theorem B869777 : Blo 385764 869777 := bstep (se 2 (by rfl) ⟨326166, by rfl⟩ : syracuseStep 869777 = 652333) B652333
theorem B869795 : Blo 385764 869795 := bstep (se 1 (by rfl) ⟨652346, by rfl⟩ : syracuseStep 869795 = 1304693) B1304693
theorem B1656227 : Blo 385764 1656227 := bstep (se 1 (by rfl) ⟨1242170, by rfl⟩ : syracuseStep 1656227 = 2484341) B2484341
theorem B1263107 : Blo 385764 1263107 := bstep (se 1 (by rfl) ⟨947330, by rfl⟩ : syracuseStep 1263107 = 1894661) B1894661
theorem B870065 : Blo 385764 870065 := bstep (se 2 (by rfl) ⟨326274, by rfl⟩ : syracuseStep 870065 = 652549) B652549
theorem B870083 : Blo 385764 870083 := bstep (se 1 (by rfl) ⟨652562, by rfl⟩ : syracuseStep 870083 = 1305125) B1305125
theorem B1099469 : Blo 385764 1099469 := bstep (se 3 (by rfl) ⟨206150, by rfl⟩ : syracuseStep 1099469 = 412301) B412301
theorem B1099651 : Blo 385764 1099651 := bstep (se 1 (by rfl) ⟨824738, by rfl⟩ : syracuseStep 1099651 = 1649477) B1649477
theorem B2213837 : Blo 385764 2213837 := bstep (se 3 (by rfl) ⟨415094, by rfl⟩ : syracuseStep 2213837 = 830189) B830189
theorem B870353 : Blo 385764 870353 := bstep (se 2 (by rfl) ⟨326382, by rfl⟩ : syracuseStep 870353 = 652765) B652765
theorem B870371 : Blo 385764 870371 := bstep (se 1 (by rfl) ⟨652778, by rfl⟩ : syracuseStep 870371 = 1305557) B1305557
theorem B1099811 : Blo 385764 1099811 := bstep (se 1 (by rfl) ⟨824858, by rfl⟩ : syracuseStep 1099811 = 1649717) B1649717
theorem B870641 : Blo 385764 870641 := bstep (se 2 (by rfl) ⟨326490, by rfl⟩ : syracuseStep 870641 = 652981) B652981
theorem B870659 : Blo 385764 870659 := bstep (se 1 (by rfl) ⟨652994, by rfl⟩ : syracuseStep 870659 = 1305989) B1305989
theorem B739601 : Blo 385764 739601 := bstep (se 2 (by rfl) ⟨277350, by rfl⟩ : syracuseStep 739601 = 554701) B554701
theorem B412147 : Blo 385764 412147 := bstep (se 1 (by rfl) ⟨309110, by rfl⟩ : syracuseStep 412147 = 618221) B618221
theorem B870929 : Blo 385764 870929 := bstep (se 2 (by rfl) ⟨326598, by rfl⟩ : syracuseStep 870929 = 653197) B653197
theorem B870947 : Blo 385764 870947 := bstep (se 1 (by rfl) ⟨653210, by rfl⟩ : syracuseStep 870947 = 1306421) B1306421
theorem B1854029 : Blo 385764 1854029 := bstep (se 3 (by rfl) ⟨347630, by rfl⟩ : syracuseStep 1854029 = 695261) B695261
theorem B543313 : Blo 385764 543313 := bstep (se 2 (by rfl) ⟨203742, by rfl⟩ : syracuseStep 543313 = 407485) B407485
theorem B871217 : Blo 385764 871217 := bstep (se 2 (by rfl) ⟨326706, by rfl⟩ : syracuseStep 871217 = 653413) B653413
theorem B871235 : Blo 385764 871235 := bstep (se 1 (by rfl) ⟨653426, by rfl⟩ : syracuseStep 871235 = 1306853) B1306853
theorem B1100881 : Blo 385764 1100881 := bstep (se 2 (by rfl) ⟨412830, by rfl⟩ : syracuseStep 1100881 = 825661) B825661
theorem B871505 : Blo 385764 871505 := bstep (se 2 (by rfl) ⟨326814, by rfl⟩ : syracuseStep 871505 = 653629) B653629
theorem B412771 : Blo 385764 412771 := bstep (se 1 (by rfl) ⟨309578, by rfl⟩ : syracuseStep 412771 = 619157) B619157
theorem B871523 : Blo 385764 871523 := bstep (se 1 (by rfl) ⟨653642, by rfl⟩ : syracuseStep 871523 = 1307285) B1307285
theorem B2346317 : Blo 385764 2346317 := bstep (se 3 (by rfl) ⟨439934, by rfl⟩ : syracuseStep 2346317 = 879869) B879869
theorem B871793 : Blo 385764 871793 := bstep (se 2 (by rfl) ⟨326922, by rfl⟩ : syracuseStep 871793 = 653845) B653845
theorem B1658225 : Blo 385764 1658225 := bstep (se 2 (by rfl) ⟨621834, by rfl⟩ : syracuseStep 1658225 = 1243669) B1243669
theorem B871811 : Blo 385764 871811 := bstep (se 1 (by rfl) ⟨653858, by rfl⟩ : syracuseStep 871811 = 1307717) B1307717
theorem B872081 : Blo 385764 872081 := bstep (se 2 (by rfl) ⟨327030, by rfl⟩ : syracuseStep 872081 = 654061) B654061
theorem B872099 : Blo 385764 872099 := bstep (se 1 (by rfl) ⟨654074, by rfl⟩ : syracuseStep 872099 = 1308149) B1308149
theorem B1986275 : Blo 385764 1986275 := bstep (se 1 (by rfl) ⟨1489706, by rfl⟩ : syracuseStep 1986275 = 2979413) B2979413
theorem B872369 : Blo 385764 872369 := bstep (se 2 (by rfl) ⟨327138, by rfl⟩ : syracuseStep 872369 = 654277) B654277
theorem B872387 : Blo 385764 872387 := bstep (se 1 (by rfl) ⟨654290, by rfl⟩ : syracuseStep 872387 = 1308581) B1308581
theorem B2216069 : Blo 385764 2216069 := bstep (se 4 (by rfl) ⟨207756, by rfl⟩ : syracuseStep 2216069 = 415513) B415513
theorem B3133637 : Blo 385764 3133637 := bstep (se 4 (by rfl) ⟨293778, by rfl⟩ : syracuseStep 3133637 = 587557) B587557
theorem B872657 : Blo 385764 872657 := bstep (se 2 (by rfl) ⟨327246, by rfl⟩ : syracuseStep 872657 = 654493) B654493
theorem B872675 : Blo 385764 872675 := bstep (se 1 (by rfl) ⟨654506, by rfl⟩ : syracuseStep 872675 = 1309013) B1309013
theorem B1659149 : Blo 385764 1659149 := bstep (se 3 (by rfl) ⟨311090, by rfl⟩ : syracuseStep 1659149 = 622181) B622181
theorem B1200419 : Blo 385764 1200419 := bstep (se 1 (by rfl) ⟨900314, by rfl⟩ : syracuseStep 1200419 = 1800629) B1800629
theorem B1102157 : Blo 385764 1102157 := bstep (se 3 (by rfl) ⟨206654, by rfl⟩ : syracuseStep 1102157 = 413309) B413309
theorem B872945 : Blo 385764 872945 := bstep (se 2 (by rfl) ⟨327354, by rfl⟩ : syracuseStep 872945 = 654709) B654709
theorem B1102339 : Blo 385764 1102339 := bstep (se 1 (by rfl) ⟨826754, by rfl⟩ : syracuseStep 1102339 = 1653509) B1653509
theorem B872963 : Blo 385764 872963 := bstep (se 1 (by rfl) ⟨654722, by rfl⟩ : syracuseStep 872963 = 1309445) B1309445
theorem B1102385 : Blo 385764 1102385 := bstep (se 2 (by rfl) ⟨413394, by rfl⟩ : syracuseStep 1102385 = 826789) B826789
theorem B873233 : Blo 385764 873233 := bstep (se 2 (by rfl) ⟨327462, by rfl⟩ : syracuseStep 873233 = 654925) B654925
theorem B873251 : Blo 385764 873251 := bstep (se 1 (by rfl) ⟨654938, by rfl⟩ : syracuseStep 873251 = 1309877) B1309877
theorem B2216753 : Blo 385764 2216753 := bstep (se 2 (by rfl) ⟨831282, by rfl⟩ : syracuseStep 2216753 = 1662565) B1662565
theorem B414659 : Blo 385764 414659 := bstep (se 1 (by rfl) ⟨310994, by rfl⟩ : syracuseStep 414659 = 621989) B621989
theorem B513011 : Blo 385764 513011 := bstep (se 1 (by rfl) ⟨384758, by rfl⟩ : syracuseStep 513011 = 769517) B769517
theorem B2937869 : Blo 385764 2937869 := bstep (se 3 (by rfl) ⟨550850, by rfl⟩ : syracuseStep 2937869 = 1101701) B1101701
theorem B873521 : Blo 385764 873521 := bstep (se 2 (by rfl) ⟨327570, by rfl⟩ : syracuseStep 873521 = 655141) B655141
theorem B873539 : Blo 385764 873539 := bstep (se 1 (by rfl) ⟨655154, by rfl⟩ : syracuseStep 873539 = 1310309) B1310309
theorem B578657 : Blo 385764 578657 := bstep (se 2 (by rfl) ⟨216996, by rfl⟩ : syracuseStep 578657 = 433993) B433993
theorem B578675 : Blo 385764 578675 := bstep (se 1 (by rfl) ⟨434006, by rfl⟩ : syracuseStep 578675 = 868013) B868013
theorem B578705 : Blo 385764 578705 := bstep (se 2 (by rfl) ⟨217014, by rfl⟩ : syracuseStep 578705 = 434029) B434029
theorem B578723 : Blo 385764 578723 := bstep (se 1 (by rfl) ⟨434042, by rfl⟩ : syracuseStep 578723 = 868085) B868085
theorem B578753 : Blo 385764 578753 := bstep (se 2 (by rfl) ⟨217032, by rfl⟩ : syracuseStep 578753 = 434065) B434065
theorem B578771 : Blo 385764 578771 := bstep (se 1 (by rfl) ⟨434078, by rfl⟩ : syracuseStep 578771 = 868157) B868157
theorem B578801 : Blo 385764 578801 := bstep (se 2 (by rfl) ⟨217050, by rfl⟩ : syracuseStep 578801 = 434101) B434101
theorem B578819 : Blo 385764 578819 := bstep (se 1 (by rfl) ⟨434114, by rfl⟩ : syracuseStep 578819 = 868229) B868229
theorem B578849 : Blo 385764 578849 := bstep (se 2 (by rfl) ⟨217068, by rfl⟩ : syracuseStep 578849 = 434137) B434137
theorem B2086193 : Blo 385764 2086193 := bstep (se 2 (by rfl) ⟨782322, by rfl⟩ : syracuseStep 2086193 = 1564645) B1564645
theorem B578867 : Blo 385764 578867 := bstep (se 1 (by rfl) ⟨434150, by rfl⟩ : syracuseStep 578867 = 868301) B868301
theorem B578897 : Blo 385764 578897 := bstep (se 2 (by rfl) ⟨217086, by rfl⟩ : syracuseStep 578897 = 434173) B434173
theorem B873809 : Blo 385764 873809 := bstep (se 2 (by rfl) ⟨327678, by rfl⟩ : syracuseStep 873809 = 655357) B655357
theorem B578915 : Blo 385764 578915 := bstep (se 1 (by rfl) ⟨434186, by rfl⟩ : syracuseStep 578915 = 868373) B868373
theorem B873827 : Blo 385764 873827 := bstep (se 1 (by rfl) ⟨655370, by rfl⟩ : syracuseStep 873827 = 1310741) B1310741
theorem B578945 : Blo 385764 578945 := bstep (se 2 (by rfl) ⟨217104, by rfl⟩ : syracuseStep 578945 = 434209) B434209
theorem B578963 : Blo 385764 578963 := bstep (se 1 (by rfl) ⟨434222, by rfl⟩ : syracuseStep 578963 = 868445) B868445
theorem B578993 : Blo 385764 578993 := bstep (se 2 (by rfl) ⟨217122, by rfl⟩ : syracuseStep 578993 = 434245) B434245
theorem B579011 : Blo 385764 579011 := bstep (se 1 (by rfl) ⟨434258, by rfl⟩ : syracuseStep 579011 = 868517) B868517
theorem B579041 : Blo 385764 579041 := bstep (se 2 (by rfl) ⟨217140, by rfl⟩ : syracuseStep 579041 = 434281) B434281
theorem B579059 : Blo 385764 579059 := bstep (se 1 (by rfl) ⟨434294, by rfl⟩ : syracuseStep 579059 = 868589) B868589
theorem B579089 : Blo 385764 579089 := bstep (se 2 (by rfl) ⟨217158, by rfl⟩ : syracuseStep 579089 = 434317) B434317
theorem B579107 : Blo 385764 579107 := bstep (se 1 (by rfl) ⟨434330, by rfl⟩ : syracuseStep 579107 = 868661) B868661
theorem B579137 : Blo 385764 579137 := bstep (se 2 (by rfl) ⟨217176, by rfl⟩ : syracuseStep 579137 = 434353) B434353
theorem B579155 : Blo 385764 579155 := bstep (se 1 (by rfl) ⟨434366, by rfl⟩ : syracuseStep 579155 = 868733) B868733
theorem B579185 : Blo 385764 579185 := bstep (se 2 (by rfl) ⟨217194, by rfl⟩ : syracuseStep 579185 = 434389) B434389
theorem B874097 : Blo 385764 874097 := bstep (se 2 (by rfl) ⟨327786, by rfl⟩ : syracuseStep 874097 = 655573) B655573
theorem B579203 : Blo 385764 579203 := bstep (se 1 (by rfl) ⟨434402, by rfl⟩ : syracuseStep 579203 = 868805) B868805
theorem B874115 : Blo 385764 874115 := bstep (se 1 (by rfl) ⟨655586, by rfl⟩ : syracuseStep 874115 = 1311173) B1311173
theorem B579233 : Blo 385764 579233 := bstep (se 2 (by rfl) ⟨217212, by rfl⟩ : syracuseStep 579233 = 434425) B434425
theorem B579251 : Blo 385764 579251 := bstep (se 1 (by rfl) ⟨434438, by rfl⟩ : syracuseStep 579251 = 868877) B868877
theorem B579281 : Blo 385764 579281 := bstep (se 2 (by rfl) ⟨217230, by rfl⟩ : syracuseStep 579281 = 434461) B434461
theorem B579299 : Blo 385764 579299 := bstep (se 1 (by rfl) ⟨434474, by rfl⟩ : syracuseStep 579299 = 868949) B868949
theorem B579329 : Blo 385764 579329 := bstep (se 2 (by rfl) ⟨217248, by rfl⟩ : syracuseStep 579329 = 434497) B434497
theorem B579347 : Blo 385764 579347 := bstep (se 1 (by rfl) ⟨434510, by rfl⟩ : syracuseStep 579347 = 869021) B869021
theorem B579377 : Blo 385764 579377 := bstep (se 2 (by rfl) ⟨217266, by rfl⟩ : syracuseStep 579377 = 434533) B434533
theorem B546625 : Blo 385764 546625 := bstep (se 2 (by rfl) ⟨204984, by rfl⟩ : syracuseStep 546625 = 409969) B409969
theorem B579395 : Blo 385764 579395 := bstep (se 1 (by rfl) ⟨434546, by rfl⟩ : syracuseStep 579395 = 869093) B869093
theorem B579425 : Blo 385764 579425 := bstep (se 2 (by rfl) ⟨217284, by rfl⟩ : syracuseStep 579425 = 434569) B434569
theorem B579443 : Blo 385764 579443 := bstep (se 1 (by rfl) ⟨434582, by rfl⟩ : syracuseStep 579443 = 869165) B869165
theorem B579473 : Blo 385764 579473 := bstep (se 2 (by rfl) ⟨217302, by rfl⟩ : syracuseStep 579473 = 434605) B434605
theorem B874385 : Blo 385764 874385 := bstep (se 2 (by rfl) ⟨327894, by rfl⟩ : syracuseStep 874385 = 655789) B655789
theorem B579491 : Blo 385764 579491 := bstep (se 1 (by rfl) ⟨434618, by rfl⟩ : syracuseStep 579491 = 869237) B869237
theorem B874403 : Blo 385764 874403 := bstep (se 1 (by rfl) ⟨655802, by rfl⟩ : syracuseStep 874403 = 1311605) B1311605
theorem B4413365 : Blo 385764 4413365 := bstep (se 5 (by rfl) ⟨206876, by rfl⟩ : syracuseStep 4413365 = 413753) B413753
theorem B579521 : Blo 385764 579521 := bstep (se 2 (by rfl) ⟨217320, by rfl⟩ : syracuseStep 579521 = 434641) B434641
theorem B579539 : Blo 385764 579539 := bstep (se 1 (by rfl) ⟨434654, by rfl⟩ : syracuseStep 579539 = 869309) B869309
theorem B1103843 : Blo 385764 1103843 := bstep (se 1 (by rfl) ⟨827882, by rfl⟩ : syracuseStep 1103843 = 1655765) B1655765
theorem B1955825 : Blo 385764 1955825 := bstep (se 2 (by rfl) ⟨733434, by rfl⟩ : syracuseStep 1955825 = 1466869) B1466869
theorem B579569 : Blo 385764 579569 := bstep (se 2 (by rfl) ⟨217338, by rfl⟩ : syracuseStep 579569 = 434677) B434677
theorem B579587 : Blo 385764 579587 := bstep (se 1 (by rfl) ⟨434690, by rfl⟩ : syracuseStep 579587 = 869381) B869381
theorem B579617 : Blo 385764 579617 := bstep (se 2 (by rfl) ⟨217356, by rfl⟩ : syracuseStep 579617 = 434713) B434713
theorem B579635 : Blo 385764 579635 := bstep (se 1 (by rfl) ⟨434726, by rfl⟩ : syracuseStep 579635 = 869453) B869453
theorem B579665 : Blo 385764 579665 := bstep (se 2 (by rfl) ⟨217374, by rfl⟩ : syracuseStep 579665 = 434749) B434749
theorem B579683 : Blo 385764 579683 := bstep (se 1 (by rfl) ⟨434762, by rfl⟩ : syracuseStep 579683 = 869525) B869525
theorem B579713 : Blo 385764 579713 := bstep (se 2 (by rfl) ⟨217392, by rfl⟩ : syracuseStep 579713 = 434785) B434785
theorem B3528845 : Blo 385764 3528845 := bstep (se 3 (by rfl) ⟨661658, by rfl⟩ : syracuseStep 3528845 = 1323317) B1323317
theorem B579731 : Blo 385764 579731 := bstep (se 1 (by rfl) ⟨434798, by rfl⟩ : syracuseStep 579731 = 869597) B869597
theorem B579761 : Blo 385764 579761 := bstep (se 2 (by rfl) ⟨217410, by rfl⟩ : syracuseStep 579761 = 434821) B434821
theorem B874673 : Blo 385764 874673 := bstep (se 2 (by rfl) ⟨328002, by rfl⟩ : syracuseStep 874673 = 656005) B656005
theorem B579779 : Blo 385764 579779 := bstep (se 1 (by rfl) ⟨434834, by rfl⟩ : syracuseStep 579779 = 869669) B869669
theorem B874691 : Blo 385764 874691 := bstep (se 1 (by rfl) ⟨656018, by rfl⟩ : syracuseStep 874691 = 1312037) B1312037
theorem B579809 : Blo 385764 579809 := bstep (se 2 (by rfl) ⟨217428, by rfl⟩ : syracuseStep 579809 = 434857) B434857
theorem B2218211 : Blo 385764 2218211 := bstep (se 1 (by rfl) ⟨1663658, by rfl⟩ : syracuseStep 2218211 = 3327317) B3327317
theorem B579827 : Blo 385764 579827 := bstep (se 1 (by rfl) ⟨434870, by rfl⟩ : syracuseStep 579827 = 869741) B869741
theorem B579857 : Blo 385764 579857 := bstep (se 2 (by rfl) ⟨217446, by rfl⟩ : syracuseStep 579857 = 434893) B434893
theorem B579875 : Blo 385764 579875 := bstep (se 1 (by rfl) ⟨434906, by rfl⟩ : syracuseStep 579875 = 869813) B869813
theorem B579905 : Blo 385764 579905 := bstep (se 2 (by rfl) ⟨217464, by rfl⟩ : syracuseStep 579905 = 434929) B434929
theorem B579923 : Blo 385764 579923 := bstep (se 1 (by rfl) ⟨434942, by rfl⟩ : syracuseStep 579923 = 869885) B869885
theorem B9525617 : Blo 385764 9525617 := bstep (se 2 (by rfl) ⟨3572106, by rfl⟩ : syracuseStep 9525617 = 7144213) B7144213
theorem B579953 : Blo 385764 579953 := bstep (se 2 (by rfl) ⟨217482, by rfl⟩ : syracuseStep 579953 = 434965) B434965
theorem B579971 : Blo 385764 579971 := bstep (se 1 (by rfl) ⟨434978, by rfl⟩ : syracuseStep 579971 = 869957) B869957
theorem B580001 : Blo 385764 580001 := bstep (se 2 (by rfl) ⟨217500, by rfl⟩ : syracuseStep 580001 = 435001) B435001
theorem B580019 : Blo 385764 580019 := bstep (se 1 (by rfl) ⟨435014, by rfl⟩ : syracuseStep 580019 = 870029) B870029
theorem B580049 : Blo 385764 580049 := bstep (se 2 (by rfl) ⟨217518, by rfl⟩ : syracuseStep 580049 = 435037) B435037
theorem B874961 : Blo 385764 874961 := bstep (se 2 (by rfl) ⟨328110, by rfl⟩ : syracuseStep 874961 = 656221) B656221
theorem B580067 : Blo 385764 580067 := bstep (se 1 (by rfl) ⟨435050, by rfl⟩ : syracuseStep 580067 = 870101) B870101
theorem B3135971 : Blo 385764 3135971 := bstep (se 1 (by rfl) ⟨2351978, by rfl⟩ : syracuseStep 3135971 = 4703957) B4703957
theorem B874979 : Blo 385764 874979 := bstep (se 1 (by rfl) ⟨656234, by rfl⟩ : syracuseStep 874979 = 1312469) B1312469
theorem B580097 : Blo 385764 580097 := bstep (se 2 (by rfl) ⟨217536, by rfl⟩ : syracuseStep 580097 = 435073) B435073
theorem B580115 : Blo 385764 580115 := bstep (se 1 (by rfl) ⟨435086, by rfl⟩ : syracuseStep 580115 = 870173) B870173
theorem B1399331 : Blo 385764 1399331 := bstep (se 1 (by rfl) ⟨1049498, by rfl⟩ : syracuseStep 1399331 = 2098997) B2098997
theorem B580145 : Blo 385764 580145 := bstep (se 2 (by rfl) ⟨217554, by rfl⟩ : syracuseStep 580145 = 435109) B435109
theorem B580163 : Blo 385764 580163 := bstep (se 1 (by rfl) ⟨435122, by rfl⟩ : syracuseStep 580163 = 870245) B870245
theorem B580193 : Blo 385764 580193 := bstep (se 2 (by rfl) ⟨217572, by rfl⟩ : syracuseStep 580193 = 435145) B435145
theorem B580211 : Blo 385764 580211 := bstep (se 1 (by rfl) ⟨435158, by rfl⟩ : syracuseStep 580211 = 870317) B870317
theorem B580241 : Blo 385764 580241 := bstep (se 2 (by rfl) ⟨217590, by rfl⟩ : syracuseStep 580241 = 435181) B435181
theorem B580259 : Blo 385764 580259 := bstep (se 1 (by rfl) ⟨435194, by rfl⟩ : syracuseStep 580259 = 870389) B870389
theorem B580289 : Blo 385764 580289 := bstep (se 2 (by rfl) ⟨217608, by rfl⟩ : syracuseStep 580289 = 435217) B435217
theorem B580307 : Blo 385764 580307 := bstep (se 1 (by rfl) ⟨435230, by rfl⟩ : syracuseStep 580307 = 870461) B870461
theorem B580337 : Blo 385764 580337 := bstep (se 2 (by rfl) ⟨217626, by rfl⟩ : syracuseStep 580337 = 435253) B435253
theorem B875249 : Blo 385764 875249 := bstep (se 2 (by rfl) ⟨328218, by rfl⟩ : syracuseStep 875249 = 656437) B656437
theorem B580355 : Blo 385764 580355 := bstep (se 1 (by rfl) ⟨435266, by rfl⟩ : syracuseStep 580355 = 870533) B870533
theorem B875267 : Blo 385764 875267 := bstep (se 1 (by rfl) ⟨656450, by rfl⟩ : syracuseStep 875267 = 1312901) B1312901
theorem B580385 : Blo 385764 580385 := bstep (se 2 (by rfl) ⟨217644, by rfl⟩ : syracuseStep 580385 = 435289) B435289
theorem B940835 : Blo 385764 940835 := bstep (se 1 (by rfl) ⟨705626, by rfl⟩ : syracuseStep 940835 = 1411253) B1411253
theorem B580403 : Blo 385764 580403 := bstep (se 1 (by rfl) ⟨435302, by rfl⟩ : syracuseStep 580403 = 870605) B870605
theorem B580433 : Blo 385764 580433 := bstep (se 2 (by rfl) ⟨217662, by rfl⟩ : syracuseStep 580433 = 435325) B435325
theorem B580451 : Blo 385764 580451 := bstep (se 1 (by rfl) ⟨435338, by rfl⟩ : syracuseStep 580451 = 870677) B870677
theorem B580481 : Blo 385764 580481 := bstep (se 2 (by rfl) ⟨217680, by rfl⟩ : syracuseStep 580481 = 435361) B435361
theorem B1465229 : Blo 385764 1465229 := bstep (se 3 (by rfl) ⟨274730, by rfl⟩ : syracuseStep 1465229 = 549461) B549461
theorem B580499 : Blo 385764 580499 := bstep (se 1 (by rfl) ⟨435374, by rfl⟩ : syracuseStep 580499 = 870749) B870749
theorem B580529 : Blo 385764 580529 := bstep (se 2 (by rfl) ⟨217698, by rfl⟩ : syracuseStep 580529 = 435397) B435397
theorem B580547 : Blo 385764 580547 := bstep (se 1 (by rfl) ⟨435410, by rfl⟩ : syracuseStep 580547 = 870821) B870821
theorem B580577 : Blo 385764 580577 := bstep (se 2 (by rfl) ⟨217716, by rfl⟩ : syracuseStep 580577 = 435433) B435433
theorem B2481137 : Blo 385764 2481137 := bstep (se 2 (by rfl) ⟨930426, by rfl⟩ : syracuseStep 2481137 = 1860853) B1860853
theorem B580595 : Blo 385764 580595 := bstep (se 1 (by rfl) ⟨435446, by rfl⟩ : syracuseStep 580595 = 870893) B870893
theorem B580625 : Blo 385764 580625 := bstep (se 2 (by rfl) ⟨217734, by rfl⟩ : syracuseStep 580625 = 435469) B435469
theorem B875537 : Blo 385764 875537 := bstep (se 2 (by rfl) ⟨328326, by rfl⟩ : syracuseStep 875537 = 656653) B656653
theorem B580643 : Blo 385764 580643 := bstep (se 1 (by rfl) ⟨435482, by rfl⟩ : syracuseStep 580643 = 870965) B870965
theorem B875555 : Blo 385764 875555 := bstep (se 1 (by rfl) ⟨656666, by rfl⟩ : syracuseStep 875555 = 1313333) B1313333
theorem B580673 : Blo 385764 580673 := bstep (se 2 (by rfl) ⟨217752, by rfl⟩ : syracuseStep 580673 = 435505) B435505
theorem B580691 : Blo 385764 580691 := bstep (se 1 (by rfl) ⟨435518, by rfl⟩ : syracuseStep 580691 = 871037) B871037
theorem B580721 : Blo 385764 580721 := bstep (se 2 (by rfl) ⟨217770, by rfl⟩ : syracuseStep 580721 = 435541) B435541
theorem B580739 : Blo 385764 580739 := bstep (se 1 (by rfl) ⟨435554, by rfl⟩ : syracuseStep 580739 = 871109) B871109
theorem B580769 : Blo 385764 580769 := bstep (se 2 (by rfl) ⟨217788, by rfl⟩ : syracuseStep 580769 = 435577) B435577
theorem B1105073 : Blo 385764 1105073 := bstep (se 2 (by rfl) ⟨414402, by rfl⟩ : syracuseStep 1105073 = 828805) B828805
theorem B580787 : Blo 385764 580787 := bstep (se 1 (by rfl) ⟨435590, by rfl⟩ : syracuseStep 580787 = 871181) B871181
theorem B580817 : Blo 385764 580817 := bstep (se 2 (by rfl) ⟨217806, by rfl⟩ : syracuseStep 580817 = 435613) B435613
theorem B4709603 : Blo 385764 4709603 := bstep (se 1 (by rfl) ⟨3532202, by rfl⟩ : syracuseStep 4709603 = 7064405) B7064405
theorem B580835 : Blo 385764 580835 := bstep (se 1 (by rfl) ⟨435626, by rfl⟩ : syracuseStep 580835 = 871253) B871253
theorem B580865 : Blo 385764 580865 := bstep (se 2 (by rfl) ⟨217824, by rfl⟩ : syracuseStep 580865 = 435649) B435649
theorem B580883 : Blo 385764 580883 := bstep (se 1 (by rfl) ⟨435662, by rfl⟩ : syracuseStep 580883 = 871325) B871325
theorem B580913 : Blo 385764 580913 := bstep (se 2 (by rfl) ⟨217842, by rfl⟩ : syracuseStep 580913 = 435685) B435685
theorem B1662257 : Blo 385764 1662257 := bstep (se 2 (by rfl) ⟨623346, by rfl⟩ : syracuseStep 1662257 = 1246693) B1246693
theorem B875825 : Blo 385764 875825 := bstep (se 2 (by rfl) ⟨328434, by rfl⟩ : syracuseStep 875825 = 656869) B656869
theorem B580931 : Blo 385764 580931 := bstep (se 1 (by rfl) ⟨435698, by rfl⟩ : syracuseStep 580931 = 871397) B871397
theorem B875843 : Blo 385764 875843 := bstep (se 1 (by rfl) ⟨656882, by rfl⟩ : syracuseStep 875843 = 1313765) B1313765
theorem B580961 : Blo 385764 580961 := bstep (se 2 (by rfl) ⟨217860, by rfl⟩ : syracuseStep 580961 = 435721) B435721
theorem B2809187 : Blo 385764 2809187 := bstep (se 1 (by rfl) ⟨2106890, by rfl⟩ : syracuseStep 2809187 = 4213781) B4213781
theorem B580979 : Blo 385764 580979 := bstep (se 1 (by rfl) ⟨435734, by rfl⟩ : syracuseStep 580979 = 871469) B871469
theorem B581009 : Blo 385764 581009 := bstep (se 2 (by rfl) ⟨217878, by rfl⟩ : syracuseStep 581009 = 435757) B435757
theorem B1957283 : Blo 385764 1957283 := bstep (se 1 (by rfl) ⟨1467962, by rfl⟩ : syracuseStep 1957283 = 2935925) B2935925
theorem B581027 : Blo 385764 581027 := bstep (se 1 (by rfl) ⟨435770, by rfl⟩ : syracuseStep 581027 = 871541) B871541
theorem B581057 : Blo 385764 581057 := bstep (se 2 (by rfl) ⟨217896, by rfl⟩ : syracuseStep 581057 = 435793) B435793
theorem B581075 : Blo 385764 581075 := bstep (se 1 (by rfl) ⟨435806, by rfl⟩ : syracuseStep 581075 = 871613) B871613
theorem B581105 : Blo 385764 581105 := bstep (se 2 (by rfl) ⟨217914, by rfl⟩ : syracuseStep 581105 = 435829) B435829
theorem B581123 : Blo 385764 581123 := bstep (se 1 (by rfl) ⟨435842, by rfl⟩ : syracuseStep 581123 = 871685) B871685
theorem B2481677 : Blo 385764 2481677 := bstep (se 3 (by rfl) ⟨465314, by rfl⟩ : syracuseStep 2481677 = 930629) B930629
theorem B581153 : Blo 385764 581153 := bstep (se 2 (by rfl) ⟨217932, by rfl⟩ : syracuseStep 581153 = 435865) B435865
theorem B581171 : Blo 385764 581171 := bstep (se 1 (by rfl) ⟨435878, by rfl⟩ : syracuseStep 581171 = 871757) B871757
theorem B581201 : Blo 385764 581201 := bstep (se 2 (by rfl) ⟨217950, by rfl⟩ : syracuseStep 581201 = 435901) B435901
theorem B876113 : Blo 385764 876113 := bstep (se 2 (by rfl) ⟨328542, by rfl⟩ : syracuseStep 876113 = 657085) B657085
theorem B581219 : Blo 385764 581219 := bstep (se 1 (by rfl) ⟨435914, by rfl⟩ : syracuseStep 581219 = 871829) B871829
theorem B876131 : Blo 385764 876131 := bstep (se 1 (by rfl) ⟨657098, by rfl⟩ : syracuseStep 876131 = 1314197) B1314197
theorem B581249 : Blo 385764 581249 := bstep (se 2 (by rfl) ⟨217968, by rfl⟩ : syracuseStep 581249 = 435937) B435937
theorem B581267 : Blo 385764 581267 := bstep (se 1 (by rfl) ⟨435950, by rfl⟩ : syracuseStep 581267 = 871901) B871901
theorem B581297 : Blo 385764 581297 := bstep (se 2 (by rfl) ⟨217986, by rfl⟩ : syracuseStep 581297 = 435973) B435973
theorem B581315 : Blo 385764 581315 := bstep (se 1 (by rfl) ⟨435986, by rfl⟩ : syracuseStep 581315 = 871973) B871973
theorem B581345 : Blo 385764 581345 := bstep (se 2 (by rfl) ⟨218004, by rfl⟩ : syracuseStep 581345 = 436009) B436009
theorem B581363 : Blo 385764 581363 := bstep (se 1 (by rfl) ⟨436022, by rfl⟩ : syracuseStep 581363 = 872045) B872045
theorem B450307 : Blo 385764 450307 := bstep (se 1 (by rfl) ⟨337730, by rfl⟩ : syracuseStep 450307 = 675461) B675461
theorem B581393 : Blo 385764 581393 := bstep (se 2 (by rfl) ⟨218022, by rfl⟩ : syracuseStep 581393 = 436045) B436045
theorem B581411 : Blo 385764 581411 := bstep (se 1 (by rfl) ⟨436058, by rfl⟩ : syracuseStep 581411 = 872117) B872117
theorem B1302317 : Blo 385764 1302317 := bstep (se 3 (by rfl) ⟨244184, by rfl⟩ : syracuseStep 1302317 = 488369) B488369
theorem B581441 : Blo 385764 581441 := bstep (se 2 (by rfl) ⟨218040, by rfl⟩ : syracuseStep 581441 = 436081) B436081
theorem B581459 : Blo 385764 581459 := bstep (se 1 (by rfl) ⟨436094, by rfl⟩ : syracuseStep 581459 = 872189) B872189
theorem B1302371 : Blo 385764 1302371 := bstep (se 1 (by rfl) ⟨976778, by rfl⟩ : syracuseStep 1302371 = 1953557) B1953557
theorem B2940785 : Blo 385764 2940785 := bstep (se 2 (by rfl) ⟨1102794, by rfl⟩ : syracuseStep 2940785 = 2205589) B2205589
theorem B581489 : Blo 385764 581489 := bstep (se 2 (by rfl) ⟨218058, by rfl⟩ : syracuseStep 581489 = 436117) B436117
theorem B876401 : Blo 385764 876401 := bstep (se 2 (by rfl) ⟨328650, by rfl⟩ : syracuseStep 876401 = 657301) B657301
theorem B581507 : Blo 385764 581507 := bstep (se 1 (by rfl) ⟨436130, by rfl⟩ : syracuseStep 581507 = 872261) B872261
theorem B876419 : Blo 385764 876419 := bstep (se 1 (by rfl) ⟨657314, by rfl⟩ : syracuseStep 876419 = 1314629) B1314629
theorem B581537 : Blo 385764 581537 := bstep (se 2 (by rfl) ⟨218076, by rfl⟩ : syracuseStep 581537 = 436153) B436153
theorem B581555 : Blo 385764 581555 := bstep (se 1 (by rfl) ⟨436166, by rfl⟩ : syracuseStep 581555 = 872333) B872333
theorem B581585 : Blo 385764 581585 := bstep (se 2 (by rfl) ⟨218094, by rfl⟩ : syracuseStep 581585 = 436189) B436189
theorem B581603 : Blo 385764 581603 := bstep (se 1 (by rfl) ⟨436202, by rfl⟩ : syracuseStep 581603 = 872405) B872405
theorem B581633 : Blo 385764 581633 := bstep (se 2 (by rfl) ⟨218112, by rfl⟩ : syracuseStep 581633 = 436225) B436225
theorem B581651 : Blo 385764 581651 := bstep (se 1 (by rfl) ⟨436238, by rfl⟩ : syracuseStep 581651 = 872477) B872477
theorem B581681 : Blo 385764 581681 := bstep (se 2 (by rfl) ⟨218130, by rfl⟩ : syracuseStep 581681 = 436261) B436261
theorem B581699 : Blo 385764 581699 := bstep (se 1 (by rfl) ⟨436274, by rfl⟩ : syracuseStep 581699 = 872549) B872549
theorem B581729 : Blo 385764 581729 := bstep (se 2 (by rfl) ⟨218148, by rfl⟩ : syracuseStep 581729 = 436297) B436297
theorem B1302641 : Blo 385764 1302641 := bstep (se 2 (by rfl) ⟨488490, by rfl⟩ : syracuseStep 1302641 = 976981) B976981
theorem B581747 : Blo 385764 581747 := bstep (se 1 (by rfl) ⟨436310, by rfl⟩ : syracuseStep 581747 = 872621) B872621
theorem B581777 : Blo 385764 581777 := bstep (se 2 (by rfl) ⟨218166, by rfl⟩ : syracuseStep 581777 = 436333) B436333
theorem B876689 : Blo 385764 876689 := bstep (se 2 (by rfl) ⟨328758, by rfl⟩ : syracuseStep 876689 = 657517) B657517
theorem B581795 : Blo 385764 581795 := bstep (se 1 (by rfl) ⟨436346, by rfl⟩ : syracuseStep 581795 = 872693) B872693
theorem B876707 : Blo 385764 876707 := bstep (se 1 (by rfl) ⟨657530, by rfl⟩ : syracuseStep 876707 = 1315061) B1315061
theorem B581825 : Blo 385764 581825 := bstep (se 2 (by rfl) ⟨218184, by rfl⟩ : syracuseStep 581825 = 436369) B436369
theorem B1958093 : Blo 385764 1958093 := bstep (se 3 (by rfl) ⟨367142, by rfl⟩ : syracuseStep 1958093 = 734285) B734285
theorem B581843 : Blo 385764 581843 := bstep (se 1 (by rfl) ⟨436382, by rfl⟩ : syracuseStep 581843 = 872765) B872765
theorem B581873 : Blo 385764 581873 := bstep (se 2 (by rfl) ⟨218202, by rfl⟩ : syracuseStep 581873 = 436405) B436405
theorem B581891 : Blo 385764 581891 := bstep (se 1 (by rfl) ⟨436418, by rfl⟩ : syracuseStep 581891 = 872837) B872837
theorem B581921 : Blo 385764 581921 := bstep (se 2 (by rfl) ⟨218220, by rfl⟩ : syracuseStep 581921 = 436441) B436441
theorem B581939 : Blo 385764 581939 := bstep (se 1 (by rfl) ⟨436454, by rfl⟩ : syracuseStep 581939 = 872909) B872909
theorem B581969 : Blo 385764 581969 := bstep (se 2 (by rfl) ⟨218238, by rfl⟩ : syracuseStep 581969 = 436477) B436477
theorem B581987 : Blo 385764 581987 := bstep (se 1 (by rfl) ⟨436490, by rfl⟩ : syracuseStep 581987 = 872981) B872981
theorem B582017 : Blo 385764 582017 := bstep (se 2 (by rfl) ⟨218256, by rfl⟩ : syracuseStep 582017 = 436513) B436513
theorem B582035 : Blo 385764 582035 := bstep (se 1 (by rfl) ⟨436526, by rfl⟩ : syracuseStep 582035 = 873053) B873053
theorem B582065 : Blo 385764 582065 := bstep (se 2 (by rfl) ⟨218274, by rfl⟩ : syracuseStep 582065 = 436549) B436549
theorem B582083 : Blo 385764 582083 := bstep (se 1 (by rfl) ⟨436562, by rfl⟩ : syracuseStep 582083 = 873125) B873125
theorem B582113 : Blo 385764 582113 := bstep (se 2 (by rfl) ⟨218292, by rfl⟩ : syracuseStep 582113 = 436585) B436585
theorem B549347 : Blo 385764 549347 := bstep (se 1 (by rfl) ⟨412010, by rfl⟩ : syracuseStep 549347 = 824021) B824021
theorem B582131 : Blo 385764 582131 := bstep (se 1 (by rfl) ⟨436598, by rfl⟩ : syracuseStep 582131 = 873197) B873197
theorem B582161 : Blo 385764 582161 := bstep (se 2 (by rfl) ⟨218310, by rfl⟩ : syracuseStep 582161 = 436621) B436621
theorem B10641941 : Blo 385764 10641941 := bstep (se 6 (by rfl) ⟨249420, by rfl⟩ : syracuseStep 10641941 = 498841) B498841
theorem B582179 : Blo 385764 582179 := bstep (se 1 (by rfl) ⟨436634, by rfl⟩ : syracuseStep 582179 = 873269) B873269
theorem B1663523 : Blo 385764 1663523 := bstep (se 1 (by rfl) ⟨1247642, by rfl⟩ : syracuseStep 1663523 = 2495285) B2495285
theorem B582209 : Blo 385764 582209 := bstep (se 2 (by rfl) ⟨218328, by rfl⟩ : syracuseStep 582209 = 436657) B436657
theorem B1565261 : Blo 385764 1565261 := bstep (se 3 (by rfl) ⟨293486, by rfl⟩ : syracuseStep 1565261 = 586973) B586973
theorem B582227 : Blo 385764 582227 := bstep (se 1 (by rfl) ⟨436670, by rfl⟩ : syracuseStep 582227 = 873341) B873341
theorem B1106531 : Blo 385764 1106531 := bstep (se 1 (by rfl) ⟨829898, by rfl⟩ : syracuseStep 1106531 = 1659797) B1659797
theorem B582257 : Blo 385764 582257 := bstep (se 2 (by rfl) ⟨218346, by rfl⟩ : syracuseStep 582257 = 436693) B436693
theorem B582275 : Blo 385764 582275 := bstep (se 1 (by rfl) ⟨436706, by rfl⟩ : syracuseStep 582275 = 873413) B873413
theorem B1303181 : Blo 385764 1303181 := bstep (se 3 (by rfl) ⟨244346, by rfl⟩ : syracuseStep 1303181 = 488693) B488693
theorem B582305 : Blo 385764 582305 := bstep (se 2 (by rfl) ⟨218364, by rfl⟩ : syracuseStep 582305 = 436729) B436729
theorem B582323 : Blo 385764 582323 := bstep (se 1 (by rfl) ⟨436742, by rfl⟩ : syracuseStep 582323 = 873485) B873485
theorem B1303235 : Blo 385764 1303235 := bstep (se 1 (by rfl) ⟨977426, by rfl⟩ : syracuseStep 1303235 = 1954853) B1954853
theorem B582353 : Blo 385764 582353 := bstep (se 2 (by rfl) ⟨218382, by rfl⟩ : syracuseStep 582353 = 436765) B436765
theorem B582371 : Blo 385764 582371 := bstep (se 1 (by rfl) ⟨436778, by rfl⟩ : syracuseStep 582371 = 873557) B873557
theorem B385779 : Blo 385764 385779 := bstep (se 1 (by rfl) ⟨289334, by rfl⟩ : syracuseStep 385779 = 578669) B578669
theorem B582401 : Blo 385764 582401 := bstep (se 2 (by rfl) ⟨218400, by rfl⟩ : syracuseStep 582401 = 436801) B436801
theorem B385795 : Blo 385764 385795 := bstep (se 1 (by rfl) ⟨289346, by rfl⟩ : syracuseStep 385795 = 578693) B578693
theorem B385811 : Blo 385764 385811 := bstep (se 1 (by rfl) ⟨289358, by rfl⟩ : syracuseStep 385811 = 578717) B578717
theorem B582419 : Blo 385764 582419 := bstep (se 1 (by rfl) ⟨436814, by rfl⟩ : syracuseStep 582419 = 873629) B873629
theorem B385827 : Blo 385764 385827 := bstep (se 1 (by rfl) ⟨289370, by rfl⟩ : syracuseStep 385827 = 578741) B578741
theorem B582449 : Blo 385764 582449 := bstep (se 2 (by rfl) ⟨218418, by rfl⟩ : syracuseStep 582449 = 436837) B436837
theorem B385843 : Blo 385764 385843 := bstep (se 1 (by rfl) ⟨289382, by rfl⟩ : syracuseStep 385843 = 578765) B578765
theorem B385859 : Blo 385764 385859 := bstep (se 1 (by rfl) ⟨289394, by rfl⟩ : syracuseStep 385859 = 578789) B578789
theorem B582467 : Blo 385764 582467 := bstep (se 1 (by rfl) ⟨436850, by rfl⟩ : syracuseStep 582467 = 873701) B873701
theorem B385875 : Blo 385764 385875 := bstep (se 1 (by rfl) ⟨289406, by rfl⟩ : syracuseStep 385875 = 578813) B578813
theorem B582497 : Blo 385764 582497 := bstep (se 2 (by rfl) ⟨218436, by rfl⟩ : syracuseStep 582497 = 436873) B436873
theorem B385891 : Blo 385764 385891 := bstep (se 1 (by rfl) ⟨289418, by rfl⟩ : syracuseStep 385891 = 578837) B578837
theorem B385907 : Blo 385764 385907 := bstep (se 1 (by rfl) ⟨289430, by rfl⟩ : syracuseStep 385907 = 578861) B578861
theorem B582515 : Blo 385764 582515 := bstep (se 1 (by rfl) ⟨436886, by rfl⟩ : syracuseStep 582515 = 873773) B873773
theorem B385923 : Blo 385764 385923 := bstep (se 1 (by rfl) ⟨289442, by rfl⟩ : syracuseStep 385923 = 578885) B578885
theorem B582545 : Blo 385764 582545 := bstep (se 2 (by rfl) ⟨218454, by rfl⟩ : syracuseStep 582545 = 436909) B436909
theorem B385939 : Blo 385764 385939 := bstep (se 1 (by rfl) ⟨289454, by rfl⟩ : syracuseStep 385939 = 578909) B578909
theorem B385955 : Blo 385764 385955 := bstep (se 1 (by rfl) ⟨289466, by rfl⟩ : syracuseStep 385955 = 578933) B578933
theorem B582563 : Blo 385764 582563 := bstep (se 1 (by rfl) ⟨436922, by rfl⟩ : syracuseStep 582563 = 873845) B873845
theorem B385971 : Blo 385764 385971 := bstep (se 1 (by rfl) ⟨289478, by rfl⟩ : syracuseStep 385971 = 578957) B578957
theorem B582593 : Blo 385764 582593 := bstep (se 2 (by rfl) ⟨218472, by rfl⟩ : syracuseStep 582593 = 436945) B436945
theorem B385987 : Blo 385764 385987 := bstep (se 1 (by rfl) ⟨289490, by rfl⟩ : syracuseStep 385987 = 578981) B578981
theorem B1467341 : Blo 385764 1467341 := bstep (se 3 (by rfl) ⟨275126, by rfl⟩ : syracuseStep 1467341 = 550253) B550253
theorem B1303505 : Blo 385764 1303505 := bstep (se 2 (by rfl) ⟨488814, by rfl⟩ : syracuseStep 1303505 = 977629) B977629
theorem B386003 : Blo 385764 386003 := bstep (se 1 (by rfl) ⟨289502, by rfl⟩ : syracuseStep 386003 = 579005) B579005
theorem B582611 : Blo 385764 582611 := bstep (se 1 (by rfl) ⟨436958, by rfl⟩ : syracuseStep 582611 = 873917) B873917
theorem B386019 : Blo 385764 386019 := bstep (se 1 (by rfl) ⟨289514, by rfl⟩ : syracuseStep 386019 = 579029) B579029
theorem B582641 : Blo 385764 582641 := bstep (se 2 (by rfl) ⟨218490, by rfl⟩ : syracuseStep 582641 = 436981) B436981
theorem B386035 : Blo 385764 386035 := bstep (se 1 (by rfl) ⟨289526, by rfl⟩ : syracuseStep 386035 = 579053) B579053
theorem B386051 : Blo 385764 386051 := bstep (se 1 (by rfl) ⟨289538, by rfl⟩ : syracuseStep 386051 = 579077) B579077
theorem B582659 : Blo 385764 582659 := bstep (se 1 (by rfl) ⟨436994, by rfl⟩ : syracuseStep 582659 = 873989) B873989
theorem B386067 : Blo 385764 386067 := bstep (se 1 (by rfl) ⟨289550, by rfl⟩ : syracuseStep 386067 = 579101) B579101
theorem B582689 : Blo 385764 582689 := bstep (se 2 (by rfl) ⟨218508, by rfl⟩ : syracuseStep 582689 = 437017) B437017
theorem B386083 : Blo 385764 386083 := bstep (se 1 (by rfl) ⟨289562, by rfl⟩ : syracuseStep 386083 = 579125) B579125
theorem B386099 : Blo 385764 386099 := bstep (se 1 (by rfl) ⟨289574, by rfl⟩ : syracuseStep 386099 = 579149) B579149
theorem B582707 : Blo 385764 582707 := bstep (se 1 (by rfl) ⟨437030, by rfl⟩ : syracuseStep 582707 = 874061) B874061
theorem B386115 : Blo 385764 386115 := bstep (se 1 (by rfl) ⟨289586, by rfl⟩ : syracuseStep 386115 = 579173) B579173
theorem B582737 : Blo 385764 582737 := bstep (se 2 (by rfl) ⟨218526, by rfl⟩ : syracuseStep 582737 = 437053) B437053
theorem B386131 : Blo 385764 386131 := bstep (se 1 (by rfl) ⟨289598, by rfl⟩ : syracuseStep 386131 = 579197) B579197
theorem B549985 : Blo 385764 549985 := bstep (se 2 (by rfl) ⟨206244, by rfl⟩ : syracuseStep 549985 = 412489) B412489
theorem B386147 : Blo 385764 386147 := bstep (se 1 (by rfl) ⟨289610, by rfl⟩ : syracuseStep 386147 = 579221) B579221
theorem B582755 : Blo 385764 582755 := bstep (se 1 (by rfl) ⟨437066, by rfl⟩ : syracuseStep 582755 = 874133) B874133
theorem B386163 : Blo 385764 386163 := bstep (se 1 (by rfl) ⟨289622, by rfl⟩ : syracuseStep 386163 = 579245) B579245
theorem B582785 : Blo 385764 582785 := bstep (se 2 (by rfl) ⟨218544, by rfl⟩ : syracuseStep 582785 = 437089) B437089
theorem B386179 : Blo 385764 386179 := bstep (se 1 (by rfl) ⟨289634, by rfl⟩ : syracuseStep 386179 = 579269) B579269
theorem B386195 : Blo 385764 386195 := bstep (se 1 (by rfl) ⟨289646, by rfl⟩ : syracuseStep 386195 = 579293) B579293
theorem B582803 : Blo 385764 582803 := bstep (se 1 (by rfl) ⟨437102, by rfl⟩ : syracuseStep 582803 = 874205) B874205
theorem B386211 : Blo 385764 386211 := bstep (se 1 (by rfl) ⟨289658, by rfl⟩ : syracuseStep 386211 = 579317) B579317
theorem B582833 : Blo 385764 582833 := bstep (se 2 (by rfl) ⟨218562, by rfl⟩ : syracuseStep 582833 = 437125) B437125
theorem B386227 : Blo 385764 386227 := bstep (se 1 (by rfl) ⟨289670, by rfl⟩ : syracuseStep 386227 = 579341) B579341
theorem B386243 : Blo 385764 386243 := bstep (se 1 (by rfl) ⟨289682, by rfl⟩ : syracuseStep 386243 = 579365) B579365
theorem B582851 : Blo 385764 582851 := bstep (se 1 (by rfl) ⟨437138, by rfl⟩ : syracuseStep 582851 = 874277) B874277
theorem B386259 : Blo 385764 386259 := bstep (se 1 (by rfl) ⟨289694, by rfl⟩ : syracuseStep 386259 = 579389) B579389
theorem B550099 : Blo 385764 550099 := bstep (se 1 (by rfl) ⟨412574, by rfl⟩ : syracuseStep 550099 = 825149) B825149
theorem B582881 : Blo 385764 582881 := bstep (se 2 (by rfl) ⟨218580, by rfl⟩ : syracuseStep 582881 = 437161) B437161
theorem B386275 : Blo 385764 386275 := bstep (se 1 (by rfl) ⟨289706, by rfl⟩ : syracuseStep 386275 = 579413) B579413
theorem B386291 : Blo 385764 386291 := bstep (se 1 (by rfl) ⟨289718, by rfl⟩ : syracuseStep 386291 = 579437) B579437
theorem B582899 : Blo 385764 582899 := bstep (se 1 (by rfl) ⟨437174, by rfl⟩ : syracuseStep 582899 = 874349) B874349
theorem B386307 : Blo 385764 386307 := bstep (se 1 (by rfl) ⟨289730, by rfl⟩ : syracuseStep 386307 = 579461) B579461
theorem B582929 : Blo 385764 582929 := bstep (se 2 (by rfl) ⟨218598, by rfl⟩ : syracuseStep 582929 = 437197) B437197
theorem B386323 : Blo 385764 386323 := bstep (se 1 (by rfl) ⟨289742, by rfl⟩ : syracuseStep 386323 = 579485) B579485
theorem B386339 : Blo 385764 386339 := bstep (se 1 (by rfl) ⟨289754, by rfl⟩ : syracuseStep 386339 = 579509) B579509
theorem B582947 : Blo 385764 582947 := bstep (se 1 (by rfl) ⟨437210, by rfl⟩ : syracuseStep 582947 = 874421) B874421
theorem B2647345 : Blo 385764 2647345 := bstep (se 2 (by rfl) ⟨992754, by rfl⟩ : syracuseStep 2647345 = 1985509) B1985509
theorem B386355 : Blo 385764 386355 := bstep (se 1 (by rfl) ⟨289766, by rfl⟩ : syracuseStep 386355 = 579533) B579533
theorem B582977 : Blo 385764 582977 := bstep (se 2 (by rfl) ⟨218616, by rfl⟩ : syracuseStep 582977 = 437233) B437233
theorem B386371 : Blo 385764 386371 := bstep (se 1 (by rfl) ⟨289778, by rfl⟩ : syracuseStep 386371 = 579557) B579557
theorem B386387 : Blo 385764 386387 := bstep (se 1 (by rfl) ⟨289790, by rfl⟩ : syracuseStep 386387 = 579581) B579581
theorem B582995 : Blo 385764 582995 := bstep (se 1 (by rfl) ⟨437246, by rfl⟩ : syracuseStep 582995 = 874493) B874493
theorem B386403 : Blo 385764 386403 := bstep (se 1 (by rfl) ⟨289802, by rfl⟩ : syracuseStep 386403 = 579605) B579605
theorem B583025 : Blo 385764 583025 := bstep (se 2 (by rfl) ⟨218634, by rfl⟩ : syracuseStep 583025 = 437269) B437269
theorem B386419 : Blo 385764 386419 := bstep (se 1 (by rfl) ⟨289814, by rfl⟩ : syracuseStep 386419 = 579629) B579629
theorem B386435 : Blo 385764 386435 := bstep (se 1 (by rfl) ⟨289826, by rfl⟩ : syracuseStep 386435 = 579653) B579653
theorem B583043 : Blo 385764 583043 := bstep (se 1 (by rfl) ⟨437282, by rfl⟩ : syracuseStep 583043 = 874565) B874565
theorem B1107341 : Blo 385764 1107341 := bstep (se 3 (by rfl) ⟨207626, by rfl⟩ : syracuseStep 1107341 = 415253) B415253
theorem B386451 : Blo 385764 386451 := bstep (se 1 (by rfl) ⟨289838, by rfl⟩ : syracuseStep 386451 = 579677) B579677
theorem B583073 : Blo 385764 583073 := bstep (se 2 (by rfl) ⟨218652, by rfl⟩ : syracuseStep 583073 = 437305) B437305
theorem B386467 : Blo 385764 386467 := bstep (se 1 (by rfl) ⟨289850, by rfl⟩ : syracuseStep 386467 = 579701) B579701
theorem B386483 : Blo 385764 386483 := bstep (se 1 (by rfl) ⟨289862, by rfl⟩ : syracuseStep 386483 = 579725) B579725
theorem B583091 : Blo 385764 583091 := bstep (se 1 (by rfl) ⟨437318, by rfl⟩ : syracuseStep 583091 = 874637) B874637
theorem B386499 : Blo 385764 386499 := bstep (se 1 (by rfl) ⟨289874, by rfl⟩ : syracuseStep 386499 = 579749) B579749
theorem B583121 : Blo 385764 583121 := bstep (se 2 (by rfl) ⟨218670, by rfl⟩ : syracuseStep 583121 = 437341) B437341
theorem B386515 : Blo 385764 386515 := bstep (se 1 (by rfl) ⟨289886, by rfl⟩ : syracuseStep 386515 = 579773) B579773
theorem B386531 : Blo 385764 386531 := bstep (se 1 (by rfl) ⟨289898, by rfl⟩ : syracuseStep 386531 = 579797) B579797
theorem B583139 : Blo 385764 583139 := bstep (se 1 (by rfl) ⟨437354, by rfl⟩ : syracuseStep 583139 = 874709) B874709
theorem B1304045 : Blo 385764 1304045 := bstep (se 3 (by rfl) ⟨244508, by rfl⟩ : syracuseStep 1304045 = 489017) B489017
theorem B386547 : Blo 385764 386547 := bstep (se 1 (by rfl) ⟨289910, by rfl⟩ : syracuseStep 386547 = 579821) B579821
theorem B583169 : Blo 385764 583169 := bstep (se 2 (by rfl) ⟨218688, by rfl⟩ : syracuseStep 583169 = 437377) B437377
theorem B386563 : Blo 385764 386563 := bstep (se 1 (by rfl) ⟨289922, by rfl⟩ : syracuseStep 386563 = 579845) B579845
theorem B386579 : Blo 385764 386579 := bstep (se 1 (by rfl) ⟨289934, by rfl⟩ : syracuseStep 386579 = 579869) B579869
theorem B583187 : Blo 385764 583187 := bstep (se 1 (by rfl) ⟨437390, by rfl⟩ : syracuseStep 583187 = 874781) B874781
theorem B1304099 : Blo 385764 1304099 := bstep (se 1 (by rfl) ⟨978074, by rfl⟩ : syracuseStep 1304099 = 1956149) B1956149
theorem B386595 : Blo 385764 386595 := bstep (se 1 (by rfl) ⟨289946, by rfl⟩ : syracuseStep 386595 = 579893) B579893
theorem B583217 : Blo 385764 583217 := bstep (se 2 (by rfl) ⟨218706, by rfl⟩ : syracuseStep 583217 = 437413) B437413
theorem B386611 : Blo 385764 386611 := bstep (se 1 (by rfl) ⟨289958, by rfl⟩ : syracuseStep 386611 = 579917) B579917
theorem B386627 : Blo 385764 386627 := bstep (se 1 (by rfl) ⟨289970, by rfl⟩ : syracuseStep 386627 = 579941) B579941
theorem B583235 : Blo 385764 583235 := bstep (se 1 (by rfl) ⟨437426, by rfl⟩ : syracuseStep 583235 = 874853) B874853
theorem B1107533 : Blo 385764 1107533 := bstep (se 3 (by rfl) ⟨207662, by rfl⟩ : syracuseStep 1107533 = 415325) B415325
theorem B386643 : Blo 385764 386643 := bstep (se 1 (by rfl) ⟨289982, by rfl⟩ : syracuseStep 386643 = 579965) B579965
theorem B583265 : Blo 385764 583265 := bstep (se 2 (by rfl) ⟨218724, by rfl⟩ : syracuseStep 583265 = 437449) B437449
theorem B386659 : Blo 385764 386659 := bstep (se 1 (by rfl) ⟨289994, by rfl⟩ : syracuseStep 386659 = 579989) B579989
theorem B386675 : Blo 385764 386675 := bstep (se 1 (by rfl) ⟨290006, by rfl⟩ : syracuseStep 386675 = 580013) B580013
theorem B583283 : Blo 385764 583283 := bstep (se 1 (by rfl) ⟨437462, by rfl⟩ : syracuseStep 583283 = 874925) B874925
theorem B386691 : Blo 385764 386691 := bstep (se 1 (by rfl) ⟨290018, by rfl⟩ : syracuseStep 386691 = 580037) B580037
theorem B583313 : Blo 385764 583313 := bstep (se 2 (by rfl) ⟨218742, by rfl⟩ : syracuseStep 583313 = 437485) B437485
theorem B386707 : Blo 385764 386707 := bstep (se 1 (by rfl) ⟨290030, by rfl⟩ : syracuseStep 386707 = 580061) B580061
theorem B386723 : Blo 385764 386723 := bstep (se 1 (by rfl) ⟨290042, by rfl⟩ : syracuseStep 386723 = 580085) B580085
theorem B583331 : Blo 385764 583331 := bstep (se 1 (by rfl) ⟨437498, by rfl⟩ : syracuseStep 583331 = 874997) B874997
theorem B386739 : Blo 385764 386739 := bstep (se 1 (by rfl) ⟨290054, by rfl⟩ : syracuseStep 386739 = 580109) B580109
theorem B583361 : Blo 385764 583361 := bstep (se 2 (by rfl) ⟨218760, by rfl⟩ : syracuseStep 583361 = 437521) B437521
theorem B1238723 : Blo 385764 1238723 := bstep (se 1 (by rfl) ⟨929042, by rfl⟩ : syracuseStep 1238723 = 1858085) B1858085
theorem B386755 : Blo 385764 386755 := bstep (se 1 (by rfl) ⟨290066, by rfl⟩ : syracuseStep 386755 = 580133) B580133
theorem B1009361 : Blo 385764 1009361 := bstep (se 2 (by rfl) ⟨378510, by rfl⟩ : syracuseStep 1009361 = 757021) B757021
theorem B386771 : Blo 385764 386771 := bstep (se 1 (by rfl) ⟨290078, by rfl⟩ : syracuseStep 386771 = 580157) B580157
theorem B583379 : Blo 385764 583379 := bstep (se 1 (by rfl) ⟨437534, by rfl⟩ : syracuseStep 583379 = 875069) B875069
theorem B386787 : Blo 385764 386787 := bstep (se 1 (by rfl) ⟨290090, by rfl⟩ : syracuseStep 386787 = 580181) B580181
theorem B1468145 : Blo 385764 1468145 := bstep (se 2 (by rfl) ⟨550554, by rfl⟩ : syracuseStep 1468145 = 1101109) B1101109
theorem B583409 : Blo 385764 583409 := bstep (se 2 (by rfl) ⟨218778, by rfl⟩ : syracuseStep 583409 = 437557) B437557
theorem B386803 : Blo 385764 386803 := bstep (se 1 (by rfl) ⟨290102, by rfl⟩ : syracuseStep 386803 = 580205) B580205
theorem B386819 : Blo 385764 386819 := bstep (se 1 (by rfl) ⟨290114, by rfl⟩ : syracuseStep 386819 = 580229) B580229
theorem B583427 : Blo 385764 583427 := bstep (se 1 (by rfl) ⟨437570, by rfl⟩ : syracuseStep 583427 = 875141) B875141
theorem B976657 : Blo 385764 976657 := bstep (se 2 (by rfl) ⟨366246, by rfl⟩ : syracuseStep 976657 = 732493) B732493
theorem B386835 : Blo 385764 386835 := bstep (se 1 (by rfl) ⟨290126, by rfl⟩ : syracuseStep 386835 = 580253) B580253
theorem B386851 : Blo 385764 386851 := bstep (se 1 (by rfl) ⟨290138, by rfl⟩ : syracuseStep 386851 = 580277) B580277
theorem B583457 : Blo 385764 583457 := bstep (se 2 (by rfl) ⟨218796, by rfl⟩ : syracuseStep 583457 = 437593) B437593
theorem B1304369 : Blo 385764 1304369 := bstep (se 2 (by rfl) ⟨489138, by rfl⟩ : syracuseStep 1304369 = 978277) B978277
theorem B386867 : Blo 385764 386867 := bstep (se 1 (by rfl) ⟨290150, by rfl⟩ : syracuseStep 386867 = 580301) B580301
theorem B583475 : Blo 385764 583475 := bstep (se 1 (by rfl) ⟨437606, by rfl⟩ : syracuseStep 583475 = 875213) B875213
theorem B386883 : Blo 385764 386883 := bstep (se 1 (by rfl) ⟨290162, by rfl⟩ : syracuseStep 386883 = 580325) B580325
theorem B583505 : Blo 385764 583505 := bstep (se 2 (by rfl) ⟨218814, by rfl⟩ : syracuseStep 583505 = 437629) B437629
theorem B386899 : Blo 385764 386899 := bstep (se 1 (by rfl) ⟨290174, by rfl⟩ : syracuseStep 386899 = 580349) B580349
theorem B386915 : Blo 385764 386915 := bstep (se 1 (by rfl) ⟨290186, by rfl⟩ : syracuseStep 386915 = 580373) B580373
theorem B583523 : Blo 385764 583523 := bstep (se 1 (by rfl) ⟨437642, by rfl⟩ : syracuseStep 583523 = 875285) B875285
theorem B386931 : Blo 385764 386931 := bstep (se 1 (by rfl) ⟨290198, by rfl⟩ : syracuseStep 386931 = 580397) B580397
theorem B583553 : Blo 385764 583553 := bstep (se 2 (by rfl) ⟨218832, by rfl⟩ : syracuseStep 583553 = 437665) B437665
theorem B386947 : Blo 385764 386947 := bstep (se 1 (by rfl) ⟨290210, by rfl⟩ : syracuseStep 386947 = 580421) B580421
theorem B386963 : Blo 385764 386963 := bstep (se 1 (by rfl) ⟨290222, by rfl⟩ : syracuseStep 386963 = 580445) B580445
theorem B583571 : Blo 385764 583571 := bstep (se 1 (by rfl) ⟨437678, by rfl⟩ : syracuseStep 583571 = 875357) B875357
theorem B386979 : Blo 385764 386979 := bstep (se 1 (by rfl) ⟨290234, by rfl⟩ : syracuseStep 386979 = 580469) B580469
theorem B583601 : Blo 385764 583601 := bstep (se 2 (by rfl) ⟨218850, by rfl⟩ : syracuseStep 583601 = 437701) B437701
theorem B386995 : Blo 385764 386995 := bstep (se 1 (by rfl) ⟨290246, by rfl⟩ : syracuseStep 386995 = 580493) B580493
theorem B387011 : Blo 385764 387011 := bstep (se 1 (by rfl) ⟨290258, by rfl⟩ : syracuseStep 387011 = 580517) B580517
theorem B583619 : Blo 385764 583619 := bstep (se 1 (by rfl) ⟨437714, by rfl⟩ : syracuseStep 583619 = 875429) B875429
theorem B387027 : Blo 385764 387027 := bstep (se 1 (by rfl) ⟨290270, by rfl⟩ : syracuseStep 387027 = 580541) B580541
theorem B583649 : Blo 385764 583649 := bstep (se 2 (by rfl) ⟨218868, by rfl⟩ : syracuseStep 583649 = 437737) B437737
theorem B387043 : Blo 385764 387043 := bstep (se 1 (by rfl) ⟨290282, by rfl⟩ : syracuseStep 387043 = 580565) B580565
theorem B387059 : Blo 385764 387059 := bstep (se 1 (by rfl) ⟨290294, by rfl⟩ : syracuseStep 387059 = 580589) B580589
theorem B583667 : Blo 385764 583667 := bstep (se 1 (by rfl) ⟨437750, by rfl⟩ : syracuseStep 583667 = 875501) B875501
theorem B387075 : Blo 385764 387075 := bstep (se 1 (by rfl) ⟨290306, by rfl⟩ : syracuseStep 387075 = 580613) B580613
theorem B583697 : Blo 385764 583697 := bstep (se 2 (by rfl) ⟨218886, by rfl⟩ : syracuseStep 583697 = 437773) B437773
theorem B387091 : Blo 385764 387091 := bstep (se 1 (by rfl) ⟨290318, by rfl⟩ : syracuseStep 387091 = 580637) B580637
theorem B976931 : Blo 385764 976931 := bstep (se 1 (by rfl) ⟨732698, by rfl⟩ : syracuseStep 976931 = 1465397) B1465397
theorem B387107 : Blo 385764 387107 := bstep (se 1 (by rfl) ⟨290330, by rfl⟩ : syracuseStep 387107 = 580661) B580661
theorem B583715 : Blo 385764 583715 := bstep (se 1 (by rfl) ⟨437786, by rfl⟩ : syracuseStep 583715 = 875573) B875573
theorem B387123 : Blo 385764 387123 := bstep (se 1 (by rfl) ⟨290342, by rfl⟩ : syracuseStep 387123 = 580685) B580685
theorem B583745 : Blo 385764 583745 := bstep (se 2 (by rfl) ⟨218904, by rfl⟩ : syracuseStep 583745 = 437809) B437809
theorem B387139 : Blo 385764 387139 := bstep (se 1 (by rfl) ⟨290354, by rfl⟩ : syracuseStep 387139 = 580709) B580709
theorem B387155 : Blo 385764 387155 := bstep (se 1 (by rfl) ⟨290366, by rfl⟩ : syracuseStep 387155 = 580733) B580733
theorem B583763 : Blo 385764 583763 := bstep (se 1 (by rfl) ⟨437822, by rfl⟩ : syracuseStep 583763 = 875645) B875645
theorem B387171 : Blo 385764 387171 := bstep (se 1 (by rfl) ⟨290378, by rfl⟩ : syracuseStep 387171 = 580757) B580757
theorem B583793 : Blo 385764 583793 := bstep (se 2 (by rfl) ⟨218922, by rfl⟩ : syracuseStep 583793 = 437845) B437845
theorem B387187 : Blo 385764 387187 := bstep (se 1 (by rfl) ⟨290390, by rfl⟩ : syracuseStep 387187 = 580781) B580781
theorem B387203 : Blo 385764 387203 := bstep (se 1 (by rfl) ⟨290402, by rfl⟩ : syracuseStep 387203 = 580805) B580805
theorem B583811 : Blo 385764 583811 := bstep (se 1 (by rfl) ⟨437858, by rfl⟩ : syracuseStep 583811 = 875717) B875717
theorem B1403021 : Blo 385764 1403021 := bstep (se 3 (by rfl) ⟨263066, by rfl⟩ : syracuseStep 1403021 = 526133) B526133
theorem B387219 : Blo 385764 387219 := bstep (se 1 (by rfl) ⟨290414, by rfl⟩ : syracuseStep 387219 = 580829) B580829
theorem B583841 : Blo 385764 583841 := bstep (se 2 (by rfl) ⟨218940, by rfl⟩ : syracuseStep 583841 = 437881) B437881
theorem B387235 : Blo 385764 387235 := bstep (se 1 (by rfl) ⟨290426, by rfl⟩ : syracuseStep 387235 = 580853) B580853
theorem B387251 : Blo 385764 387251 := bstep (se 1 (by rfl) ⟨290438, by rfl⟩ : syracuseStep 387251 = 580877) B580877
theorem B583859 : Blo 385764 583859 := bstep (se 1 (by rfl) ⟨437894, by rfl⟩ : syracuseStep 583859 = 875789) B875789
theorem B387267 : Blo 385764 387267 := bstep (se 1 (by rfl) ⟨290450, by rfl⟩ : syracuseStep 387267 = 580901) B580901
theorem B583889 : Blo 385764 583889 := bstep (se 2 (by rfl) ⟨218958, by rfl⟩ : syracuseStep 583889 = 437917) B437917
theorem B387283 : Blo 385764 387283 := bstep (se 1 (by rfl) ⟨290462, by rfl⟩ : syracuseStep 387283 = 580925) B580925
theorem B977123 : Blo 385764 977123 := bstep (se 1 (by rfl) ⟨732842, by rfl⟩ : syracuseStep 977123 = 1465685) B1465685
theorem B387299 : Blo 385764 387299 := bstep (se 1 (by rfl) ⟨290474, by rfl⟩ : syracuseStep 387299 = 580949) B580949
theorem B583907 : Blo 385764 583907 := bstep (se 1 (by rfl) ⟨437930, by rfl⟩ : syracuseStep 583907 = 875861) B875861
theorem B387315 : Blo 385764 387315 := bstep (se 1 (by rfl) ⟨290486, by rfl⟩ : syracuseStep 387315 = 580973) B580973
theorem B583937 : Blo 385764 583937 := bstep (se 2 (by rfl) ⟨218976, by rfl⟩ : syracuseStep 583937 = 437953) B437953
theorem B387331 : Blo 385764 387331 := bstep (se 1 (by rfl) ⟨290498, by rfl⟩ : syracuseStep 387331 = 580997) B580997
theorem B387347 : Blo 385764 387347 := bstep (se 1 (by rfl) ⟨290510, by rfl⟩ : syracuseStep 387347 = 581021) B581021
theorem B583955 : Blo 385764 583955 := bstep (se 1 (by rfl) ⟨437966, by rfl⟩ : syracuseStep 583955 = 875933) B875933
theorem B387363 : Blo 385764 387363 := bstep (se 1 (by rfl) ⟨290522, by rfl⟩ : syracuseStep 387363 = 581045) B581045
theorem B583985 : Blo 385764 583985 := bstep (se 2 (by rfl) ⟨218994, by rfl⟩ : syracuseStep 583985 = 437989) B437989
theorem B387379 : Blo 385764 387379 := bstep (se 1 (by rfl) ⟨290534, by rfl⟩ : syracuseStep 387379 = 581069) B581069
theorem B387395 : Blo 385764 387395 := bstep (se 1 (by rfl) ⟨290546, by rfl⟩ : syracuseStep 387395 = 581093) B581093
theorem B584003 : Blo 385764 584003 := bstep (se 1 (by rfl) ⟨438002, by rfl⟩ : syracuseStep 584003 = 876005) B876005
theorem B1304909 : Blo 385764 1304909 := bstep (se 3 (by rfl) ⟨244670, by rfl⟩ : syracuseStep 1304909 = 489341) B489341
theorem B387411 : Blo 385764 387411 := bstep (se 1 (by rfl) ⟨290558, by rfl⟩ : syracuseStep 387411 = 581117) B581117
theorem B584033 : Blo 385764 584033 := bstep (se 2 (by rfl) ⟨219012, by rfl⟩ : syracuseStep 584033 = 438025) B438025
theorem B387427 : Blo 385764 387427 := bstep (se 1 (by rfl) ⟨290570, by rfl⟩ : syracuseStep 387427 = 581141) B581141
theorem B387443 : Blo 385764 387443 := bstep (se 1 (by rfl) ⟨290582, by rfl⟩ : syracuseStep 387443 = 581165) B581165
theorem B584051 : Blo 385764 584051 := bstep (se 1 (by rfl) ⟨438038, by rfl⟩ : syracuseStep 584051 = 876077) B876077
theorem B1304963 : Blo 385764 1304963 := bstep (se 1 (by rfl) ⟨978722, by rfl⟩ : syracuseStep 1304963 = 1957445) B1957445
theorem B387459 : Blo 385764 387459 := bstep (se 1 (by rfl) ⟨290594, by rfl⟩ : syracuseStep 387459 = 581189) B581189
theorem B1337741 : Blo 385764 1337741 := bstep (se 3 (by rfl) ⟨250826, by rfl⟩ : syracuseStep 1337741 = 501653) B501653
theorem B1468813 : Blo 385764 1468813 := bstep (se 3 (by rfl) ⟨275402, by rfl⟩ : syracuseStep 1468813 = 550805) B550805
theorem B584081 : Blo 385764 584081 := bstep (se 2 (by rfl) ⟨219030, by rfl⟩ : syracuseStep 584081 = 438061) B438061
theorem B387475 : Blo 385764 387475 := bstep (se 1 (by rfl) ⟨290606, by rfl⟩ : syracuseStep 387475 = 581213) B581213
theorem B387491 : Blo 385764 387491 := bstep (se 1 (by rfl) ⟨290618, by rfl⟩ : syracuseStep 387491 = 581237) B581237
theorem B584099 : Blo 385764 584099 := bstep (se 1 (by rfl) ⟨438074, by rfl⟩ : syracuseStep 584099 = 876149) B876149
theorem B387507 : Blo 385764 387507 := bstep (se 1 (by rfl) ⟨290630, by rfl⟩ : syracuseStep 387507 = 581261) B581261
theorem B584129 : Blo 385764 584129 := bstep (se 2 (by rfl) ⟨219048, by rfl⟩ : syracuseStep 584129 = 438097) B438097
theorem B387523 : Blo 385764 387523 := bstep (se 1 (by rfl) ⟨290642, by rfl⟩ : syracuseStep 387523 = 581285) B581285
theorem B387539 : Blo 385764 387539 := bstep (se 1 (by rfl) ⟨290654, by rfl⟩ : syracuseStep 387539 = 581309) B581309
theorem B584147 : Blo 385764 584147 := bstep (se 1 (by rfl) ⟨438110, by rfl⟩ : syracuseStep 584147 = 876221) B876221
theorem B387555 : Blo 385764 387555 := bstep (se 1 (by rfl) ⟨290666, by rfl⟩ : syracuseStep 387555 = 581333) B581333
theorem B1993187 : Blo 385764 1993187 := bstep (se 1 (by rfl) ⟨1494890, by rfl⟩ : syracuseStep 1993187 = 2989781) B2989781
theorem B584177 : Blo 385764 584177 := bstep (se 2 (by rfl) ⟨219066, by rfl⟩ : syracuseStep 584177 = 438133) B438133
theorem B387571 : Blo 385764 387571 := bstep (se 1 (by rfl) ⟨290678, by rfl⟩ : syracuseStep 387571 = 581357) B581357
theorem B387587 : Blo 385764 387587 := bstep (se 1 (by rfl) ⟨290690, by rfl⟩ : syracuseStep 387587 = 581381) B581381
theorem B584195 : Blo 385764 584195 := bstep (se 1 (by rfl) ⟨438146, by rfl⟩ : syracuseStep 584195 = 876293) B876293
theorem B1239569 : Blo 385764 1239569 := bstep (se 2 (by rfl) ⟨464838, by rfl⟩ : syracuseStep 1239569 = 929677) B929677
theorem B551443 : Blo 385764 551443 := bstep (se 1 (by rfl) ⟨413582, by rfl⟩ : syracuseStep 551443 = 827165) B827165
theorem B387603 : Blo 385764 387603 := bstep (se 1 (by rfl) ⟨290702, by rfl⟩ : syracuseStep 387603 = 581405) B581405
theorem B584225 : Blo 385764 584225 := bstep (se 2 (by rfl) ⟨219084, by rfl⟩ : syracuseStep 584225 = 438169) B438169
theorem B387619 : Blo 385764 387619 := bstep (se 1 (by rfl) ⟨290714, by rfl⟩ : syracuseStep 387619 = 581429) B581429
theorem B1108525 : Blo 385764 1108525 := bstep (se 3 (by rfl) ⟨207848, by rfl⟩ : syracuseStep 1108525 = 415697) B415697
theorem B387635 : Blo 385764 387635 := bstep (se 1 (by rfl) ⟨290726, by rfl⟩ : syracuseStep 387635 = 581453) B581453
theorem B584243 : Blo 385764 584243 := bstep (se 1 (by rfl) ⟨438182, by rfl⟩ : syracuseStep 584243 = 876365) B876365
theorem B1239619 : Blo 385764 1239619 := bstep (se 1 (by rfl) ⟨929714, by rfl⟩ : syracuseStep 1239619 = 1859429) B1859429
theorem B387651 : Blo 385764 387651 := bstep (se 1 (by rfl) ⟨290738, by rfl⟩ : syracuseStep 387651 = 581477) B581477
theorem B584273 : Blo 385764 584273 := bstep (se 2 (by rfl) ⟨219102, by rfl⟩ : syracuseStep 584273 = 438205) B438205
theorem B387667 : Blo 385764 387667 := bstep (se 1 (by rfl) ⟨290750, by rfl⟩ : syracuseStep 387667 = 581501) B581501
theorem B387683 : Blo 385764 387683 := bstep (se 1 (by rfl) ⟨290762, by rfl⟩ : syracuseStep 387683 = 581525) B581525
theorem B584291 : Blo 385764 584291 := bstep (se 1 (by rfl) ⟨438218, by rfl⟩ : syracuseStep 584291 = 876437) B876437
theorem B387699 : Blo 385764 387699 := bstep (se 1 (by rfl) ⟨290774, by rfl⟩ : syracuseStep 387699 = 581549) B581549
theorem B584321 : Blo 385764 584321 := bstep (se 2 (by rfl) ⟨219120, by rfl⟩ : syracuseStep 584321 = 438241) B438241
theorem B387715 : Blo 385764 387715 := bstep (se 1 (by rfl) ⟨290786, by rfl⟩ : syracuseStep 387715 = 581573) B581573
theorem B2484877 : Blo 385764 2484877 := bstep (se 3 (by rfl) ⟨465914, by rfl⟩ : syracuseStep 2484877 = 931829) B931829
theorem B1305233 : Blo 385764 1305233 := bstep (se 2 (by rfl) ⟨489462, by rfl⟩ : syracuseStep 1305233 = 978925) B978925
theorem B387731 : Blo 385764 387731 := bstep (se 1 (by rfl) ⟨290798, by rfl⟩ : syracuseStep 387731 = 581597) B581597
theorem B584339 : Blo 385764 584339 := bstep (se 1 (by rfl) ⟨438254, by rfl⟩ : syracuseStep 584339 = 876509) B876509
theorem B387747 : Blo 385764 387747 := bstep (se 1 (by rfl) ⟨290810, by rfl⟩ : syracuseStep 387747 = 581621) B581621
theorem B584369 : Blo 385764 584369 := bstep (se 2 (by rfl) ⟨219138, by rfl⟩ : syracuseStep 584369 = 438277) B438277
theorem B387763 : Blo 385764 387763 := bstep (se 1 (by rfl) ⟨290822, by rfl⟩ : syracuseStep 387763 = 581645) B581645
theorem B387779 : Blo 385764 387779 := bstep (se 1 (by rfl) ⟨290834, by rfl⟩ : syracuseStep 387779 = 581669) B581669
theorem B584387 : Blo 385764 584387 := bstep (se 1 (by rfl) ⟨438290, by rfl⟩ : syracuseStep 584387 = 876581) B876581
theorem B387795 : Blo 385764 387795 := bstep (se 1 (by rfl) ⟨290846, by rfl⟩ : syracuseStep 387795 = 581693) B581693
theorem B584417 : Blo 385764 584417 := bstep (se 2 (by rfl) ⟨219156, by rfl⟩ : syracuseStep 584417 = 438313) B438313
theorem B387811 : Blo 385764 387811 := bstep (se 1 (by rfl) ⟨290858, by rfl⟩ : syracuseStep 387811 = 581717) B581717
theorem B387827 : Blo 385764 387827 := bstep (se 1 (by rfl) ⟨290870, by rfl⟩ : syracuseStep 387827 = 581741) B581741
theorem B584435 : Blo 385764 584435 := bstep (se 1 (by rfl) ⟨438326, by rfl⟩ : syracuseStep 584435 = 876653) B876653
theorem B387843 : Blo 385764 387843 := bstep (se 1 (by rfl) ⟨290882, by rfl⟩ : syracuseStep 387843 = 581765) B581765
theorem B584465 : Blo 385764 584465 := bstep (se 2 (by rfl) ⟨219174, by rfl⟩ : syracuseStep 584465 = 438349) B438349
theorem B387859 : Blo 385764 387859 := bstep (se 1 (by rfl) ⟨290894, by rfl⟩ : syracuseStep 387859 = 581789) B581789
theorem B387875 : Blo 385764 387875 := bstep (se 1 (by rfl) ⟨290906, by rfl⟩ : syracuseStep 387875 = 581813) B581813
theorem B584483 : Blo 385764 584483 := bstep (se 1 (by rfl) ⟨438362, by rfl⟩ : syracuseStep 584483 = 876725) B876725
theorem B387891 : Blo 385764 387891 := bstep (se 1 (by rfl) ⟨290918, by rfl⟩ : syracuseStep 387891 = 581837) B581837
theorem B584513 : Blo 385764 584513 := bstep (se 2 (by rfl) ⟨219192, by rfl⟩ : syracuseStep 584513 = 438385) B438385
theorem B387907 : Blo 385764 387907 := bstep (se 1 (by rfl) ⟨290930, by rfl⟩ : syracuseStep 387907 = 581861) B581861
theorem B387923 : Blo 385764 387923 := bstep (se 1 (by rfl) ⟨290942, by rfl⟩ : syracuseStep 387923 = 581885) B581885
theorem B584531 : Blo 385764 584531 := bstep (se 1 (by rfl) ⟨438398, by rfl⟩ : syracuseStep 584531 = 876797) B876797
theorem B387939 : Blo 385764 387939 := bstep (se 1 (by rfl) ⟨290954, by rfl⟩ : syracuseStep 387939 = 581909) B581909
theorem B584561 : Blo 385764 584561 := bstep (se 2 (by rfl) ⟨219210, by rfl⟩ : syracuseStep 584561 = 438421) B438421
theorem B387955 : Blo 385764 387955 := bstep (se 1 (by rfl) ⟨290966, by rfl⟩ : syracuseStep 387955 = 581933) B581933
theorem B387971 : Blo 385764 387971 := bstep (se 1 (by rfl) ⟨290978, by rfl⟩ : syracuseStep 387971 = 581957) B581957
theorem B584579 : Blo 385764 584579 := bstep (se 1 (by rfl) ⟨438434, by rfl⟩ : syracuseStep 584579 = 876869) B876869
theorem B387987 : Blo 385764 387987 := bstep (se 1 (by rfl) ⟨290990, by rfl⟩ : syracuseStep 387987 = 581981) B581981
theorem B584609 : Blo 385764 584609 := bstep (se 2 (by rfl) ⟨219228, by rfl⟩ : syracuseStep 584609 = 438457) B438457
theorem B388003 : Blo 385764 388003 := bstep (se 1 (by rfl) ⟨291002, by rfl⟩ : syracuseStep 388003 = 582005) B582005
theorem B388019 : Blo 385764 388019 := bstep (se 1 (by rfl) ⟨291014, by rfl⟩ : syracuseStep 388019 = 582029) B582029
theorem B584627 : Blo 385764 584627 := bstep (se 1 (by rfl) ⟨438470, by rfl⟩ : syracuseStep 584627 = 876941) B876941
theorem B388035 : Blo 385764 388035 := bstep (se 1 (by rfl) ⟨291026, by rfl⟩ : syracuseStep 388035 = 582053) B582053
theorem B388051 : Blo 385764 388051 := bstep (se 1 (by rfl) ⟨291038, by rfl⟩ : syracuseStep 388051 = 582077) B582077
theorem B388067 : Blo 385764 388067 := bstep (se 1 (by rfl) ⟨291050, by rfl⟩ : syracuseStep 388067 = 582101) B582101
theorem B388083 : Blo 385764 388083 := bstep (se 1 (by rfl) ⟨291062, by rfl⟩ : syracuseStep 388083 = 582125) B582125
theorem B388099 : Blo 385764 388099 := bstep (se 1 (by rfl) ⟨291074, by rfl⟩ : syracuseStep 388099 = 582149) B582149
theorem B388115 : Blo 385764 388115 := bstep (se 1 (by rfl) ⟨291086, by rfl⟩ : syracuseStep 388115 = 582173) B582173
theorem B2583587 : Blo 385764 2583587 := bstep (se 1 (by rfl) ⟨1937690, by rfl⟩ : syracuseStep 2583587 = 3875381) B3875381
theorem B388131 : Blo 385764 388131 := bstep (se 1 (by rfl) ⟨291098, by rfl⟩ : syracuseStep 388131 = 582197) B582197
theorem B1961009 : Blo 385764 1961009 := bstep (se 2 (by rfl) ⟨735378, by rfl⟩ : syracuseStep 1961009 = 1470757) B1470757
theorem B388147 : Blo 385764 388147 := bstep (se 1 (by rfl) ⟨291110, by rfl⟩ : syracuseStep 388147 = 582221) B582221
theorem B388163 : Blo 385764 388163 := bstep (se 1 (by rfl) ⟨291122, by rfl⟩ : syracuseStep 388163 = 582245) B582245
theorem B388179 : Blo 385764 388179 := bstep (se 1 (by rfl) ⟨291134, by rfl⟩ : syracuseStep 388179 = 582269) B582269
theorem B388195 : Blo 385764 388195 := bstep (se 1 (by rfl) ⟨291146, by rfl⟩ : syracuseStep 388195 = 582293) B582293
theorem B388211 : Blo 385764 388211 := bstep (se 1 (by rfl) ⟨291158, by rfl⟩ : syracuseStep 388211 = 582317) B582317
theorem B388227 : Blo 385764 388227 := bstep (se 1 (by rfl) ⟨291170, by rfl⟩ : syracuseStep 388227 = 582341) B582341
theorem B978065 : Blo 385764 978065 := bstep (se 2 (by rfl) ⟨366774, by rfl⟩ : syracuseStep 978065 = 733549) B733549
theorem B388243 : Blo 385764 388243 := bstep (se 1 (by rfl) ⟨291182, by rfl⟩ : syracuseStep 388243 = 582365) B582365
theorem B1469603 : Blo 385764 1469603 := bstep (se 1 (by rfl) ⟨1102202, by rfl⟩ : syracuseStep 1469603 = 2204405) B2204405
theorem B388259 : Blo 385764 388259 := bstep (se 1 (by rfl) ⟨291194, by rfl⟩ : syracuseStep 388259 = 582389) B582389
theorem B1305773 : Blo 385764 1305773 := bstep (se 3 (by rfl) ⟨244832, by rfl⟩ : syracuseStep 1305773 = 489665) B489665
theorem B388275 : Blo 385764 388275 := bstep (se 1 (by rfl) ⟨291206, by rfl⟩ : syracuseStep 388275 = 582413) B582413
theorem B978115 : Blo 385764 978115 := bstep (se 1 (by rfl) ⟨733586, by rfl⟩ : syracuseStep 978115 = 1467173) B1467173
theorem B388291 : Blo 385764 388291 := bstep (se 1 (by rfl) ⟨291218, by rfl⟩ : syracuseStep 388291 = 582437) B582437
theorem B388307 : Blo 385764 388307 := bstep (se 1 (by rfl) ⟨291230, by rfl⟩ : syracuseStep 388307 = 582461) B582461
theorem B1305827 : Blo 385764 1305827 := bstep (se 1 (by rfl) ⟨979370, by rfl⟩ : syracuseStep 1305827 = 1958741) B1958741
theorem B388323 : Blo 385764 388323 := bstep (se 1 (by rfl) ⟨291242, by rfl⟩ : syracuseStep 388323 = 582485) B582485
theorem B1404145 : Blo 385764 1404145 := bstep (se 2 (by rfl) ⟨526554, by rfl⟩ : syracuseStep 1404145 = 1053109) B1053109
theorem B388339 : Blo 385764 388339 := bstep (se 1 (by rfl) ⟨291254, by rfl⟩ : syracuseStep 388339 = 582509) B582509
theorem B388355 : Blo 385764 388355 := bstep (se 1 (by rfl) ⟨291266, by rfl⟩ : syracuseStep 388355 = 582533) B582533
theorem B388371 : Blo 385764 388371 := bstep (se 1 (by rfl) ⟨291278, by rfl⟩ : syracuseStep 388371 = 582557) B582557
theorem B388387 : Blo 385764 388387 := bstep (se 1 (by rfl) ⟨291290, by rfl⟩ : syracuseStep 388387 = 582581) B582581
theorem B388403 : Blo 385764 388403 := bstep (se 1 (by rfl) ⟨291302, by rfl⟩ : syracuseStep 388403 = 582605) B582605
theorem B388419 : Blo 385764 388419 := bstep (se 1 (by rfl) ⟨291314, by rfl⟩ : syracuseStep 388419 = 582629) B582629
theorem B978257 : Blo 385764 978257 := bstep (se 2 (by rfl) ⟨366846, by rfl⟩ : syracuseStep 978257 = 733693) B733693
theorem B388435 : Blo 385764 388435 := bstep (se 1 (by rfl) ⟨291326, by rfl⟩ : syracuseStep 388435 = 582653) B582653
theorem B388451 : Blo 385764 388451 := bstep (se 1 (by rfl) ⟨291338, by rfl⟩ : syracuseStep 388451 = 582677) B582677
theorem B1404259 : Blo 385764 1404259 := bstep (se 1 (by rfl) ⟨1053194, by rfl⟩ : syracuseStep 1404259 = 2106389) B2106389
theorem B388467 : Blo 385764 388467 := bstep (se 1 (by rfl) ⟨291350, by rfl⟩ : syracuseStep 388467 = 582701) B582701
theorem B388483 : Blo 385764 388483 := bstep (se 1 (by rfl) ⟨291362, by rfl⟩ : syracuseStep 388483 = 582725) B582725
theorem B388499 : Blo 385764 388499 := bstep (se 1 (by rfl) ⟨291374, by rfl⟩ : syracuseStep 388499 = 582749) B582749
theorem B388515 : Blo 385764 388515 := bstep (se 1 (by rfl) ⟨291386, by rfl⟩ : syracuseStep 388515 = 582773) B582773
theorem B388531 : Blo 385764 388531 := bstep (se 1 (by rfl) ⟨291398, by rfl⟩ : syracuseStep 388531 = 582797) B582797
theorem B388547 : Blo 385764 388547 := bstep (se 1 (by rfl) ⟨291410, by rfl⟩ : syracuseStep 388547 = 582821) B582821
theorem B388563 : Blo 385764 388563 := bstep (se 1 (by rfl) ⟨291422, by rfl⟩ : syracuseStep 388563 = 582845) B582845
theorem B388579 : Blo 385764 388579 := bstep (se 1 (by rfl) ⟨291434, by rfl⟩ : syracuseStep 388579 = 582869) B582869
theorem B1306097 : Blo 385764 1306097 := bstep (se 2 (by rfl) ⟨489786, by rfl⟩ : syracuseStep 1306097 = 979573) B979573
theorem B388595 : Blo 385764 388595 := bstep (se 1 (by rfl) ⟨291446, by rfl⟩ : syracuseStep 388595 = 582893) B582893
theorem B388611 : Blo 385764 388611 := bstep (se 1 (by rfl) ⟨291458, by rfl⟩ : syracuseStep 388611 = 582917) B582917
theorem B388627 : Blo 385764 388627 := bstep (se 1 (by rfl) ⟨291470, by rfl⟩ : syracuseStep 388627 = 582941) B582941
theorem B388643 : Blo 385764 388643 := bstep (se 1 (by rfl) ⟨291482, by rfl⟩ : syracuseStep 388643 = 582965) B582965
theorem B388659 : Blo 385764 388659 := bstep (se 1 (by rfl) ⟨291494, by rfl⟩ : syracuseStep 388659 = 582989) B582989
theorem B388675 : Blo 385764 388675 := bstep (se 1 (by rfl) ⟨291506, by rfl⟩ : syracuseStep 388675 = 583013) B583013
theorem B618067 : Blo 385764 618067 := bstep (se 1 (by rfl) ⟨463550, by rfl⟩ : syracuseStep 618067 = 927101) B927101
theorem B388691 : Blo 385764 388691 := bstep (se 1 (by rfl) ⟨291518, by rfl⟩ : syracuseStep 388691 = 583037) B583037
theorem B388707 : Blo 385764 388707 := bstep (se 1 (by rfl) ⟨291530, by rfl⟩ : syracuseStep 388707 = 583061) B583061
theorem B388723 : Blo 385764 388723 := bstep (se 1 (by rfl) ⟨291542, by rfl⟩ : syracuseStep 388723 = 583085) B583085
theorem B618113 : Blo 385764 618113 := bstep (se 2 (by rfl) ⟨231792, by rfl⟩ : syracuseStep 618113 = 463585) B463585
theorem B552577 : Blo 385764 552577 := bstep (se 2 (by rfl) ⟨207216, by rfl⟩ : syracuseStep 552577 = 414433) B414433
theorem B388739 : Blo 385764 388739 := bstep (se 1 (by rfl) ⟨291554, by rfl⟩ : syracuseStep 388739 = 583109) B583109
theorem B388755 : Blo 385764 388755 := bstep (se 1 (by rfl) ⟨291566, by rfl⟩ : syracuseStep 388755 = 583133) B583133
theorem B388771 : Blo 385764 388771 := bstep (se 1 (by rfl) ⟨291578, by rfl⟩ : syracuseStep 388771 = 583157) B583157
theorem B388787 : Blo 385764 388787 := bstep (se 1 (by rfl) ⟨291590, by rfl⟩ : syracuseStep 388787 = 583181) B583181
theorem B388803 : Blo 385764 388803 := bstep (se 1 (by rfl) ⟨291602, by rfl⟩ : syracuseStep 388803 = 583205) B583205
theorem B388819 : Blo 385764 388819 := bstep (se 1 (by rfl) ⟨291614, by rfl⟩ : syracuseStep 388819 = 583229) B583229
theorem B552673 : Blo 385764 552673 := bstep (se 2 (by rfl) ⟨207252, by rfl⟩ : syracuseStep 552673 = 414505) B414505
theorem B388835 : Blo 385764 388835 := bstep (se 1 (by rfl) ⟨291626, by rfl⟩ : syracuseStep 388835 = 583253) B583253
theorem B388851 : Blo 385764 388851 := bstep (se 1 (by rfl) ⟨291638, by rfl⟩ : syracuseStep 388851 = 583277) B583277
theorem B388867 : Blo 385764 388867 := bstep (se 1 (by rfl) ⟨291650, by rfl⟩ : syracuseStep 388867 = 583301) B583301
theorem B1240849 : Blo 385764 1240849 := bstep (se 2 (by rfl) ⟨465318, by rfl⟩ : syracuseStep 1240849 = 930637) B930637
theorem B388883 : Blo 385764 388883 := bstep (se 1 (by rfl) ⟨291662, by rfl⟩ : syracuseStep 388883 = 583325) B583325
theorem B388899 : Blo 385764 388899 := bstep (se 1 (by rfl) ⟨291674, by rfl⟩ : syracuseStep 388899 = 583349) B583349
theorem B1470257 : Blo 385764 1470257 := bstep (se 2 (by rfl) ⟨551346, by rfl⟩ : syracuseStep 1470257 = 1102693) B1102693
theorem B388915 : Blo 385764 388915 := bstep (se 1 (by rfl) ⟨291686, by rfl⟩ : syracuseStep 388915 = 583373) B583373
theorem B388931 : Blo 385764 388931 := bstep (se 1 (by rfl) ⟨291698, by rfl⟩ : syracuseStep 388931 = 583397) B583397
theorem B651091 : Blo 385764 651091 := bstep (se 1 (by rfl) ⟨488318, by rfl⟩ : syracuseStep 651091 = 976637) B976637
theorem B388947 : Blo 385764 388947 := bstep (se 1 (by rfl) ⟨291710, by rfl⟩ : syracuseStep 388947 = 583421) B583421
theorem B388963 : Blo 385764 388963 := bstep (se 1 (by rfl) ⟨291722, by rfl⟩ : syracuseStep 388963 = 583445) B583445
theorem B388979 : Blo 385764 388979 := bstep (se 1 (by rfl) ⟨291734, by rfl⟩ : syracuseStep 388979 = 583469) B583469
theorem B388995 : Blo 385764 388995 := bstep (se 1 (by rfl) ⟨291746, by rfl⟩ : syracuseStep 388995 = 583493) B583493
theorem B389011 : Blo 385764 389011 := bstep (se 1 (by rfl) ⟨291758, by rfl⟩ : syracuseStep 389011 = 583517) B583517
theorem B389027 : Blo 385764 389027 := bstep (se 1 (by rfl) ⟨291770, by rfl⟩ : syracuseStep 389027 = 583541) B583541
theorem B389043 : Blo 385764 389043 := bstep (se 1 (by rfl) ⟨291782, by rfl⟩ : syracuseStep 389043 = 583565) B583565
theorem B389059 : Blo 385764 389059 := bstep (se 1 (by rfl) ⟨291794, by rfl⟩ : syracuseStep 389059 = 583589) B583589
theorem B389075 : Blo 385764 389075 := bstep (se 1 (by rfl) ⟨291806, by rfl⟩ : syracuseStep 389075 = 583613) B583613
theorem B651233 : Blo 385764 651233 := bstep (se 2 (by rfl) ⟨244212, by rfl⟩ : syracuseStep 651233 = 488425) B488425
theorem B389091 : Blo 385764 389091 := bstep (se 1 (by rfl) ⟨291818, by rfl⟩ : syracuseStep 389091 = 583637) B583637
theorem B1568753 : Blo 385764 1568753 := bstep (se 2 (by rfl) ⟨588282, by rfl⟩ : syracuseStep 1568753 = 1176565) B1176565
theorem B389107 : Blo 385764 389107 := bstep (se 1 (by rfl) ⟨291830, by rfl⟩ : syracuseStep 389107 = 583661) B583661
theorem B389123 : Blo 385764 389123 := bstep (se 1 (by rfl) ⟨291842, by rfl⟩ : syracuseStep 389123 = 583685) B583685
theorem B1306637 : Blo 385764 1306637 := bstep (se 3 (by rfl) ⟨244994, by rfl⟩ : syracuseStep 1306637 = 489989) B489989
theorem B389139 : Blo 385764 389139 := bstep (se 1 (by rfl) ⟨291854, by rfl⟩ : syracuseStep 389139 = 583709) B583709
theorem B389155 : Blo 385764 389155 := bstep (se 1 (by rfl) ⟨291866, by rfl⟩ : syracuseStep 389155 = 583733) B583733
theorem B389171 : Blo 385764 389171 := bstep (se 1 (by rfl) ⟨291878, by rfl⟩ : syracuseStep 389171 = 583757) B583757
theorem B1306691 : Blo 385764 1306691 := bstep (se 1 (by rfl) ⟨980018, by rfl⟩ : syracuseStep 1306691 = 1960037) B1960037
theorem B389187 : Blo 385764 389187 := bstep (se 1 (by rfl) ⟨291890, by rfl⟩ : syracuseStep 389187 = 583781) B583781
theorem B389203 : Blo 385764 389203 := bstep (se 1 (by rfl) ⟨291902, by rfl⟩ : syracuseStep 389203 = 583805) B583805
theorem B651361 : Blo 385764 651361 := bstep (se 2 (by rfl) ⟨244260, by rfl⟩ : syracuseStep 651361 = 488521) B488521
theorem B389219 : Blo 385764 389219 := bstep (se 1 (by rfl) ⟨291914, by rfl⟩ : syracuseStep 389219 = 583829) B583829
theorem B389235 : Blo 385764 389235 := bstep (se 1 (by rfl) ⟨291926, by rfl⟩ : syracuseStep 389235 = 583853) B583853
theorem B618625 : Blo 385764 618625 := bstep (se 2 (by rfl) ⟨231984, by rfl⟩ : syracuseStep 618625 = 463969) B463969
theorem B651395 : Blo 385764 651395 := bstep (se 1 (by rfl) ⟨488546, by rfl⟩ : syracuseStep 651395 = 977093) B977093
theorem B389251 : Blo 385764 389251 := bstep (se 1 (by rfl) ⟨291938, by rfl⟩ : syracuseStep 389251 = 583877) B583877
theorem B389267 : Blo 385764 389267 := bstep (se 1 (by rfl) ⟨291950, by rfl⟩ : syracuseStep 389267 = 583901) B583901
theorem B389283 : Blo 385764 389283 := bstep (se 1 (by rfl) ⟨291962, by rfl⟩ : syracuseStep 389283 = 583925) B583925
theorem B389299 : Blo 385764 389299 := bstep (se 1 (by rfl) ⟨291974, by rfl⟩ : syracuseStep 389299 = 583949) B583949
theorem B389315 : Blo 385764 389315 := bstep (se 1 (by rfl) ⟨291986, by rfl⟩ : syracuseStep 389315 = 583973) B583973
theorem B553169 : Blo 385764 553169 := bstep (se 2 (by rfl) ⟨207438, by rfl⟩ : syracuseStep 553169 = 414877) B414877
theorem B389331 : Blo 385764 389331 := bstep (se 1 (by rfl) ⟨291998, by rfl⟩ : syracuseStep 389331 = 583997) B583997
theorem B389347 : Blo 385764 389347 := bstep (se 1 (by rfl) ⟨292010, by rfl⟩ : syracuseStep 389347 = 584021) B584021
theorem B389363 : Blo 385764 389363 := bstep (se 1 (by rfl) ⟨292022, by rfl⟩ : syracuseStep 389363 = 584045) B584045
theorem B651523 : Blo 385764 651523 := bstep (se 1 (by rfl) ⟨488642, by rfl⟩ : syracuseStep 651523 = 977285) B977285
theorem B389379 : Blo 385764 389379 := bstep (se 1 (by rfl) ⟨292034, by rfl⟩ : syracuseStep 389379 = 584069) B584069
theorem B389395 : Blo 385764 389395 := bstep (se 1 (by rfl) ⟨292046, by rfl⟩ : syracuseStep 389395 = 584093) B584093
theorem B389411 : Blo 385764 389411 := bstep (se 1 (by rfl) ⟨292058, by rfl⟩ : syracuseStep 389411 = 584117) B584117
theorem B979249 : Blo 385764 979249 := bstep (se 2 (by rfl) ⟨367218, by rfl⟩ : syracuseStep 979249 = 734437) B734437
theorem B389427 : Blo 385764 389427 := bstep (se 1 (by rfl) ⟨292070, by rfl⟩ : syracuseStep 389427 = 584141) B584141
theorem B389443 : Blo 385764 389443 := bstep (se 1 (by rfl) ⟨292082, by rfl⟩ : syracuseStep 389443 = 584165) B584165
theorem B1306961 : Blo 385764 1306961 := bstep (se 2 (by rfl) ⟨490110, by rfl⟩ : syracuseStep 1306961 = 980221) B980221
theorem B389459 : Blo 385764 389459 := bstep (se 1 (by rfl) ⟨292094, by rfl⟩ : syracuseStep 389459 = 584189) B584189
theorem B389475 : Blo 385764 389475 := bstep (se 1 (by rfl) ⟨292106, by rfl⟩ : syracuseStep 389475 = 584213) B584213
theorem B389491 : Blo 385764 389491 := bstep (se 1 (by rfl) ⟨292118, by rfl⟩ : syracuseStep 389491 = 584237) B584237
theorem B389507 : Blo 385764 389507 := bstep (se 1 (by rfl) ⟨292130, by rfl⟩ : syracuseStep 389507 = 584261) B584261
theorem B651665 : Blo 385764 651665 := bstep (se 2 (by rfl) ⟨244374, by rfl⟩ : syracuseStep 651665 = 488749) B488749
theorem B389523 : Blo 385764 389523 := bstep (se 1 (by rfl) ⟨292142, by rfl⟩ : syracuseStep 389523 = 584285) B584285
theorem B389539 : Blo 385764 389539 := bstep (se 1 (by rfl) ⟨292154, by rfl⟩ : syracuseStep 389539 = 584309) B584309
theorem B389555 : Blo 385764 389555 := bstep (se 1 (by rfl) ⟨292166, by rfl⟩ : syracuseStep 389555 = 584333) B584333
theorem B389571 : Blo 385764 389571 := bstep (se 1 (by rfl) ⟨292178, by rfl⟩ : syracuseStep 389571 = 584357) B584357
theorem B389587 : Blo 385764 389587 := bstep (se 1 (by rfl) ⟨292190, by rfl⟩ : syracuseStep 389587 = 584381) B584381
theorem B1962467 : Blo 385764 1962467 := bstep (se 1 (by rfl) ⟨1471850, by rfl⟩ : syracuseStep 1962467 = 2943701) B2943701
theorem B389603 : Blo 385764 389603 := bstep (se 1 (by rfl) ⟨292202, by rfl⟩ : syracuseStep 389603 = 584405) B584405
theorem B389619 : Blo 385764 389619 := bstep (se 1 (by rfl) ⟨292214, by rfl⟩ : syracuseStep 389619 = 584429) B584429
theorem B389635 : Blo 385764 389635 := bstep (se 1 (by rfl) ⟨292226, by rfl⟩ : syracuseStep 389635 = 584453) B584453
theorem B651793 : Blo 385764 651793 := bstep (se 2 (by rfl) ⟨244422, by rfl⟩ : syracuseStep 651793 = 488845) B488845
theorem B389651 : Blo 385764 389651 := bstep (se 1 (by rfl) ⟨292238, by rfl⟩ : syracuseStep 389651 = 584477) B584477
theorem B389667 : Blo 385764 389667 := bstep (se 1 (by rfl) ⟨292250, by rfl⟩ : syracuseStep 389667 = 584501) B584501
theorem B651827 : Blo 385764 651827 := bstep (se 1 (by rfl) ⟨488870, by rfl⟩ : syracuseStep 651827 = 977741) B977741
theorem B389683 : Blo 385764 389683 := bstep (se 1 (by rfl) ⟨292262, by rfl⟩ : syracuseStep 389683 = 584525) B584525
theorem B979523 : Blo 385764 979523 := bstep (se 1 (by rfl) ⟨734642, by rfl⟩ : syracuseStep 979523 = 1469285) B1469285
theorem B389699 : Blo 385764 389699 := bstep (se 1 (by rfl) ⟨292274, by rfl⟩ : syracuseStep 389699 = 584549) B584549
theorem B389715 : Blo 385764 389715 := bstep (se 1 (by rfl) ⟨292286, by rfl⟩ : syracuseStep 389715 = 584573) B584573
theorem B389731 : Blo 385764 389731 := bstep (se 1 (by rfl) ⟨292298, by rfl⟩ : syracuseStep 389731 = 584597) B584597
theorem B389747 : Blo 385764 389747 := bstep (se 1 (by rfl) ⟨292310, by rfl⟩ : syracuseStep 389747 = 584621) B584621
theorem B389763 : Blo 385764 389763 := bstep (se 1 (by rfl) ⟨292322, by rfl⟩ : syracuseStep 389763 = 584645) B584645
theorem B619169 : Blo 385764 619169 := bstep (se 2 (by rfl) ⟨232188, by rfl⟩ : syracuseStep 619169 = 464377) B464377
theorem B651955 : Blo 385764 651955 := bstep (se 1 (by rfl) ⟨488966, by rfl⟩ : syracuseStep 651955 = 977933) B977933
theorem B979715 : Blo 385764 979715 := bstep (se 1 (by rfl) ⟨734786, by rfl⟩ : syracuseStep 979715 = 1469573) B1469573
theorem B652097 : Blo 385764 652097 := bstep (se 2 (by rfl) ⟨244536, by rfl⟩ : syracuseStep 652097 = 489073) B489073
theorem B2356067 : Blo 385764 2356067 := bstep (se 1 (by rfl) ⟨1767050, by rfl⟩ : syracuseStep 2356067 = 3534101) B3534101
theorem B1307501 : Blo 385764 1307501 := bstep (se 3 (by rfl) ⟨245156, by rfl⟩ : syracuseStep 1307501 = 490313) B490313
theorem B1307555 : Blo 385764 1307555 := bstep (se 1 (by rfl) ⟨980666, by rfl⟩ : syracuseStep 1307555 = 1961333) B1961333
theorem B1242029 : Blo 385764 1242029 := bstep (se 3 (by rfl) ⟨232880, by rfl⟩ : syracuseStep 1242029 = 465761) B465761
theorem B652225 : Blo 385764 652225 := bstep (se 2 (by rfl) ⟨244584, by rfl⟩ : syracuseStep 652225 = 489169) B489169
theorem B652259 : Blo 385764 652259 := bstep (se 1 (by rfl) ⟨489194, by rfl⟩ : syracuseStep 652259 = 978389) B978389
theorem B554035 : Blo 385764 554035 := bstep (se 1 (by rfl) ⟨415526, by rfl⟩ : syracuseStep 554035 = 831053) B831053
theorem B488531 : Blo 385764 488531 := bstep (se 1 (by rfl) ⟨366398, by rfl⟩ : syracuseStep 488531 = 732797) B732797
theorem B652387 : Blo 385764 652387 := bstep (se 1 (by rfl) ⟨489290, by rfl⟩ : syracuseStep 652387 = 978581) B978581
theorem B1537165 : Blo 385764 1537165 := bstep (se 3 (by rfl) ⟨288218, by rfl⟩ : syracuseStep 1537165 = 576437) B576437
theorem B554131 : Blo 385764 554131 := bstep (se 1 (by rfl) ⟨415598, by rfl⟩ : syracuseStep 554131 = 831197) B831197
theorem B1307825 : Blo 385764 1307825 := bstep (se 2 (by rfl) ⟨490434, by rfl⟩ : syracuseStep 1307825 = 980869) B980869
theorem B1471715 : Blo 385764 1471715 := bstep (se 1 (by rfl) ⟨1103786, by rfl⟩ : syracuseStep 1471715 = 2207573) B2207573
theorem B652529 : Blo 385764 652529 := bstep (se 2 (by rfl) ⟨244698, by rfl⟩ : syracuseStep 652529 = 489397) B489397
theorem B1471729 : Blo 385764 1471729 := bstep (se 2 (by rfl) ⟨551898, by rfl⟩ : syracuseStep 1471729 = 1103797) B1103797
theorem B1570061 : Blo 385764 1570061 := bstep (se 3 (by rfl) ⟨294386, by rfl⟩ : syracuseStep 1570061 = 588773) B588773
theorem B1963277 : Blo 385764 1963277 := bstep (se 3 (by rfl) ⟨368114, by rfl⟩ : syracuseStep 1963277 = 736229) B736229
theorem B652657 : Blo 385764 652657 := bstep (se 2 (by rfl) ⟨244746, by rfl⟩ : syracuseStep 652657 = 489493) B489493
theorem B1865101 : Blo 385764 1865101 := bstep (se 3 (by rfl) ⟨349706, by rfl⟩ : syracuseStep 1865101 = 699413) B699413
theorem B652691 : Blo 385764 652691 := bstep (se 1 (by rfl) ⟨489518, by rfl⟩ : syracuseStep 652691 = 979037) B979037
theorem B783857 : Blo 385764 783857 := bstep (se 2 (by rfl) ⟨293946, by rfl⟩ : syracuseStep 783857 = 587893) B587893
theorem B652819 : Blo 385764 652819 := bstep (se 1 (by rfl) ⟨489614, by rfl⟩ : syracuseStep 652819 = 979229) B979229
theorem B620131 : Blo 385764 620131 := bstep (se 1 (by rfl) ⟨465098, by rfl⟩ : syracuseStep 620131 = 930197) B930197
theorem B554627 : Blo 385764 554627 := bstep (se 1 (by rfl) ⟨415970, by rfl⟩ : syracuseStep 554627 = 831941) B831941
theorem B652961 : Blo 385764 652961 := bstep (se 2 (by rfl) ⟨244860, by rfl⟩ : syracuseStep 652961 = 489721) B489721
theorem B1767089 : Blo 385764 1767089 := bstep (se 2 (by rfl) ⟨662658, by rfl⟩ : syracuseStep 1767089 = 1325317) B1325317
theorem B980657 : Blo 385764 980657 := bstep (se 2 (by rfl) ⟨367746, by rfl⟩ : syracuseStep 980657 = 735493) B735493
theorem B1308365 : Blo 385764 1308365 := bstep (se 3 (by rfl) ⟨245318, by rfl⟩ : syracuseStep 1308365 = 490637) B490637
theorem B980707 : Blo 385764 980707 := bstep (se 1 (by rfl) ⟨735530, by rfl⟩ : syracuseStep 980707 = 1471061) B1471061
theorem B587521 : Blo 385764 587521 := bstep (se 2 (by rfl) ⟨220320, by rfl⟩ : syracuseStep 587521 = 440641) B440641
theorem B1308419 : Blo 385764 1308419 := bstep (se 1 (by rfl) ⟨981314, by rfl⟩ : syracuseStep 1308419 = 1962629) B1962629
theorem B489235 : Blo 385764 489235 := bstep (se 1 (by rfl) ⟨366926, by rfl⟩ : syracuseStep 489235 = 733853) B733853
theorem B653089 : Blo 385764 653089 := bstep (se 2 (by rfl) ⟨244908, by rfl⟩ : syracuseStep 653089 = 489817) B489817
theorem B653123 : Blo 385764 653123 := bstep (se 1 (by rfl) ⟨489842, by rfl⟩ : syracuseStep 653123 = 979685) B979685
theorem B620387 : Blo 385764 620387 := bstep (se 1 (by rfl) ⟨465290, by rfl⟩ : syracuseStep 620387 = 930581) B930581
theorem B980849 : Blo 385764 980849 := bstep (se 2 (by rfl) ⟨367818, by rfl⟩ : syracuseStep 980849 = 735637) B735637
theorem B489331 : Blo 385764 489331 := bstep (se 1 (by rfl) ⟨366998, by rfl⟩ : syracuseStep 489331 = 733997) B733997
theorem B1046449 : Blo 385764 1046449 := bstep (se 2 (by rfl) ⟨392418, by rfl⟩ : syracuseStep 1046449 = 784837) B784837
theorem B653251 : Blo 385764 653251 := bstep (se 1 (by rfl) ⟨489938, by rfl⟩ : syracuseStep 653251 = 979877) B979877
theorem B2488333 : Blo 385764 2488333 := bstep (se 3 (by rfl) ⟨466562, by rfl⟩ : syracuseStep 2488333 = 933125) B933125
theorem B1308689 : Blo 385764 1308689 := bstep (se 2 (by rfl) ⟨490758, by rfl⟩ : syracuseStep 1308689 = 981517) B981517
theorem B1767473 : Blo 385764 1767473 := bstep (se 2 (by rfl) ⟨662802, by rfl⟩ : syracuseStep 1767473 = 1325605) B1325605
theorem B20183093 : Blo 385764 20183093 := bstep (se 5 (by rfl) ⟨946082, by rfl⟩ : syracuseStep 20183093 = 1892165) B1892165
theorem B1701965 : Blo 385764 1701965 := bstep (se 3 (by rfl) ⟨319118, by rfl⟩ : syracuseStep 1701965 = 638237) B638237
theorem B653393 : Blo 385764 653393 := bstep (se 2 (by rfl) ⟨245022, by rfl⟩ : syracuseStep 653393 = 490045) B490045
theorem B653521 : Blo 385764 653521 := bstep (se 2 (by rfl) ⟨245070, by rfl⟩ : syracuseStep 653521 = 490141) B490141
theorem B653555 : Blo 385764 653555 := bstep (se 1 (by rfl) ⟨490166, by rfl⟩ : syracuseStep 653555 = 980333) B980333
theorem B489827 : Blo 385764 489827 := bstep (se 1 (by rfl) ⟨367370, by rfl⟩ : syracuseStep 489827 = 734741) B734741
theorem B653683 : Blo 385764 653683 := bstep (se 1 (by rfl) ⟨490262, by rfl⟩ : syracuseStep 653683 = 980525) B980525
theorem B1210801 : Blo 385764 1210801 := bstep (se 2 (by rfl) ⟨454050, by rfl⟩ : syracuseStep 1210801 = 908101) B908101
theorem B653825 : Blo 385764 653825 := bstep (se 2 (by rfl) ⟨245184, by rfl⟩ : syracuseStep 653825 = 490369) B490369
theorem B621091 : Blo 385764 621091 := bstep (se 1 (by rfl) ⟨465818, by rfl⟩ : syracuseStep 621091 = 931637) B931637
theorem B1309229 : Blo 385764 1309229 := bstep (se 3 (by rfl) ⟨245480, by rfl⟩ : syracuseStep 1309229 = 490961) B490961
theorem B1309283 : Blo 385764 1309283 := bstep (se 1 (by rfl) ⟨981962, by rfl⟩ : syracuseStep 1309283 = 1963925) B1963925
theorem B653953 : Blo 385764 653953 := bstep (se 2 (by rfl) ⟨245232, by rfl⟩ : syracuseStep 653953 = 490465) B490465
theorem B653987 : Blo 385764 653987 := bstep (se 1 (by rfl) ⟨490490, by rfl⟩ : syracuseStep 653987 = 980981) B980981
theorem B1473187 : Blo 385764 1473187 := bstep (se 1 (by rfl) ⟨1104890, by rfl⟩ : syracuseStep 1473187 = 2209781) B2209781
theorem B1243811 : Blo 385764 1243811 := bstep (se 1 (by rfl) ⟨932858, by rfl⟩ : syracuseStep 1243811 = 1865717) B1865717
theorem B654115 : Blo 385764 654115 := bstep (se 1 (by rfl) ⟨490586, by rfl⟩ : syracuseStep 654115 = 981173) B981173
theorem B621361 : Blo 385764 621361 := bstep (se 2 (by rfl) ⟨233010, by rfl⟩ : syracuseStep 621361 = 466021) B466021
theorem B981841 : Blo 385764 981841 := bstep (se 2 (by rfl) ⟨368190, by rfl⟩ : syracuseStep 981841 = 736381) B736381
theorem B621425 : Blo 385764 621425 := bstep (se 2 (by rfl) ⟨233034, by rfl⟩ : syracuseStep 621425 = 466069) B466069
theorem B1309553 : Blo 385764 1309553 := bstep (se 2 (by rfl) ⟨491082, by rfl⟩ : syracuseStep 1309553 = 982165) B982165
theorem B588689 : Blo 385764 588689 := bstep (se 2 (by rfl) ⟨220758, by rfl⟩ : syracuseStep 588689 = 441517) B441517
theorem B654257 : Blo 385764 654257 := bstep (se 2 (by rfl) ⟨245346, by rfl⟩ : syracuseStep 654257 = 490693) B490693
theorem B2489285 : Blo 385764 2489285 := bstep (se 4 (by rfl) ⟨233370, by rfl⟩ : syracuseStep 2489285 = 466741) B466741
theorem B490531 : Blo 385764 490531 := bstep (se 1 (by rfl) ⟨367898, by rfl⟩ : syracuseStep 490531 = 735797) B735797
theorem B654385 : Blo 385764 654385 := bstep (se 2 (by rfl) ⟨245394, by rfl⟩ : syracuseStep 654385 = 490789) B490789
theorem B654419 : Blo 385764 654419 := bstep (se 1 (by rfl) ⟨490814, by rfl⟩ : syracuseStep 654419 = 981629) B981629
theorem B982115 : Blo 385764 982115 := bstep (se 1 (by rfl) ⟨736586, by rfl⟩ : syracuseStep 982115 = 1473173) B1473173
theorem B621697 : Blo 385764 621697 := bstep (se 2 (by rfl) ⟨233136, by rfl⟩ : syracuseStep 621697 = 466273) B466273
theorem B490627 : Blo 385764 490627 := bstep (se 1 (by rfl) ⟨367970, by rfl⟩ : syracuseStep 490627 = 735941) B735941
theorem B654547 : Blo 385764 654547 := bstep (se 1 (by rfl) ⟨490910, by rfl⟩ : syracuseStep 654547 = 981821) B981821
theorem B392483 : Blo 385764 392483 := bstep (se 1 (by rfl) ⟨294362, by rfl⟩ : syracuseStep 392483 = 588725) B588725
theorem B982307 : Blo 385764 982307 := bstep (se 1 (by rfl) ⟨736730, by rfl⟩ : syracuseStep 982307 = 1473461) B1473461
theorem B785713 : Blo 385764 785713 := bstep (se 2 (by rfl) ⟨294642, by rfl⟩ : syracuseStep 785713 = 589285) B589285
theorem B1572173 : Blo 385764 1572173 := bstep (se 3 (by rfl) ⟨294782, by rfl⟩ : syracuseStep 1572173 = 589565) B589565
theorem B654689 : Blo 385764 654689 := bstep (se 2 (by rfl) ⟨245508, by rfl⟩ : syracuseStep 654689 = 491017) B491017
theorem B1080707 : Blo 385764 1080707 := bstep (se 1 (by rfl) ⟨810530, by rfl⟩ : syracuseStep 1080707 = 1621061) B1621061
theorem B1310093 : Blo 385764 1310093 := bstep (se 3 (by rfl) ⟨245642, by rfl⟩ : syracuseStep 1310093 = 491285) B491285
theorem B1146275 : Blo 385764 1146275 := bstep (se 1 (by rfl) ⟨859706, by rfl⟩ : syracuseStep 1146275 = 1719413) B1719413
theorem B1310147 : Blo 385764 1310147 := bstep (se 1 (by rfl) ⟨982610, by rfl⟩ : syracuseStep 1310147 = 1965221) B1965221
theorem B654817 : Blo 385764 654817 := bstep (se 2 (by rfl) ⟨245556, by rfl⟩ : syracuseStep 654817 = 491113) B491113
theorem B654851 : Blo 385764 654851 := bstep (se 1 (by rfl) ⟨491138, by rfl⟩ : syracuseStep 654851 = 982277) B982277
theorem B491123 : Blo 385764 491123 := bstep (se 1 (by rfl) ⟨368342, by rfl⟩ : syracuseStep 491123 = 736685) B736685
theorem B654979 : Blo 385764 654979 := bstep (se 1 (by rfl) ⟨491234, by rfl⟩ : syracuseStep 654979 = 982469) B982469
theorem B523955 : Blo 385764 523955 := bstep (se 1 (by rfl) ⟨392966, by rfl⟩ : syracuseStep 523955 = 785933) B785933
theorem B2358989 : Blo 385764 2358989 := bstep (se 3 (by rfl) ⟨442310, by rfl⟩ : syracuseStep 2358989 = 884621) B884621
theorem B1310417 : Blo 385764 1310417 := bstep (se 2 (by rfl) ⟨491406, by rfl⟩ : syracuseStep 1310417 = 982813) B982813
theorem B1244899 : Blo 385764 1244899 := bstep (se 1 (by rfl) ⟨933674, by rfl⟩ : syracuseStep 1244899 = 1867349) B1867349
theorem B655121 : Blo 385764 655121 := bstep (se 2 (by rfl) ⟨245670, by rfl⟩ : syracuseStep 655121 = 491341) B491341
theorem B589601 : Blo 385764 589601 := bstep (se 2 (by rfl) ⟨221100, by rfl⟩ : syracuseStep 589601 = 442201) B442201
theorem B1245041 : Blo 385764 1245041 := bstep (se 2 (by rfl) ⟨466890, by rfl⟩ : syracuseStep 1245041 = 933781) B933781
theorem B884611 : Blo 385764 884611 := bstep (se 1 (by rfl) ⟨663458, by rfl⟩ : syracuseStep 884611 = 1326917) B1326917
theorem B2359181 : Blo 385764 2359181 := bstep (se 3 (by rfl) ⟨442346, by rfl⟩ : syracuseStep 2359181 = 884693) B884693
theorem B655249 : Blo 385764 655249 := bstep (se 2 (by rfl) ⟨245718, by rfl⟩ : syracuseStep 655249 = 491437) B491437
theorem B655283 : Blo 385764 655283 := bstep (se 1 (by rfl) ⟨491462, by rfl⟩ : syracuseStep 655283 = 982925) B982925
theorem B1310795 : Blo 385764 1310795 := bstep (se 1 (by rfl) ⟨983096, by rfl⟩ : syracuseStep 1310795 = 1966193) B1966193
theorem B655499 : Blo 385764 655499 := bstep (se 1 (by rfl) ⟨491624, by rfl⟩ : syracuseStep 655499 = 983249) B983249
theorem B622745 : Blo 385764 622745 := bstep (se 2 (by rfl) ⟨233529, by rfl⟩ : syracuseStep 622745 = 467059) B467059
theorem B655627 : Blo 385764 655627 := bstep (se 1 (by rfl) ⟨491720, by rfl⟩ : syracuseStep 655627 = 983441) B983441
theorem B1311065 : Blo 385764 1311065 := bstep (se 2 (by rfl) ⟨491649, by rfl⟩ : syracuseStep 1311065 = 983299) B983299
theorem B622937 : Blo 385764 622937 := bstep (se 2 (by rfl) ⟨233601, by rfl⟩ : syracuseStep 622937 = 467203) B467203
theorem B655769 : Blo 385764 655769 := bstep (se 2 (by rfl) ⟨245913, by rfl⟩ : syracuseStep 655769 = 491827) B491827
theorem B623065 : Blo 385764 623065 := bstep (se 2 (by rfl) ⟨233649, by rfl⟩ : syracuseStep 623065 = 467299) B467299
theorem B1245719 : Blo 385764 1245719 := bstep (se 1 (by rfl) ⟨934289, by rfl⟩ : syracuseStep 1245719 = 1868579) B1868579
theorem B655897 : Blo 385764 655897 := bstep (se 2 (by rfl) ⟨245961, by rfl⟩ : syracuseStep 655897 = 491923) B491923
theorem B1475117 : Blo 385764 1475117 := bstep (se 3 (by rfl) ⟨276584, by rfl⟩ : syracuseStep 1475117 = 553169) B553169
theorem B2490925 : Blo 385764 2490925 := bstep (se 3 (by rfl) ⟨467048, by rfl⟩ : syracuseStep 2490925 = 934097) B934097
theorem B983603 : Blo 385764 983603 := bstep (se 1 (by rfl) ⟨737702, by rfl⟩ : syracuseStep 983603 = 1475405) B1475405
theorem B492247 : Blo 385764 492247 := bstep (se 1 (by rfl) ⟨369185, by rfl⟩ : syracuseStep 492247 = 738371) B738371
theorem B983897 : Blo 385764 983897 := bstep (se 2 (by rfl) ⟨368961, by rfl⟩ : syracuseStep 983897 = 737923) B737923
theorem B2950019 : Blo 385764 2950019 := bstep (se 1 (by rfl) ⟨2212514, by rfl⟩ : syracuseStep 2950019 = 4425029) B4425029
theorem B1311767 : Blo 385764 1311767 := bstep (se 1 (by rfl) ⟨983825, by rfl⟩ : syracuseStep 1311767 = 1967651) B1967651
theorem B1246283 : Blo 385764 1246283 := bstep (se 1 (by rfl) ⟨934712, by rfl⟩ : syracuseStep 1246283 = 1869425) B1869425
theorem B656471 : Blo 385764 656471 := bstep (se 1 (by rfl) ⟨492353, by rfl⟩ : syracuseStep 656471 = 984707) B984707
theorem B623705 : Blo 385764 623705 := bstep (se 2 (by rfl) ⟨233889, by rfl⟩ : syracuseStep 623705 = 467779) B467779
theorem B656599 : Blo 385764 656599 := bstep (se 1 (by rfl) ⟨492449, by rfl⟩ : syracuseStep 656599 = 984899) B984899
theorem B1869101 : Blo 385764 1869101 := bstep (se 3 (by rfl) ⟨350456, by rfl⟩ : syracuseStep 1869101 = 700913) B700913
theorem B1475891 : Blo 385764 1475891 := bstep (se 1 (by rfl) ⟨1106918, by rfl⟩ : syracuseStep 1475891 = 2213837) B2213837
theorem B2098649 : Blo 385764 2098649 := bstep (se 2 (by rfl) ⟨786993, by rfl⟩ : syracuseStep 2098649 = 1573987) B1573987
theorem B1246681 : Blo 385764 1246681 := bstep (se 2 (by rfl) ⟨467505, by rfl⟩ : syracuseStep 1246681 = 935011) B935011
theorem B493067 : Blo 385764 493067 := bstep (se 1 (by rfl) ⟨369800, by rfl⟩ : syracuseStep 493067 = 739601) B739601
theorem B1312307 : Blo 385764 1312307 := bstep (se 1 (by rfl) ⟨984230, by rfl⟩ : syracuseStep 1312307 = 1968461) B1968461
theorem B1574603 : Blo 385764 1574603 := bstep (se 1 (by rfl) ⟨1180952, by rfl⟩ : syracuseStep 1574603 = 2361905) B2361905
theorem B1312577 : Blo 385764 1312577 := bstep (se 2 (by rfl) ⟨492216, by rfl⟩ : syracuseStep 1312577 = 984433) B984433
theorem B657227 : Blo 385764 657227 := bstep (se 1 (by rfl) ⟨492920, by rfl⟩ : syracuseStep 657227 = 985841) B985841
theorem B1574801 : Blo 385764 1574801 := bstep (se 2 (by rfl) ⟨590550, by rfl⟩ : syracuseStep 1574801 = 1181101) B1181101
theorem B1771415 : Blo 385764 1771415 := bstep (se 1 (by rfl) ⟨1328561, by rfl⟩ : syracuseStep 1771415 = 2657123) B2657123
theorem B657355 : Blo 385764 657355 := bstep (se 1 (by rfl) ⟨493016, by rfl⟩ : syracuseStep 657355 = 986033) B986033
theorem B657497 : Blo 385764 657497 := bstep (se 2 (by rfl) ⟨246561, by rfl⟩ : syracuseStep 657497 = 493123) B493123
theorem B657625 : Blo 385764 657625 := bstep (se 2 (by rfl) ⟨246609, by rfl⟩ : syracuseStep 657625 = 493219) B493219
theorem B1313117 : Blo 385764 1313117 := bstep (se 3 (by rfl) ⟨246209, by rfl⟩ : syracuseStep 1313117 = 492419) B492419
theorem B985547 : Blo 385764 985547 := bstep (se 1 (by rfl) ⟨739160, by rfl⟩ : syracuseStep 985547 = 1478321) B1478321
theorem B2198117 : Blo 385764 2198117 := bstep (se 4 (by rfl) ⟨206073, by rfl⟩ : syracuseStep 2198117 = 412147) B412147
theorem B1247923 : Blo 385764 1247923 := bstep (se 1 (by rfl) ⟨935942, by rfl⟩ : syracuseStep 1247923 = 1871885) B1871885
theorem B1477379 : Blo 385764 1477379 := bstep (se 1 (by rfl) ⟨1108034, by rfl⟩ : syracuseStep 1477379 = 2216069) B2216069
theorem B1772381 : Blo 385764 1772381 := bstep (se 3 (by rfl) ⟨332321, by rfl⟩ : syracuseStep 1772381 = 664643) B664643
theorem B1575773 : Blo 385764 1575773 := bstep (se 3 (by rfl) ⟨295457, by rfl⟩ : syracuseStep 1575773 = 590915) B590915
theorem B3312485 : Blo 385764 3312485 := bstep (se 4 (by rfl) ⟨310545, by rfl⟩ : syracuseStep 3312485 = 621091) B621091
theorem B2198573 : Blo 385764 2198573 := bstep (se 3 (by rfl) ⟨412232, by rfl⟩ : syracuseStep 2198573 = 824465) B824465
theorem B1477835 : Blo 385764 1477835 := bstep (se 1 (by rfl) ⟨1108376, by rfl⟩ : syracuseStep 1477835 = 2216753) B2216753
theorem B757081 : Blo 385764 757081 := bstep (se 2 (by rfl) ⟨283905, by rfl⟩ : syracuseStep 757081 = 567811) B567811
theorem B1478033 : Blo 385764 1478033 := bstep (se 2 (by rfl) ⟨554262, by rfl⟩ : syracuseStep 1478033 = 1108525) B1108525
theorem B986519 : Blo 385764 986519 := bstep (se 1 (by rfl) ⟨739889, by rfl⟩ : syracuseStep 986519 = 1479779) B1479779
theorem B1314251 : Blo 385764 1314251 := bstep (se 1 (by rfl) ⟨985688, by rfl⟩ : syracuseStep 1314251 = 1971377) B1971377
theorem B3313169 : Blo 385764 3313169 := bstep (se 2 (by rfl) ⟨1242438, by rfl⟩ : syracuseStep 3313169 = 2484877) B2484877
theorem B1969757 : Blo 385764 1969757 := bstep (se 3 (by rfl) ⟨369329, by rfl⟩ : syracuseStep 1969757 = 738659) B738659
theorem B2199257 : Blo 385764 2199257 := bstep (se 2 (by rfl) ⟨824721, by rfl⟩ : syracuseStep 2199257 = 1649443) B1649443
theorem B1314521 : Blo 385764 1314521 := bstep (se 2 (by rfl) ⟨492945, by rfl⟩ : syracuseStep 1314521 = 985891) B985891
theorem B1576793 : Blo 385764 1576793 := bstep (se 2 (by rfl) ⟨591297, by rfl⟩ : syracuseStep 1576793 = 1182595) B1182595
theorem B3543115 : Blo 385764 3543115 := bstep (se 1 (by rfl) ⟨2657336, by rfl⟩ : syracuseStep 3543115 = 5314673) B5314673
theorem B1478807 : Blo 385764 1478807 := bstep (se 1 (by rfl) ⟨1109105, by rfl⟩ : syracuseStep 1478807 = 2218211) B2218211
theorem B2953421 : Blo 385764 2953421 := bstep (se 3 (by rfl) ⟨553766, by rfl⟩ : syracuseStep 2953421 = 1107533) B1107533
theorem B1872193 : Blo 385764 1872193 := bstep (se 2 (by rfl) ⟨702072, by rfl⟩ : syracuseStep 1872193 = 1404145) B1404145
theorem B1479005 : Blo 385764 1479005 := bstep (se 3 (by rfl) ⟨277313, by rfl⟩ : syracuseStep 1479005 = 554627) B554627
theorem B1315223 : Blo 385764 1315223 := bstep (se 1 (by rfl) ⟨986417, by rfl⟩ : syracuseStep 1315223 = 1972835) B1972835
theorem B2691629 : Blo 385764 2691629 := bstep (se 3 (by rfl) ⟨504680, by rfl⟩ : syracuseStep 2691629 = 1009361) B1009361
theorem B2953907 : Blo 385764 2953907 := bstep (se 1 (by rfl) ⟨2215430, by rfl⟩ : syracuseStep 2953907 = 4430861) B4430861
theorem B463627 : Blo 385764 463627 := bstep (se 1 (by rfl) ⟨347720, by rfl⟩ : syracuseStep 463627 = 695441) B695441
theorem B824089 : Blo 385764 824089 := bstep (se 2 (by rfl) ⟨309033, by rfl⟩ : syracuseStep 824089 = 618067) B618067
theorem B1872791 : Blo 385764 1872791 := bstep (se 1 (by rfl) ⟨1404593, by rfl⟩ : syracuseStep 1872791 = 2809187) B2809187
theorem B824833 : Blo 385764 824833 := bstep (se 2 (by rfl) ⟨309312, by rfl⟩ : syracuseStep 824833 = 618625) B618625
theorem B1971863 : Blo 385764 1971863 := bstep (se 1 (by rfl) ⟨1478897, by rfl⟩ : syracuseStep 1971863 = 2957795) B2957795
theorem B3741389 : Blo 385764 3741389 := bstep (se 3 (by rfl) ⟨701510, by rfl⟩ : syracuseStep 3741389 = 1403021) B1403021
theorem B464791 : Blo 385764 464791 := bstep (se 1 (by rfl) ⟨348593, by rfl⟩ : syracuseStep 464791 = 697187) B697187
theorem B8198213 : Blo 385764 8198213 := bstep (se 4 (by rfl) ⟨768582, by rfl⟩ : syracuseStep 8198213 = 1537165) B1537165
theorem B2955365 : Blo 385764 2955365 := bstep (se 4 (by rfl) ⟨277065, by rfl⟩ : syracuseStep 2955365 = 554131) B554131
theorem B825815 : Blo 385764 825815 := bstep (se 1 (by rfl) ⟨619361, by rfl⟩ : syracuseStep 825815 = 1238723) B1238723
theorem B2955851 : Blo 385764 2955851 := bstep (se 1 (by rfl) ⟨2216888, by rfl⟩ : syracuseStep 2955851 = 4433777) B4433777
theorem B793367 : Blo 385764 793367 := bstep (se 1 (by rfl) ⟨595025, by rfl⟩ : syracuseStep 793367 = 1190051) B1190051
theorem B891827 : Blo 385764 891827 := bstep (se 1 (by rfl) ⟨668870, by rfl⟩ : syracuseStep 891827 = 1337741) B1337741
theorem B826379 : Blo 385764 826379 := bstep (se 1 (by rfl) ⟨619784, by rfl⟩ : syracuseStep 826379 = 1239569) B1239569
theorem B1580249 : Blo 385764 1580249 := bstep (se 2 (by rfl) ⟨592593, by rfl⟩ : syracuseStep 1580249 = 1185187) B1185187
theorem B1580311 : Blo 385764 1580311 := bstep (se 1 (by rfl) ⟨1185233, by rfl⟩ : syracuseStep 1580311 = 2370467) B2370467
theorem B826841 : Blo 385764 826841 := bstep (se 2 (by rfl) ⟨310065, by rfl⟩ : syracuseStep 826841 = 620131) B620131
theorem B728833 : Blo 385764 728833 := bstep (se 2 (by rfl) ⟨273312, by rfl⟩ : syracuseStep 728833 = 546625) B546625
theorem B434155 : Blo 385764 434155 := bstep (se 1 (by rfl) ⟨325616, by rfl⟩ : syracuseStep 434155 = 651233) B651233
theorem B3317777 : Blo 385764 3317777 := bstep (se 2 (by rfl) ⟨1244166, by rfl⟩ : syracuseStep 3317777 = 2488333) B2488333
theorem B4464715 : Blo 385764 4464715 := bstep (se 1 (by rfl) ⟨3348536, by rfl⟩ : syracuseStep 4464715 = 6697073) B6697073
theorem B434263 : Blo 385764 434263 := bstep (se 1 (by rfl) ⟨325697, by rfl⟩ : syracuseStep 434263 = 651395) B651395
theorem B434443 : Blo 385764 434443 := bstep (se 1 (by rfl) ⟨325832, by rfl⟩ : syracuseStep 434443 = 651665) B651665
theorem B2203949 : Blo 385764 2203949 := bstep (se 3 (by rfl) ⟨413240, by rfl⟩ : syracuseStep 2203949 = 826481) B826481
theorem B434551 : Blo 385764 434551 := bstep (se 1 (by rfl) ⟨325913, by rfl⟩ : syracuseStep 434551 = 651827) B651827
theorem B434731 : Blo 385764 434731 := bstep (se 1 (by rfl) ⟨326048, by rfl⟩ : syracuseStep 434731 = 652097) B652097
theorem B1614401 : Blo 385764 1614401 := bstep (se 2 (by rfl) ⟨605400, by rfl⟩ : syracuseStep 1614401 = 1210801) B1210801
theorem B631385 : Blo 385764 631385 := bstep (se 2 (by rfl) ⟨236769, by rfl⟩ : syracuseStep 631385 = 473539) B473539
theorem B828019 : Blo 385764 828019 := bstep (se 1 (by rfl) ⟨621014, by rfl⟩ : syracuseStep 828019 = 1242029) B1242029
theorem B434839 : Blo 385764 434839 := bstep (se 1 (by rfl) ⟨326129, by rfl⟩ : syracuseStep 434839 = 652259) B652259
theorem B435019 : Blo 385764 435019 := bstep (se 1 (by rfl) ⟨326264, by rfl⟩ : syracuseStep 435019 = 652529) B652529
theorem B2106263 : Blo 385764 2106263 := bstep (se 1 (by rfl) ⟨1579697, by rfl⟩ : syracuseStep 2106263 = 3159395) B3159395
theorem B435127 : Blo 385764 435127 := bstep (se 1 (by rfl) ⟨326345, by rfl⟩ : syracuseStep 435127 = 652691) B652691
theorem B828481 : Blo 385764 828481 := bstep (se 2 (by rfl) ⟨310680, by rfl⟩ : syracuseStep 828481 = 621361) B621361
theorem B435307 : Blo 385764 435307 := bstep (se 1 (by rfl) ⟨326480, by rfl⟩ : syracuseStep 435307 = 652961) B652961
theorem B435415 : Blo 385764 435415 := bstep (se 1 (by rfl) ⟨326561, by rfl⟩ : syracuseStep 435415 = 653123) B653123
theorem B435595 : Blo 385764 435595 := bstep (se 1 (by rfl) ⟨326696, by rfl⟩ : syracuseStep 435595 = 653393) B653393
theorem B435703 : Blo 385764 435703 := bstep (se 1 (by rfl) ⟨326777, by rfl⟩ : syracuseStep 435703 = 653555) B653555
theorem B828929 : Blo 385764 828929 := bstep (se 2 (by rfl) ⟨310848, by rfl⟩ : syracuseStep 828929 = 621697) B621697
theorem B8955485 : Blo 385764 8955485 := bstep (se 3 (by rfl) ⟨1679153, by rfl⟩ : syracuseStep 8955485 = 3358307) B3358307
theorem B435883 : Blo 385764 435883 := bstep (se 1 (by rfl) ⟨326912, by rfl⟩ : syracuseStep 435883 = 653825) B653825
theorem B1058525 : Blo 385764 1058525 := bstep (se 3 (by rfl) ⟨198473, by rfl⟩ : syracuseStep 1058525 = 396947) B396947
theorem B435991 : Blo 385764 435991 := bstep (se 1 (by rfl) ⟨326993, by rfl⟩ : syracuseStep 435991 = 653987) B653987
theorem B829207 : Blo 385764 829207 := bstep (se 1 (by rfl) ⟨621905, by rfl⟩ : syracuseStep 829207 = 1243811) B1243811
theorem B436171 : Blo 385764 436171 := bstep (se 1 (by rfl) ⟨327128, by rfl⟩ : syracuseStep 436171 = 654257) B654257
theorem B436279 : Blo 385764 436279 := bstep (se 1 (by rfl) ⟨327209, by rfl⟩ : syracuseStep 436279 = 654419) B654419
theorem B436459 : Blo 385764 436459 := bstep (se 1 (by rfl) ⟨327344, by rfl⟩ : syracuseStep 436459 = 654689) B654689
theorem B764183 : Blo 385764 764183 := bstep (se 1 (by rfl) ⟨573137, by rfl⟩ : syracuseStep 764183 = 1146275) B1146275
theorem B436567 : Blo 385764 436567 := bstep (se 1 (by rfl) ⟨327425, by rfl⟩ : syracuseStep 436567 = 654851) B654851
theorem B600409 : Blo 385764 600409 := bstep (se 2 (by rfl) ⟨225153, by rfl⟩ : syracuseStep 600409 = 450307) B450307
theorem B436747 : Blo 385764 436747 := bstep (se 1 (by rfl) ⟨327560, by rfl⟩ : syracuseStep 436747 = 655121) B655121
theorem B928331 : Blo 385764 928331 := bstep (se 1 (by rfl) ⟨696248, by rfl⟩ : syracuseStep 928331 = 1392497) B1392497
theorem B830027 : Blo 385764 830027 := bstep (se 1 (by rfl) ⟨622520, by rfl⟩ : syracuseStep 830027 = 1245041) B1245041
theorem B436855 : Blo 385764 436855 := bstep (se 1 (by rfl) ⟨327641, by rfl⟩ : syracuseStep 436855 = 655283) B655283
theorem B1288921 : Blo 385764 1288921 := bstep (se 2 (by rfl) ⟨483345, by rfl⟩ : syracuseStep 1288921 = 966691) B966691
theorem B437035 : Blo 385764 437035 := bstep (se 1 (by rfl) ⟨327776, by rfl⟩ : syracuseStep 437035 = 655553) B655553
theorem B2796353 : Blo 385764 2796353 := bstep (se 2 (by rfl) ⟨1048632, by rfl⟩ : syracuseStep 2796353 = 2097265) B2097265
theorem B437143 : Blo 385764 437143 := bstep (se 1 (by rfl) ⟨327857, by rfl⟩ : syracuseStep 437143 = 655715) B655715
theorem B1485899 : Blo 385764 1485899 := bstep (se 1 (by rfl) ⟨1114424, by rfl⟩ : syracuseStep 1485899 = 2228849) B2228849
theorem B437323 : Blo 385764 437323 := bstep (se 1 (by rfl) ⟨327992, by rfl⟩ : syracuseStep 437323 = 655985) B655985
theorem B1059929 : Blo 385764 1059929 := bstep (se 2 (by rfl) ⟨397473, by rfl⟩ : syracuseStep 1059929 = 794947) B794947
theorem B437431 : Blo 385764 437431 := bstep (se 1 (by rfl) ⟨328073, by rfl⟩ : syracuseStep 437431 = 656147) B656147
theorem B3288385 : Blo 385764 3288385 := bstep (se 2 (by rfl) ⟨1233144, by rfl⟩ : syracuseStep 3288385 = 2466289) B2466289
theorem B437611 : Blo 385764 437611 := bstep (se 1 (by rfl) ⟨328208, by rfl⟩ : syracuseStep 437611 = 656417) B656417
theorem B830873 : Blo 385764 830873 := bstep (se 2 (by rfl) ⟨311577, by rfl⟩ : syracuseStep 830873 = 623155) B623155
theorem B437719 : Blo 385764 437719 := bstep (se 1 (by rfl) ⟨328289, by rfl⟩ : syracuseStep 437719 = 656579) B656579
theorem B929369 : Blo 385764 929369 := bstep (se 2 (by rfl) ⟨348513, by rfl⟩ : syracuseStep 929369 = 697027) B697027
theorem B437899 : Blo 385764 437899 := bstep (se 1 (by rfl) ⟨328424, by rfl⟩ : syracuseStep 437899 = 656849) B656849
theorem B438007 : Blo 385764 438007 := bstep (se 1 (by rfl) ⟨328505, by rfl⟩ : syracuseStep 438007 = 657011) B657011
theorem B732979 : Blo 385764 732979 := bstep (se 1 (by rfl) ⟨549734, by rfl⟩ : syracuseStep 732979 = 1099469) B1099469
theorem B438187 : Blo 385764 438187 := bstep (se 1 (by rfl) ⟨328640, by rfl⟩ : syracuseStep 438187 = 657281) B657281
theorem B733207 : Blo 385764 733207 := bstep (se 1 (by rfl) ⟨549905, by rfl⟩ : syracuseStep 733207 = 1099811) B1099811
theorem B438295 : Blo 385764 438295 := bstep (se 1 (by rfl) ⟨328721, by rfl⟩ : syracuseStep 438295 = 657443) B657443
theorem B831539 : Blo 385764 831539 := bstep (se 1 (by rfl) ⟨623654, by rfl⟩ : syracuseStep 831539 = 1247309) B1247309
theorem B733313 : Blo 385764 733313 := bstep (se 2 (by rfl) ⟨274992, by rfl⟩ : syracuseStep 733313 = 549985) B549985
theorem B438475 : Blo 385764 438475 := bstep (se 1 (by rfl) ⟨328856, by rfl⟩ : syracuseStep 438475 = 657713) B657713
theorem B700631 : Blo 385764 700631 := bstep (se 1 (by rfl) ⟨525473, by rfl⟩ : syracuseStep 700631 = 1050947) B1050947
theorem B733465 : Blo 385764 733465 := bstep (se 2 (by rfl) ⟨275049, by rfl⟩ : syracuseStep 733465 = 550099) B550099
theorem B1651117 : Blo 385764 1651117 := bstep (se 3 (by rfl) ⟨309584, by rfl⟩ : syracuseStep 1651117 = 619169) B619169
theorem B1324183 : Blo 385764 1324183 := bstep (se 1 (by rfl) ⟨993137, by rfl⟩ : syracuseStep 1324183 = 1986275) B1986275
theorem B800279 : Blo 385764 800279 := bstep (se 1 (by rfl) ⟨600209, by rfl⟩ : syracuseStep 800279 = 1200419) B1200419
theorem B734771 : Blo 385764 734771 := bstep (se 1 (by rfl) ⟨551078, by rfl⟩ : syracuseStep 734771 = 1102157) B1102157
theorem B734923 : Blo 385764 734923 := bstep (se 1 (by rfl) ⟨551192, by rfl⟩ : syracuseStep 734923 = 1102385) B1102385
theorem B2897669 : Blo 385764 2897669 := bstep (se 4 (by rfl) ⟨271656, by rfl⟩ : syracuseStep 2897669 = 543313) B543313
theorem B3323693 : Blo 385764 3323693 := bstep (se 3 (by rfl) ⟨623192, by rfl⟩ : syracuseStep 3323693 = 1246385) B1246385
theorem B2471755 : Blo 385764 2471755 := bstep (se 1 (by rfl) ⟨1853816, by rfl⟩ : syracuseStep 2471755 = 3707633) B3707633
theorem B735257 : Blo 385764 735257 := bstep (se 2 (by rfl) ⟨275721, by rfl⟩ : syracuseStep 735257 = 551443) B551443
theorem B1652825 : Blo 385764 1652825 := bstep (se 2 (by rfl) ⟨619809, by rfl⟩ : syracuseStep 1652825 = 1239619) B1239619
theorem B735895 : Blo 385764 735895 := bstep (se 1 (by rfl) ⟨551921, by rfl⟩ : syracuseStep 735895 = 1103843) B1103843
theorem B932887 : Blo 385764 932887 := bstep (se 1 (by rfl) ⟨699665, by rfl⟩ : syracuseStep 932887 = 1399331) B1399331
theorem B1654091 : Blo 385764 1654091 := bstep (se 1 (by rfl) ⟨1240568, by rfl⟩ : syracuseStep 1654091 = 2481137) B2481137
theorem B736715 : Blo 385764 736715 := bstep (se 1 (by rfl) ⟨552536, by rfl⟩ : syracuseStep 736715 = 1105073) B1105073
theorem B736769 : Blo 385764 736769 := bstep (se 2 (by rfl) ⟨276288, by rfl⟩ : syracuseStep 736769 = 552577) B552577
theorem B1490521 : Blo 385764 1490521 := bstep (se 2 (by rfl) ⟨558945, by rfl⟩ : syracuseStep 1490521 = 1117891) B1117891
theorem B2211421 : Blo 385764 2211421 := bstep (se 3 (by rfl) ⟨414641, by rfl⟩ : syracuseStep 2211421 = 829283) B829283
theorem B1654451 : Blo 385764 1654451 := bstep (se 1 (by rfl) ⟨1240838, by rfl⟩ : syracuseStep 1654451 = 2481677) B2481677
theorem B1326809 : Blo 385764 1326809 := bstep (se 2 (by rfl) ⟨497553, by rfl⟩ : syracuseStep 1326809 = 995107) B995107
theorem B868121 : Blo 385764 868121 := bstep (se 2 (by rfl) ⟨325545, by rfl⟩ : syracuseStep 868121 = 651091) B651091
theorem B868211 : Blo 385764 868211 := bstep (se 1 (by rfl) ⟨651158, by rfl⟩ : syracuseStep 868211 = 1302317) B1302317
theorem B868247 : Blo 385764 868247 := bstep (se 1 (by rfl) ⟨651185, by rfl⟩ : syracuseStep 868247 = 1302371) B1302371
theorem B868427 : Blo 385764 868427 := bstep (se 1 (by rfl) ⟨651320, by rfl⟩ : syracuseStep 868427 = 1302641) B1302641
theorem B868481 : Blo 385764 868481 := bstep (se 2 (by rfl) ⟨325680, by rfl⟩ : syracuseStep 868481 = 651361) B651361
theorem B2933009 : Blo 385764 2933009 := bstep (se 2 (by rfl) ⟨1099878, by rfl⟩ : syracuseStep 2933009 = 2199757) B2199757
theorem B442711 : Blo 385764 442711 := bstep (se 1 (by rfl) ⟨332033, by rfl⟩ : syracuseStep 442711 = 664067) B664067
theorem B868697 : Blo 385764 868697 := bstep (se 2 (by rfl) ⟨325761, by rfl⟩ : syracuseStep 868697 = 651523) B651523
theorem B7094627 : Blo 385764 7094627 := bstep (se 1 (by rfl) ⟨5320970, by rfl⟩ : syracuseStep 7094627 = 10641941) B10641941
theorem B737687 : Blo 385764 737687 := bstep (se 1 (by rfl) ⟨553265, by rfl⟩ : syracuseStep 737687 = 1106531) B1106531
theorem B868787 : Blo 385764 868787 := bstep (se 1 (by rfl) ⟨651590, by rfl⟩ : syracuseStep 868787 = 1303181) B1303181
theorem B868823 : Blo 385764 868823 := bstep (se 1 (by rfl) ⟨651617, by rfl⟩ : syracuseStep 868823 = 1303235) B1303235
theorem B869003 : Blo 385764 869003 := bstep (se 1 (by rfl) ⟨651752, by rfl⟩ : syracuseStep 869003 = 1303505) B1303505
theorem B869057 : Blo 385764 869057 := bstep (se 2 (by rfl) ⟨325896, by rfl⟩ : syracuseStep 869057 = 651793) B651793
theorem B3326669 : Blo 385764 3326669 := bstep (se 3 (by rfl) ⟨623750, by rfl⟩ : syracuseStep 3326669 = 1247501) B1247501
theorem B869273 : Blo 385764 869273 := bstep (se 2 (by rfl) ⟨325977, by rfl⟩ : syracuseStep 869273 = 651955) B651955
theorem B738227 : Blo 385764 738227 := bstep (se 1 (by rfl) ⟨553670, by rfl⟩ : syracuseStep 738227 = 1107341) B1107341
theorem B869363 : Blo 385764 869363 := bstep (se 1 (by rfl) ⟨652022, by rfl⟩ : syracuseStep 869363 = 1304045) B1304045
theorem B869399 : Blo 385764 869399 := bstep (se 1 (by rfl) ⟨652049, by rfl⟩ : syracuseStep 869399 = 1304099) B1304099
theorem B869579 : Blo 385764 869579 := bstep (se 1 (by rfl) ⟨652184, by rfl⟩ : syracuseStep 869579 = 1304369) B1304369
theorem B869633 : Blo 385764 869633 := bstep (se 2 (by rfl) ⟨326112, by rfl⟩ : syracuseStep 869633 = 652225) B652225
theorem B738713 : Blo 385764 738713 := bstep (se 2 (by rfl) ⟨277017, by rfl⟩ : syracuseStep 738713 = 554035) B554035
theorem B869849 : Blo 385764 869849 := bstep (se 2 (by rfl) ⟨326193, by rfl⟩ : syracuseStep 869849 = 652387) B652387
theorem B706099 : Blo 385764 706099 := bstep (se 1 (by rfl) ⟨529574, by rfl⟩ : syracuseStep 706099 = 1059149) B1059149
theorem B869939 : Blo 385764 869939 := bstep (se 1 (by rfl) ⟨652454, by rfl⟩ : syracuseStep 869939 = 1304909) B1304909
theorem B869975 : Blo 385764 869975 := bstep (se 1 (by rfl) ⟨652481, by rfl⟩ : syracuseStep 869975 = 1304963) B1304963
theorem B706187 : Blo 385764 706187 := bstep (se 1 (by rfl) ⟨529640, by rfl⟩ : syracuseStep 706187 = 1059281) B1059281
theorem B1328791 : Blo 385764 1328791 := bstep (se 1 (by rfl) ⟨996593, by rfl⟩ : syracuseStep 1328791 = 1993187) B1993187
theorem B1492673 : Blo 385764 1492673 := bstep (se 2 (by rfl) ⟨559752, by rfl⟩ : syracuseStep 1492673 = 1119505) B1119505
theorem B870155 : Blo 385764 870155 := bstep (se 1 (by rfl) ⟨652616, by rfl⟩ : syracuseStep 870155 = 1305233) B1305233
theorem B870209 : Blo 385764 870209 := bstep (se 2 (by rfl) ⟨326328, by rfl⟩ : syracuseStep 870209 = 652657) B652657
theorem B1099595 : Blo 385764 1099595 := bstep (se 1 (by rfl) ⟨824696, by rfl⟩ : syracuseStep 1099595 = 1649393) B1649393
theorem B7489381 : Blo 385764 7489381 := bstep (se 4 (by rfl) ⟨702129, by rfl⟩ : syracuseStep 7489381 = 1404259) B1404259
theorem B1722391 : Blo 385764 1722391 := bstep (se 1 (by rfl) ⟨1291793, by rfl⟩ : syracuseStep 1722391 = 2583587) B2583587
theorem B870425 : Blo 385764 870425 := bstep (se 2 (by rfl) ⟨326409, by rfl⟩ : syracuseStep 870425 = 652819) B652819
theorem B2508893 : Blo 385764 2508893 := bstep (se 3 (by rfl) ⟨470417, by rfl⟩ : syracuseStep 2508893 = 940835) B940835
theorem B870515 : Blo 385764 870515 := bstep (se 1 (by rfl) ⟨652886, by rfl⟩ : syracuseStep 870515 = 1305773) B1305773
theorem B2476163 : Blo 385764 2476163 := bstep (se 1 (by rfl) ⟨1857122, by rfl⟩ : syracuseStep 2476163 = 3714245) B3714245
theorem B870551 : Blo 385764 870551 := bstep (se 1 (by rfl) ⟨652913, by rfl⟩ : syracuseStep 870551 = 1305827) B1305827
theorem B1099993 : Blo 385764 1099993 := bstep (se 2 (by rfl) ⟨412497, by rfl⟩ : syracuseStep 1099993 = 824995) B824995
theorem B870731 : Blo 385764 870731 := bstep (se 1 (by rfl) ⟨653048, by rfl⟩ : syracuseStep 870731 = 1306097) B1306097
theorem B870785 : Blo 385764 870785 := bstep (se 2 (by rfl) ⟨326544, by rfl⟩ : syracuseStep 870785 = 653089) B653089
theorem B412075 : Blo 385764 412075 := bstep (se 1 (by rfl) ⟨309056, by rfl⟩ : syracuseStep 412075 = 618113) B618113
theorem B707033 : Blo 385764 707033 := bstep (se 2 (by rfl) ⟨265137, by rfl⟩ : syracuseStep 707033 = 530275) B530275
theorem B1395265 : Blo 385764 1395265 := bstep (se 2 (by rfl) ⟨523224, by rfl⟩ : syracuseStep 1395265 = 1046449) B1046449
theorem B871001 : Blo 385764 871001 := bstep (se 2 (by rfl) ⟨326625, by rfl⟩ : syracuseStep 871001 = 653251) B653251
theorem B871091 : Blo 385764 871091 := bstep (se 1 (by rfl) ⟨653318, by rfl⟩ : syracuseStep 871091 = 1306637) B1306637
theorem B871127 : Blo 385764 871127 := bstep (se 1 (by rfl) ⟨653345, by rfl⟩ : syracuseStep 871127 = 1306691) B1306691
theorem B904051 : Blo 385764 904051 := bstep (se 1 (by rfl) ⟨678038, by rfl⟩ : syracuseStep 904051 = 1356077) B1356077
theorem B871307 : Blo 385764 871307 := bstep (se 1 (by rfl) ⟨653480, by rfl⟩ : syracuseStep 871307 = 1306961) B1306961
theorem B871361 : Blo 385764 871361 := bstep (se 2 (by rfl) ⟨326760, by rfl⟩ : syracuseStep 871361 = 653521) B653521
theorem B871577 : Blo 385764 871577 := bstep (se 2 (by rfl) ⟨326841, by rfl⟩ : syracuseStep 871577 = 653683) B653683
theorem B871667 : Blo 385764 871667 := bstep (se 1 (by rfl) ⟨653750, by rfl⟩ : syracuseStep 871667 = 1307501) B1307501
theorem B871703 : Blo 385764 871703 := bstep (se 1 (by rfl) ⟨653777, by rfl⟩ : syracuseStep 871703 = 1307555) B1307555
theorem B707969 : Blo 385764 707969 := bstep (se 2 (by rfl) ⟨265488, by rfl⟩ : syracuseStep 707969 = 530977) B530977
theorem B1101235 : Blo 385764 1101235 := bstep (se 1 (by rfl) ⟨825926, by rfl⟩ : syracuseStep 1101235 = 1651853) B1651853
theorem B871883 : Blo 385764 871883 := bstep (se 1 (by rfl) ⟨653912, by rfl⟩ : syracuseStep 871883 = 1307825) B1307825
theorem B871937 : Blo 385764 871937 := bstep (se 2 (by rfl) ⟨326976, by rfl⟩ : syracuseStep 871937 = 653953) B653953
theorem B872153 : Blo 385764 872153 := bstep (se 2 (by rfl) ⟨327057, by rfl⟩ : syracuseStep 872153 = 654115) B654115
theorem B872243 : Blo 385764 872243 := bstep (se 1 (by rfl) ⟨654182, by rfl⟩ : syracuseStep 872243 = 1308365) B1308365
theorem B872279 : Blo 385764 872279 := bstep (se 1 (by rfl) ⟨654209, by rfl⟩ : syracuseStep 872279 = 1308419) B1308419
theorem B413591 : Blo 385764 413591 := bstep (se 1 (by rfl) ⟨310193, by rfl⟩ : syracuseStep 413591 = 620387) B620387
theorem B872459 : Blo 385764 872459 := bstep (se 1 (by rfl) ⟨654344, by rfl⟩ : syracuseStep 872459 = 1308689) B1308689
theorem B13455395 : Blo 385764 13455395 := bstep (se 1 (by rfl) ⟨10091546, by rfl⟩ : syracuseStep 13455395 = 20183093) B20183093
theorem B1134643 : Blo 385764 1134643 := bstep (se 1 (by rfl) ⟨850982, by rfl⟩ : syracuseStep 1134643 = 1701965) B1701965
theorem B2936897 : Blo 385764 2936897 := bstep (se 2 (by rfl) ⟨1101336, by rfl⟩ : syracuseStep 2936897 = 2202673) B2202673
theorem B872513 : Blo 385764 872513 := bstep (se 2 (by rfl) ⟨327192, by rfl⟩ : syracuseStep 872513 = 654385) B654385
theorem B872729 : Blo 385764 872729 := bstep (se 2 (by rfl) ⟨327273, by rfl⟩ : syracuseStep 872729 = 654547) B654547
theorem B1495385 : Blo 385764 1495385 := bstep (se 2 (by rfl) ⟨560769, by rfl⟩ : syracuseStep 1495385 = 1121539) B1121539
theorem B872819 : Blo 385764 872819 := bstep (se 1 (by rfl) ⟨654614, by rfl⟩ : syracuseStep 872819 = 1309229) B1309229
theorem B872855 : Blo 385764 872855 := bstep (se 1 (by rfl) ⟨654641, by rfl⟩ : syracuseStep 872855 = 1309283) B1309283
theorem B1397213 : Blo 385764 1397213 := bstep (se 3 (by rfl) ⟨261977, by rfl⟩ : syracuseStep 1397213 = 523955) B523955
theorem B414283 : Blo 385764 414283 := bstep (se 1 (by rfl) ⟨310712, by rfl⟩ : syracuseStep 414283 = 621425) B621425
theorem B873035 : Blo 385764 873035 := bstep (se 1 (by rfl) ⟨654776, by rfl⟩ : syracuseStep 873035 = 1309553) B1309553
theorem B873089 : Blo 385764 873089 := bstep (se 2 (by rfl) ⟨327408, by rfl⟩ : syracuseStep 873089 = 654817) B654817
theorem B1659523 : Blo 385764 1659523 := bstep (se 1 (by rfl) ⟨1244642, by rfl⟩ : syracuseStep 1659523 = 2489285) B2489285
theorem B2347699 : Blo 385764 2347699 := bstep (se 1 (by rfl) ⟨1760774, by rfl⟩ : syracuseStep 2347699 = 3521549) B3521549
theorem B840385 : Blo 385764 840385 := bstep (se 2 (by rfl) ⟨315144, by rfl⟩ : syracuseStep 840385 = 630289) B630289
theorem B1200961 : Blo 385764 1200961 := bstep (se 2 (by rfl) ⟨450360, by rfl⟩ : syracuseStep 1200961 = 900721) B900721
theorem B873305 : Blo 385764 873305 := bstep (se 2 (by rfl) ⟨327489, by rfl⟩ : syracuseStep 873305 = 654979) B654979
theorem B1954691 : Blo 385764 1954691 := bstep (se 1 (by rfl) ⟨1466018, by rfl⟩ : syracuseStep 1954691 = 2932037) B2932037
theorem B873395 : Blo 385764 873395 := bstep (se 1 (by rfl) ⟨655046, by rfl⟩ : syracuseStep 873395 = 1310093) B1310093
theorem B873431 : Blo 385764 873431 := bstep (se 1 (by rfl) ⟨655073, by rfl⟩ : syracuseStep 873431 = 1310147) B1310147
theorem B1659865 : Blo 385764 1659865 := bstep (se 2 (by rfl) ⟨622449, by rfl⟩ : syracuseStep 1659865 = 1244899) B1244899
theorem B578699 : Blo 385764 578699 := bstep (se 1 (by rfl) ⟨434024, by rfl⟩ : syracuseStep 578699 = 868049) B868049
theorem B873611 : Blo 385764 873611 := bstep (se 1 (by rfl) ⟨655208, by rfl⟩ : syracuseStep 873611 = 1310417) B1310417
theorem B578711 : Blo 385764 578711 := bstep (se 1 (by rfl) ⟨434033, by rfl⟩ : syracuseStep 578711 = 868067) B868067
theorem B873665 : Blo 385764 873665 := bstep (se 2 (by rfl) ⟨327624, by rfl⟩ : syracuseStep 873665 = 655249) B655249
theorem B578777 : Blo 385764 578777 := bstep (se 2 (by rfl) ⟨217041, by rfl⟩ : syracuseStep 578777 = 434083) B434083
theorem B578891 : Blo 385764 578891 := bstep (se 1 (by rfl) ⟨434168, by rfl⟩ : syracuseStep 578891 = 868337) B868337
theorem B578903 : Blo 385764 578903 := bstep (se 1 (by rfl) ⟨434177, by rfl⟩ : syracuseStep 578903 = 868355) B868355
theorem B578969 : Blo 385764 578969 := bstep (se 2 (by rfl) ⟨217113, by rfl⟩ : syracuseStep 578969 = 434227) B434227
theorem B873881 : Blo 385764 873881 := bstep (se 2 (by rfl) ⟨327705, by rfl⟩ : syracuseStep 873881 = 655411) B655411
theorem B873971 : Blo 385764 873971 := bstep (se 1 (by rfl) ⟨655478, by rfl⟩ : syracuseStep 873971 = 1310957) B1310957
theorem B579083 : Blo 385764 579083 := bstep (se 1 (by rfl) ⟨434312, by rfl⟩ : syracuseStep 579083 = 868625) B868625
theorem B579095 : Blo 385764 579095 := bstep (se 1 (by rfl) ⟨434321, by rfl⟩ : syracuseStep 579095 = 868643) B868643
theorem B874007 : Blo 385764 874007 := bstep (se 1 (by rfl) ⟨655505, by rfl⟩ : syracuseStep 874007 = 1311011) B1311011
theorem B579161 : Blo 385764 579161 := bstep (se 2 (by rfl) ⟨217185, by rfl⟩ : syracuseStep 579161 = 434371) B434371
theorem B1594973 : Blo 385764 1594973 := bstep (se 3 (by rfl) ⟨299057, by rfl⟩ : syracuseStep 1594973 = 598115) B598115
theorem B579275 : Blo 385764 579275 := bstep (se 1 (by rfl) ⟨434456, by rfl⟩ : syracuseStep 579275 = 868913) B868913
theorem B874187 : Blo 385764 874187 := bstep (se 1 (by rfl) ⟨655640, by rfl⟩ : syracuseStep 874187 = 1311281) B1311281
theorem B579287 : Blo 385764 579287 := bstep (se 1 (by rfl) ⟨434465, by rfl⟩ : syracuseStep 579287 = 868931) B868931
theorem B1398493 : Blo 385764 1398493 := bstep (se 3 (by rfl) ⟨262217, by rfl⟩ : syracuseStep 1398493 = 524435) B524435
theorem B874241 : Blo 385764 874241 := bstep (se 2 (by rfl) ⟨327840, by rfl⟩ : syracuseStep 874241 = 655681) B655681
theorem B3299089 : Blo 385764 3299089 := bstep (se 2 (by rfl) ⟨1237158, by rfl⟩ : syracuseStep 3299089 = 2474317) B2474317
theorem B579353 : Blo 385764 579353 := bstep (se 2 (by rfl) ⟨217257, by rfl⟩ : syracuseStep 579353 = 434515) B434515
theorem B579467 : Blo 385764 579467 := bstep (se 1 (by rfl) ⟨434600, by rfl⟩ : syracuseStep 579467 = 869201) B869201
theorem B579479 : Blo 385764 579479 := bstep (se 1 (by rfl) ⟨434609, by rfl⟩ : syracuseStep 579479 = 869219) B869219
theorem B1857431 : Blo 385764 1857431 := bstep (se 1 (by rfl) ⟨1393073, by rfl⟩ : syracuseStep 1857431 = 2786147) B2786147
theorem B1660823 : Blo 385764 1660823 := bstep (se 1 (by rfl) ⟨1245617, by rfl⟩ : syracuseStep 1660823 = 2491235) B2491235
theorem B579545 : Blo 385764 579545 := bstep (se 2 (by rfl) ⟨217329, by rfl⟩ : syracuseStep 579545 = 434659) B434659
theorem B2938841 : Blo 385764 2938841 := bstep (se 2 (by rfl) ⟨1102065, by rfl⟩ : syracuseStep 2938841 = 2204131) B2204131
theorem B5593049 : Blo 385764 5593049 := bstep (se 2 (by rfl) ⟨2097393, by rfl⟩ : syracuseStep 5593049 = 4194787) B4194787
theorem B874457 : Blo 385764 874457 := bstep (se 2 (by rfl) ⟨327921, by rfl⟩ : syracuseStep 874457 = 655843) B655843
theorem B415735 : Blo 385764 415735 := bstep (se 1 (by rfl) ⟨311801, by rfl⟩ : syracuseStep 415735 = 623603) B623603
theorem B3299363 : Blo 385764 3299363 := bstep (se 1 (by rfl) ⟨2474522, by rfl⟩ : syracuseStep 3299363 = 4949045) B4949045
theorem B874547 : Blo 385764 874547 := bstep (se 1 (by rfl) ⟨655910, by rfl⟩ : syracuseStep 874547 = 1311821) B1311821
theorem B579659 : Blo 385764 579659 := bstep (se 1 (by rfl) ⟨434744, by rfl⟩ : syracuseStep 579659 = 869489) B869489
theorem B5036107 : Blo 385764 5036107 := bstep (se 1 (by rfl) ⟨3777080, by rfl⟩ : syracuseStep 5036107 = 7554161) B7554161
theorem B579671 : Blo 385764 579671 := bstep (se 1 (by rfl) ⟨434753, by rfl⟩ : syracuseStep 579671 = 869507) B869507
theorem B874583 : Blo 385764 874583 := bstep (se 1 (by rfl) ⟨655937, by rfl⟩ : syracuseStep 874583 = 1311875) B1311875
theorem B579737 : Blo 385764 579737 := bstep (se 2 (by rfl) ⟨217401, by rfl⟩ : syracuseStep 579737 = 434803) B434803
theorem B579851 : Blo 385764 579851 := bstep (se 1 (by rfl) ⟨434888, by rfl⟩ : syracuseStep 579851 = 869777) B869777
theorem B874763 : Blo 385764 874763 := bstep (se 1 (by rfl) ⟨656072, by rfl⟩ : syracuseStep 874763 = 1312145) B1312145
theorem B579863 : Blo 385764 579863 := bstep (se 1 (by rfl) ⟨434897, by rfl⟩ : syracuseStep 579863 = 869795) B869795
theorem B1104151 : Blo 385764 1104151 := bstep (se 1 (by rfl) ⟨828113, by rfl⟩ : syracuseStep 1104151 = 1656227) B1656227
theorem B874817 : Blo 385764 874817 := bstep (se 2 (by rfl) ⟨328056, by rfl⟩ : syracuseStep 874817 = 656113) B656113
theorem B842071 : Blo 385764 842071 := bstep (se 1 (by rfl) ⟨631553, by rfl⟩ : syracuseStep 842071 = 1263107) B1263107
theorem B579929 : Blo 385764 579929 := bstep (se 2 (by rfl) ⟨217473, by rfl⟩ : syracuseStep 579929 = 434947) B434947
theorem B416107 : Blo 385764 416107 := bstep (se 1 (by rfl) ⟨312080, by rfl⟩ : syracuseStep 416107 = 624161) B624161
theorem B580043 : Blo 385764 580043 := bstep (se 1 (by rfl) ⟨435032, by rfl⟩ : syracuseStep 580043 = 870065) B870065
theorem B580055 : Blo 385764 580055 := bstep (se 1 (by rfl) ⟨435041, by rfl⟩ : syracuseStep 580055 = 870083) B870083
theorem B580121 : Blo 385764 580121 := bstep (se 2 (by rfl) ⟨217545, by rfl⟩ : syracuseStep 580121 = 435091) B435091
theorem B875033 : Blo 385764 875033 := bstep (se 2 (by rfl) ⟨328137, by rfl⟩ : syracuseStep 875033 = 656275) B656275
theorem B1464925 : Blo 385764 1464925 := bstep (se 3 (by rfl) ⟨274673, by rfl⟩ : syracuseStep 1464925 = 549347) B549347
theorem B875123 : Blo 385764 875123 := bstep (se 1 (by rfl) ⟨656342, by rfl⟩ : syracuseStep 875123 = 1312685) B1312685
theorem B580235 : Blo 385764 580235 := bstep (se 1 (by rfl) ⟨435176, by rfl⟩ : syracuseStep 580235 = 870353) B870353
theorem B580247 : Blo 385764 580247 := bstep (se 1 (by rfl) ⟨435185, by rfl⟩ : syracuseStep 580247 = 870371) B870371
theorem B875159 : Blo 385764 875159 := bstep (se 1 (by rfl) ⟨656369, by rfl⟩ : syracuseStep 875159 = 1312739) B1312739
theorem B580313 : Blo 385764 580313 := bstep (se 2 (by rfl) ⟨217617, by rfl⟩ : syracuseStep 580313 = 435235) B435235
theorem B580427 : Blo 385764 580427 := bstep (se 1 (by rfl) ⟨435320, by rfl⟩ : syracuseStep 580427 = 870641) B870641
theorem B875339 : Blo 385764 875339 := bstep (se 1 (by rfl) ⟨656504, by rfl⟩ : syracuseStep 875339 = 1313009) B1313009
theorem B580439 : Blo 385764 580439 := bstep (se 1 (by rfl) ⟨435329, by rfl⟩ : syracuseStep 580439 = 870659) B870659
theorem B875393 : Blo 385764 875393 := bstep (se 2 (by rfl) ⟨328272, by rfl⟩ : syracuseStep 875393 = 656545) B656545
theorem B580505 : Blo 385764 580505 := bstep (se 2 (by rfl) ⟨217689, by rfl⟩ : syracuseStep 580505 = 435379) B435379
theorem B580619 : Blo 385764 580619 := bstep (se 1 (by rfl) ⟨435464, by rfl⟩ : syracuseStep 580619 = 870929) B870929
theorem B580631 : Blo 385764 580631 := bstep (se 1 (by rfl) ⟨435473, by rfl⟩ : syracuseStep 580631 = 870947) B870947
theorem B3529793 : Blo 385764 3529793 := bstep (se 2 (by rfl) ⟨1323672, by rfl⟩ : syracuseStep 3529793 = 2647345) B2647345
theorem B580697 : Blo 385764 580697 := bstep (se 2 (by rfl) ⟨217761, by rfl⟩ : syracuseStep 580697 = 435523) B435523
theorem B875609 : Blo 385764 875609 := bstep (se 2 (by rfl) ⟨328353, by rfl⟩ : syracuseStep 875609 = 656707) B656707
theorem B875699 : Blo 385764 875699 := bstep (se 1 (by rfl) ⟨656774, by rfl⟩ : syracuseStep 875699 = 1313549) B1313549
theorem B1236161 : Blo 385764 1236161 := bstep (se 2 (by rfl) ⟨463560, by rfl⟩ : syracuseStep 1236161 = 927121) B927121
theorem B580811 : Blo 385764 580811 := bstep (se 1 (by rfl) ⟨435608, by rfl⟩ : syracuseStep 580811 = 871217) B871217
theorem B580823 : Blo 385764 580823 := bstep (se 1 (by rfl) ⟨435617, by rfl⟩ : syracuseStep 580823 = 871235) B871235
theorem B875735 : Blo 385764 875735 := bstep (se 1 (by rfl) ⟨656801, by rfl⟩ : syracuseStep 875735 = 1313603) B1313603
theorem B580889 : Blo 385764 580889 := bstep (se 2 (by rfl) ⟨217833, by rfl⟩ : syracuseStep 580889 = 435667) B435667
theorem B581003 : Blo 385764 581003 := bstep (se 1 (by rfl) ⟨435752, by rfl⟩ : syracuseStep 581003 = 871505) B871505
theorem B875915 : Blo 385764 875915 := bstep (se 1 (by rfl) ⟨656936, by rfl⟩ : syracuseStep 875915 = 1313873) B1313873
theorem B581015 : Blo 385764 581015 := bstep (se 1 (by rfl) ⟨435761, by rfl⟩ : syracuseStep 581015 = 871523) B871523
theorem B875969 : Blo 385764 875969 := bstep (se 2 (by rfl) ⟨328488, by rfl⟩ : syracuseStep 875969 = 656977) B656977
theorem B581081 : Blo 385764 581081 := bstep (se 2 (by rfl) ⟨217905, by rfl⟩ : syracuseStep 581081 = 435811) B435811
theorem B1564211 : Blo 385764 1564211 := bstep (se 1 (by rfl) ⟨1173158, by rfl⟩ : syracuseStep 1564211 = 2346317) B2346317
theorem B1662515 : Blo 385764 1662515 := bstep (se 1 (by rfl) ⟨1246886, by rfl⟩ : syracuseStep 1662515 = 2493773) B2493773
theorem B581195 : Blo 385764 581195 := bstep (se 1 (by rfl) ⟨435896, by rfl⟩ : syracuseStep 581195 = 871793) B871793
theorem B1105483 : Blo 385764 1105483 := bstep (se 1 (by rfl) ⟨829112, by rfl⟩ : syracuseStep 1105483 = 1658225) B1658225
theorem B581207 : Blo 385764 581207 := bstep (se 1 (by rfl) ⟨435905, by rfl⟩ : syracuseStep 581207 = 871811) B871811
theorem B581273 : Blo 385764 581273 := bstep (se 2 (by rfl) ⟨217977, by rfl⟩ : syracuseStep 581273 = 435955) B435955
theorem B876185 : Blo 385764 876185 := bstep (se 2 (by rfl) ⟨328569, by rfl⟩ : syracuseStep 876185 = 657139) B657139
theorem B1302209 : Blo 385764 1302209 := bstep (se 2 (by rfl) ⟨488328, by rfl⟩ : syracuseStep 1302209 = 976657) B976657
theorem B409001669 : Blo 385764 409001669 := bstep (se 4 (by rfl) ⟨38343906, by rfl⟩ : syracuseStep 409001669 = 76687813) B76687813
theorem B876275 : Blo 385764 876275 := bstep (se 1 (by rfl) ⟨657206, by rfl⟩ : syracuseStep 876275 = 1314413) B1314413
theorem B581387 : Blo 385764 581387 := bstep (se 1 (by rfl) ⟨436040, by rfl⟩ : syracuseStep 581387 = 872081) B872081
theorem B581399 : Blo 385764 581399 := bstep (se 1 (by rfl) ⟨436049, by rfl⟩ : syracuseStep 581399 = 872099) B872099
theorem B876311 : Blo 385764 876311 := bstep (se 1 (by rfl) ⟨657233, by rfl⟩ : syracuseStep 876311 = 1314467) B1314467
theorem B1466201 : Blo 385764 1466201 := bstep (se 2 (by rfl) ⟨549825, by rfl⟩ : syracuseStep 1466201 = 1099651) B1099651
theorem B581465 : Blo 385764 581465 := bstep (se 2 (by rfl) ⟨218049, by rfl⟩ : syracuseStep 581465 = 436099) B436099
theorem B1105757 : Blo 385764 1105757 := bstep (se 3 (by rfl) ⟨207329, by rfl⟩ : syracuseStep 1105757 = 414659) B414659
theorem B941975 : Blo 385764 941975 := bstep (se 1 (by rfl) ⟨706481, by rfl⟩ : syracuseStep 941975 = 1412963) B1412963
theorem B581579 : Blo 385764 581579 := bstep (se 1 (by rfl) ⟨436184, by rfl⟩ : syracuseStep 581579 = 872369) B872369
theorem B876491 : Blo 385764 876491 := bstep (se 1 (by rfl) ⟨657368, by rfl⟩ : syracuseStep 876491 = 1314737) B1314737
theorem B581591 : Blo 385764 581591 := bstep (se 1 (by rfl) ⟨436193, by rfl⟩ : syracuseStep 581591 = 872387) B872387
theorem B1368029 : Blo 385764 1368029 := bstep (se 3 (by rfl) ⟨256505, by rfl⟩ : syracuseStep 1368029 = 513011) B513011
theorem B876545 : Blo 385764 876545 := bstep (se 2 (by rfl) ⟨328704, by rfl⟩ : syracuseStep 876545 = 657409) B657409
theorem B581657 : Blo 385764 581657 := bstep (se 2 (by rfl) ⟨218121, by rfl⟩ : syracuseStep 581657 = 436243) B436243
theorem B2089091 : Blo 385764 2089091 := bstep (se 1 (by rfl) ⟨1566818, by rfl⟩ : syracuseStep 2089091 = 3133637) B3133637
theorem B581771 : Blo 385764 581771 := bstep (se 1 (by rfl) ⟨436328, by rfl⟩ : syracuseStep 581771 = 872657) B872657
theorem B581783 : Blo 385764 581783 := bstep (se 1 (by rfl) ⟨436337, by rfl⟩ : syracuseStep 581783 = 872675) B872675
theorem B1106099 : Blo 385764 1106099 := bstep (se 1 (by rfl) ⟨829574, by rfl⟩ : syracuseStep 1106099 = 1659149) B1659149
theorem B581849 : Blo 385764 581849 := bstep (se 2 (by rfl) ⟨218193, by rfl⟩ : syracuseStep 581849 = 436387) B436387
theorem B876761 : Blo 385764 876761 := bstep (se 2 (by rfl) ⟨328785, by rfl⟩ : syracuseStep 876761 = 657571) B657571
theorem B1302749 : Blo 385764 1302749 := bstep (se 3 (by rfl) ⟨244265, by rfl⟩ : syracuseStep 1302749 = 488531) B488531
theorem B1401133 : Blo 385764 1401133 := bstep (se 3 (by rfl) ⟨262712, by rfl⟩ : syracuseStep 1401133 = 525425) B525425
theorem B876851 : Blo 385764 876851 := bstep (se 1 (by rfl) ⟨657638, by rfl⟩ : syracuseStep 876851 = 1315277) B1315277
theorem B581963 : Blo 385764 581963 := bstep (se 1 (by rfl) ⟨436472, by rfl⟩ : syracuseStep 581963 = 872945) B872945
theorem B581975 : Blo 385764 581975 := bstep (se 1 (by rfl) ⟨436481, by rfl⟩ : syracuseStep 581975 = 872963) B872963
theorem B876887 : Blo 385764 876887 := bstep (se 1 (by rfl) ⟨657665, by rfl⟩ : syracuseStep 876887 = 1315331) B1315331
theorem B582041 : Blo 385764 582041 := bstep (se 2 (by rfl) ⟨218265, by rfl⟩ : syracuseStep 582041 = 436531) B436531
theorem B418231 : Blo 385764 418231 := bstep (se 1 (by rfl) ⟨313673, by rfl⟩ : syracuseStep 418231 = 627347) B627347
theorem B582155 : Blo 385764 582155 := bstep (se 1 (by rfl) ⟨436616, by rfl⟩ : syracuseStep 582155 = 873233) B873233
theorem B1958417 : Blo 385764 1958417 := bstep (se 2 (by rfl) ⟨734406, by rfl⟩ : syracuseStep 1958417 = 1468813) B1468813
theorem B582167 : Blo 385764 582167 := bstep (se 1 (by rfl) ⟨436625, by rfl⟩ : syracuseStep 582167 = 873251) B873251
theorem B582233 : Blo 385764 582233 := bstep (se 2 (by rfl) ⟨218337, by rfl⟩ : syracuseStep 582233 = 436675) B436675
theorem B1958579 : Blo 385764 1958579 := bstep (se 1 (by rfl) ⟨1468934, by rfl⟩ : syracuseStep 1958579 = 2937869) B2937869
theorem B582347 : Blo 385764 582347 := bstep (se 1 (by rfl) ⟨436760, by rfl⟩ : syracuseStep 582347 = 873521) B873521
theorem B4186829 : Blo 385764 4186829 := bstep (se 3 (by rfl) ⟨785030, by rfl⟩ : syracuseStep 4186829 = 1570061) B1570061
theorem B582359 : Blo 385764 582359 := bstep (se 1 (by rfl) ⟨436769, by rfl⟩ : syracuseStep 582359 = 873539) B873539
theorem B385771 : Blo 385764 385771 := bstep (se 1 (by rfl) ⟨289328, by rfl⟩ : syracuseStep 385771 = 578657) B578657
theorem B385783 : Blo 385764 385783 := bstep (se 1 (by rfl) ⟨289337, by rfl⟩ : syracuseStep 385783 = 578675) B578675
theorem B385803 : Blo 385764 385803 := bstep (se 1 (by rfl) ⟨289352, by rfl⟩ : syracuseStep 385803 = 578705) B578705
theorem B385815 : Blo 385764 385815 := bstep (se 1 (by rfl) ⟨289361, by rfl⟩ : syracuseStep 385815 = 578723) B578723
theorem B582425 : Blo 385764 582425 := bstep (se 2 (by rfl) ⟨218409, by rfl⟩ : syracuseStep 582425 = 436819) B436819
theorem B385835 : Blo 385764 385835 := bstep (se 1 (by rfl) ⟨289376, by rfl⟩ : syracuseStep 385835 = 578753) B578753
theorem B5563181 : Blo 385764 5563181 := bstep (se 3 (by rfl) ⟨1043096, by rfl⟩ : syracuseStep 5563181 = 2086193) B2086193
theorem B385847 : Blo 385764 385847 := bstep (se 1 (by rfl) ⟨289385, by rfl⟩ : syracuseStep 385847 = 578771) B578771
theorem B385867 : Blo 385764 385867 := bstep (se 1 (by rfl) ⟨289400, by rfl⟩ : syracuseStep 385867 = 578801) B578801
theorem B385879 : Blo 385764 385879 := bstep (se 1 (by rfl) ⟨289409, by rfl⟩ : syracuseStep 385879 = 578819) B578819
theorem B385899 : Blo 385764 385899 := bstep (se 1 (by rfl) ⟨289424, by rfl⟩ : syracuseStep 385899 = 578849) B578849
theorem B385911 : Blo 385764 385911 := bstep (se 1 (by rfl) ⟨289433, by rfl⟩ : syracuseStep 385911 = 578867) B578867
theorem B385931 : Blo 385764 385931 := bstep (se 1 (by rfl) ⟨289448, by rfl⟩ : syracuseStep 385931 = 578897) B578897
theorem B582539 : Blo 385764 582539 := bstep (se 1 (by rfl) ⟨436904, by rfl⟩ : syracuseStep 582539 = 873809) B873809
theorem B385943 : Blo 385764 385943 := bstep (se 1 (by rfl) ⟨289457, by rfl⟩ : syracuseStep 385943 = 578915) B578915
theorem B582551 : Blo 385764 582551 := bstep (se 1 (by rfl) ⟨436913, by rfl⟩ : syracuseStep 582551 = 873827) B873827
theorem B385963 : Blo 385764 385963 := bstep (se 1 (by rfl) ⟨289472, by rfl⟩ : syracuseStep 385963 = 578945) B578945
theorem B385975 : Blo 385764 385975 := bstep (se 1 (by rfl) ⟨289481, by rfl⟩ : syracuseStep 385975 = 578963) B578963
theorem B385995 : Blo 385764 385995 := bstep (se 1 (by rfl) ⟨289496, by rfl⟩ : syracuseStep 385995 = 578993) B578993
theorem B386007 : Blo 385764 386007 := bstep (se 1 (by rfl) ⟨289505, by rfl⟩ : syracuseStep 386007 = 579011) B579011
theorem B582617 : Blo 385764 582617 := bstep (se 2 (by rfl) ⟨218481, by rfl⟩ : syracuseStep 582617 = 436963) B436963
theorem B386027 : Blo 385764 386027 := bstep (se 1 (by rfl) ⟨289520, by rfl⟩ : syracuseStep 386027 = 579041) B579041
theorem B386039 : Blo 385764 386039 := bstep (se 1 (by rfl) ⟨289529, by rfl⟩ : syracuseStep 386039 = 579059) B579059
theorem B386059 : Blo 385764 386059 := bstep (se 1 (by rfl) ⟨289544, by rfl⟩ : syracuseStep 386059 = 579089) B579089
theorem B386071 : Blo 385764 386071 := bstep (se 1 (by rfl) ⟨289553, by rfl⟩ : syracuseStep 386071 = 579107) B579107
theorem B386091 : Blo 385764 386091 := bstep (se 1 (by rfl) ⟨289568, by rfl⟩ : syracuseStep 386091 = 579137) B579137
theorem B386103 : Blo 385764 386103 := bstep (se 1 (by rfl) ⟨289577, by rfl⟩ : syracuseStep 386103 = 579155) B579155
theorem B386123 : Blo 385764 386123 := bstep (se 1 (by rfl) ⟨289592, by rfl⟩ : syracuseStep 386123 = 579185) B579185
theorem B582731 : Blo 385764 582731 := bstep (se 1 (by rfl) ⟨437048, by rfl⟩ : syracuseStep 582731 = 874097) B874097
theorem B386135 : Blo 385764 386135 := bstep (se 1 (by rfl) ⟨289601, by rfl⟩ : syracuseStep 386135 = 579203) B579203
theorem B582743 : Blo 385764 582743 := bstep (se 1 (by rfl) ⟨437057, by rfl⟩ : syracuseStep 582743 = 874115) B874115
theorem B386155 : Blo 385764 386155 := bstep (se 1 (by rfl) ⟨289616, by rfl⟩ : syracuseStep 386155 = 579233) B579233
theorem B386167 : Blo 385764 386167 := bstep (se 1 (by rfl) ⟨289625, by rfl⟩ : syracuseStep 386167 = 579251) B579251
theorem B386187 : Blo 385764 386187 := bstep (se 1 (by rfl) ⟨289640, by rfl⟩ : syracuseStep 386187 = 579281) B579281
theorem B386199 : Blo 385764 386199 := bstep (se 1 (by rfl) ⟨289649, by rfl⟩ : syracuseStep 386199 = 579299) B579299
theorem B582809 : Blo 385764 582809 := bstep (se 2 (by rfl) ⟨218553, by rfl⟩ : syracuseStep 582809 = 437107) B437107
theorem B386219 : Blo 385764 386219 := bstep (se 1 (by rfl) ⟨289664, by rfl⟩ : syracuseStep 386219 = 579329) B579329
theorem B386231 : Blo 385764 386231 := bstep (se 1 (by rfl) ⟨289673, by rfl⟩ : syracuseStep 386231 = 579347) B579347
theorem B386251 : Blo 385764 386251 := bstep (se 1 (by rfl) ⟨289688, by rfl⟩ : syracuseStep 386251 = 579377) B579377
theorem B386263 : Blo 385764 386263 := bstep (se 1 (by rfl) ⟨289697, by rfl⟩ : syracuseStep 386263 = 579395) B579395
theorem B1238237 : Blo 385764 1238237 := bstep (se 3 (by rfl) ⟨232169, by rfl⟩ : syracuseStep 1238237 = 464339) B464339
theorem B386283 : Blo 385764 386283 := bstep (se 1 (by rfl) ⟨289712, by rfl⟩ : syracuseStep 386283 = 579425) B579425
theorem B386295 : Blo 385764 386295 := bstep (se 1 (by rfl) ⟨289721, by rfl⟩ : syracuseStep 386295 = 579443) B579443
theorem B386315 : Blo 385764 386315 := bstep (se 1 (by rfl) ⟨289736, by rfl⟩ : syracuseStep 386315 = 579473) B579473
theorem B582923 : Blo 385764 582923 := bstep (se 1 (by rfl) ⟨437192, by rfl⟩ : syracuseStep 582923 = 874385) B874385
theorem B386327 : Blo 385764 386327 := bstep (se 1 (by rfl) ⟨289745, by rfl⟩ : syracuseStep 386327 = 579491) B579491
theorem B582935 : Blo 385764 582935 := bstep (se 1 (by rfl) ⟨437201, by rfl⟩ : syracuseStep 582935 = 874403) B874403
theorem B2942243 : Blo 385764 2942243 := bstep (se 1 (by rfl) ⟨2206682, by rfl⟩ : syracuseStep 2942243 = 4413365) B4413365
theorem B386347 : Blo 385764 386347 := bstep (se 1 (by rfl) ⟨289760, by rfl⟩ : syracuseStep 386347 = 579521) B579521
theorem B2090285 : Blo 385764 2090285 := bstep (se 3 (by rfl) ⟨391928, by rfl⟩ : syracuseStep 2090285 = 783857) B783857
theorem B386359 : Blo 385764 386359 := bstep (se 1 (by rfl) ⟨289769, by rfl⟩ : syracuseStep 386359 = 579539) B579539
theorem B1303883 : Blo 385764 1303883 := bstep (se 1 (by rfl) ⟨977912, by rfl⟩ : syracuseStep 1303883 = 1955825) B1955825
theorem B386379 : Blo 385764 386379 := bstep (se 1 (by rfl) ⟨289784, by rfl⟩ : syracuseStep 386379 = 579569) B579569
theorem B386391 : Blo 385764 386391 := bstep (se 1 (by rfl) ⟨289793, by rfl⟩ : syracuseStep 386391 = 579587) B579587
theorem B583001 : Blo 385764 583001 := bstep (se 2 (by rfl) ⟨218625, by rfl⟩ : syracuseStep 583001 = 437251) B437251
theorem B386411 : Blo 385764 386411 := bstep (se 1 (by rfl) ⟨289808, by rfl⟩ : syracuseStep 386411 = 579617) B579617
theorem B386423 : Blo 385764 386423 := bstep (se 1 (by rfl) ⟨289817, by rfl⟩ : syracuseStep 386423 = 579635) B579635
theorem B386443 : Blo 385764 386443 := bstep (se 1 (by rfl) ⟨289832, by rfl⟩ : syracuseStep 386443 = 579665) B579665
theorem B386455 : Blo 385764 386455 := bstep (se 1 (by rfl) ⟨289841, by rfl⟩ : syracuseStep 386455 = 579683) B579683
theorem B386475 : Blo 385764 386475 := bstep (se 1 (by rfl) ⟨289856, by rfl⟩ : syracuseStep 386475 = 579713) B579713
theorem B1467827 : Blo 385764 1467827 := bstep (se 1 (by rfl) ⟨1100870, by rfl⟩ : syracuseStep 1467827 = 2201741) B2201741
theorem B2352563 : Blo 385764 2352563 := bstep (se 1 (by rfl) ⟨1764422, by rfl⟩ : syracuseStep 2352563 = 3528845) B3528845
theorem B386487 : Blo 385764 386487 := bstep (se 1 (by rfl) ⟨289865, by rfl⟩ : syracuseStep 386487 = 579731) B579731
theorem B1467841 : Blo 385764 1467841 := bstep (se 2 (by rfl) ⟨550440, by rfl⟩ : syracuseStep 1467841 = 1100881) B1100881
theorem B386507 : Blo 385764 386507 := bstep (se 1 (by rfl) ⟨289880, by rfl⟩ : syracuseStep 386507 = 579761) B579761
theorem B583115 : Blo 385764 583115 := bstep (se 1 (by rfl) ⟨437336, by rfl⟩ : syracuseStep 583115 = 874673) B874673
theorem B386519 : Blo 385764 386519 := bstep (se 1 (by rfl) ⟨289889, by rfl⟩ : syracuseStep 386519 = 579779) B579779
theorem B583127 : Blo 385764 583127 := bstep (se 1 (by rfl) ⟨437345, by rfl⟩ : syracuseStep 583127 = 874691) B874691
theorem B550361 : Blo 385764 550361 := bstep (se 2 (by rfl) ⟨206385, by rfl⟩ : syracuseStep 550361 = 412771) B412771
theorem B386539 : Blo 385764 386539 := bstep (se 1 (by rfl) ⟨289904, by rfl⟩ : syracuseStep 386539 = 579809) B579809
theorem B386551 : Blo 385764 386551 := bstep (se 1 (by rfl) ⟨289913, by rfl⟩ : syracuseStep 386551 = 579827) B579827
theorem B386571 : Blo 385764 386571 := bstep (se 1 (by rfl) ⟨289928, by rfl⟩ : syracuseStep 386571 = 579857) B579857
theorem B6743569 : Blo 385764 6743569 := bstep (se 2 (by rfl) ⟨2528838, by rfl⟩ : syracuseStep 6743569 = 5057677) B5057677
theorem B386583 : Blo 385764 386583 := bstep (se 1 (by rfl) ⟨289937, by rfl⟩ : syracuseStep 386583 = 579875) B579875
theorem B583193 : Blo 385764 583193 := bstep (se 2 (by rfl) ⟨218697, by rfl⟩ : syracuseStep 583193 = 437395) B437395
theorem B386603 : Blo 385764 386603 := bstep (se 1 (by rfl) ⟨289952, by rfl⟩ : syracuseStep 386603 = 579905) B579905
theorem B386615 : Blo 385764 386615 := bstep (se 1 (by rfl) ⟨289961, by rfl⟩ : syracuseStep 386615 = 579923) B579923
theorem B6350411 : Blo 385764 6350411 := bstep (se 1 (by rfl) ⟨4762808, by rfl⟩ : syracuseStep 6350411 = 9525617) B9525617
theorem B386635 : Blo 385764 386635 := bstep (se 1 (by rfl) ⟨289976, by rfl⟩ : syracuseStep 386635 = 579953) B579953
theorem B386647 : Blo 385764 386647 := bstep (se 1 (by rfl) ⟨289985, by rfl⟩ : syracuseStep 386647 = 579971) B579971
theorem B1304153 : Blo 385764 1304153 := bstep (se 2 (by rfl) ⟨489057, by rfl⟩ : syracuseStep 1304153 = 978115) B978115
theorem B386667 : Blo 385764 386667 := bstep (se 1 (by rfl) ⟨290000, by rfl⟩ : syracuseStep 386667 = 580001) B580001
theorem B386679 : Blo 385764 386679 := bstep (se 1 (by rfl) ⟨290009, by rfl⟩ : syracuseStep 386679 = 580019) B580019
theorem B386699 : Blo 385764 386699 := bstep (se 1 (by rfl) ⟨290024, by rfl⟩ : syracuseStep 386699 = 580049) B580049
theorem B583307 : Blo 385764 583307 := bstep (se 1 (by rfl) ⟨437480, by rfl⟩ : syracuseStep 583307 = 874961) B874961
theorem B386711 : Blo 385764 386711 := bstep (se 1 (by rfl) ⟨290033, by rfl⟩ : syracuseStep 386711 = 580067) B580067
theorem B2090647 : Blo 385764 2090647 := bstep (se 1 (by rfl) ⟨1567985, by rfl⟩ : syracuseStep 2090647 = 3135971) B3135971
theorem B583319 : Blo 385764 583319 := bstep (se 1 (by rfl) ⟨437489, by rfl⟩ : syracuseStep 583319 = 874979) B874979
theorem B386731 : Blo 385764 386731 := bstep (se 1 (by rfl) ⟨290048, by rfl⟩ : syracuseStep 386731 = 580097) B580097
theorem B386743 : Blo 385764 386743 := bstep (se 1 (by rfl) ⟨290057, by rfl⟩ : syracuseStep 386743 = 580115) B580115
theorem B386763 : Blo 385764 386763 := bstep (se 1 (by rfl) ⟨290072, by rfl⟩ : syracuseStep 386763 = 580145) B580145
theorem B386775 : Blo 385764 386775 := bstep (se 1 (by rfl) ⟨290081, by rfl⟩ : syracuseStep 386775 = 580163) B580163
theorem B583385 : Blo 385764 583385 := bstep (se 2 (by rfl) ⟨218769, by rfl⟩ : syracuseStep 583385 = 437539) B437539
theorem B1402589 : Blo 385764 1402589 := bstep (se 3 (by rfl) ⟨262985, by rfl⟩ : syracuseStep 1402589 = 525971) B525971
theorem B386795 : Blo 385764 386795 := bstep (se 1 (by rfl) ⟨290096, by rfl⟩ : syracuseStep 386795 = 580193) B580193
theorem B386807 : Blo 385764 386807 := bstep (se 1 (by rfl) ⟨290105, by rfl⟩ : syracuseStep 386807 = 580211) B580211
theorem B386827 : Blo 385764 386827 := bstep (se 1 (by rfl) ⟨290120, by rfl⟩ : syracuseStep 386827 = 580241) B580241
theorem B386839 : Blo 385764 386839 := bstep (se 1 (by rfl) ⟨290129, by rfl⟩ : syracuseStep 386839 = 580259) B580259
theorem B386859 : Blo 385764 386859 := bstep (se 1 (by rfl) ⟨290144, by rfl⟩ : syracuseStep 386859 = 580289) B580289
theorem B386871 : Blo 385764 386871 := bstep (se 1 (by rfl) ⟨290153, by rfl⟩ : syracuseStep 386871 = 580307) B580307
theorem B386891 : Blo 385764 386891 := bstep (se 1 (by rfl) ⟨290168, by rfl⟩ : syracuseStep 386891 = 580337) B580337
theorem B583499 : Blo 385764 583499 := bstep (se 1 (by rfl) ⟨437624, by rfl⟩ : syracuseStep 583499 = 875249) B875249
theorem B386903 : Blo 385764 386903 := bstep (se 1 (by rfl) ⟨290177, by rfl⟩ : syracuseStep 386903 = 580355) B580355
theorem B583511 : Blo 385764 583511 := bstep (se 1 (by rfl) ⟨437633, by rfl⟩ : syracuseStep 583511 = 875267) B875267
theorem B386923 : Blo 385764 386923 := bstep (se 1 (by rfl) ⟨290192, by rfl⟩ : syracuseStep 386923 = 580385) B580385
theorem B386935 : Blo 385764 386935 := bstep (se 1 (by rfl) ⟨290201, by rfl⟩ : syracuseStep 386935 = 580403) B580403
theorem B386955 : Blo 385764 386955 := bstep (se 1 (by rfl) ⟨290216, by rfl⟩ : syracuseStep 386955 = 580433) B580433
theorem B386967 : Blo 385764 386967 := bstep (se 1 (by rfl) ⟨290225, by rfl⟩ : syracuseStep 386967 = 580451) B580451
theorem B583577 : Blo 385764 583577 := bstep (se 2 (by rfl) ⟨218841, by rfl⟩ : syracuseStep 583577 = 437683) B437683
theorem B386987 : Blo 385764 386987 := bstep (se 1 (by rfl) ⟨290240, by rfl⟩ : syracuseStep 386987 = 580481) B580481
theorem B976819 : Blo 385764 976819 := bstep (se 1 (by rfl) ⟨732614, by rfl⟩ : syracuseStep 976819 = 1465229) B1465229
theorem B386999 : Blo 385764 386999 := bstep (se 1 (by rfl) ⟨290249, by rfl⟩ : syracuseStep 386999 = 580499) B580499
theorem B387019 : Blo 385764 387019 := bstep (se 1 (by rfl) ⟨290264, by rfl⟩ : syracuseStep 387019 = 580529) B580529
theorem B387031 : Blo 385764 387031 := bstep (se 1 (by rfl) ⟨290273, by rfl⟩ : syracuseStep 387031 = 580547) B580547
theorem B387051 : Blo 385764 387051 := bstep (se 1 (by rfl) ⟨290288, by rfl⟩ : syracuseStep 387051 = 580577) B580577
theorem B387063 : Blo 385764 387063 := bstep (se 1 (by rfl) ⟨290297, by rfl⟩ : syracuseStep 387063 = 580595) B580595
theorem B387083 : Blo 385764 387083 := bstep (se 1 (by rfl) ⟨290312, by rfl⟩ : syracuseStep 387083 = 580625) B580625
theorem B583691 : Blo 385764 583691 := bstep (se 1 (by rfl) ⟨437768, by rfl⟩ : syracuseStep 583691 = 875537) B875537
theorem B5597201 : Blo 385764 5597201 := bstep (se 2 (by rfl) ⟨2098950, by rfl⟩ : syracuseStep 5597201 = 4197901) B4197901
theorem B387095 : Blo 385764 387095 := bstep (se 1 (by rfl) ⟨290321, by rfl⟩ : syracuseStep 387095 = 580643) B580643
theorem B583703 : Blo 385764 583703 := bstep (se 1 (by rfl) ⟨437777, by rfl⟩ : syracuseStep 583703 = 875555) B875555
theorem B387115 : Blo 385764 387115 := bstep (se 1 (by rfl) ⟨290336, by rfl⟩ : syracuseStep 387115 = 580673) B580673
theorem B387127 : Blo 385764 387127 := bstep (se 1 (by rfl) ⟨290345, by rfl⟩ : syracuseStep 387127 = 580691) B580691
theorem B976961 : Blo 385764 976961 := bstep (se 2 (by rfl) ⟨366360, by rfl⟩ : syracuseStep 976961 = 732721) B732721
theorem B387147 : Blo 385764 387147 := bstep (se 1 (by rfl) ⟨290360, by rfl⟩ : syracuseStep 387147 = 580721) B580721
theorem B550999 : Blo 385764 550999 := bstep (se 1 (by rfl) ⟨413249, by rfl⟩ : syracuseStep 550999 = 826499) B826499
theorem B387159 : Blo 385764 387159 := bstep (se 1 (by rfl) ⟨290369, by rfl⟩ : syracuseStep 387159 = 580739) B580739
theorem B583769 : Blo 385764 583769 := bstep (se 2 (by rfl) ⟨218913, by rfl⟩ : syracuseStep 583769 = 437827) B437827
theorem B1239133 : Blo 385764 1239133 := bstep (se 3 (by rfl) ⟨232337, by rfl⟩ : syracuseStep 1239133 = 464675) B464675
theorem B387179 : Blo 385764 387179 := bstep (se 1 (by rfl) ⟨290384, by rfl⟩ : syracuseStep 387179 = 580769) B580769
theorem B387191 : Blo 385764 387191 := bstep (se 1 (by rfl) ⟨290393, by rfl⟩ : syracuseStep 387191 = 580787) B580787
theorem B387211 : Blo 385764 387211 := bstep (se 1 (by rfl) ⟨290408, by rfl⟩ : syracuseStep 387211 = 580817) B580817
theorem B3139735 : Blo 385764 3139735 := bstep (se 1 (by rfl) ⟨2354801, by rfl⟩ : syracuseStep 3139735 = 4709603) B4709603
theorem B387223 : Blo 385764 387223 := bstep (se 1 (by rfl) ⟨290417, by rfl⟩ : syracuseStep 387223 = 580835) B580835
theorem B387243 : Blo 385764 387243 := bstep (se 1 (by rfl) ⟨290432, by rfl⟩ : syracuseStep 387243 = 580865) B580865
theorem B387255 : Blo 385764 387255 := bstep (se 1 (by rfl) ⟨290441, by rfl⟩ : syracuseStep 387255 = 580883) B580883
theorem B387275 : Blo 385764 387275 := bstep (se 1 (by rfl) ⟨290456, by rfl⟩ : syracuseStep 387275 = 580913) B580913
theorem B1108171 : Blo 385764 1108171 := bstep (se 1 (by rfl) ⟨831128, by rfl⟩ : syracuseStep 1108171 = 1662257) B1662257
theorem B583883 : Blo 385764 583883 := bstep (se 1 (by rfl) ⟨437912, by rfl⟩ : syracuseStep 583883 = 875825) B875825
theorem B387287 : Blo 385764 387287 := bstep (se 1 (by rfl) ⟨290465, by rfl⟩ : syracuseStep 387287 = 580931) B580931
theorem B583895 : Blo 385764 583895 := bstep (se 1 (by rfl) ⟨437921, by rfl⟩ : syracuseStep 583895 = 875843) B875843
theorem B387307 : Blo 385764 387307 := bstep (se 1 (by rfl) ⟨290480, by rfl⟩ : syracuseStep 387307 = 580961) B580961
theorem B387319 : Blo 385764 387319 := bstep (se 1 (by rfl) ⟨290489, by rfl⟩ : syracuseStep 387319 = 580979) B580979
theorem B387339 : Blo 385764 387339 := bstep (se 1 (by rfl) ⟨290504, by rfl⟩ : syracuseStep 387339 = 581009) B581009
theorem B1304855 : Blo 385764 1304855 := bstep (se 1 (by rfl) ⟨978641, by rfl⟩ : syracuseStep 1304855 = 1957283) B1957283
theorem B387351 : Blo 385764 387351 := bstep (se 1 (by rfl) ⟨290513, by rfl⟩ : syracuseStep 387351 = 581027) B581027
theorem B583961 : Blo 385764 583961 := bstep (se 2 (by rfl) ⟨218985, by rfl⟩ : syracuseStep 583961 = 437971) B437971
theorem B387371 : Blo 385764 387371 := bstep (se 1 (by rfl) ⟨290528, by rfl⟩ : syracuseStep 387371 = 581057) B581057
theorem B387383 : Blo 385764 387383 := bstep (se 1 (by rfl) ⟨290537, by rfl⟩ : syracuseStep 387383 = 581075) B581075
theorem B387403 : Blo 385764 387403 := bstep (se 1 (by rfl) ⟨290552, by rfl⟩ : syracuseStep 387403 = 581105) B581105
theorem B387415 : Blo 385764 387415 := bstep (se 1 (by rfl) ⟨290561, by rfl⟩ : syracuseStep 387415 = 581123) B581123
theorem B387435 : Blo 385764 387435 := bstep (se 1 (by rfl) ⟨290576, by rfl⟩ : syracuseStep 387435 = 581153) B581153
theorem B387447 : Blo 385764 387447 := bstep (se 1 (by rfl) ⟨290585, by rfl⟩ : syracuseStep 387447 = 581171) B581171
theorem B387467 : Blo 385764 387467 := bstep (se 1 (by rfl) ⟨290600, by rfl⟩ : syracuseStep 387467 = 581201) B581201
theorem B584075 : Blo 385764 584075 := bstep (se 1 (by rfl) ⟨438056, by rfl⟩ : syracuseStep 584075 = 876113) B876113
theorem B387479 : Blo 385764 387479 := bstep (se 1 (by rfl) ⟨290609, by rfl⟩ : syracuseStep 387479 = 581219) B581219
theorem B584087 : Blo 385764 584087 := bstep (se 1 (by rfl) ⟨438065, by rfl⟩ : syracuseStep 584087 = 876131) B876131
theorem B387499 : Blo 385764 387499 := bstep (se 1 (by rfl) ⟨290624, by rfl⟩ : syracuseStep 387499 = 581249) B581249
theorem B387511 : Blo 385764 387511 := bstep (se 1 (by rfl) ⟨290633, by rfl⟩ : syracuseStep 387511 = 581267) B581267
theorem B387531 : Blo 385764 387531 := bstep (se 1 (by rfl) ⟨290648, by rfl⟩ : syracuseStep 387531 = 581297) B581297
theorem B387543 : Blo 385764 387543 := bstep (se 1 (by rfl) ⟨290657, by rfl⟩ : syracuseStep 387543 = 581315) B581315
theorem B584153 : Blo 385764 584153 := bstep (se 2 (by rfl) ⟨219057, by rfl⟩ : syracuseStep 584153 = 438115) B438115
theorem B387563 : Blo 385764 387563 := bstep (se 1 (by rfl) ⟨290672, by rfl⟩ : syracuseStep 387563 = 581345) B581345
theorem B387575 : Blo 385764 387575 := bstep (se 1 (by rfl) ⟨290681, by rfl⟩ : syracuseStep 387575 = 581363) B581363
theorem B387595 : Blo 385764 387595 := bstep (se 1 (by rfl) ⟨290696, by rfl⟩ : syracuseStep 387595 = 581393) B581393
theorem B387607 : Blo 385764 387607 := bstep (se 1 (by rfl) ⟨290705, by rfl⟩ : syracuseStep 387607 = 581411) B581411
theorem B387627 : Blo 385764 387627 := bstep (se 1 (by rfl) ⟨290720, by rfl⟩ : syracuseStep 387627 = 581441) B581441
theorem B387639 : Blo 385764 387639 := bstep (se 1 (by rfl) ⟨290729, by rfl⟩ : syracuseStep 387639 = 581459) B581459
theorem B1960523 : Blo 385764 1960523 := bstep (se 1 (by rfl) ⟨1470392, by rfl⟩ : syracuseStep 1960523 = 2940785) B2940785
theorem B387659 : Blo 385764 387659 := bstep (se 1 (by rfl) ⟨290744, by rfl⟩ : syracuseStep 387659 = 581489) B581489
theorem B584267 : Blo 385764 584267 := bstep (se 1 (by rfl) ⟨438200, by rfl⟩ : syracuseStep 584267 = 876401) B876401
theorem B387671 : Blo 385764 387671 := bstep (se 1 (by rfl) ⟨290753, by rfl⟩ : syracuseStep 387671 = 581507) B581507
theorem B584279 : Blo 385764 584279 := bstep (se 1 (by rfl) ⟨438209, by rfl⟩ : syracuseStep 584279 = 876419) B876419
theorem B387691 : Blo 385764 387691 := bstep (se 1 (by rfl) ⟨290768, by rfl⟩ : syracuseStep 387691 = 581537) B581537
theorem B387703 : Blo 385764 387703 := bstep (se 1 (by rfl) ⟨290777, by rfl⟩ : syracuseStep 387703 = 581555) B581555
theorem B387723 : Blo 385764 387723 := bstep (se 1 (by rfl) ⟨290792, by rfl⟩ : syracuseStep 387723 = 581585) B581585
theorem B387735 : Blo 385764 387735 := bstep (se 1 (by rfl) ⟨290801, by rfl⟩ : syracuseStep 387735 = 581603) B581603
theorem B584345 : Blo 385764 584345 := bstep (se 2 (by rfl) ⟨219129, by rfl⟩ : syracuseStep 584345 = 438259) B438259
theorem B387755 : Blo 385764 387755 := bstep (se 1 (by rfl) ⟨290816, by rfl⟩ : syracuseStep 387755 = 581633) B581633
theorem B387767 : Blo 385764 387767 := bstep (se 1 (by rfl) ⟨290825, by rfl⟩ : syracuseStep 387767 = 581651) B581651
theorem B1108673 : Blo 385764 1108673 := bstep (se 2 (by rfl) ⟨415752, by rfl⟩ : syracuseStep 1108673 = 831505) B831505
theorem B387787 : Blo 385764 387787 := bstep (se 1 (by rfl) ⟨290840, by rfl⟩ : syracuseStep 387787 = 581681) B581681
theorem B387799 : Blo 385764 387799 := bstep (se 1 (by rfl) ⟨290849, by rfl⟩ : syracuseStep 387799 = 581699) B581699
theorem B387819 : Blo 385764 387819 := bstep (se 1 (by rfl) ⟨290864, by rfl⟩ : syracuseStep 387819 = 581729) B581729
theorem B387831 : Blo 385764 387831 := bstep (se 1 (by rfl) ⟨290873, by rfl⟩ : syracuseStep 387831 = 581747) B581747
theorem B387851 : Blo 385764 387851 := bstep (se 1 (by rfl) ⟨290888, by rfl⟩ : syracuseStep 387851 = 581777) B581777
theorem B584459 : Blo 385764 584459 := bstep (se 1 (by rfl) ⟨438344, by rfl⟩ : syracuseStep 584459 = 876689) B876689
theorem B387863 : Blo 385764 387863 := bstep (se 1 (by rfl) ⟨290897, by rfl⟩ : syracuseStep 387863 = 581795) B581795
theorem B584471 : Blo 385764 584471 := bstep (se 1 (by rfl) ⟨438353, by rfl⟩ : syracuseStep 584471 = 876707) B876707
theorem B387883 : Blo 385764 387883 := bstep (se 1 (by rfl) ⟨290912, by rfl⟩ : syracuseStep 387883 = 581825) B581825
theorem B1305395 : Blo 385764 1305395 := bstep (se 1 (by rfl) ⟨979046, by rfl⟩ : syracuseStep 1305395 = 1958093) B1958093
theorem B387895 : Blo 385764 387895 := bstep (se 1 (by rfl) ⟨290921, by rfl⟩ : syracuseStep 387895 = 581843) B581843
theorem B387915 : Blo 385764 387915 := bstep (se 1 (by rfl) ⟨290936, by rfl⟩ : syracuseStep 387915 = 581873) B581873
theorem B387927 : Blo 385764 387927 := bstep (se 1 (by rfl) ⟨290945, by rfl⟩ : syracuseStep 387927 = 581891) B581891
theorem B584537 : Blo 385764 584537 := bstep (se 2 (by rfl) ⟨219201, by rfl⟩ : syracuseStep 584537 = 438403) B438403
theorem B387947 : Blo 385764 387947 := bstep (se 1 (by rfl) ⟨290960, by rfl⟩ : syracuseStep 387947 = 581921) B581921
theorem B387959 : Blo 385764 387959 := bstep (se 1 (by rfl) ⟨290969, by rfl⟩ : syracuseStep 387959 = 581939) B581939
theorem B551819 : Blo 385764 551819 := bstep (se 1 (by rfl) ⟨413864, by rfl⟩ : syracuseStep 551819 = 827729) B827729
theorem B387979 : Blo 385764 387979 := bstep (se 1 (by rfl) ⟨290984, by rfl⟩ : syracuseStep 387979 = 581969) B581969
theorem B387991 : Blo 385764 387991 := bstep (se 1 (by rfl) ⟨290993, by rfl⟩ : syracuseStep 387991 = 581987) B581987
theorem B388011 : Blo 385764 388011 := bstep (se 1 (by rfl) ⟨291008, by rfl⟩ : syracuseStep 388011 = 582017) B582017
theorem B388023 : Blo 385764 388023 := bstep (se 1 (by rfl) ⟨291017, by rfl⟩ : syracuseStep 388023 = 582035) B582035
theorem B388043 : Blo 385764 388043 := bstep (se 1 (by rfl) ⟨291032, by rfl⟩ : syracuseStep 388043 = 582065) B582065
theorem B388055 : Blo 385764 388055 := bstep (se 1 (by rfl) ⟨291041, by rfl⟩ : syracuseStep 388055 = 582083) B582083
theorem B388075 : Blo 385764 388075 := bstep (se 1 (by rfl) ⟨291056, by rfl⟩ : syracuseStep 388075 = 582113) B582113
theorem B388087 : Blo 385764 388087 := bstep (se 1 (by rfl) ⟨291065, by rfl⟩ : syracuseStep 388087 = 582131) B582131
theorem B388107 : Blo 385764 388107 := bstep (se 1 (by rfl) ⟨291080, by rfl⟩ : syracuseStep 388107 = 582161) B582161
theorem B388119 : Blo 385764 388119 := bstep (se 1 (by rfl) ⟨291089, by rfl⟩ : syracuseStep 388119 = 582179) B582179
theorem B1109015 : Blo 385764 1109015 := bstep (se 1 (by rfl) ⟨831761, by rfl⟩ : syracuseStep 1109015 = 1663523) B1663523
theorem B388139 : Blo 385764 388139 := bstep (se 1 (by rfl) ⟨291104, by rfl⟩ : syracuseStep 388139 = 582209) B582209
theorem B1043507 : Blo 385764 1043507 := bstep (se 1 (by rfl) ⟨782630, by rfl⟩ : syracuseStep 1043507 = 1565261) B1565261
theorem B388151 : Blo 385764 388151 := bstep (se 1 (by rfl) ⟨291113, by rfl⟩ : syracuseStep 388151 = 582227) B582227
theorem B1305665 : Blo 385764 1305665 := bstep (se 2 (by rfl) ⟨489624, by rfl⟩ : syracuseStep 1305665 = 979249) B979249
theorem B388171 : Blo 385764 388171 := bstep (se 1 (by rfl) ⟨291128, by rfl⟩ : syracuseStep 388171 = 582257) B582257
theorem B388183 : Blo 385764 388183 := bstep (se 1 (by rfl) ⟨291137, by rfl⟩ : syracuseStep 388183 = 582275) B582275
theorem B388203 : Blo 385764 388203 := bstep (se 1 (by rfl) ⟨291152, by rfl⟩ : syracuseStep 388203 = 582305) B582305
theorem B388215 : Blo 385764 388215 := bstep (se 1 (by rfl) ⟨291161, by rfl⟩ : syracuseStep 388215 = 582323) B582323
theorem B388235 : Blo 385764 388235 := bstep (se 1 (by rfl) ⟨291176, by rfl⟩ : syracuseStep 388235 = 582353) B582353
theorem B388247 : Blo 385764 388247 := bstep (se 1 (by rfl) ⟨291185, by rfl⟩ : syracuseStep 388247 = 582371) B582371
theorem B388267 : Blo 385764 388267 := bstep (se 1 (by rfl) ⟨291200, by rfl⟩ : syracuseStep 388267 = 582401) B582401
theorem B388279 : Blo 385764 388279 := bstep (se 1 (by rfl) ⟨291209, by rfl⟩ : syracuseStep 388279 = 582419) B582419
theorem B388299 : Blo 385764 388299 := bstep (se 1 (by rfl) ⟨291224, by rfl⟩ : syracuseStep 388299 = 582449) B582449
theorem B388311 : Blo 385764 388311 := bstep (se 1 (by rfl) ⟨291233, by rfl⟩ : syracuseStep 388311 = 582467) B582467
theorem B388331 : Blo 385764 388331 := bstep (se 1 (by rfl) ⟨291248, by rfl⟩ : syracuseStep 388331 = 582497) B582497
theorem B388343 : Blo 385764 388343 := bstep (se 1 (by rfl) ⟨291257, by rfl⟩ : syracuseStep 388343 = 582515) B582515
theorem B388363 : Blo 385764 388363 := bstep (se 1 (by rfl) ⟨291272, by rfl⟩ : syracuseStep 388363 = 582545) B582545
theorem B388375 : Blo 385764 388375 := bstep (se 1 (by rfl) ⟨291281, by rfl⟩ : syracuseStep 388375 = 582563) B582563
theorem B388395 : Blo 385764 388395 := bstep (se 1 (by rfl) ⟨291296, by rfl⟩ : syracuseStep 388395 = 582593) B582593
theorem B978227 : Blo 385764 978227 := bstep (se 1 (by rfl) ⟨733670, by rfl⟩ : syracuseStep 978227 = 1467341) B1467341
theorem B388407 : Blo 385764 388407 := bstep (se 1 (by rfl) ⟨291305, by rfl⟩ : syracuseStep 388407 = 582611) B582611
theorem B1469771 : Blo 385764 1469771 := bstep (se 1 (by rfl) ⟨1102328, by rfl⟩ : syracuseStep 1469771 = 2204657) B2204657
theorem B388427 : Blo 385764 388427 := bstep (se 1 (by rfl) ⟨291320, by rfl⟩ : syracuseStep 388427 = 582641) B582641
theorem B388439 : Blo 385764 388439 := bstep (se 1 (by rfl) ⟨291329, by rfl⟩ : syracuseStep 388439 = 582659) B582659
theorem B1469785 : Blo 385764 1469785 := bstep (se 2 (by rfl) ⟨551169, by rfl⟩ : syracuseStep 1469785 = 1102339) B1102339
theorem B388459 : Blo 385764 388459 := bstep (se 1 (by rfl) ⟨291344, by rfl⟩ : syracuseStep 388459 = 582689) B582689
theorem B388471 : Blo 385764 388471 := bstep (se 1 (by rfl) ⟨291353, by rfl⟩ : syracuseStep 388471 = 582707) B582707
theorem B388491 : Blo 385764 388491 := bstep (se 1 (by rfl) ⟨291368, by rfl⟩ : syracuseStep 388491 = 582737) B582737
theorem B388503 : Blo 385764 388503 := bstep (se 1 (by rfl) ⟨291377, by rfl⟩ : syracuseStep 388503 = 582755) B582755
theorem B388523 : Blo 385764 388523 := bstep (se 1 (by rfl) ⟨291392, by rfl⟩ : syracuseStep 388523 = 582785) B582785
theorem B388535 : Blo 385764 388535 := bstep (se 1 (by rfl) ⟨291401, by rfl⟩ : syracuseStep 388535 = 582803) B582803
theorem B388555 : Blo 385764 388555 := bstep (se 1 (by rfl) ⟨291416, by rfl⟩ : syracuseStep 388555 = 582833) B582833
theorem B388567 : Blo 385764 388567 := bstep (se 1 (by rfl) ⟨291425, by rfl⟩ : syracuseStep 388567 = 582851) B582851
theorem B749017 : Blo 385764 749017 := bstep (se 2 (by rfl) ⟨280881, by rfl⟩ : syracuseStep 749017 = 561763) B561763
theorem B1404377 : Blo 385764 1404377 := bstep (se 2 (by rfl) ⟨526641, by rfl⟩ : syracuseStep 1404377 = 1053283) B1053283
theorem B388587 : Blo 385764 388587 := bstep (se 1 (by rfl) ⟨291440, by rfl⟩ : syracuseStep 388587 = 582881) B582881
theorem B388599 : Blo 385764 388599 := bstep (se 1 (by rfl) ⟨291449, by rfl⟩ : syracuseStep 388599 = 582899) B582899
theorem B388619 : Blo 385764 388619 := bstep (se 1 (by rfl) ⟨291464, by rfl⟩ : syracuseStep 388619 = 582929) B582929
theorem B388631 : Blo 385764 388631 := bstep (se 1 (by rfl) ⟨291473, by rfl⟩ : syracuseStep 388631 = 582947) B582947
theorem B388651 : Blo 385764 388651 := bstep (se 1 (by rfl) ⟨291488, by rfl⟩ : syracuseStep 388651 = 582977) B582977
theorem B749107 : Blo 385764 749107 := bstep (se 1 (by rfl) ⟨561830, by rfl⟩ : syracuseStep 749107 = 1123661) B1123661
theorem B388663 : Blo 385764 388663 := bstep (se 1 (by rfl) ⟨291497, by rfl⟩ : syracuseStep 388663 = 582995) B582995
theorem B388683 : Blo 385764 388683 := bstep (se 1 (by rfl) ⟨291512, by rfl⟩ : syracuseStep 388683 = 583025) B583025
theorem B388695 : Blo 385764 388695 := bstep (se 1 (by rfl) ⟨291521, by rfl⟩ : syracuseStep 388695 = 583043) B583043
theorem B1306205 : Blo 385764 1306205 := bstep (se 3 (by rfl) ⟨244913, by rfl⟩ : syracuseStep 1306205 = 489827) B489827
theorem B388715 : Blo 385764 388715 := bstep (se 1 (by rfl) ⟨291536, by rfl⟩ : syracuseStep 388715 = 583073) B583073
theorem B388727 : Blo 385764 388727 := bstep (se 1 (by rfl) ⟨291545, by rfl⟩ : syracuseStep 388727 = 583091) B583091
theorem B388747 : Blo 385764 388747 := bstep (se 1 (by rfl) ⟨291560, by rfl⟩ : syracuseStep 388747 = 583121) B583121
theorem B388759 : Blo 385764 388759 := bstep (se 1 (by rfl) ⟨291569, by rfl⟩ : syracuseStep 388759 = 583139) B583139
theorem B388779 : Blo 385764 388779 := bstep (se 1 (by rfl) ⟨291584, by rfl⟩ : syracuseStep 388779 = 583169) B583169
theorem B1994419 : Blo 385764 1994419 := bstep (se 1 (by rfl) ⟨1495814, by rfl⟩ : syracuseStep 1994419 = 2991629) B2991629
theorem B388791 : Blo 385764 388791 := bstep (se 1 (by rfl) ⟨291593, by rfl⟩ : syracuseStep 388791 = 583187) B583187
theorem B388811 : Blo 385764 388811 := bstep (se 1 (by rfl) ⟨291608, by rfl⟩ : syracuseStep 388811 = 583217) B583217
theorem B388823 : Blo 385764 388823 := bstep (se 1 (by rfl) ⟨291617, by rfl⟩ : syracuseStep 388823 = 583235) B583235
theorem B388843 : Blo 385764 388843 := bstep (se 1 (by rfl) ⟨291632, by rfl⟩ : syracuseStep 388843 = 583265) B583265
theorem B388855 : Blo 385764 388855 := bstep (se 1 (by rfl) ⟨291641, by rfl⟩ : syracuseStep 388855 = 583283) B583283
theorem B388875 : Blo 385764 388875 := bstep (se 1 (by rfl) ⟨291656, by rfl⟩ : syracuseStep 388875 = 583313) B583313
theorem B388887 : Blo 385764 388887 := bstep (se 1 (by rfl) ⟨291665, by rfl⟩ : syracuseStep 388887 = 583331) B583331
theorem B388907 : Blo 385764 388907 := bstep (se 1 (by rfl) ⟨291680, by rfl⟩ : syracuseStep 388907 = 583361) B583361
theorem B388919 : Blo 385764 388919 := bstep (se 1 (by rfl) ⟨291689, by rfl⟩ : syracuseStep 388919 = 583379) B583379
theorem B978763 : Blo 385764 978763 := bstep (se 1 (by rfl) ⟨734072, by rfl⟩ : syracuseStep 978763 = 1468145) B1468145
theorem B388939 : Blo 385764 388939 := bstep (se 1 (by rfl) ⟨291704, by rfl⟩ : syracuseStep 388939 = 583409) B583409
theorem B749387 : Blo 385764 749387 := bstep (se 1 (by rfl) ⟨562040, by rfl⟩ : syracuseStep 749387 = 1124081) B1124081
theorem B388951 : Blo 385764 388951 := bstep (se 1 (by rfl) ⟨291713, by rfl⟩ : syracuseStep 388951 = 583427) B583427
theorem B388971 : Blo 385764 388971 := bstep (se 1 (by rfl) ⟨291728, by rfl⟩ : syracuseStep 388971 = 583457) B583457
theorem B388983 : Blo 385764 388983 := bstep (se 1 (by rfl) ⟨291737, by rfl⟩ : syracuseStep 388983 = 583475) B583475
theorem B389003 : Blo 385764 389003 := bstep (se 1 (by rfl) ⟨291752, by rfl⟩ : syracuseStep 389003 = 583505) B583505
theorem B389015 : Blo 385764 389015 := bstep (se 1 (by rfl) ⟨291761, by rfl⟩ : syracuseStep 389015 = 583523) B583523
theorem B389035 : Blo 385764 389035 := bstep (se 1 (by rfl) ⟨291776, by rfl⟩ : syracuseStep 389035 = 583553) B583553
theorem B389047 : Blo 385764 389047 := bstep (se 1 (by rfl) ⟨291785, by rfl⟩ : syracuseStep 389047 = 583571) B583571
theorem B389067 : Blo 385764 389067 := bstep (se 1 (by rfl) ⟨291800, by rfl⟩ : syracuseStep 389067 = 583601) B583601
theorem B389079 : Blo 385764 389079 := bstep (se 1 (by rfl) ⟨291809, by rfl⟩ : syracuseStep 389079 = 583619) B583619
theorem B978905 : Blo 385764 978905 := bstep (se 2 (by rfl) ⟨367089, by rfl⟩ : syracuseStep 978905 = 734179) B734179
theorem B389099 : Blo 385764 389099 := bstep (se 1 (by rfl) ⟨291824, by rfl⟩ : syracuseStep 389099 = 583649) B583649
theorem B880627 : Blo 385764 880627 := bstep (se 1 (by rfl) ⟨660470, by rfl⟩ : syracuseStep 880627 = 1320941) B1320941
theorem B389111 : Blo 385764 389111 := bstep (se 1 (by rfl) ⟨291833, by rfl⟩ : syracuseStep 389111 = 583667) B583667
theorem B389131 : Blo 385764 389131 := bstep (se 1 (by rfl) ⟨291848, by rfl⟩ : syracuseStep 389131 = 583697) B583697
theorem B651287 : Blo 385764 651287 := bstep (se 1 (by rfl) ⟨488465, by rfl⟩ : syracuseStep 651287 = 976931) B976931
theorem B389143 : Blo 385764 389143 := bstep (se 1 (by rfl) ⟨291857, by rfl⟩ : syracuseStep 389143 = 583715) B583715
theorem B389163 : Blo 385764 389163 := bstep (se 1 (by rfl) ⟨291872, by rfl⟩ : syracuseStep 389163 = 583745) B583745
theorem B389175 : Blo 385764 389175 := bstep (se 1 (by rfl) ⟨291881, by rfl⟩ : syracuseStep 389175 = 583763) B583763
theorem B389195 : Blo 385764 389195 := bstep (se 1 (by rfl) ⟨291896, by rfl⟩ : syracuseStep 389195 = 583793) B583793
theorem B389207 : Blo 385764 389207 := bstep (se 1 (by rfl) ⟨291905, by rfl⟩ : syracuseStep 389207 = 583811) B583811
theorem B389227 : Blo 385764 389227 := bstep (se 1 (by rfl) ⟨291920, by rfl⟩ : syracuseStep 389227 = 583841) B583841
theorem B389239 : Blo 385764 389239 := bstep (se 1 (by rfl) ⟨291929, by rfl⟩ : syracuseStep 389239 = 583859) B583859
theorem B389259 : Blo 385764 389259 := bstep (se 1 (by rfl) ⟨291944, by rfl⟩ : syracuseStep 389259 = 583889) B583889
theorem B651415 : Blo 385764 651415 := bstep (se 1 (by rfl) ⟨488561, by rfl⟩ : syracuseStep 651415 = 977123) B977123
theorem B389271 : Blo 385764 389271 := bstep (se 1 (by rfl) ⟨291953, by rfl⟩ : syracuseStep 389271 = 583907) B583907
theorem B389291 : Blo 385764 389291 := bstep (se 1 (by rfl) ⟨291968, by rfl⟩ : syracuseStep 389291 = 583937) B583937
theorem B389303 : Blo 385764 389303 := bstep (se 1 (by rfl) ⟨291977, by rfl⟩ : syracuseStep 389303 = 583955) B583955
theorem B389323 : Blo 385764 389323 := bstep (se 1 (by rfl) ⟨291992, by rfl⟩ : syracuseStep 389323 = 583985) B583985
theorem B4944077 : Blo 385764 4944077 := bstep (se 3 (by rfl) ⟨927014, by rfl⟩ : syracuseStep 4944077 = 1854029) B1854029
theorem B389335 : Blo 385764 389335 := bstep (se 1 (by rfl) ⟨292001, by rfl⟩ : syracuseStep 389335 = 584003) B584003
theorem B389355 : Blo 385764 389355 := bstep (se 1 (by rfl) ⟨292016, by rfl⟩ : syracuseStep 389355 = 584033) B584033
theorem B389367 : Blo 385764 389367 := bstep (se 1 (by rfl) ⟨292025, by rfl⟩ : syracuseStep 389367 = 584051) B584051
theorem B389387 : Blo 385764 389387 := bstep (se 1 (by rfl) ⟨292040, by rfl⟩ : syracuseStep 389387 = 584081) B584081
theorem B1470743 : Blo 385764 1470743 := bstep (se 1 (by rfl) ⟨1103057, by rfl⟩ : syracuseStep 1470743 = 2206115) B2206115
theorem B389399 : Blo 385764 389399 := bstep (se 1 (by rfl) ⟨292049, by rfl⟩ : syracuseStep 389399 = 584099) B584099
theorem B389419 : Blo 385764 389419 := bstep (se 1 (by rfl) ⟨292064, by rfl⟩ : syracuseStep 389419 = 584129) B584129
theorem B389431 : Blo 385764 389431 := bstep (se 1 (by rfl) ⟨292073, by rfl⟩ : syracuseStep 389431 = 584147) B584147
theorem B1962305 : Blo 385764 1962305 := bstep (se 2 (by rfl) ⟨735864, by rfl⟩ : syracuseStep 1962305 = 1471729) B1471729
theorem B389451 : Blo 385764 389451 := bstep (se 1 (by rfl) ⟨292088, by rfl⟩ : syracuseStep 389451 = 584177) B584177
theorem B389463 : Blo 385764 389463 := bstep (se 1 (by rfl) ⟨292097, by rfl⟩ : syracuseStep 389463 = 584195) B584195
theorem B389483 : Blo 385764 389483 := bstep (se 1 (by rfl) ⟨292112, by rfl⟩ : syracuseStep 389483 = 584225) B584225
theorem B389495 : Blo 385764 389495 := bstep (se 1 (by rfl) ⟨292121, by rfl⟩ : syracuseStep 389495 = 584243) B584243
theorem B389515 : Blo 385764 389515 := bstep (se 1 (by rfl) ⟨292136, by rfl⟩ : syracuseStep 389515 = 584273) B584273
theorem B389527 : Blo 385764 389527 := bstep (se 1 (by rfl) ⟨292145, by rfl⟩ : syracuseStep 389527 = 584291) B584291
theorem B389547 : Blo 385764 389547 := bstep (se 1 (by rfl) ⟨292160, by rfl⟩ : syracuseStep 389547 = 584321) B584321
theorem B389559 : Blo 385764 389559 := bstep (se 1 (by rfl) ⟨292169, by rfl⟩ : syracuseStep 389559 = 584339) B584339
theorem B389579 : Blo 385764 389579 := bstep (se 1 (by rfl) ⟨292184, by rfl⟩ : syracuseStep 389579 = 584369) B584369
theorem B389591 : Blo 385764 389591 := bstep (se 1 (by rfl) ⟨292193, by rfl⟩ : syracuseStep 389591 = 584387) B584387
theorem B389611 : Blo 385764 389611 := bstep (se 1 (by rfl) ⟨292208, by rfl⟩ : syracuseStep 389611 = 584417) B584417
theorem B389623 : Blo 385764 389623 := bstep (se 1 (by rfl) ⟨292217, by rfl⟩ : syracuseStep 389623 = 584435) B584435
theorem B389643 : Blo 385764 389643 := bstep (se 1 (by rfl) ⟨292232, by rfl⟩ : syracuseStep 389643 = 584465) B584465
theorem B2486801 : Blo 385764 2486801 := bstep (se 2 (by rfl) ⟨932550, by rfl⟩ : syracuseStep 2486801 = 1865101) B1865101
theorem B389655 : Blo 385764 389655 := bstep (se 1 (by rfl) ⟨292241, by rfl⟩ : syracuseStep 389655 = 584483) B584483
theorem B389675 : Blo 385764 389675 := bstep (se 1 (by rfl) ⟨292256, by rfl⟩ : syracuseStep 389675 = 584513) B584513
theorem B389687 : Blo 385764 389687 := bstep (se 1 (by rfl) ⟨292265, by rfl⟩ : syracuseStep 389687 = 584531) B584531
theorem B389707 : Blo 385764 389707 := bstep (se 1 (by rfl) ⟨292280, by rfl⟩ : syracuseStep 389707 = 584561) B584561
theorem B389719 : Blo 385764 389719 := bstep (se 1 (by rfl) ⟨292289, by rfl⟩ : syracuseStep 389719 = 584579) B584579
theorem B389739 : Blo 385764 389739 := bstep (se 1 (by rfl) ⟨292304, by rfl⟩ : syracuseStep 389739 = 584609) B584609
theorem B389751 : Blo 385764 389751 := bstep (se 1 (by rfl) ⟨292313, by rfl⟩ : syracuseStep 389751 = 584627) B584627
theorem B1307339 : Blo 385764 1307339 := bstep (se 1 (by rfl) ⟨980504, by rfl⟩ : syracuseStep 1307339 = 1961009) B1961009
theorem B652043 : Blo 385764 652043 := bstep (se 1 (by rfl) ⟨489032, by rfl⟩ : syracuseStep 652043 = 978065) B978065
theorem B979735 : Blo 385764 979735 := bstep (se 1 (by rfl) ⟨734801, by rfl⟩ : syracuseStep 979735 = 1469603) B1469603
theorem B652171 : Blo 385764 652171 := bstep (se 1 (by rfl) ⟨489128, by rfl⟩ : syracuseStep 652171 = 978257) B978257
theorem B1307609 : Blo 385764 1307609 := bstep (se 2 (by rfl) ⟨490353, by rfl⟩ : syracuseStep 1307609 = 980707) B980707
theorem B783361 : Blo 385764 783361 := bstep (se 2 (by rfl) ⟨293760, by rfl⟩ : syracuseStep 783361 = 587521) B587521
theorem B652313 : Blo 385764 652313 := bstep (se 2 (by rfl) ⟨244617, by rfl⟩ : syracuseStep 652313 = 489235) B489235
theorem B2651237 : Blo 385764 2651237 := bstep (se 4 (by rfl) ⟨248553, by rfl⟩ : syracuseStep 2651237 = 497107) B497107
theorem B488587 : Blo 385764 488587 := bstep (se 1 (by rfl) ⟨366440, by rfl⟩ : syracuseStep 488587 = 732881) B732881
theorem B652441 : Blo 385764 652441 := bstep (se 2 (by rfl) ⟨244665, by rfl⟩ : syracuseStep 652441 = 489331) B489331
theorem B980171 : Blo 385764 980171 := bstep (se 1 (by rfl) ⟨735128, by rfl⟩ : syracuseStep 980171 = 1470257) B1470257
theorem B1045835 : Blo 385764 1045835 := bstep (se 1 (by rfl) ⟨784376, by rfl⟩ : syracuseStep 1045835 = 1568753) B1568753
theorem B488855 : Blo 385764 488855 := bstep (se 1 (by rfl) ⟨366641, by rfl⟩ : syracuseStep 488855 = 733283) B733283
theorem B1472003 : Blo 385764 1472003 := bstep (se 1 (by rfl) ⟨1104002, by rfl⟩ : syracuseStep 1472003 = 2208005) B2208005
theorem B980545 : Blo 385764 980545 := bstep (se 2 (by rfl) ⟨367704, by rfl⟩ : syracuseStep 980545 = 735409) B735409
theorem B1308311 : Blo 385764 1308311 := bstep (se 1 (by rfl) ⟨981233, by rfl⟩ : syracuseStep 1308311 = 1962467) B1962467
theorem B653015 : Blo 385764 653015 := bstep (se 1 (by rfl) ⟨489761, by rfl⟩ : syracuseStep 653015 = 979523) B979523
theorem B1767233 : Blo 385764 1767233 := bstep (se 2 (by rfl) ⟨662712, by rfl⟩ : syracuseStep 1767233 = 1325425) B1325425
theorem B653143 : Blo 385764 653143 := bstep (se 1 (by rfl) ⟨489857, by rfl⟩ : syracuseStep 653143 = 979715) B979715
theorem B1570711 : Blo 385764 1570711 := bstep (se 1 (by rfl) ⟨1178033, by rfl⟩ : syracuseStep 1570711 = 2356067) B2356067
theorem B489559 : Blo 385764 489559 := bstep (se 1 (by rfl) ⟨367169, by rfl⟩ : syracuseStep 489559 = 734339) B734339
theorem B1046621 : Blo 385764 1046621 := bstep (se 3 (by rfl) ⟨196241, by rfl⟩ : syracuseStep 1046621 = 392483) B392483
theorem B981143 : Blo 385764 981143 := bstep (se 1 (by rfl) ⟨735857, by rfl⟩ : syracuseStep 981143 = 1471715) B1471715
theorem B1308851 : Blo 385764 1308851 := bstep (se 1 (by rfl) ⟨981638, by rfl⟩ : syracuseStep 1308851 = 1963277) B1963277
theorem B620759 : Blo 385764 620759 := bstep (se 1 (by rfl) ⟨465569, by rfl⟩ : syracuseStep 620759 = 931139) B931139
theorem B1964249 : Blo 385764 1964249 := bstep (se 2 (by rfl) ⟨736593, by rfl⟩ : syracuseStep 1964249 = 1473187) B1473187
theorem B2881885 : Blo 385764 2881885 := bstep (se 3 (by rfl) ⟨540353, by rfl⟩ : syracuseStep 2881885 = 1080707) B1080707
theorem B1309121 : Blo 385764 1309121 := bstep (se 2 (by rfl) ⟨490920, by rfl⟩ : syracuseStep 1309121 = 981841) B981841
theorem B1178059 : Blo 385764 1178059 := bstep (se 1 (by rfl) ⟨883544, by rfl⟩ : syracuseStep 1178059 = 1767089) B1767089
theorem B653771 : Blo 385764 653771 := bstep (se 1 (by rfl) ⟨490328, by rfl⟩ : syracuseStep 653771 = 980657) B980657
theorem B2947589 : Blo 385764 2947589 := bstep (se 4 (by rfl) ⟨276336, by rfl⟩ : syracuseStep 2947589 = 552673) B552673
theorem B653899 : Blo 385764 653899 := bstep (se 1 (by rfl) ⟨490424, by rfl⟩ : syracuseStep 653899 = 980849) B980849
theorem B1178315 : Blo 385764 1178315 := bstep (se 1 (by rfl) ⟨883736, by rfl⟩ : syracuseStep 1178315 = 1767473) B1767473
theorem B654041 : Blo 385764 654041 := bstep (se 2 (by rfl) ⟨245265, by rfl⟩ : syracuseStep 654041 = 490531) B490531
theorem B6617861 : Blo 385764 6617861 := bstep (se 4 (by rfl) ⟨620424, by rfl⟩ : syracuseStep 6617861 = 1240849) B1240849
theorem B654169 : Blo 385764 654169 := bstep (se 2 (by rfl) ⟨245313, by rfl⟩ : syracuseStep 654169 = 490627) B490627
theorem B981953 : Blo 385764 981953 := bstep (se 2 (by rfl) ⟨368232, by rfl⟩ : syracuseStep 981953 = 736465) B736465
theorem B621515 : Blo 385764 621515 := bstep (se 1 (by rfl) ⟨466136, by rfl⟩ : syracuseStep 621515 = 932273) B932273
theorem B1309661 : Blo 385764 1309661 := bstep (se 3 (by rfl) ⟨245561, by rfl⟩ : syracuseStep 1309661 = 491123) B491123
theorem B1047617 : Blo 385764 1047617 := bstep (se 2 (by rfl) ⟨392856, by rfl⟩ : syracuseStep 1047617 = 785713) B785713
theorem B392459 : Blo 385764 392459 := bstep (se 1 (by rfl) ⟨294344, by rfl⟩ : syracuseStep 392459 = 588689) B588689
theorem B3734849 : Blo 385764 3734849 := bstep (se 2 (by rfl) ⟨1400568, by rfl⟩ : syracuseStep 3734849 = 2801137) B2801137
theorem B4717925 : Blo 385764 4717925 := bstep (se 4 (by rfl) ⟨442305, by rfl⟩ : syracuseStep 4717925 = 884611) B884611
theorem B654743 : Blo 385764 654743 := bstep (se 1 (by rfl) ⟨491057, by rfl⟩ : syracuseStep 654743 = 982115) B982115
theorem B622027 : Blo 385764 622027 := bstep (se 1 (by rfl) ⟨466520, by rfl⟩ : syracuseStep 622027 = 933041) B933041
theorem B982489 : Blo 385764 982489 := bstep (se 2 (by rfl) ⟨368433, by rfl⟩ : syracuseStep 982489 = 736867) B736867
theorem B1801745 : Blo 385764 1801745 := bstep (se 2 (by rfl) ⟨675654, by rfl⟩ : syracuseStep 1801745 = 1351309) B1351309
theorem B654871 : Blo 385764 654871 := bstep (se 1 (by rfl) ⟨491153, by rfl⟩ : syracuseStep 654871 = 982307) B982307
theorem B1048115 : Blo 385764 1048115 := bstep (se 1 (by rfl) ⟨786086, by rfl⟩ : syracuseStep 1048115 = 1572173) B1572173
theorem B491275 : Blo 385764 491275 := bstep (se 1 (by rfl) ⟨368456, by rfl⟩ : syracuseStep 491275 = 736913) B736913
theorem B1965869 : Blo 385764 1965869 := bstep (se 3 (by rfl) ⟨368600, by rfl⟩ : syracuseStep 1965869 = 737201) B737201
theorem B1572659 : Blo 385764 1572659 := bstep (se 1 (by rfl) ⟨1179494, by rfl⟩ : syracuseStep 1572659 = 2358989) B2358989
theorem B393067 : Blo 385764 393067 := bstep (se 1 (by rfl) ⟨294800, by rfl⟩ : syracuseStep 393067 = 589601) B589601
theorem B1572787 : Blo 385764 1572787 := bstep (se 1 (by rfl) ⟨1179590, by rfl⟩ : syracuseStep 1572787 = 2359181) B2359181
theorem B983411 : Blo 385764 983411 := bstep (se 1 (by rfl) ⟨737558, by rfl⟩ : syracuseStep 983411 = 1475117) B1475117
theorem B655735 : Blo 385764 655735 := bstep (se 1 (by rfl) ⟨491801, by rfl⟩ : syracuseStep 655735 = 983603) B983603
theorem B1868177 : Blo 385764 1868177 := bstep (se 2 (by rfl) ⟨700566, by rfl⟩ : syracuseStep 1868177 = 1401133) B1401133
theorem B655931 : Blo 385764 655931 := bstep (se 1 (by rfl) ⟨491948, by rfl⟩ : syracuseStep 655931 = 983897) B983897
theorem B557641 : Blo 385764 557641 := bstep (se 2 (by rfl) ⟨209115, by rfl⟩ : syracuseStep 557641 = 418231) B418231
theorem B1966679 : Blo 385764 1966679 := bstep (se 1 (by rfl) ⟨1475009, by rfl⟩ : syracuseStep 1966679 = 2950019) B2950019
theorem B492151 : Blo 385764 492151 := bstep (se 1 (by rfl) ⟨369113, by rfl⟩ : syracuseStep 492151 = 738227) B738227
theorem B1246067 : Blo 385764 1246067 := bstep (se 1 (by rfl) ⟨934550, by rfl⟩ : syracuseStep 1246067 = 1869101) B1869101
theorem B983927 : Blo 385764 983927 := bstep (se 1 (by rfl) ⟨737945, by rfl⟩ : syracuseStep 983927 = 1475891) B1475891
theorem B6652853 : Blo 385764 6652853 := bstep (se 5 (by rfl) ⟨311852, by rfl⟩ : syracuseStep 6652853 = 623705) B623705
theorem B492475 : Blo 385764 492475 := bstep (se 1 (by rfl) ⟨369356, by rfl⟩ : syracuseStep 492475 = 738713) B738713
theorem B656329 : Blo 385764 656329 := bstep (se 2 (by rfl) ⟨246123, by rfl⟩ : syracuseStep 656329 = 492247) B492247
theorem B1967165 : Blo 385764 1967165 := bstep (se 3 (by rfl) ⟨368843, by rfl⟩ : syracuseStep 1967165 = 737687) B737687
theorem B1049735 : Blo 385764 1049735 := bstep (se 1 (by rfl) ⟨787301, by rfl⟩ : syracuseStep 1049735 = 1574603) B1574603
theorem B1049867 : Blo 385764 1049867 := bstep (se 1 (by rfl) ⟨787400, by rfl⟩ : syracuseStep 1049867 = 1574801) B1574801
theorem B1180943 : Blo 385764 1180943 := bstep (se 1 (by rfl) ⟨885707, by rfl⟩ : syracuseStep 1180943 = 1771415) B1771415
theorem B1672595 : Blo 385764 1672595 := bstep (se 1 (by rfl) ⟨1254446, by rfl⟩ : syracuseStep 1672595 = 2508893) B2508893
theorem B657031 : Blo 385764 657031 := bstep (se 1 (by rfl) ⟨492773, by rfl⟩ : syracuseStep 657031 = 985547) B985547
theorem B2361125 : Blo 385764 2361125 := bstep (se 4 (by rfl) ⟨221355, by rfl⟩ : syracuseStep 2361125 = 442711) B442711
theorem B984919 : Blo 385764 984919 := bstep (se 1 (by rfl) ⟨738689, by rfl⟩ : syracuseStep 984919 = 1477379) B1477379
theorem B1050515 : Blo 385764 1050515 := bstep (se 1 (by rfl) ⟨787886, by rfl⟩ : syracuseStep 1050515 = 1575773) B1575773
theorem B985223 : Blo 385764 985223 := bstep (se 1 (by rfl) ⟨738917, by rfl⟩ : syracuseStep 985223 = 1477835) B1477835
theorem B2787529 : Blo 385764 2787529 := bstep (se 2 (by rfl) ⟨1045323, by rfl⟩ : syracuseStep 2787529 = 2090647) B2090647
theorem B1771721 : Blo 385764 1771721 := bstep (se 2 (by rfl) ⟨664395, by rfl⟩ : syracuseStep 1771721 = 1328791) B1328791
theorem B985355 : Blo 385764 985355 := bstep (se 1 (by rfl) ⟨739016, by rfl⟩ : syracuseStep 985355 = 1478033) B1478033
theorem B657679 : Blo 385764 657679 := bstep (se 1 (by rfl) ⟨493259, by rfl⟩ : syracuseStep 657679 = 986519) B986519
theorem B1313171 : Blo 385764 1313171 := bstep (se 1 (by rfl) ⟨984878, by rfl⟩ : syracuseStep 1313171 = 1969757) B1969757
theorem B985871 : Blo 385764 985871 := bstep (se 1 (by rfl) ⟨739403, by rfl⟩ : syracuseStep 985871 = 1478807) B1478807
theorem B1968947 : Blo 385764 1968947 := bstep (se 1 (by rfl) ⟨1476710, by rfl⟩ : syracuseStep 1968947 = 2953421) B2953421
theorem B986003 : Blo 385764 986003 := bstep (se 1 (by rfl) ⟨739502, by rfl⟩ : syracuseStep 986003 = 1479005) B1479005
theorem B1477561 : Blo 385764 1477561 := bstep (se 2 (by rfl) ⟨554085, by rfl⟩ : syracuseStep 1477561 = 1108171) B1108171
theorem B1969271 : Blo 385764 1969271 := bstep (se 1 (by rfl) ⟨1476953, by rfl⟩ : syracuseStep 1969271 = 2953907) B2953907
theorem B1248527 : Blo 385764 1248527 := bstep (se 1 (by rfl) ⟨936395, by rfl⟩ : syracuseStep 1248527 = 1872791) B1872791
theorem B1314575 : Blo 385764 1314575 := bstep (se 1 (by rfl) ⟨985931, by rfl⟩ : syracuseStep 1314575 = 1971863) B1971863
theorem B2494259 : Blo 385764 2494259 := bstep (se 1 (by rfl) ⟨1870694, by rfl⟩ : syracuseStep 2494259 = 3741389) B3741389
theorem B2199575 : Blo 385764 2199575 := bstep (se 1 (by rfl) ⟨1649681, by rfl⟩ : syracuseStep 2199575 = 3299363) B3299363
theorem B1314845 : Blo 385764 1314845 := bstep (se 3 (by rfl) ⟨246533, by rfl⟩ : syracuseStep 1314845 = 493067) B493067
theorem B1970243 : Blo 385764 1970243 := bstep (se 1 (by rfl) ⟨1477682, by rfl⟩ : syracuseStep 1970243 = 2955365) B2955365
theorem B1970567 : Blo 385764 1970567 := bstep (se 1 (by rfl) ⟨1477925, by rfl⟩ : syracuseStep 1970567 = 2955851) B2955851
theorem B528911 : Blo 385764 528911 := bstep (se 1 (by rfl) ⟨396683, by rfl⟩ : syracuseStep 528911 = 793367) B793367
theorem B4821605 : Blo 385764 4821605 := bstep (se 4 (by rfl) ⟨452025, by rfl⟩ : syracuseStep 4821605 = 904051) B904051
theorem B594551 : Blo 385764 594551 := bstep (se 1 (by rfl) ⟨445913, by rfl⟩ : syracuseStep 594551 = 891827) B891827
theorem B824107 : Blo 385764 824107 := bstep (se 1 (by rfl) ⟨618080, by rfl⟩ : syracuseStep 824107 = 1236161) B1236161
theorem B1053499 : Blo 385764 1053499 := bstep (se 1 (by rfl) ⟨790124, by rfl⟩ : syracuseStep 1053499 = 1580249) B1580249
theorem B2659225 : Blo 385764 2659225 := bstep (se 2 (by rfl) ⟨997209, by rfl⟩ : syracuseStep 2659225 = 1994419) B1994419
theorem B272667779 : Blo 385764 272667779 := bstep (se 1 (by rfl) ⟨204500834, by rfl⟩ : syracuseStep 272667779 = 409001669) B409001669
theorem B627983 : Blo 385764 627983 := bstep (se 1 (by rfl) ⟨470987, by rfl⟩ : syracuseStep 627983 = 941975) B941975
theorem B1512857 : Blo 385764 1512857 := bstep (se 2 (by rfl) ⟨567321, by rfl⟩ : syracuseStep 1512857 = 1134643) B1134643
theorem B4724153 : Blo 385764 4724153 := bstep (se 2 (by rfl) ⟨1771557, by rfl⟩ : syracuseStep 4724153 = 3543115) B3543115
theorem B2790989 : Blo 385764 2790989 := bstep (se 3 (by rfl) ⟨523310, by rfl⟩ : syracuseStep 2790989 = 1046621) B1046621
theorem B2496257 : Blo 385764 2496257 := bstep (se 2 (by rfl) ⟨936096, by rfl⟩ : syracuseStep 2496257 = 1872193) B1872193
theorem B3708787 : Blo 385764 3708787 := bstep (se 1 (by rfl) ⟨2781590, by rfl⟩ : syracuseStep 3708787 = 5563181) B5563181
theorem B2201489 : Blo 385764 2201489 := bstep (se 2 (by rfl) ⟨825558, by rfl⟩ : syracuseStep 2201489 = 1651117) B1651117
theorem B825491 : Blo 385764 825491 := bstep (se 1 (by rfl) ⟨619118, by rfl⟩ : syracuseStep 825491 = 1238237) B1238237
theorem B5970323 : Blo 385764 5970323 := bstep (se 1 (by rfl) ⟨4477742, by rfl⟩ : syracuseStep 5970323 = 8955485) B8955485
theorem B2202173 : Blo 385764 2202173 := bstep (se 3 (by rfl) ⟨412907, by rfl⟩ : syracuseStep 2202173 = 825815) B825815
theorem B17538053 : Blo 385764 17538053 := bstep (se 4 (by rfl) ⟨1644192, by rfl⟩ : syracuseStep 17538053 = 3288385) B3288385
theorem B695671 : Blo 385764 695671 := bstep (se 1 (by rfl) ⟨521753, by rfl⟩ : syracuseStep 695671 = 1043507) B1043507
theorem B990599 : Blo 385764 990599 := bstep (se 1 (by rfl) ⟨742949, by rfl⟩ : syracuseStep 990599 = 1485899) B1485899
theorem B4726349 : Blo 385764 4726349 := bstep (se 3 (by rfl) ⟨886190, by rfl⟩ : syracuseStep 4726349 = 1772381) B1772381
theorem B4398785 : Blo 385764 4398785 := bstep (se 2 (by rfl) ⟨1649544, by rfl⟩ : syracuseStep 4398785 = 3299089) B3299089
theorem B499591 : Blo 385764 499591 := bstep (se 1 (by rfl) ⟨374693, by rfl⟩ : syracuseStep 499591 = 749387) B749387
theorem B434191 : Blo 385764 434191 := bstep (se 1 (by rfl) ⟨325643, by rfl⟩ : syracuseStep 434191 = 651287) B651287
theorem B467087 : Blo 385764 467087 := bstep (se 1 (by rfl) ⟨350315, by rfl⟩ : syracuseStep 467087 = 700631) B700631
theorem B1122761 : Blo 385764 1122761 := bstep (se 2 (by rfl) ⟨421035, by rfl⟩ : syracuseStep 1122761 = 842071) B842071
theorem B3842513 : Blo 385764 3842513 := bstep (se 2 (by rfl) ⟨1440942, by rfl⟩ : syracuseStep 3842513 = 2881885) B2881885
theorem B434695 : Blo 385764 434695 := bstep (se 1 (by rfl) ⟨326021, by rfl⟩ : syracuseStep 434695 = 652043) B652043
theorem B434875 : Blo 385764 434875 := bstep (se 1 (by rfl) ⟨326156, by rfl⟩ : syracuseStep 434875 = 652313) B652313
theorem B697223 : Blo 385764 697223 := bstep (se 1 (by rfl) ⟨522917, by rfl⟩ : syracuseStep 697223 = 1045835) B1045835
theorem B533519 : Blo 385764 533519 := bstep (se 1 (by rfl) ⟨400139, by rfl⟩ : syracuseStep 533519 = 800279) B800279
theorem B435343 : Blo 385764 435343 := bstep (se 1 (by rfl) ⟨326507, by rfl⟩ : syracuseStep 435343 = 653015) B653015
theorem B435847 : Blo 385764 435847 := bstep (se 1 (by rfl) ⟨326885, by rfl⟩ : syracuseStep 435847 = 653771) B653771
theorem B2107081 : Blo 385764 2107081 := bstep (se 2 (by rfl) ⟨790155, by rfl⟩ : syracuseStep 2107081 = 1580311) B1580311
theorem B436027 : Blo 385764 436027 := bstep (se 1 (by rfl) ⟨327020, by rfl⟩ : syracuseStep 436027 = 654041) B654041
theorem B829369 : Blo 385764 829369 := bstep (se 2 (by rfl) ⟨311013, by rfl⟩ : syracuseStep 829369 = 622027) B622027
theorem B698411 : Blo 385764 698411 := bstep (se 1 (by rfl) ⟨523808, by rfl⟩ : syracuseStep 698411 = 1047617) B1047617
theorem B4204781 : Blo 385764 4204781 := bstep (se 3 (by rfl) ⟨788396, by rfl⟩ : syracuseStep 4204781 = 1576793) B1576793
theorem B436495 : Blo 385764 436495 := bstep (se 1 (by rfl) ⟨327371, by rfl⟩ : syracuseStep 436495 = 654743) B654743
theorem B698743 : Blo 385764 698743 := bstep (se 1 (by rfl) ⟨524057, by rfl⟩ : syracuseStep 698743 = 1048115) B1048115
theorem B3648077 : Blo 385764 3648077 := bstep (se 3 (by rfl) ⟨684014, by rfl⟩ : syracuseStep 3648077 = 1368029) B1368029
theorem B436999 : Blo 385764 436999 := bstep (se 1 (by rfl) ⟨327749, by rfl⟩ : syracuseStep 436999 = 655499) B655499
theorem B9186085 : Blo 385764 9186085 := bstep (se 4 (by rfl) ⟨861195, by rfl⟩ : syracuseStep 9186085 = 1722391) B1722391
theorem B4729751 : Blo 385764 4729751 := bstep (se 1 (by rfl) ⟨3547313, by rfl⟩ : syracuseStep 4729751 = 7094627) B7094627
theorem B437179 : Blo 385764 437179 := bstep (se 1 (by rfl) ⟨327884, by rfl⟩ : syracuseStep 437179 = 655769) B655769
theorem B830753 : Blo 385764 830753 := bstep (se 2 (by rfl) ⟨311532, by rfl⟩ : syracuseStep 830753 = 623065) B623065
theorem B830855 : Blo 385764 830855 := bstep (se 1 (by rfl) ⟨623141, by rfl⟩ : syracuseStep 830855 = 1246283) B1246283
theorem B437647 : Blo 385764 437647 := bstep (se 1 (by rfl) ⟨328235, by rfl⟩ : syracuseStep 437647 = 656471) B656471
theorem B3321233 : Blo 385764 3321233 := bstep (se 2 (by rfl) ⟨1245462, by rfl⟩ : syracuseStep 3321233 = 2490925) B2490925
theorem B470791 : Blo 385764 470791 := bstep (se 1 (by rfl) ⟨353093, by rfl⟩ : syracuseStep 470791 = 706187) B706187
theorem B733063 : Blo 385764 733063 := bstep (se 1 (by rfl) ⟨549797, by rfl⟩ : syracuseStep 733063 = 1099595) B1099595
theorem B438151 : Blo 385764 438151 := bstep (se 1 (by rfl) ⟨328613, by rfl⟩ : syracuseStep 438151 = 657227) B657227
theorem B438331 : Blo 385764 438331 := bstep (se 1 (by rfl) ⟨328748, by rfl⟩ : syracuseStep 438331 = 657497) B657497
theorem B3321917 : Blo 385764 3321917 := bstep (se 3 (by rfl) ⟨622859, by rfl⟩ : syracuseStep 3321917 = 1245719) B1245719
theorem B1650775 : Blo 385764 1650775 := bstep (se 1 (by rfl) ⟨1238081, by rfl⟩ : syracuseStep 1650775 = 2476163) B2476163
theorem B2208323 : Blo 385764 2208323 := bstep (se 1 (by rfl) ⟨1656242, by rfl⟩ : syracuseStep 2208323 = 3312485) B3312485
theorem B8991425 : Blo 385764 8991425 := bstep (se 2 (by rfl) ⟨3371784, by rfl⟩ : syracuseStep 8991425 = 6743569) B6743569
theorem B471979 : Blo 385764 471979 := bstep (se 1 (by rfl) ⟨353984, by rfl⟩ : syracuseStep 471979 = 707969) B707969
theorem B2208779 : Blo 385764 2208779 := bstep (se 1 (by rfl) ⟨1656584, by rfl⟩ : syracuseStep 2208779 = 3313169) B3313169
theorem B734665 : Blo 385764 734665 := bstep (se 2 (by rfl) ⟨275499, by rfl⟩ : syracuseStep 734665 = 550999) B550999
theorem B1652177 : Blo 385764 1652177 := bstep (se 2 (by rfl) ⟨619566, by rfl⟩ : syracuseStep 1652177 = 1239133) B1239133
theorem B996923 : Blo 385764 996923 := bstep (se 1 (by rfl) ⟨747692, by rfl⟩ : syracuseStep 996923 = 1495385) B1495385
theorem B931475 : Blo 385764 931475 := bstep (se 1 (by rfl) ⟨698606, by rfl⟩ : syracuseStep 931475 = 1397213) B1397213
theorem B800545 : Blo 385764 800545 := bstep (se 2 (by rfl) ⟨300204, by rfl⟩ : syracuseStep 800545 = 600409) B600409
theorem B1718561 : Blo 385764 1718561 := bstep (se 2 (by rfl) ⟨644460, by rfl⟩ : syracuseStep 1718561 = 1288921) B1288921
theorem B1063315 : Blo 385764 1063315 := bstep (se 1 (by rfl) ⟨797486, by rfl⟩ : syracuseStep 1063315 = 1594973) B1594973
theorem B2472677 : Blo 385764 2472677 := bstep (se 4 (by rfl) ⟨231813, by rfl⟩ : syracuseStep 2472677 = 463627) B463627
theorem B3980461 : Blo 385764 3980461 := bstep (se 3 (by rfl) ⟨746336, by rfl⟩ : syracuseStep 3980461 = 1492673) B1492673
theorem B998689 : Blo 385764 998689 := bstep (se 2 (by rfl) ⟨374508, by rfl⟩ : syracuseStep 998689 = 749017) B749017
theorem B868139 : Blo 385764 868139 := bstep (se 1 (by rfl) ⟨651104, by rfl⟩ : syracuseStep 868139 = 1302209) B1302209
theorem B737171 : Blo 385764 737171 := bstep (se 1 (by rfl) ⟨552878, by rfl⟩ : syracuseStep 737171 = 1105757) B1105757
theorem B2211851 : Blo 385764 2211851 := bstep (se 1 (by rfl) ⟨1658888, by rfl⟩ : syracuseStep 2211851 = 3317777) B3317777
theorem B1392727 : Blo 385764 1392727 := bstep (se 1 (by rfl) ⟨1044545, by rfl⟩ : syracuseStep 1392727 = 2089091) B2089091
theorem B737399 : Blo 385764 737399 := bstep (se 1 (by rfl) ⟨553049, by rfl⟩ : syracuseStep 737399 = 1106099) B1106099
theorem B868499 : Blo 385764 868499 := bstep (se 1 (by rfl) ⟨651374, by rfl⟩ : syracuseStep 868499 = 1302749) B1302749
theorem B868553 : Blo 385764 868553 := bstep (se 2 (by rfl) ⟨325707, by rfl⟩ : syracuseStep 868553 = 651415) B651415
theorem B4407533 : Blo 385764 4407533 := bstep (se 3 (by rfl) ⟨826412, by rfl⟩ : syracuseStep 4407533 = 1652825) B1652825
theorem B2212697 : Blo 385764 2212697 := bstep (se 2 (by rfl) ⟨829761, by rfl⟩ : syracuseStep 2212697 = 1659523) B1659523
theorem B1393523 : Blo 385764 1393523 := bstep (se 1 (by rfl) ⟨1045142, by rfl⟩ : syracuseStep 1393523 = 2090285) B2090285
theorem B869255 : Blo 385764 869255 := bstep (se 1 (by rfl) ⟨651941, by rfl⟩ : syracuseStep 869255 = 1303883) B1303883
theorem B3130265 : Blo 385764 3130265 := bstep (se 2 (by rfl) ⟨1173849, by rfl⟩ : syracuseStep 3130265 = 2347699) B2347699
theorem B1098785 : Blo 385764 1098785 := bstep (se 2 (by rfl) ⟨412044, by rfl⟩ : syracuseStep 1098785 = 824089) B824089
theorem B869435 : Blo 385764 869435 := bstep (se 1 (by rfl) ⟨652076, by rfl⟩ : syracuseStep 869435 = 1304153) B1304153
theorem B705683 : Blo 385764 705683 := bstep (se 1 (by rfl) ⟨529262, by rfl⟩ : syracuseStep 705683 = 1058525) B1058525
theorem B935059 : Blo 385764 935059 := bstep (se 1 (by rfl) ⟨701294, by rfl⟩ : syracuseStep 935059 = 1402589) B1402589
theorem B869561 : Blo 385764 869561 := bstep (se 2 (by rfl) ⟨326085, by rfl⟩ : syracuseStep 869561 = 652171) B652171
theorem B1885421 : Blo 385764 1885421 := bstep (se 3 (by rfl) ⟨353516, by rfl⟩ : syracuseStep 1885421 = 707033) B707033
theorem B2213153 : Blo 385764 2213153 := bstep (se 2 (by rfl) ⟨829932, by rfl⟩ : syracuseStep 2213153 = 1659865) B1659865
theorem B509455 : Blo 385764 509455 := bstep (se 1 (by rfl) ⟨382091, by rfl⟩ : syracuseStep 509455 = 764183) B764183
theorem B869903 : Blo 385764 869903 := bstep (se 1 (by rfl) ⟨652427, by rfl⟩ : syracuseStep 869903 = 1304855) B1304855
theorem B2213405 : Blo 385764 2213405 := bstep (se 3 (by rfl) ⟨415013, by rfl⟩ : syracuseStep 2213405 = 830027) B830027
theorem B869921 : Blo 385764 869921 := bstep (se 2 (by rfl) ⟨326220, by rfl⟩ : syracuseStep 869921 = 652441) B652441
theorem B739115 : Blo 385764 739115 := bstep (se 1 (by rfl) ⟨554336, by rfl⟩ : syracuseStep 739115 = 1108673) B1108673
theorem B870263 : Blo 385764 870263 := bstep (se 1 (by rfl) ⟨652697, by rfl⟩ : syracuseStep 870263 = 1305395) B1305395
theorem B1099777 : Blo 385764 1099777 := bstep (se 2 (by rfl) ⟨412416, by rfl⟩ : syracuseStep 1099777 = 824833) B824833
theorem B739343 : Blo 385764 739343 := bstep (se 1 (by rfl) ⟨554507, by rfl⟩ : syracuseStep 739343 = 1109015) B1109015
theorem B870443 : Blo 385764 870443 := bstep (se 1 (by rfl) ⟨652832, by rfl⟩ : syracuseStep 870443 = 1305665) B1305665
theorem B706619 : Blo 385764 706619 := bstep (se 1 (by rfl) ⟨529964, by rfl⟩ : syracuseStep 706619 = 1059929) B1059929
theorem B936251 : Blo 385764 936251 := bstep (se 1 (by rfl) ⟨702188, by rfl⟩ : syracuseStep 936251 = 1404377) B1404377
theorem B870803 : Blo 385764 870803 := bstep (se 1 (by rfl) ⟨653102, by rfl⟩ : syracuseStep 870803 = 1306205) B1306205
theorem B3295673 : Blo 385764 3295673 := bstep (se 2 (by rfl) ⟨1235877, by rfl⟩ : syracuseStep 3295673 = 2471755) B2471755
theorem B870857 : Blo 385764 870857 := bstep (se 2 (by rfl) ⟨326571, by rfl⟩ : syracuseStep 870857 = 653143) B653143
theorem B3296051 : Blo 385764 3296051 := bstep (se 1 (by rfl) ⟨2472038, by rfl⟩ : syracuseStep 3296051 = 4944077) B4944077
theorem B1657867 : Blo 385764 1657867 := bstep (se 1 (by rfl) ⟨1243400, by rfl⟩ : syracuseStep 1657867 = 2486801) B2486801
theorem B871559 : Blo 385764 871559 := bstep (se 1 (by rfl) ⟨653669, by rfl⟩ : syracuseStep 871559 = 1307339) B1307339
theorem B871739 : Blo 385764 871739 := bstep (se 1 (by rfl) ⟨653804, by rfl⟩ : syracuseStep 871739 = 1307609) B1307609
theorem B871865 : Blo 385764 871865 := bstep (se 2 (by rfl) ⟨326949, by rfl⟩ : syracuseStep 871865 = 653899) B653899
theorem B1953233 : Blo 385764 1953233 := bstep (se 2 (by rfl) ⟨732462, by rfl⟩ : syracuseStep 1953233 = 1464925) B1464925
theorem B872207 : Blo 385764 872207 := bstep (se 1 (by rfl) ⟨654155, by rfl⟩ : syracuseStep 872207 = 1308311) B1308311
theorem B872225 : Blo 385764 872225 := bstep (se 2 (by rfl) ⟨327084, by rfl⟩ : syracuseStep 872225 = 654169) B654169
theorem B2215795 : Blo 385764 2215795 := bstep (se 1 (by rfl) ⟨1661846, by rfl⟩ : syracuseStep 2215795 = 3323693) B3323693
theorem B872567 : Blo 385764 872567 := bstep (se 1 (by rfl) ⟨654425, by rfl⟩ : syracuseStep 872567 = 1308851) B1308851
theorem B413839 : Blo 385764 413839 := bstep (se 1 (by rfl) ⟨310379, by rfl⟩ : syracuseStep 413839 = 620759) B620759
theorem B872747 : Blo 385764 872747 := bstep (se 1 (by rfl) ⟨654560, by rfl⟩ : syracuseStep 872747 = 1309121) B1309121
theorem B4411907 : Blo 385764 4411907 := bstep (se 1 (by rfl) ⟨3308930, by rfl⟩ : syracuseStep 4411907 = 6617861) B6617861
theorem B414343 : Blo 385764 414343 := bstep (se 1 (by rfl) ⟨310757, by rfl⟩ : syracuseStep 414343 = 621515) B621515
theorem B873107 : Blo 385764 873107 := bstep (se 1 (by rfl) ⟨654830, by rfl⟩ : syracuseStep 873107 = 1309661) B1309661
theorem B873161 : Blo 385764 873161 := bstep (se 2 (by rfl) ⟨327435, by rfl⟩ : syracuseStep 873161 = 654871) B654871
theorem B1987361 : Blo 385764 1987361 := bstep (se 2 (by rfl) ⟨745260, by rfl⟩ : syracuseStep 1987361 = 1490521) B1490521
theorem B1102727 : Blo 385764 1102727 := bstep (se 1 (by rfl) ⟨827045, by rfl⟩ : syracuseStep 1102727 = 1654091) B1654091
theorem B971777 : Blo 385764 971777 := bstep (se 2 (by rfl) ⟨364416, by rfl⟩ : syracuseStep 971777 = 728833) B728833
theorem B1201163 : Blo 385764 1201163 := bstep (se 1 (by rfl) ⟨900872, by rfl⟩ : syracuseStep 1201163 = 1801745) B1801745
theorem B1102909 : Blo 385764 1102909 := bstep (se 3 (by rfl) ⟨206795, by rfl⟩ : syracuseStep 1102909 = 413591) B413591
theorem B1102967 : Blo 385764 1102967 := bstep (se 1 (by rfl) ⟨827225, by rfl⟩ : syracuseStep 1102967 = 1654451) B1654451
theorem B578747 : Blo 385764 578747 := bstep (se 1 (by rfl) ⟨434060, by rfl⟩ : syracuseStep 578747 = 868121) B868121
theorem B578807 : Blo 385764 578807 := bstep (se 1 (by rfl) ⟨434105, by rfl⟩ : syracuseStep 578807 = 868211) B868211
theorem B578831 : Blo 385764 578831 := bstep (se 1 (by rfl) ⟨434123, by rfl⟩ : syracuseStep 578831 = 868247) B868247
theorem B2217253 : Blo 385764 2217253 := bstep (se 4 (by rfl) ⟨207867, by rfl⟩ : syracuseStep 2217253 = 415735) B415735
theorem B578873 : Blo 385764 578873 := bstep (se 2 (by rfl) ⟨217077, by rfl⟩ : syracuseStep 578873 = 434155) B434155
theorem B578951 : Blo 385764 578951 := bstep (se 1 (by rfl) ⟨434213, by rfl⟩ : syracuseStep 578951 = 868427) B868427
theorem B873863 : Blo 385764 873863 := bstep (se 1 (by rfl) ⟨655397, by rfl⟩ : syracuseStep 873863 = 1310795) B1310795
theorem B578987 : Blo 385764 578987 := bstep (se 1 (by rfl) ⟨434240, by rfl⟩ : syracuseStep 578987 = 868481) B868481
theorem B5952953 : Blo 385764 5952953 := bstep (se 2 (by rfl) ⟨2232357, by rfl⟩ : syracuseStep 5952953 = 4464715) B4464715
theorem B415163 : Blo 385764 415163 := bstep (se 1 (by rfl) ⟨311372, by rfl⟩ : syracuseStep 415163 = 622745) B622745
theorem B579017 : Blo 385764 579017 := bstep (se 2 (by rfl) ⟨217131, by rfl⟩ : syracuseStep 579017 = 434263) B434263
theorem B1955339 : Blo 385764 1955339 := bstep (se 1 (by rfl) ⟨1466504, by rfl⟩ : syracuseStep 1955339 = 2933009) B2933009
theorem B579131 : Blo 385764 579131 := bstep (se 1 (by rfl) ⟨434348, by rfl⟩ : syracuseStep 579131 = 868697) B868697
theorem B874043 : Blo 385764 874043 := bstep (se 1 (by rfl) ⟨655532, by rfl⟩ : syracuseStep 874043 = 1311065) B1311065
theorem B415291 : Blo 385764 415291 := bstep (se 1 (by rfl) ⟨311468, by rfl⟩ : syracuseStep 415291 = 622937) B622937
theorem B579191 : Blo 385764 579191 := bstep (se 1 (by rfl) ⟨434393, by rfl⟩ : syracuseStep 579191 = 868787) B868787
theorem B579215 : Blo 385764 579215 := bstep (se 1 (by rfl) ⟨434411, by rfl⟩ : syracuseStep 579215 = 868823) B868823
theorem B1955501 : Blo 385764 1955501 := bstep (se 3 (by rfl) ⟨366656, by rfl⟩ : syracuseStep 1955501 = 733313) B733313
theorem B579257 : Blo 385764 579257 := bstep (se 2 (by rfl) ⟨217221, by rfl⟩ : syracuseStep 579257 = 434443) B434443
theorem B874169 : Blo 385764 874169 := bstep (se 2 (by rfl) ⟨327813, by rfl⟩ : syracuseStep 874169 = 655627) B655627
theorem B579335 : Blo 385764 579335 := bstep (se 1 (by rfl) ⟨434501, by rfl⟩ : syracuseStep 579335 = 869003) B869003
theorem B579371 : Blo 385764 579371 := bstep (se 1 (by rfl) ⟨434528, by rfl⟩ : syracuseStep 579371 = 869057) B869057
theorem B2217779 : Blo 385764 2217779 := bstep (se 1 (by rfl) ⟨1663334, by rfl⟩ : syracuseStep 2217779 = 3326669) B3326669
theorem B579401 : Blo 385764 579401 := bstep (se 2 (by rfl) ⟨217275, by rfl⟩ : syracuseStep 579401 = 434551) B434551
theorem B579515 : Blo 385764 579515 := bstep (se 1 (by rfl) ⟨434636, by rfl⟩ : syracuseStep 579515 = 869273) B869273
theorem B579575 : Blo 385764 579575 := bstep (se 1 (by rfl) ⟨434681, by rfl⟩ : syracuseStep 579575 = 869363) B869363
theorem B579599 : Blo 385764 579599 := bstep (se 1 (by rfl) ⟨434699, by rfl⟩ : syracuseStep 579599 = 869399) B869399
theorem B874511 : Blo 385764 874511 := bstep (se 1 (by rfl) ⟨655883, by rfl⟩ : syracuseStep 874511 = 1311767) B1311767
theorem B874529 : Blo 385764 874529 := bstep (se 2 (by rfl) ⟨327948, by rfl⟩ : syracuseStep 874529 = 655897) B655897
theorem B87447605 : Blo 385764 87447605 := bstep (se 5 (by rfl) ⟨4099106, by rfl⟩ : syracuseStep 87447605 = 8198213) B8198213
theorem B579641 : Blo 385764 579641 := bstep (se 2 (by rfl) ⟨217365, by rfl⟩ : syracuseStep 579641 = 434731) B434731
theorem B579719 : Blo 385764 579719 := bstep (se 1 (by rfl) ⟨434789, by rfl⟩ : syracuseStep 579719 = 869579) B869579
theorem B1104025 : Blo 385764 1104025 := bstep (se 2 (by rfl) ⟨414009, by rfl⟩ : syracuseStep 1104025 = 828019) B828019
theorem B579755 : Blo 385764 579755 := bstep (se 1 (by rfl) ⟨434816, by rfl⟩ : syracuseStep 579755 = 869633) B869633
theorem B579785 : Blo 385764 579785 := bstep (se 2 (by rfl) ⟨217419, by rfl⟩ : syracuseStep 579785 = 434839) B434839
theorem B579899 : Blo 385764 579899 := bstep (se 1 (by rfl) ⟨434924, by rfl⟩ : syracuseStep 579899 = 869849) B869849
theorem B579959 : Blo 385764 579959 := bstep (se 1 (by rfl) ⟨434969, by rfl⟩ : syracuseStep 579959 = 869939) B869939
theorem B874871 : Blo 385764 874871 := bstep (se 1 (by rfl) ⟨656153, by rfl⟩ : syracuseStep 874871 = 1312307) B1312307
theorem B579983 : Blo 385764 579983 := bstep (se 1 (by rfl) ⟨434987, by rfl⟩ : syracuseStep 579983 = 869975) B869975
theorem B580025 : Blo 385764 580025 := bstep (se 2 (by rfl) ⟨217509, by rfl⟩ : syracuseStep 580025 = 435019) B435019
theorem B580103 : Blo 385764 580103 := bstep (se 1 (by rfl) ⟨435077, by rfl⟩ : syracuseStep 580103 = 870155) B870155
theorem B580139 : Blo 385764 580139 := bstep (se 1 (by rfl) ⟨435104, by rfl⟩ : syracuseStep 580139 = 870209) B870209
theorem B875051 : Blo 385764 875051 := bstep (se 1 (by rfl) ⟨656288, by rfl⟩ : syracuseStep 875051 = 1312577) B1312577
theorem B580169 : Blo 385764 580169 := bstep (se 2 (by rfl) ⟨217563, by rfl⟩ : syracuseStep 580169 = 435127) B435127
theorem B580283 : Blo 385764 580283 := bstep (se 1 (by rfl) ⟨435212, by rfl⟩ : syracuseStep 580283 = 870425) B870425
theorem B580343 : Blo 385764 580343 := bstep (se 1 (by rfl) ⟨435257, by rfl⟩ : syracuseStep 580343 = 870515) B870515
theorem B1104641 : Blo 385764 1104641 := bstep (se 2 (by rfl) ⟨414240, by rfl⟩ : syracuseStep 1104641 = 828481) B828481
theorem B580367 : Blo 385764 580367 := bstep (se 1 (by rfl) ⟨435275, by rfl⟩ : syracuseStep 580367 = 870551) B870551
theorem B580409 : Blo 385764 580409 := bstep (se 2 (by rfl) ⟨217653, by rfl⟩ : syracuseStep 580409 = 435307) B435307
theorem B580487 : Blo 385764 580487 := bstep (se 1 (by rfl) ⟨435365, by rfl⟩ : syracuseStep 580487 = 870731) B870731
theorem B875411 : Blo 385764 875411 := bstep (se 1 (by rfl) ⟨656558, by rfl⟩ : syracuseStep 875411 = 1313117) B1313117
theorem B580523 : Blo 385764 580523 := bstep (se 1 (by rfl) ⟨435392, by rfl⟩ : syracuseStep 580523 = 870785) B870785
theorem B580553 : Blo 385764 580553 := bstep (se 2 (by rfl) ⟨217707, by rfl⟩ : syracuseStep 580553 = 435415) B435415
theorem B875465 : Blo 385764 875465 := bstep (se 2 (by rfl) ⟨328299, by rfl⟩ : syracuseStep 875465 = 656599) B656599
theorem B580667 : Blo 385764 580667 := bstep (se 1 (by rfl) ⟨435500, by rfl⟩ : syracuseStep 580667 = 871001) B871001
theorem B1465411 : Blo 385764 1465411 := bstep (se 1 (by rfl) ⟨1099058, by rfl⟩ : syracuseStep 1465411 = 2198117) B2198117
theorem B580727 : Blo 385764 580727 := bstep (se 1 (by rfl) ⟨435545, by rfl⟩ : syracuseStep 580727 = 871091) B871091
theorem B580751 : Blo 385764 580751 := bstep (se 1 (by rfl) ⟨435563, by rfl⟩ : syracuseStep 580751 = 871127) B871127
theorem B580793 : Blo 385764 580793 := bstep (se 2 (by rfl) ⟨217797, by rfl⟩ : syracuseStep 580793 = 435595) B435595
theorem B11164877 : Blo 385764 11164877 := bstep (se 3 (by rfl) ⟨2093414, by rfl⟩ : syracuseStep 11164877 = 4186829) B4186829
theorem B2219237 : Blo 385764 2219237 := bstep (se 4 (by rfl) ⟨208053, by rfl⟩ : syracuseStep 2219237 = 416107) B416107
theorem B1957121 : Blo 385764 1957121 := bstep (se 2 (by rfl) ⟨733920, by rfl⟩ : syracuseStep 1957121 = 1467841) B1467841
theorem B580871 : Blo 385764 580871 := bstep (se 1 (by rfl) ⟨435653, by rfl⟩ : syracuseStep 580871 = 871307) B871307
theorem B1662241 : Blo 385764 1662241 := bstep (se 2 (by rfl) ⟨623340, by rfl⟩ : syracuseStep 1662241 = 1246681) B1246681
theorem B580907 : Blo 385764 580907 := bstep (se 1 (by rfl) ⟨435680, by rfl⟩ : syracuseStep 580907 = 871361) B871361
theorem B580937 : Blo 385764 580937 := bstep (se 2 (by rfl) ⟨217851, by rfl⟩ : syracuseStep 580937 = 435703) B435703
theorem B1465715 : Blo 385764 1465715 := bstep (se 1 (by rfl) ⟨1099286, by rfl⟩ : syracuseStep 1465715 = 2198573) B2198573
theorem B941465 : Blo 385764 941465 := bstep (se 2 (by rfl) ⟨353049, by rfl⟩ : syracuseStep 941465 = 706099) B706099
theorem B581051 : Blo 385764 581051 := bstep (se 1 (by rfl) ⟨435788, by rfl⟩ : syracuseStep 581051 = 871577) B871577
theorem B581111 : Blo 385764 581111 := bstep (se 1 (by rfl) ⟨435833, by rfl⟩ : syracuseStep 581111 = 871667) B871667
theorem B581135 : Blo 385764 581135 := bstep (se 1 (by rfl) ⟨435851, by rfl⟩ : syracuseStep 581135 = 871703) B871703
theorem B581177 : Blo 385764 581177 := bstep (se 2 (by rfl) ⟨217941, by rfl⟩ : syracuseStep 581177 = 435883) B435883
theorem B581255 : Blo 385764 581255 := bstep (se 1 (by rfl) ⟨435941, by rfl⟩ : syracuseStep 581255 = 871883) B871883
theorem B876167 : Blo 385764 876167 := bstep (se 1 (by rfl) ⟨657125, by rfl⟩ : syracuseStep 876167 = 1314251) B1314251
theorem B581291 : Blo 385764 581291 := bstep (se 1 (by rfl) ⟨435968, by rfl⟩ : syracuseStep 581291 = 871937) B871937
theorem B581321 : Blo 385764 581321 := bstep (se 2 (by rfl) ⟨217995, by rfl⟩ : syracuseStep 581321 = 435991) B435991
theorem B1105609 : Blo 385764 1105609 := bstep (se 2 (by rfl) ⟨414603, by rfl⟩ : syracuseStep 1105609 = 829207) B829207
theorem B9985841 : Blo 385764 9985841 := bstep (se 2 (by rfl) ⟨3744690, by rfl⟩ : syracuseStep 9985841 = 7489381) B7489381
theorem B1466171 : Blo 385764 1466171 := bstep (se 1 (by rfl) ⟨1099628, by rfl⟩ : syracuseStep 1466171 = 2199257) B2199257
theorem B581435 : Blo 385764 581435 := bstep (se 1 (by rfl) ⟨436076, by rfl⟩ : syracuseStep 581435 = 872153) B872153
theorem B876347 : Blo 385764 876347 := bstep (se 1 (by rfl) ⟨657260, by rfl⟩ : syracuseStep 876347 = 1314521) B1314521
theorem B581495 : Blo 385764 581495 := bstep (se 1 (by rfl) ⟨436121, by rfl⟩ : syracuseStep 581495 = 872243) B872243
theorem B581519 : Blo 385764 581519 := bstep (se 1 (by rfl) ⟨436139, by rfl⟩ : syracuseStep 581519 = 872279) B872279
theorem B1302425 : Blo 385764 1302425 := bstep (se 2 (by rfl) ⟨488409, by rfl⟩ : syracuseStep 1302425 = 976819) B976819
theorem B581561 : Blo 385764 581561 := bstep (se 2 (by rfl) ⟨218085, by rfl⟩ : syracuseStep 581561 = 436171) B436171
theorem B876473 : Blo 385764 876473 := bstep (se 2 (by rfl) ⟨328677, by rfl⟩ : syracuseStep 876473 = 657355) B657355
theorem B581639 : Blo 385764 581639 := bstep (se 1 (by rfl) ⟨436229, by rfl⟩ : syracuseStep 581639 = 872459) B872459
theorem B8970263 : Blo 385764 8970263 := bstep (se 1 (by rfl) ⟨6727697, by rfl⟩ : syracuseStep 8970263 = 13455395) B13455395
theorem B1957931 : Blo 385764 1957931 := bstep (se 1 (by rfl) ⟨1468448, by rfl⟩ : syracuseStep 1957931 = 2936897) B2936897
theorem B581675 : Blo 385764 581675 := bstep (se 1 (by rfl) ⟨436256, by rfl⟩ : syracuseStep 581675 = 872513) B872513
theorem B581705 : Blo 385764 581705 := bstep (se 2 (by rfl) ⟨218139, by rfl⟩ : syracuseStep 581705 = 436279) B436279
theorem B581819 : Blo 385764 581819 := bstep (se 1 (by rfl) ⟨436364, by rfl⟩ : syracuseStep 581819 = 872729) B872729
theorem B4186313 : Blo 385764 4186313 := bstep (se 2 (by rfl) ⟨1569867, by rfl⟩ : syracuseStep 4186313 = 3139735) B3139735
theorem B581879 : Blo 385764 581879 := bstep (se 1 (by rfl) ⟨436409, by rfl⟩ : syracuseStep 581879 = 872819) B872819
theorem B581903 : Blo 385764 581903 := bstep (se 1 (by rfl) ⟨436427, by rfl⟩ : syracuseStep 581903 = 872855) B872855
theorem B876815 : Blo 385764 876815 := bstep (se 1 (by rfl) ⟨657611, by rfl⟩ : syracuseStep 876815 = 1315223) B1315223
theorem B1466657 : Blo 385764 1466657 := bstep (se 2 (by rfl) ⟨549996, by rfl⟩ : syracuseStep 1466657 = 1099993) B1099993
theorem B876833 : Blo 385764 876833 := bstep (se 2 (by rfl) ⟨328812, by rfl⟩ : syracuseStep 876833 = 657625) B657625
theorem B581945 : Blo 385764 581945 := bstep (se 2 (by rfl) ⟨218229, by rfl⟩ : syracuseStep 581945 = 436459) B436459
theorem B1794419 : Blo 385764 1794419 := bstep (se 1 (by rfl) ⟨1345814, by rfl⟩ : syracuseStep 1794419 = 2691629) B2691629
theorem B582023 : Blo 385764 582023 := bstep (se 1 (by rfl) ⟨436517, by rfl⟩ : syracuseStep 582023 = 873035) B873035
theorem B582059 : Blo 385764 582059 := bstep (se 1 (by rfl) ⟨436544, by rfl⟩ : syracuseStep 582059 = 873089) B873089
theorem B582089 : Blo 385764 582089 := bstep (se 2 (by rfl) ⟨218283, by rfl⟩ : syracuseStep 582089 = 436567) B436567
theorem B549433 : Blo 385764 549433 := bstep (se 2 (by rfl) ⟨206037, by rfl⟩ : syracuseStep 549433 = 412075) B412075
theorem B582203 : Blo 385764 582203 := bstep (se 1 (by rfl) ⟨436652, by rfl⟩ : syracuseStep 582203 = 873305) B873305
theorem B1303127 : Blo 385764 1303127 := bstep (se 1 (by rfl) ⟨977345, by rfl⟩ : syracuseStep 1303127 = 1954691) B1954691
theorem B582263 : Blo 385764 582263 := bstep (se 1 (by rfl) ⟨436697, by rfl⟩ : syracuseStep 582263 = 873395) B873395
theorem B582287 : Blo 385764 582287 := bstep (se 1 (by rfl) ⟨436715, by rfl⟩ : syracuseStep 582287 = 873431) B873431
theorem B582329 : Blo 385764 582329 := bstep (se 2 (by rfl) ⟨218373, by rfl⟩ : syracuseStep 582329 = 436747) B436747
theorem B1860353 : Blo 385764 1860353 := bstep (se 2 (by rfl) ⟨697632, by rfl⟩ : syracuseStep 1860353 = 1395265) B1395265
theorem B385799 : Blo 385764 385799 := bstep (se 1 (by rfl) ⟨289349, by rfl⟩ : syracuseStep 385799 = 578699) B578699
theorem B582407 : Blo 385764 582407 := bstep (se 1 (by rfl) ⟨436805, by rfl⟩ : syracuseStep 582407 = 873611) B873611
theorem B385807 : Blo 385764 385807 := bstep (se 1 (by rfl) ⟨289355, by rfl⟩ : syracuseStep 385807 = 578711) B578711
theorem B582443 : Blo 385764 582443 := bstep (se 1 (by rfl) ⟨436832, by rfl⟩ : syracuseStep 582443 = 873665) B873665
theorem B385851 : Blo 385764 385851 := bstep (se 1 (by rfl) ⟨289388, by rfl⟩ : syracuseStep 385851 = 578777) B578777
theorem B582473 : Blo 385764 582473 := bstep (se 2 (by rfl) ⟨218427, by rfl⟩ : syracuseStep 582473 = 436855) B436855
theorem B385927 : Blo 385764 385927 := bstep (se 1 (by rfl) ⟨289445, by rfl⟩ : syracuseStep 385927 = 578891) B578891
theorem B385935 : Blo 385764 385935 := bstep (se 1 (by rfl) ⟨289451, by rfl⟩ : syracuseStep 385935 = 578903) B578903
theorem B1663897 : Blo 385764 1663897 := bstep (se 2 (by rfl) ⟨623961, by rfl⟩ : syracuseStep 1663897 = 1247923) B1247923
theorem B385979 : Blo 385764 385979 := bstep (se 1 (by rfl) ⟨289484, by rfl⟩ : syracuseStep 385979 = 578969) B578969
theorem B582587 : Blo 385764 582587 := bstep (se 1 (by rfl) ⟨436940, by rfl⟩ : syracuseStep 582587 = 873881) B873881
theorem B582647 : Blo 385764 582647 := bstep (se 1 (by rfl) ⟨436985, by rfl⟩ : syracuseStep 582647 = 873971) B873971
theorem B4482053 : Blo 385764 4482053 := bstep (se 4 (by rfl) ⟨420192, by rfl⟩ : syracuseStep 4482053 = 840385) B840385
theorem B386055 : Blo 385764 386055 := bstep (se 1 (by rfl) ⟨289541, by rfl⟩ : syracuseStep 386055 = 579083) B579083
theorem B386063 : Blo 385764 386063 := bstep (se 1 (by rfl) ⟨289547, by rfl⟩ : syracuseStep 386063 = 579095) B579095
theorem B582671 : Blo 385764 582671 := bstep (se 1 (by rfl) ⟨437003, by rfl⟩ : syracuseStep 582671 = 874007) B874007
theorem B582713 : Blo 385764 582713 := bstep (se 2 (by rfl) ⟨218517, by rfl⟩ : syracuseStep 582713 = 437035) B437035
theorem B386107 : Blo 385764 386107 := bstep (se 1 (by rfl) ⟨289580, by rfl⟩ : syracuseStep 386107 = 579161) B579161
theorem B1303613 : Blo 385764 1303613 := bstep (se 3 (by rfl) ⟨244427, by rfl⟩ : syracuseStep 1303613 = 488855) B488855
theorem B386183 : Blo 385764 386183 := bstep (se 1 (by rfl) ⟨289637, by rfl⟩ : syracuseStep 386183 = 579275) B579275
theorem B582791 : Blo 385764 582791 := bstep (se 1 (by rfl) ⟨437093, by rfl⟩ : syracuseStep 582791 = 874187) B874187
theorem B386191 : Blo 385764 386191 := bstep (se 1 (by rfl) ⟨289643, by rfl⟩ : syracuseStep 386191 = 579287) B579287
theorem B582827 : Blo 385764 582827 := bstep (se 1 (by rfl) ⟨437120, by rfl⟩ : syracuseStep 582827 = 874241) B874241
theorem B386235 : Blo 385764 386235 := bstep (se 1 (by rfl) ⟨289676, by rfl⟩ : syracuseStep 386235 = 579353) B579353
theorem B582857 : Blo 385764 582857 := bstep (se 2 (by rfl) ⟨218571, by rfl⟩ : syracuseStep 582857 = 437143) B437143
theorem B1467629 : Blo 385764 1467629 := bstep (se 3 (by rfl) ⟨275180, by rfl⟩ : syracuseStep 1467629 = 550361) B550361
theorem B5596397 : Blo 385764 5596397 := bstep (se 3 (by rfl) ⟨1049324, by rfl⟩ : syracuseStep 5596397 = 2098649) B2098649
theorem B386311 : Blo 385764 386311 := bstep (se 1 (by rfl) ⟨289733, by rfl⟩ : syracuseStep 386311 = 579467) B579467
theorem B1107215 : Blo 385764 1107215 := bstep (se 1 (by rfl) ⟨830411, by rfl⟩ : syracuseStep 1107215 = 1660823) B1660823
theorem B386319 : Blo 385764 386319 := bstep (se 1 (by rfl) ⟨289739, by rfl⟩ : syracuseStep 386319 = 579479) B579479
theorem B1238287 : Blo 385764 1238287 := bstep (se 1 (by rfl) ⟨928715, by rfl⟩ : syracuseStep 1238287 = 1857431) B1857431
theorem B386363 : Blo 385764 386363 := bstep (se 1 (by rfl) ⟨289772, by rfl⟩ : syracuseStep 386363 = 579545) B579545
theorem B1959227 : Blo 385764 1959227 := bstep (se 1 (by rfl) ⟨1469420, by rfl⟩ : syracuseStep 1959227 = 2938841) B2938841
theorem B3728699 : Blo 385764 3728699 := bstep (se 1 (by rfl) ⟨2796524, by rfl⟩ : syracuseStep 3728699 = 5593049) B5593049
theorem B582971 : Blo 385764 582971 := bstep (se 1 (by rfl) ⟨437228, by rfl⟩ : syracuseStep 582971 = 874457) B874457
theorem B583031 : Blo 385764 583031 := bstep (se 1 (by rfl) ⟨437273, by rfl⟩ : syracuseStep 583031 = 874547) B874547
theorem B386439 : Blo 385764 386439 := bstep (se 1 (by rfl) ⟨289829, by rfl⟩ : syracuseStep 386439 = 579659) B579659
theorem B386447 : Blo 385764 386447 := bstep (se 1 (by rfl) ⟨289835, by rfl⟩ : syracuseStep 386447 = 579671) B579671
theorem B583055 : Blo 385764 583055 := bstep (se 1 (by rfl) ⟨437291, by rfl⟩ : syracuseStep 583055 = 874583) B874583
theorem B583097 : Blo 385764 583097 := bstep (se 2 (by rfl) ⟨218661, by rfl⟩ : syracuseStep 583097 = 437323) B437323
theorem B386491 : Blo 385764 386491 := bstep (se 1 (by rfl) ⟨289868, by rfl⟩ : syracuseStep 386491 = 579737) B579737
theorem B1959389 : Blo 385764 1959389 := bstep (se 3 (by rfl) ⟨367385, by rfl⟩ : syracuseStep 1959389 = 734771) B734771
theorem B386567 : Blo 385764 386567 := bstep (se 1 (by rfl) ⟨289925, by rfl⟩ : syracuseStep 386567 = 579851) B579851
theorem B583175 : Blo 385764 583175 := bstep (se 1 (by rfl) ⟨437381, by rfl⟩ : syracuseStep 583175 = 874763) B874763
theorem B386575 : Blo 385764 386575 := bstep (se 1 (by rfl) ⟨289931, by rfl⟩ : syracuseStep 386575 = 579863) B579863
theorem B16934429 : Blo 385764 16934429 := bstep (se 3 (by rfl) ⟨3175205, by rfl⟩ : syracuseStep 16934429 = 6350411) B6350411
theorem B583211 : Blo 385764 583211 := bstep (se 1 (by rfl) ⟨437408, by rfl⟩ : syracuseStep 583211 = 874817) B874817
theorem B386619 : Blo 385764 386619 := bstep (se 1 (by rfl) ⟨289964, by rfl⟩ : syracuseStep 386619 = 579929) B579929
theorem B583241 : Blo 385764 583241 := bstep (se 2 (by rfl) ⟨218715, by rfl⟩ : syracuseStep 583241 = 437431) B437431
theorem B386695 : Blo 385764 386695 := bstep (se 1 (by rfl) ⟨290021, by rfl⟩ : syracuseStep 386695 = 580043) B580043
theorem B386703 : Blo 385764 386703 := bstep (se 1 (by rfl) ⟨290027, by rfl⟩ : syracuseStep 386703 = 580055) B580055
theorem B386747 : Blo 385764 386747 := bstep (se 1 (by rfl) ⟨290060, by rfl⟩ : syracuseStep 386747 = 580121) B580121
theorem B583355 : Blo 385764 583355 := bstep (se 1 (by rfl) ⟨437516, by rfl⟩ : syracuseStep 583355 = 875033) B875033
theorem B583415 : Blo 385764 583415 := bstep (se 1 (by rfl) ⟨437561, by rfl⟩ : syracuseStep 583415 = 875123) B875123
theorem B386823 : Blo 385764 386823 := bstep (se 1 (by rfl) ⟨290117, by rfl⟩ : syracuseStep 386823 = 580235) B580235
theorem B386831 : Blo 385764 386831 := bstep (se 1 (by rfl) ⟨290123, by rfl⟩ : syracuseStep 386831 = 580247) B580247
theorem B583439 : Blo 385764 583439 := bstep (se 1 (by rfl) ⟨437579, by rfl⟩ : syracuseStep 583439 = 875159) B875159
theorem B1959713 : Blo 385764 1959713 := bstep (se 2 (by rfl) ⟨734892, by rfl⟩ : syracuseStep 1959713 = 1469785) B1469785
theorem B1009441 : Blo 385764 1009441 := bstep (se 2 (by rfl) ⟨378540, by rfl⟩ : syracuseStep 1009441 = 757081) B757081
theorem B583481 : Blo 385764 583481 := bstep (se 2 (by rfl) ⟨218805, by rfl⟩ : syracuseStep 583481 = 437611) B437611
theorem B386875 : Blo 385764 386875 := bstep (se 1 (by rfl) ⟨290156, by rfl⟩ : syracuseStep 386875 = 580313) B580313
theorem B386951 : Blo 385764 386951 := bstep (se 1 (by rfl) ⟨290213, by rfl⟩ : syracuseStep 386951 = 580427) B580427
theorem B583559 : Blo 385764 583559 := bstep (se 1 (by rfl) ⟨437669, by rfl⟩ : syracuseStep 583559 = 875339) B875339
theorem B386959 : Blo 385764 386959 := bstep (se 1 (by rfl) ⟨290219, by rfl⟩ : syracuseStep 386959 = 580439) B580439
theorem B1468313 : Blo 385764 1468313 := bstep (se 2 (by rfl) ⟨550617, by rfl⟩ : syracuseStep 1468313 = 1101235) B1101235
theorem B583595 : Blo 385764 583595 := bstep (se 1 (by rfl) ⟨437696, by rfl⟩ : syracuseStep 583595 = 875393) B875393
theorem B387003 : Blo 385764 387003 := bstep (se 1 (by rfl) ⟨290252, by rfl⟩ : syracuseStep 387003 = 580505) B580505
theorem B583625 : Blo 385764 583625 := bstep (se 2 (by rfl) ⟨218859, by rfl⟩ : syracuseStep 583625 = 437719) B437719
theorem B550919 : Blo 385764 550919 := bstep (se 1 (by rfl) ⟨413189, by rfl⟩ : syracuseStep 550919 = 826379) B826379
theorem B387079 : Blo 385764 387079 := bstep (se 1 (by rfl) ⟨290309, by rfl⟩ : syracuseStep 387079 = 580619) B580619
theorem B387087 : Blo 385764 387087 := bstep (se 1 (by rfl) ⟨290315, by rfl⟩ : syracuseStep 387087 = 580631) B580631
theorem B2353195 : Blo 385764 2353195 := bstep (se 1 (by rfl) ⟨1764896, by rfl⟩ : syracuseStep 2353195 = 3529793) B3529793
theorem B387131 : Blo 385764 387131 := bstep (se 1 (by rfl) ⟨290348, by rfl⟩ : syracuseStep 387131 = 580697) B580697
theorem B583739 : Blo 385764 583739 := bstep (se 1 (by rfl) ⟨437804, by rfl⟩ : syracuseStep 583739 = 875609) B875609
theorem B583799 : Blo 385764 583799 := bstep (se 1 (by rfl) ⟨437849, by rfl⟩ : syracuseStep 583799 = 875699) B875699
theorem B387207 : Blo 385764 387207 := bstep (se 1 (by rfl) ⟨290405, by rfl⟩ : syracuseStep 387207 = 580811) B580811
theorem B387215 : Blo 385764 387215 := bstep (se 1 (by rfl) ⟨290411, by rfl⟩ : syracuseStep 387215 = 580823) B580823
theorem B583823 : Blo 385764 583823 := bstep (se 1 (by rfl) ⟨437867, by rfl⟩ : syracuseStep 583823 = 875735) B875735
theorem B583865 : Blo 385764 583865 := bstep (se 2 (by rfl) ⟨218949, by rfl⟩ : syracuseStep 583865 = 437899) B437899
theorem B387259 : Blo 385764 387259 := bstep (se 1 (by rfl) ⟨290444, by rfl⟩ : syracuseStep 387259 = 580889) B580889
theorem B387335 : Blo 385764 387335 := bstep (se 1 (by rfl) ⟨290501, by rfl⟩ : syracuseStep 387335 = 581003) B581003
theorem B583943 : Blo 385764 583943 := bstep (se 1 (by rfl) ⟨437957, by rfl⟩ : syracuseStep 583943 = 875915) B875915
theorem B387343 : Blo 385764 387343 := bstep (se 1 (by rfl) ⟨290507, by rfl⟩ : syracuseStep 387343 = 581015) B581015
theorem B583979 : Blo 385764 583979 := bstep (se 1 (by rfl) ⟨437984, by rfl⟩ : syracuseStep 583979 = 875969) B875969
theorem B551227 : Blo 385764 551227 := bstep (se 1 (by rfl) ⟨413420, by rfl⟩ : syracuseStep 551227 = 826841) B826841
theorem B387387 : Blo 385764 387387 := bstep (se 1 (by rfl) ⟨290540, by rfl⟩ : syracuseStep 387387 = 581081) B581081
theorem B584009 : Blo 385764 584009 := bstep (se 2 (by rfl) ⟨219003, by rfl⟩ : syracuseStep 584009 = 438007) B438007
theorem B1042807 : Blo 385764 1042807 := bstep (se 1 (by rfl) ⟨782105, by rfl⟩ : syracuseStep 1042807 = 1564211) B1564211
theorem B1108343 : Blo 385764 1108343 := bstep (se 1 (by rfl) ⟨831257, by rfl⟩ : syracuseStep 1108343 = 1662515) B1662515
theorem B387463 : Blo 385764 387463 := bstep (se 1 (by rfl) ⟨290597, by rfl⟩ : syracuseStep 387463 = 581195) B581195
theorem B387471 : Blo 385764 387471 := bstep (se 1 (by rfl) ⟨290603, by rfl⟩ : syracuseStep 387471 = 581207) B581207
theorem B977305 : Blo 385764 977305 := bstep (se 2 (by rfl) ⟨366489, by rfl⟩ : syracuseStep 977305 = 732979) B732979
theorem B1305017 : Blo 385764 1305017 := bstep (se 2 (by rfl) ⟨489381, by rfl⟩ : syracuseStep 1305017 = 978763) B978763
theorem B387515 : Blo 385764 387515 := bstep (se 1 (by rfl) ⟨290636, by rfl⟩ : syracuseStep 387515 = 581273) B581273
theorem B584123 : Blo 385764 584123 := bstep (se 1 (by rfl) ⟨438092, by rfl⟩ : syracuseStep 584123 = 876185) B876185
theorem B584183 : Blo 385764 584183 := bstep (se 1 (by rfl) ⟨438137, by rfl⟩ : syracuseStep 584183 = 876275) B876275
theorem B387591 : Blo 385764 387591 := bstep (se 1 (by rfl) ⟨290693, by rfl⟩ : syracuseStep 387591 = 581387) B581387
theorem B387599 : Blo 385764 387599 := bstep (se 1 (by rfl) ⟨290699, by rfl⟩ : syracuseStep 387599 = 581399) B581399
theorem B584207 : Blo 385764 584207 := bstep (se 1 (by rfl) ⟨438155, by rfl⟩ : syracuseStep 584207 = 876311) B876311
theorem B584249 : Blo 385764 584249 := bstep (se 2 (by rfl) ⟨219093, by rfl⟩ : syracuseStep 584249 = 438187) B438187
theorem B977467 : Blo 385764 977467 := bstep (se 1 (by rfl) ⟨733100, by rfl⟩ : syracuseStep 977467 = 1466201) B1466201
theorem B387643 : Blo 385764 387643 := bstep (se 1 (by rfl) ⟨290732, by rfl⟩ : syracuseStep 387643 = 581465) B581465
theorem B387719 : Blo 385764 387719 := bstep (se 1 (by rfl) ⟨290789, by rfl⟩ : syracuseStep 387719 = 581579) B581579
theorem B584327 : Blo 385764 584327 := bstep (se 1 (by rfl) ⟨438245, by rfl⟩ : syracuseStep 584327 = 876491) B876491
theorem B387727 : Blo 385764 387727 := bstep (se 1 (by rfl) ⟨290795, by rfl⟩ : syracuseStep 387727 = 581591) B581591
theorem B1174169 : Blo 385764 1174169 := bstep (se 2 (by rfl) ⟨440313, by rfl⟩ : syracuseStep 1174169 = 880627) B880627
theorem B584363 : Blo 385764 584363 := bstep (se 1 (by rfl) ⟨438272, by rfl⟩ : syracuseStep 584363 = 876545) B876545
theorem B387771 : Blo 385764 387771 := bstep (se 1 (by rfl) ⟨290828, by rfl⟩ : syracuseStep 387771 = 581657) B581657
theorem B977609 : Blo 385764 977609 := bstep (se 2 (by rfl) ⟨366603, by rfl⟩ : syracuseStep 977609 = 733207) B733207
theorem B584393 : Blo 385764 584393 := bstep (se 2 (by rfl) ⟨219147, by rfl⟩ : syracuseStep 584393 = 438295) B438295
theorem B1960685 : Blo 385764 1960685 := bstep (se 3 (by rfl) ⟨367628, by rfl⟩ : syracuseStep 1960685 = 735257) B735257
theorem B387847 : Blo 385764 387847 := bstep (se 1 (by rfl) ⟨290885, by rfl⟩ : syracuseStep 387847 = 581771) B581771
theorem B387855 : Blo 385764 387855 := bstep (se 1 (by rfl) ⟨290891, by rfl⟩ : syracuseStep 387855 = 581783) B581783
theorem B387899 : Blo 385764 387899 := bstep (se 1 (by rfl) ⟨290924, by rfl⟩ : syracuseStep 387899 = 581849) B581849
theorem B584507 : Blo 385764 584507 := bstep (se 1 (by rfl) ⟨438380, by rfl⟩ : syracuseStep 584507 = 876761) B876761
theorem B1469299 : Blo 385764 1469299 := bstep (se 1 (by rfl) ⟨1101974, by rfl⟩ : syracuseStep 1469299 = 2203949) B2203949
theorem B584567 : Blo 385764 584567 := bstep (se 1 (by rfl) ⟨438425, by rfl⟩ : syracuseStep 584567 = 876851) B876851
theorem B387975 : Blo 385764 387975 := bstep (se 1 (by rfl) ⟨290981, by rfl⟩ : syracuseStep 387975 = 581963) B581963
theorem B387983 : Blo 385764 387983 := bstep (se 1 (by rfl) ⟨290987, by rfl⟩ : syracuseStep 387983 = 581975) B581975
theorem B584591 : Blo 385764 584591 := bstep (se 1 (by rfl) ⟨438443, by rfl⟩ : syracuseStep 584591 = 876887) B876887
theorem B584633 : Blo 385764 584633 := bstep (se 2 (by rfl) ⟨219237, by rfl⟩ : syracuseStep 584633 = 438475) B438475
theorem B388027 : Blo 385764 388027 := bstep (se 1 (by rfl) ⟨291020, by rfl⟩ : syracuseStep 388027 = 582041) B582041
theorem B388103 : Blo 385764 388103 := bstep (se 1 (by rfl) ⟨291077, by rfl⟩ : syracuseStep 388103 = 582155) B582155
theorem B1305611 : Blo 385764 1305611 := bstep (se 1 (by rfl) ⟨979208, by rfl⟩ : syracuseStep 1305611 = 1958417) B1958417
theorem B388111 : Blo 385764 388111 := bstep (se 1 (by rfl) ⟨291083, by rfl⟩ : syracuseStep 388111 = 582167) B582167
theorem B977953 : Blo 385764 977953 := bstep (se 2 (by rfl) ⟨366732, by rfl⟩ : syracuseStep 977953 = 733465) B733465
theorem B1076267 : Blo 385764 1076267 := bstep (se 1 (by rfl) ⟨807200, by rfl⟩ : syracuseStep 1076267 = 1614401) B1614401
theorem B388155 : Blo 385764 388155 := bstep (se 1 (by rfl) ⟨291116, by rfl⟩ : syracuseStep 388155 = 582233) B582233
theorem B420923 : Blo 385764 420923 := bstep (se 1 (by rfl) ⟨315692, by rfl⟩ : syracuseStep 420923 = 631385) B631385
theorem B1305719 : Blo 385764 1305719 := bstep (se 1 (by rfl) ⟨979289, by rfl⟩ : syracuseStep 1305719 = 1958579) B1958579
theorem B388231 : Blo 385764 388231 := bstep (se 1 (by rfl) ⟨291173, by rfl⟩ : syracuseStep 388231 = 582347) B582347
theorem B388239 : Blo 385764 388239 := bstep (se 1 (by rfl) ⟨291179, by rfl⟩ : syracuseStep 388239 = 582359) B582359
theorem B388283 : Blo 385764 388283 := bstep (se 1 (by rfl) ⟨291212, by rfl⟩ : syracuseStep 388283 = 582425) B582425
theorem B388359 : Blo 385764 388359 := bstep (se 1 (by rfl) ⟨291269, by rfl⟩ : syracuseStep 388359 = 582539) B582539
theorem B388367 : Blo 385764 388367 := bstep (se 1 (by rfl) ⟨291275, by rfl⟩ : syracuseStep 388367 = 582551) B582551
theorem B1404175 : Blo 385764 1404175 := bstep (se 1 (by rfl) ⟨1053131, by rfl⟩ : syracuseStep 1404175 = 2106263) B2106263
theorem B388411 : Blo 385764 388411 := bstep (se 1 (by rfl) ⟨291308, by rfl⟩ : syracuseStep 388411 = 582617) B582617
theorem B388487 : Blo 385764 388487 := bstep (se 1 (by rfl) ⟨291365, by rfl⟩ : syracuseStep 388487 = 582731) B582731
theorem B388495 : Blo 385764 388495 := bstep (se 1 (by rfl) ⟨291371, by rfl⟩ : syracuseStep 388495 = 582743) B582743
theorem B552377 : Blo 385764 552377 := bstep (se 2 (by rfl) ⟨207141, by rfl⟩ : syracuseStep 552377 = 414283) B414283
theorem B388539 : Blo 385764 388539 := bstep (se 1 (by rfl) ⟨291404, by rfl⟩ : syracuseStep 388539 = 582809) B582809
theorem B388615 : Blo 385764 388615 := bstep (se 1 (by rfl) ⟨291461, by rfl⟩ : syracuseStep 388615 = 582923) B582923
theorem B388623 : Blo 385764 388623 := bstep (se 1 (by rfl) ⟨291467, by rfl⟩ : syracuseStep 388623 = 582935) B582935
theorem B1961495 : Blo 385764 1961495 := bstep (se 1 (by rfl) ⟨1471121, by rfl⟩ : syracuseStep 1961495 = 2942243) B2942243
theorem B388667 : Blo 385764 388667 := bstep (se 1 (by rfl) ⟨291500, by rfl⟩ : syracuseStep 388667 = 583001) B583001
theorem B978551 : Blo 385764 978551 := bstep (se 1 (by rfl) ⟨733913, by rfl⟩ : syracuseStep 978551 = 1467827) B1467827
theorem B1568375 : Blo 385764 1568375 := bstep (se 1 (by rfl) ⟨1176281, by rfl⟩ : syracuseStep 1568375 = 2352563) B2352563
theorem B388743 : Blo 385764 388743 := bstep (se 1 (by rfl) ⟨291557, by rfl⟩ : syracuseStep 388743 = 583115) B583115
theorem B388751 : Blo 385764 388751 := bstep (se 1 (by rfl) ⟨291563, by rfl⟩ : syracuseStep 388751 = 583127) B583127
theorem B552619 : Blo 385764 552619 := bstep (se 1 (by rfl) ⟨414464, by rfl⟩ : syracuseStep 552619 = 828929) B828929
theorem B388795 : Blo 385764 388795 := bstep (se 1 (by rfl) ⟨291596, by rfl⟩ : syracuseStep 388795 = 583193) B583193
theorem B1306313 : Blo 385764 1306313 := bstep (se 2 (by rfl) ⟨489867, by rfl⟩ : syracuseStep 1306313 = 979735) B979735
theorem B1601281 : Blo 385764 1601281 := bstep (se 2 (by rfl) ⟨600480, by rfl⟩ : syracuseStep 1601281 = 1200961) B1200961
theorem B388871 : Blo 385764 388871 := bstep (se 1 (by rfl) ⟨291653, by rfl⟩ : syracuseStep 388871 = 583307) B583307
theorem B388879 : Blo 385764 388879 := bstep (se 1 (by rfl) ⟨291659, by rfl⟩ : syracuseStep 388879 = 583319) B583319
theorem B388923 : Blo 385764 388923 := bstep (se 1 (by rfl) ⟨291692, by rfl⟩ : syracuseStep 388923 = 583385) B583385
theorem B388999 : Blo 385764 388999 := bstep (se 1 (by rfl) ⟨291749, by rfl⟩ : syracuseStep 388999 = 583499) B583499
theorem B389007 : Blo 385764 389007 := bstep (se 1 (by rfl) ⟨291755, by rfl⟩ : syracuseStep 389007 = 583511) B583511
theorem B389051 : Blo 385764 389051 := bstep (se 1 (by rfl) ⟨291788, by rfl⟩ : syracuseStep 389051 = 583577) B583577
theorem B1044481 : Blo 385764 1044481 := bstep (se 2 (by rfl) ⟨391680, by rfl⟩ : syracuseStep 1044481 = 783361) B783361
theorem B389127 : Blo 385764 389127 := bstep (se 1 (by rfl) ⟨291845, by rfl⟩ : syracuseStep 389127 = 583691) B583691
theorem B3731467 : Blo 385764 3731467 := bstep (se 1 (by rfl) ⟨2798600, by rfl⟩ : syracuseStep 3731467 = 5597201) B5597201
theorem B389135 : Blo 385764 389135 := bstep (se 1 (by rfl) ⟨291851, by rfl⟩ : syracuseStep 389135 = 583703) B583703
theorem B651307 : Blo 385764 651307 := bstep (se 1 (by rfl) ⟨488480, by rfl⟩ : syracuseStep 651307 = 976961) B976961
theorem B389179 : Blo 385764 389179 := bstep (se 1 (by rfl) ⟨291884, by rfl⟩ : syracuseStep 389179 = 583769) B583769
theorem B389255 : Blo 385764 389255 := bstep (se 1 (by rfl) ⟨291941, by rfl⟩ : syracuseStep 389255 = 583883) B583883
theorem B389263 : Blo 385764 389263 := bstep (se 1 (by rfl) ⟨291947, by rfl⟩ : syracuseStep 389263 = 583895) B583895
theorem B651449 : Blo 385764 651449 := bstep (se 2 (by rfl) ⟨244293, by rfl⟩ : syracuseStep 651449 = 488587) B488587
theorem B389307 : Blo 385764 389307 := bstep (se 1 (by rfl) ⟨291980, by rfl⟩ : syracuseStep 389307 = 583961) B583961
theorem B1765577 : Blo 385764 1765577 := bstep (se 2 (by rfl) ⟨662091, by rfl⟩ : syracuseStep 1765577 = 1324183) B1324183
theorem B389383 : Blo 385764 389383 := bstep (se 1 (by rfl) ⟨292037, by rfl⟩ : syracuseStep 389383 = 584075) B584075
theorem B389391 : Blo 385764 389391 := bstep (se 1 (by rfl) ⟨292043, by rfl⟩ : syracuseStep 389391 = 584087) B584087
theorem B389435 : Blo 385764 389435 := bstep (se 1 (by rfl) ⟨292076, by rfl⟩ : syracuseStep 389435 = 584153) B584153
theorem B618887 : Blo 385764 618887 := bstep (se 1 (by rfl) ⟨464165, by rfl⟩ : syracuseStep 618887 = 928331) B928331
theorem B1307015 : Blo 385764 1307015 := bstep (se 1 (by rfl) ⟨980261, by rfl⟩ : syracuseStep 1307015 = 1960523) B1960523
theorem B389511 : Blo 385764 389511 := bstep (se 1 (by rfl) ⟨292133, by rfl⟩ : syracuseStep 389511 = 584267) B584267
theorem B389519 : Blo 385764 389519 := bstep (se 1 (by rfl) ⟨292139, by rfl⟩ : syracuseStep 389519 = 584279) B584279
theorem B389563 : Blo 385764 389563 := bstep (se 1 (by rfl) ⟨292172, by rfl⟩ : syracuseStep 389563 = 584345) B584345
theorem B389639 : Blo 385764 389639 := bstep (se 1 (by rfl) ⟨292229, by rfl⟩ : syracuseStep 389639 = 584459) B584459
theorem B389647 : Blo 385764 389647 := bstep (se 1 (by rfl) ⟨292235, by rfl⟩ : syracuseStep 389647 = 584471) B584471
theorem B1864235 : Blo 385764 1864235 := bstep (se 1 (by rfl) ⟨1398176, by rfl⟩ : syracuseStep 1864235 = 2796353) B2796353
theorem B389691 : Blo 385764 389691 := bstep (se 1 (by rfl) ⟨292268, by rfl⟩ : syracuseStep 389691 = 584537) B584537
theorem B1307393 : Blo 385764 1307393 := bstep (se 2 (by rfl) ⟨490272, by rfl⟩ : syracuseStep 1307393 = 980545) B980545
theorem B652151 : Blo 385764 652151 := bstep (se 1 (by rfl) ⟨489113, by rfl⟩ : syracuseStep 652151 = 978227) B978227
theorem B979847 : Blo 385764 979847 := bstep (se 1 (by rfl) ⟨734885, by rfl⟩ : syracuseStep 979847 = 1469771) B1469771
theorem B979897 : Blo 385764 979897 := bstep (se 2 (by rfl) ⟨367461, by rfl⟩ : syracuseStep 979897 = 734923) B734923
theorem B553915 : Blo 385764 553915 := bstep (se 1 (by rfl) ⟨415436, by rfl⟩ : syracuseStep 553915 = 830873) B830873
theorem B1864657 : Blo 385764 1864657 := bstep (se 2 (by rfl) ⟨699246, by rfl⟩ : syracuseStep 1864657 = 1398493) B1398493
theorem B1471517 : Blo 385764 1471517 := bstep (se 3 (by rfl) ⟨275909, by rfl⟩ : syracuseStep 1471517 = 551819) B551819
theorem B619579 : Blo 385764 619579 := bstep (se 1 (by rfl) ⟨464684, by rfl⟩ : syracuseStep 619579 = 929369) B929369
theorem B619721 : Blo 385764 619721 := bstep (se 2 (by rfl) ⟨232395, by rfl⟩ : syracuseStep 619721 = 464791) B464791
theorem B2094281 : Blo 385764 2094281 := bstep (se 2 (by rfl) ⟨785355, by rfl⟩ : syracuseStep 2094281 = 1570711) B1570711
theorem B652603 : Blo 385764 652603 := bstep (se 1 (by rfl) ⟨489452, by rfl⟩ : syracuseStep 652603 = 978905) B978905
theorem B554359 : Blo 385764 554359 := bstep (se 1 (by rfl) ⟨415769, by rfl⟩ : syracuseStep 554359 = 831539) B831539
theorem B6714809 : Blo 385764 6714809 := bstep (se 2 (by rfl) ⟨2518053, by rfl⟩ : syracuseStep 6714809 = 5036107) B5036107
theorem B652745 : Blo 385764 652745 := bstep (se 2 (by rfl) ⟨244779, by rfl⟩ : syracuseStep 652745 = 489559) B489559
theorem B980495 : Blo 385764 980495 := bstep (se 1 (by rfl) ⟨735371, by rfl⟩ : syracuseStep 980495 = 1470743) B1470743
theorem B1308203 : Blo 385764 1308203 := bstep (se 1 (by rfl) ⟨981152, by rfl⟩ : syracuseStep 1308203 = 1962305) B1962305
theorem B3995237 : Blo 385764 3995237 := bstep (se 4 (by rfl) ⟨374553, by rfl⟩ : syracuseStep 3995237 = 749107) B749107
theorem B1472201 : Blo 385764 1472201 := bstep (se 2 (by rfl) ⟨552075, by rfl⟩ : syracuseStep 1472201 = 1104151) B1104151
theorem B1570745 : Blo 385764 1570745 := bstep (se 2 (by rfl) ⟨589029, by rfl⟩ : syracuseStep 1570745 = 1178059) B1178059
theorem B1046557 : Blo 385764 1046557 := bstep (se 3 (by rfl) ⟨196229, by rfl⟩ : syracuseStep 1046557 = 392459) B392459
theorem B1767491 : Blo 385764 1767491 := bstep (se 1 (by rfl) ⟨1325618, by rfl⟩ : syracuseStep 1767491 = 2651237) B2651237
theorem B653447 : Blo 385764 653447 := bstep (se 1 (by rfl) ⟨490085, by rfl⟩ : syracuseStep 653447 = 980171) B980171
theorem B9959597 : Blo 385764 9959597 := bstep (se 3 (by rfl) ⟨1867424, by rfl⟩ : syracuseStep 9959597 = 3734849) B3734849
theorem B981193 : Blo 385764 981193 := bstep (se 2 (by rfl) ⟨367947, by rfl⟩ : syracuseStep 981193 = 735895) B735895
theorem B981335 : Blo 385764 981335 := bstep (se 1 (by rfl) ⟨736001, by rfl⟩ : syracuseStep 981335 = 1472003) B1472003
theorem B1931779 : Blo 385764 1931779 := bstep (se 1 (by rfl) ⟨1448834, by rfl⟩ : syracuseStep 1931779 = 2897669) B2897669
theorem B1964573 : Blo 385764 1964573 := bstep (se 3 (by rfl) ⟨368357, by rfl⟩ : syracuseStep 1964573 = 736715) B736715
theorem B1178155 : Blo 385764 1178155 := bstep (se 1 (by rfl) ⟨883616, by rfl⟩ : syracuseStep 1178155 = 1767233) B1767233
theorem B1243849 : Blo 385764 1243849 := bstep (se 2 (by rfl) ⟨466443, by rfl⟩ : syracuseStep 1243849 = 932887) B932887
theorem B654095 : Blo 385764 654095 := bstep (se 1 (by rfl) ⟨490571, by rfl⟩ : syracuseStep 654095 = 981143) B981143
theorem B1309499 : Blo 385764 1309499 := bstep (se 1 (by rfl) ⟨982124, by rfl⟩ : syracuseStep 1309499 = 1964249) B1964249
theorem B1965059 : Blo 385764 1965059 := bstep (se 1 (by rfl) ⟨1473794, by rfl⟩ : syracuseStep 1965059 = 2947589) B2947589
theorem B785543 : Blo 385764 785543 := bstep (se 1 (by rfl) ⟨589157, by rfl⟩ : syracuseStep 785543 = 1178315) B1178315
theorem B1309985 : Blo 385764 1309985 := bstep (se 2 (by rfl) ⟨491244, by rfl⟩ : syracuseStep 1309985 = 982489) B982489
theorem B654635 : Blo 385764 654635 := bstep (se 1 (by rfl) ⟨490976, by rfl⟩ : syracuseStep 654635 = 981953) B981953
theorem B1473977 : Blo 385764 1473977 := bstep (se 2 (by rfl) ⟨552741, by rfl⟩ : syracuseStep 1473977 = 1105483) B1105483
theorem B2948561 : Blo 385764 2948561 := bstep (se 2 (by rfl) ⟨1105710, by rfl⟩ : syracuseStep 2948561 = 2211421) B2211421
theorem B3145283 : Blo 385764 3145283 := bstep (se 1 (by rfl) ⟨2358962, by rfl⟩ : syracuseStep 3145283 = 4717925) B4717925
theorem B491179 : Blo 385764 491179 := bstep (se 1 (by rfl) ⟨368384, by rfl⟩ : syracuseStep 491179 = 736769) B736769
theorem B655033 : Blo 385764 655033 := bstep (se 2 (by rfl) ⟨245637, by rfl⟩ : syracuseStep 655033 = 491275) B491275
theorem B524089 : Blo 385764 524089 := bstep (se 2 (by rfl) ⟨196533, by rfl⟩ : syracuseStep 524089 = 393067) B393067
theorem B884539 : Blo 385764 884539 := bstep (se 1 (by rfl) ⟨663404, by rfl⟩ : syracuseStep 884539 = 1326809) B1326809
theorem B1310579 : Blo 385764 1310579 := bstep (se 1 (by rfl) ⟨982934, by rfl⟩ : syracuseStep 1310579 = 1965869) B1965869
theorem B1048439 : Blo 385764 1048439 := bstep (se 1 (by rfl) ⟨786329, by rfl⟩ : syracuseStep 1048439 = 1572659) B1572659
theorem B2097049 : Blo 385764 2097049 := bstep (se 2 (by rfl) ⟨786393, by rfl⟩ : syracuseStep 2097049 = 1572787) B1572787
theorem B5898269 : Blo 385764 5898269 := bstep (se 3 (by rfl) ⟨1105925, by rfl⟩ : syracuseStep 5898269 = 2211851) B2211851
theorem B491599 : Blo 385764 491599 := bstep (se 1 (by rfl) ⟨368699, by rfl⟩ : syracuseStep 491599 = 737399) B737399
theorem B12550373 : Blo 385764 12550373 := bstep (se 4 (by rfl) ⟨1176597, by rfl⟩ : syracuseStep 12550373 = 2353195) B2353195
theorem B655607 : Blo 385764 655607 := bstep (se 1 (by rfl) ⟨491705, by rfl⟩ : syracuseStep 655607 = 983411) B983411
theorem B1245451 : Blo 385764 1245451 := bstep (se 1 (by rfl) ⟨934088, by rfl⟩ : syracuseStep 1245451 = 1868177) B1868177
theorem B1245565 : Blo 385764 1245565 := bstep (se 3 (by rfl) ⟨233543, by rfl⟩ : syracuseStep 1245565 = 467087) B467087
theorem B1311119 : Blo 385764 1311119 := bstep (se 1 (by rfl) ⟨983339, by rfl⟩ : syracuseStep 1311119 = 1966679) B1966679
theorem B932774453 : Blo 385764 932774453 := bstep (se 5 (by rfl) ⟨43723802, by rfl⟩ : syracuseStep 932774453 = 87447605) B87447605
theorem B1475131 : Blo 385764 1475131 := bstep (se 1 (by rfl) ⟨1106348, by rfl⟩ : syracuseStep 1475131 = 2212697) B2212697
theorem B655951 : Blo 385764 655951 := bstep (se 1 (by rfl) ⟨491963, by rfl⟩ : syracuseStep 655951 = 983927) B983927
theorem B1311443 : Blo 385764 1311443 := bstep (se 1 (by rfl) ⟨983582, by rfl⟩ : syracuseStep 1311443 = 1967165) B1967165
theorem B656201 : Blo 385764 656201 := bstep (se 2 (by rfl) ⟨246075, by rfl⟩ : syracuseStep 656201 = 492151) B492151
theorem B787295 : Blo 385764 787295 := bstep (se 1 (by rfl) ⟨590471, by rfl⟩ : syracuseStep 787295 = 1180943) B1180943
theorem B1475435 : Blo 385764 1475435 := bstep (se 1 (by rfl) ⟨1106576, by rfl⟩ : syracuseStep 1475435 = 2213153) B2213153
theorem B1115063 : Blo 385764 1115063 := bstep (se 1 (by rfl) ⟨836297, by rfl⟩ : syracuseStep 1115063 = 1672595) B1672595
theorem B1475603 : Blo 385764 1475603 := bstep (se 1 (by rfl) ⟨1106702, by rfl⟩ : syracuseStep 1475603 = 2213405) B2213405
theorem B1574083 : Blo 385764 1574083 := bstep (se 1 (by rfl) ⟨1180562, by rfl⟩ : syracuseStep 1574083 = 2361125) B2361125
theorem B492743 : Blo 385764 492743 := bstep (se 1 (by rfl) ⟨369557, by rfl⟩ : syracuseStep 492743 = 739115) B739115
theorem B656633 : Blo 385764 656633 := bstep (se 2 (by rfl) ⟨246237, by rfl⟩ : syracuseStep 656633 = 492475) B492475
theorem B492895 : Blo 385764 492895 := bstep (se 1 (by rfl) ⟨369671, by rfl⟩ : syracuseStep 492895 = 739343) B739343
theorem B656815 : Blo 385764 656815 := bstep (se 1 (by rfl) ⟨492611, by rfl⟩ : syracuseStep 656815 = 985223) B985223
theorem B1181147 : Blo 385764 1181147 := bstep (se 1 (by rfl) ⟨885860, by rfl⟩ : syracuseStep 1181147 = 1771721) B1771721
theorem B656903 : Blo 385764 656903 := bstep (se 1 (by rfl) ⟨492677, by rfl⟩ : syracuseStep 656903 = 985355) B985355
theorem B1246745 : Blo 385764 1246745 := bstep (se 2 (by rfl) ⟨467529, by rfl⟩ : syracuseStep 1246745 = 935059) B935059
theorem B624167 : Blo 385764 624167 := bstep (se 1 (by rfl) ⟨468125, by rfl⟩ : syracuseStep 624167 = 936251) B936251
theorem B2197115 : Blo 385764 2197115 := bstep (se 1 (by rfl) ⟨1647836, by rfl⟩ : syracuseStep 2197115 = 3295673) B3295673
theorem B657247 : Blo 385764 657247 := bstep (se 1 (by rfl) ⟨492935, by rfl⟩ : syracuseStep 657247 = 985871) B985871
theorem B2197367 : Blo 385764 2197367 := bstep (se 1 (by rfl) ⟨1648025, by rfl⟩ : syracuseStep 2197367 = 3296051) B3296051
theorem B1312631 : Blo 385764 1312631 := bstep (se 1 (by rfl) ⟨984473, by rfl⟩ : syracuseStep 1312631 = 1968947) B1968947
theorem B657335 : Blo 385764 657335 := bstep (se 1 (by rfl) ⟨493001, by rfl⟩ : syracuseStep 657335 = 986003) B986003
theorem B1312847 : Blo 385764 1312847 := bstep (se 1 (by rfl) ⟨984635, by rfl⟩ : syracuseStep 1312847 = 1969271) B1969271
theorem B1345921 : Blo 385764 1345921 := bstep (se 2 (by rfl) ⟨504720, by rfl⟩ : syracuseStep 1345921 = 1009441) B1009441
theorem B1313225 : Blo 385764 1313225 := bstep (se 2 (by rfl) ⟨492459, by rfl⟩ : syracuseStep 1313225 = 984919) B984919
theorem B1313495 : Blo 385764 1313495 := bstep (se 1 (by rfl) ⟨985121, by rfl⟩ : syracuseStep 1313495 = 1970243) B1970243
theorem B1313711 : Blo 385764 1313711 := bstep (se 1 (by rfl) ⟨985283, by rfl⟩ : syracuseStep 1313711 = 1970567) B1970567
theorem B3214403 : Blo 385764 3214403 := bstep (se 1 (by rfl) ⟨2410802, by rfl⟩ : syracuseStep 3214403 = 4821605) B4821605
theorem B3968635 : Blo 385764 3968635 := bstep (se 1 (by rfl) ⟨2976476, by rfl⟩ : syracuseStep 3968635 = 5952953) B5952953
theorem B3149435 : Blo 385764 3149435 := bstep (se 1 (by rfl) ⟨2362076, by rfl⟩ : syracuseStep 3149435 = 4724153) B4724153
theorem B4034285 : Blo 385764 4034285 := bstep (se 3 (by rfl) ⟨756428, by rfl⟩ : syracuseStep 4034285 = 1512857) B1512857
theorem B1478519 : Blo 385764 1478519 := bstep (se 1 (by rfl) ⟨1108889, by rfl⟩ : syracuseStep 1478519 = 2217779) B2217779
theorem B1970081 : Blo 385764 1970081 := bstep (se 2 (by rfl) ⟨738780, by rfl⟩ : syracuseStep 1970081 = 1477561) B1477561
theorem B1872233 : Blo 385764 1872233 := bstep (se 2 (by rfl) ⟨702087, by rfl⟩ : syracuseStep 1872233 = 1404175) B1404175
theorem B7443251 : Blo 385764 7443251 := bstep (se 1 (by rfl) ⟨5582438, by rfl⟩ : syracuseStep 7443251 = 11164877) B11164877
theorem B1479491 : Blo 385764 1479491 := bstep (se 1 (by rfl) ⟨1109618, by rfl⟩ : syracuseStep 1479491 = 2219237) B2219237
theorem B627643 : Blo 385764 627643 := bstep (se 1 (by rfl) ⟨470732, by rfl⟩ : syracuseStep 627643 = 941465) B941465
theorem B2135041 : Blo 385764 2135041 := bstep (se 2 (by rfl) ⟨800640, by rfl⟩ : syracuseStep 2135041 = 1601281) B1601281
theorem B627721 : Blo 385764 627721 := bstep (se 2 (by rfl) ⟨235395, by rfl⟩ : syracuseStep 627721 = 470791) B470791
theorem B3150899 : Blo 385764 3150899 := bstep (se 1 (by rfl) ⟨2363174, by rfl⟩ : syracuseStep 3150899 = 4726349) B4726349
theorem B2954393 : Blo 385764 2954393 := bstep (se 2 (by rfl) ⟨1107897, by rfl⟩ : syracuseStep 2954393 = 2215795) B2215795
theorem B6657227 : Blo 385764 6657227 := bstep (se 1 (by rfl) ⟨4992920, by rfl⟩ : syracuseStep 6657227 = 9985841) B9985841
theorem B2201033 : Blo 385764 2201033 := bstep (se 2 (by rfl) ⟨825387, by rfl⟩ : syracuseStep 2201033 = 1650775) B1650775
theorem B2790875 : Blo 385764 2790875 := bstep (se 1 (by rfl) ⟨2093156, by rfl⟩ : syracuseStep 2790875 = 4186313) B4186313
theorem B2561675 : Blo 385764 2561675 := bstep (se 1 (by rfl) ⟨1921256, by rfl⟩ : syracuseStep 2561675 = 3842513) B3842513
theorem B464815 : Blo 385764 464815 := bstep (se 1 (by rfl) ⟨348611, by rfl⟩ : syracuseStep 464815 = 697223) B697223
theorem B2988035 : Blo 385764 2988035 := bstep (se 1 (by rfl) ⟨2241026, by rfl⟩ : syracuseStep 2988035 = 4482053) B4482053
theorem B3545633 : Blo 385764 3545633 := bstep (se 2 (by rfl) ⟨1329612, by rfl⟩ : syracuseStep 3545633 = 2659225) B2659225
theorem B629305 : Blo 385764 629305 := bstep (se 2 (by rfl) ⟨235989, by rfl⟩ : syracuseStep 629305 = 471979) B471979
theorem B465607 : Blo 385764 465607 := bstep (se 1 (by rfl) ⟨349205, by rfl⟩ : syracuseStep 465607 = 698411) B698411
theorem B2956337 : Blo 385764 2956337 := bstep (se 2 (by rfl) ⟨1108626, by rfl⟩ : syracuseStep 2956337 = 2217253) B2217253
theorem B2432051 : Blo 385764 2432051 := bstep (se 1 (by rfl) ⟨1824038, by rfl⟩ : syracuseStep 2432051 = 3648077) B3648077
theorem B3153167 : Blo 385764 3153167 := bstep (se 1 (by rfl) ⟨2364875, by rfl⟩ : syracuseStep 3153167 = 4729751) B4729751
theorem B46768141 : Blo 385764 46768141 := bstep (se 3 (by rfl) ⟨8769026, by rfl⟩ : syracuseStep 46768141 = 17538053) B17538053
theorem B434299 : Blo 385764 434299 := bstep (se 1 (by rfl) ⟨325724, by rfl⟩ : syracuseStep 434299 = 651449) B651449
theorem B1122461 : Blo 385764 1122461 := bstep (se 3 (by rfl) ⟨210461, by rfl⟩ : syracuseStep 1122461 = 420923) B420923
theorem B1417753 : Blo 385764 1417753 := bstep (se 2 (by rfl) ⟨531657, by rfl⟩ : syracuseStep 1417753 = 1063315) B1063315
theorem B434767 : Blo 385764 434767 := bstep (se 1 (by rfl) ⟨326075, by rfl⟩ : syracuseStep 434767 = 652151) B652151
theorem B435163 : Blo 385764 435163 := bstep (se 1 (by rfl) ⟨326372, by rfl⟩ : syracuseStep 435163 = 652745) B652745
theorem B664615 : Blo 385764 664615 := bstep (se 1 (by rfl) ⟨498461, by rfl⟩ : syracuseStep 664615 = 996923) B996923
theorem B2663491 : Blo 385764 2663491 := bstep (se 1 (by rfl) ⟨1997618, by rfl⟩ : syracuseStep 2663491 = 3995237) B3995237
theorem B435631 : Blo 385764 435631 := bstep (se 1 (by rfl) ⟨326723, by rfl⟩ : syracuseStep 435631 = 653447) B653447
theorem B2795141 : Blo 385764 2795141 := bstep (se 4 (by rfl) ⟨262044, by rfl⟩ : syracuseStep 2795141 = 524089) B524089
theorem B1648451 : Blo 385764 1648451 := bstep (se 1 (by rfl) ⟨1236338, by rfl⟩ : syracuseStep 1648451 = 2472677) B2472677
theorem B436063 : Blo 385764 436063 := bstep (se 1 (by rfl) ⟨327047, by rfl⟩ : syracuseStep 436063 = 654095) B654095
theorem B2664485 : Blo 385764 2664485 := bstep (se 4 (by rfl) ⟨249795, by rfl⟩ : syracuseStep 2664485 = 499591) B499591
theorem B436423 : Blo 385764 436423 := bstep (se 1 (by rfl) ⟨327317, by rfl⟩ : syracuseStep 436423 = 654635) B654635
theorem B2796065 : Blo 385764 2796065 := bstep (se 2 (by rfl) ⟨1048524, by rfl⟩ : syracuseStep 2796065 = 2097049) B2097049
theorem B698959 : Blo 385764 698959 := bstep (se 1 (by rfl) ⟨524219, by rfl⟩ : syracuseStep 698959 = 1048439) B1048439
theorem B437287 : Blo 385764 437287 := bstep (se 1 (by rfl) ⟨327965, by rfl⟩ : syracuseStep 437287 = 655931) B655931
theorem B929015 : Blo 385764 929015 := bstep (se 1 (by rfl) ⟨696761, by rfl⟩ : syracuseStep 929015 = 1393523) B1393523
theorem B830711 : Blo 385764 830711 := bstep (se 1 (by rfl) ⟨623033, by rfl⟩ : syracuseStep 830711 = 1246067) B1246067
theorem B4435235 : Blo 385764 4435235 := bstep (se 1 (by rfl) ⟨3326426, by rfl⟩ : syracuseStep 4435235 = 6652853) B6652853
theorem B732577 : Blo 385764 732577 := bstep (se 2 (by rfl) ⟨274716, by rfl⟩ : syracuseStep 732577 = 549433) B549433
theorem B699823 : Blo 385764 699823 := bstep (se 1 (by rfl) ⟨524867, by rfl⟩ : syracuseStep 699823 = 1049735) B1049735
theorem B470455 : Blo 385764 470455 := bstep (se 1 (by rfl) ⟨352841, by rfl⟩ : syracuseStep 470455 = 705683) B705683
theorem B699911 : Blo 385764 699911 := bstep (se 1 (by rfl) ⟨524933, by rfl⟩ : syracuseStep 699911 = 1049867) B1049867
theorem B1650365 : Blo 385764 1650365 := bstep (se 3 (by rfl) ⟨309443, by rfl⟩ : syracuseStep 1650365 = 618887) B618887
theorem B2994029 : Blo 385764 2994029 := bstep (se 3 (by rfl) ⟨561380, by rfl⟩ : syracuseStep 2994029 = 1122761) B1122761
theorem B700343 : Blo 385764 700343 := bstep (se 1 (by rfl) ⟨525257, by rfl⟩ : syracuseStep 700343 = 1050515) B1050515
theorem B471079 : Blo 385764 471079 := bstep (se 1 (by rfl) ⟨353309, by rfl⟩ : syracuseStep 471079 = 706619) B706619
theorem B1585469 : Blo 385764 1585469 := bstep (se 3 (by rfl) ⟨297275, by rfl⟩ : syracuseStep 1585469 = 594551) B594551
theorem B1651049 : Blo 385764 1651049 := bstep (se 2 (by rfl) ⟨619143, by rfl⟩ : syracuseStep 1651049 = 1238287) B1238287
theorem B832351 : Blo 385764 832351 := bstep (se 1 (by rfl) ⟨624263, by rfl⟩ : syracuseStep 832351 = 1248527) B1248527
theorem B10302821 : Blo 385764 10302821 := bstep (se 4 (by rfl) ⟨965889, by rfl⟩ : syracuseStep 10302821 = 1931779) B1931779
theorem B2930093 : Blo 385764 2930093 := bstep (se 3 (by rfl) ⟨549392, by rfl⟩ : syracuseStep 2930093 = 1098785) B1098785
theorem B3716705 : Blo 385764 3716705 := bstep (se 2 (by rfl) ⟨1393764, by rfl⟩ : syracuseStep 3716705 = 2787529) B2787529
theorem B734969 : Blo 385764 734969 := bstep (se 2 (by rfl) ⟨275613, by rfl⟩ : syracuseStep 734969 = 551227) B551227
theorem B1390409 : Blo 385764 1390409 := bstep (se 2 (by rfl) ⟨521403, by rfl⟩ : syracuseStep 1390409 = 1042807) B1042807
theorem B931657 : Blo 385764 931657 := bstep (se 2 (by rfl) ⟨349371, by rfl⟩ : syracuseStep 931657 = 698743) B698743
theorem B1324907 : Blo 385764 1324907 := bstep (se 1 (by rfl) ⟨993680, by rfl⟩ : syracuseStep 1324907 = 1987361) B1987361
theorem B735151 : Blo 385764 735151 := bstep (se 1 (by rfl) ⟨551363, by rfl⟩ : syracuseStep 735151 = 1102727) B1102727
theorem B5027789 : Blo 385764 5027789 := bstep (se 3 (by rfl) ⟨942710, by rfl⟩ : syracuseStep 5027789 = 1885421) B1885421
theorem B735311 : Blo 385764 735311 := bstep (se 1 (by rfl) ⟨551483, by rfl⟩ : syracuseStep 735311 = 1102967) B1102967
theorem B181778519 : Blo 385764 181778519 := bstep (se 1 (by rfl) ⟨136333889, by rfl⟩ : syracuseStep 181778519 = 272667779) B272667779
theorem B188627285 : Blo 385764 188627285 := bstep (se 10 (by rfl) ⟨276309, by rfl⟩ : syracuseStep 188627285 = 552619) B552619
theorem B2210489 : Blo 385764 2210489 := bstep (se 2 (by rfl) ⟨828933, by rfl⟩ : syracuseStep 2210489 = 1657867) B1657867
theorem B10566389 : Blo 385764 10566389 := bstep (se 5 (by rfl) ⟨495299, by rfl⟩ : syracuseStep 10566389 = 990599) B990599
theorem B3980215 : Blo 385764 3980215 := bstep (se 1 (by rfl) ⟨2985161, by rfl⟩ : syracuseStep 3980215 = 5970323) B5970323
theorem B736427 : Blo 385764 736427 := bstep (se 1 (by rfl) ⟨552320, by rfl⟩ : syracuseStep 736427 = 1104641) B1104641
theorem B2932523 : Blo 385764 2932523 := bstep (se 1 (by rfl) ⟨2199392, by rfl⟩ : syracuseStep 2932523 = 4398785) B4398785
theorem B868283 : Blo 385764 868283 := bstep (se 1 (by rfl) ⟨651212, by rfl⟩ : syracuseStep 868283 = 1302425) B1302425
theorem B1392641 : Blo 385764 1392641 := bstep (se 2 (by rfl) ⟨522240, by rfl⟩ : syracuseStep 1392641 = 1044481) B1044481
theorem B5980175 : Blo 385764 5980175 := bstep (se 1 (by rfl) ⟨4485131, by rfl⟩ : syracuseStep 5980175 = 8970263) B8970263
theorem B868409 : Blo 385764 868409 := bstep (se 2 (by rfl) ⟨325653, by rfl⟩ : syracuseStep 868409 = 651307) B651307
theorem B1196279 : Blo 385764 1196279 := bstep (se 1 (by rfl) ⟨897209, by rfl⟩ : syracuseStep 1196279 = 1794419) B1794419
theorem B868751 : Blo 385764 868751 := bstep (se 1 (by rfl) ⟨651563, by rfl⟩ : syracuseStep 868751 = 1303127) B1303127
theorem B869075 : Blo 385764 869075 := bstep (se 1 (by rfl) ⟨651806, by rfl⟩ : syracuseStep 869075 = 1303613) B1303613
theorem B738143 : Blo 385764 738143 := bstep (se 1 (by rfl) ⟨553607, by rfl⟩ : syracuseStep 738143 = 1107215) B1107215
theorem B11289619 : Blo 385764 11289619 := bstep (se 1 (by rfl) ⟨8467214, by rfl⟩ : syracuseStep 11289619 = 16934429) B16934429
theorem B1098809 : Blo 385764 1098809 := bstep (se 2 (by rfl) ⟨412053, by rfl⟩ : syracuseStep 1098809 = 824107) B824107
theorem B738553 : Blo 385764 738553 := bstep (se 2 (by rfl) ⟨276957, by rfl⟩ : syracuseStep 738553 = 553915) B553915
theorem B2803187 : Blo 385764 2803187 := bstep (se 1 (by rfl) ⟨2102390, by rfl⟩ : syracuseStep 2803187 = 4204781) B4204781
theorem B738895 : Blo 385764 738895 := bstep (se 1 (by rfl) ⟨554171, by rfl⟩ : syracuseStep 738895 = 1108343) B1108343
theorem B870011 : Blo 385764 870011 := bstep (se 1 (by rfl) ⟨652508, by rfl⟩ : syracuseStep 870011 = 1305017) B1305017
theorem B870137 : Blo 385764 870137 := bstep (se 2 (by rfl) ⟨326301, by rfl⟩ : syracuseStep 870137 = 652603) B652603
theorem B739145 : Blo 385764 739145 := bstep (se 2 (by rfl) ⟨277179, by rfl⟩ : syracuseStep 739145 = 554359) B554359
theorem B870407 : Blo 385764 870407 := bstep (se 1 (by rfl) ⟨652805, by rfl⟩ : syracuseStep 870407 = 1305611) B1305611
theorem B870479 : Blo 385764 870479 := bstep (se 1 (by rfl) ⟨652859, by rfl⟩ : syracuseStep 870479 = 1305719) B1305719
theorem B2214155 : Blo 385764 2214155 := bstep (se 1 (by rfl) ⟨1660616, by rfl⟩ : syracuseStep 2214155 = 3321233) B3321233
theorem B1067393 : Blo 385764 1067393 := bstep (se 2 (by rfl) ⟨400272, by rfl⟩ : syracuseStep 1067393 = 800545) B800545
theorem B870875 : Blo 385764 870875 := bstep (se 1 (by rfl) ⟨653156, by rfl⟩ : syracuseStep 870875 = 1306313) B1306313
theorem B1395409 : Blo 385764 1395409 := bstep (se 2 (by rfl) ⟨523278, by rfl⟩ : syracuseStep 1395409 = 1046557) B1046557
theorem B2214611 : Blo 385764 2214611 := bstep (se 1 (by rfl) ⟨1660958, by rfl⟩ : syracuseStep 2214611 = 3321917) B3321917
theorem B871343 : Blo 385764 871343 := bstep (se 1 (by rfl) ⟨653507, by rfl⟩ : syracuseStep 871343 = 1307015) B1307015
theorem B871595 : Blo 385764 871595 := bstep (se 1 (by rfl) ⟨653696, by rfl⟩ : syracuseStep 871595 = 1307393) B1307393
theorem B413147 : Blo 385764 413147 := bstep (se 1 (by rfl) ⟨309860, by rfl⟩ : syracuseStep 413147 = 619721) B619721
theorem B1396187 : Blo 385764 1396187 := bstep (se 1 (by rfl) ⟨1047140, by rfl⟩ : syracuseStep 1396187 = 2094281) B2094281
theorem B1658465 : Blo 385764 1658465 := bstep (se 2 (by rfl) ⟨621924, by rfl⟩ : syracuseStep 1658465 = 1243849) B1243849
theorem B4476539 : Blo 385764 4476539 := bstep (se 1 (by rfl) ⟨3357404, by rfl⟩ : syracuseStep 4476539 = 6714809) B6714809
theorem B1101451 : Blo 385764 1101451 := bstep (se 1 (by rfl) ⟨826088, by rfl⟩ : syracuseStep 1101451 = 1652177) B1652177
theorem B2215613 : Blo 385764 2215613 := bstep (se 3 (by rfl) ⟨415427, by rfl⟩ : syracuseStep 2215613 = 830855) B830855
theorem B872135 : Blo 385764 872135 := bstep (se 1 (by rfl) ⟨654101, by rfl⟩ : syracuseStep 872135 = 1308203) B1308203
theorem B1953881 : Blo 385764 1953881 := bstep (se 2 (by rfl) ⟨732705, by rfl⟩ : syracuseStep 1953881 = 1465411) B1465411
theorem B6639731 : Blo 385764 6639731 := bstep (se 1 (by rfl) ⟨4979798, by rfl⟩ : syracuseStep 6639731 = 9959597) B9959597
theorem B2216321 : Blo 385764 2216321 := bstep (se 2 (by rfl) ⟨831120, by rfl⟩ : syracuseStep 2216321 = 1662241) B1662241
theorem B1331585 : Blo 385764 1331585 := bstep (se 2 (by rfl) ⟨499344, by rfl⟩ : syracuseStep 1331585 = 998689) B998689
theorem B872999 : Blo 385764 872999 := bstep (se 1 (by rfl) ⟨654749, by rfl⟩ : syracuseStep 872999 = 1309499) B1309499
theorem B873323 : Blo 385764 873323 := bstep (se 1 (by rfl) ⟨654992, by rfl⟩ : syracuseStep 873323 = 1309985) B1309985
theorem B873377 : Blo 385764 873377 := bstep (se 2 (by rfl) ⟨327516, by rfl⟩ : syracuseStep 873377 = 655033) B655033
theorem B578759 : Blo 385764 578759 := bstep (se 1 (by rfl) ⟨434069, by rfl⟩ : syracuseStep 578759 = 868139) B868139
theorem B873719 : Blo 385764 873719 := bstep (se 1 (by rfl) ⟨655289, by rfl⟩ : syracuseStep 873719 = 1310579) B1310579
theorem B578921 : Blo 385764 578921 := bstep (se 2 (by rfl) ⟨217095, by rfl⟩ : syracuseStep 578921 = 434191) B434191
theorem B578999 : Blo 385764 578999 := bstep (se 1 (by rfl) ⟨434249, by rfl⟩ : syracuseStep 578999 = 868499) B868499
theorem B1856969 : Blo 385764 1856969 := bstep (se 2 (by rfl) ⟨696363, by rfl⟩ : syracuseStep 1856969 = 1392727) B1392727
theorem B579035 : Blo 385764 579035 := bstep (se 1 (by rfl) ⟨434276, by rfl⟩ : syracuseStep 579035 = 868553) B868553
theorem B2938355 : Blo 385764 2938355 := bstep (se 1 (by rfl) ⟨2203766, by rfl⟩ : syracuseStep 2938355 = 4407533) B4407533
theorem B874313 : Blo 385764 874313 := bstep (se 2 (by rfl) ⟨327867, by rfl⟩ : syracuseStep 874313 = 655735) B655735
theorem B579503 : Blo 385764 579503 := bstep (se 1 (by rfl) ⟨434627, by rfl⟩ : syracuseStep 579503 = 869255) B869255
theorem B2086843 : Blo 385764 2086843 := bstep (se 1 (by rfl) ⟨1565132, by rfl⟩ : syracuseStep 2086843 = 3130265) B3130265
theorem B22566869 : Blo 385764 22566869 := bstep (se 7 (by rfl) ⟨264455, by rfl⟩ : syracuseStep 22566869 = 528911) B528911
theorem B22763477 : Blo 385764 22763477 := bstep (se 7 (by rfl) ⟨266759, by rfl⟩ : syracuseStep 22763477 = 533519) B533519
theorem B579593 : Blo 385764 579593 := bstep (se 2 (by rfl) ⟨217347, by rfl⟩ : syracuseStep 579593 = 434695) B434695
theorem B579623 : Blo 385764 579623 := bstep (se 1 (by rfl) ⟨434717, by rfl⟩ : syracuseStep 579623 = 869435) B869435
theorem B743521 : Blo 385764 743521 := bstep (se 2 (by rfl) ⟨278820, by rfl⟩ : syracuseStep 743521 = 557641) B557641
theorem B579707 : Blo 385764 579707 := bstep (se 1 (by rfl) ⟨434780, by rfl⟩ : syracuseStep 579707 = 869561) B869561
theorem B579833 : Blo 385764 579833 := bstep (se 2 (by rfl) ⟨217437, by rfl⟩ : syracuseStep 579833 = 434875) B434875
theorem B579935 : Blo 385764 579935 := bstep (se 1 (by rfl) ⟨434951, by rfl⟩ : syracuseStep 579935 = 869903) B869903
theorem B579947 : Blo 385764 579947 := bstep (se 1 (by rfl) ⟨434960, by rfl⟩ : syracuseStep 579947 = 869921) B869921
theorem B2218529 : Blo 385764 2218529 := bstep (se 2 (by rfl) ⟨831948, by rfl⟩ : syracuseStep 2218529 = 1663897) B1663897
theorem B580175 : Blo 385764 580175 := bstep (se 1 (by rfl) ⟨435131, by rfl⟩ : syracuseStep 580175 = 870263) B870263
theorem B875105 : Blo 385764 875105 := bstep (se 2 (by rfl) ⟨328164, by rfl⟩ : syracuseStep 875105 = 656329) B656329
theorem B580295 : Blo 385764 580295 := bstep (se 1 (by rfl) ⟨435221, by rfl⟩ : syracuseStep 580295 = 870443) B870443
theorem B4971293 : Blo 385764 4971293 := bstep (se 3 (by rfl) ⟨932117, by rfl⟩ : syracuseStep 4971293 = 1864235) B1864235
theorem B580457 : Blo 385764 580457 := bstep (se 2 (by rfl) ⟨217671, by rfl⟩ : syracuseStep 580457 = 435343) B435343
theorem B580535 : Blo 385764 580535 := bstep (se 1 (by rfl) ⟨435401, by rfl⟩ : syracuseStep 580535 = 870803) B870803
theorem B875447 : Blo 385764 875447 := bstep (se 1 (by rfl) ⟨656585, by rfl⟩ : syracuseStep 875447 = 1313171) B1313171
theorem B580571 : Blo 385764 580571 := bstep (se 1 (by rfl) ⟨435428, by rfl⟩ : syracuseStep 580571 = 870857) B870857
theorem B581039 : Blo 385764 581039 := bstep (se 1 (by rfl) ⟨435779, by rfl⟩ : syracuseStep 581039 = 871559) B871559
theorem B581129 : Blo 385764 581129 := bstep (se 2 (by rfl) ⟨217923, by rfl⟩ : syracuseStep 581129 = 435847) B435847
theorem B876041 : Blo 385764 876041 := bstep (se 2 (by rfl) ⟨328515, by rfl⟩ : syracuseStep 876041 = 657031) B657031
theorem B581159 : Blo 385764 581159 := bstep (se 1 (by rfl) ⟨435869, by rfl⟩ : syracuseStep 581159 = 871739) B871739
theorem B2809441 : Blo 385764 2809441 := bstep (se 2 (by rfl) ⟨1053540, by rfl⟩ : syracuseStep 2809441 = 2107081) B2107081
theorem B581243 : Blo 385764 581243 := bstep (se 1 (by rfl) ⟨435932, by rfl⟩ : syracuseStep 581243 = 871865) B871865
theorem B1302155 : Blo 385764 1302155 := bstep (se 1 (by rfl) ⟨976616, by rfl⟩ : syracuseStep 1302155 = 1953233) B1953233
theorem B581369 : Blo 385764 581369 := bstep (se 2 (by rfl) ⟨218013, by rfl⟩ : syracuseStep 581369 = 436027) B436027
theorem B581471 : Blo 385764 581471 := bstep (se 1 (by rfl) ⟨436103, by rfl⟩ : syracuseStep 581471 = 872207) B872207
theorem B876383 : Blo 385764 876383 := bstep (se 1 (by rfl) ⟨657287, by rfl⟩ : syracuseStep 876383 = 1314575) B1314575
theorem B581483 : Blo 385764 581483 := bstep (se 1 (by rfl) ⟨436112, by rfl⟩ : syracuseStep 581483 = 872225) B872225
theorem B1662839 : Blo 385764 1662839 := bstep (se 1 (by rfl) ⟨1247129, by rfl⟩ : syracuseStep 1662839 = 2494259) B2494259
theorem B1105825 : Blo 385764 1105825 := bstep (se 2 (by rfl) ⟨414684, by rfl⟩ : syracuseStep 1105825 = 829369) B829369
theorem B1466369 : Blo 385764 1466369 := bstep (se 2 (by rfl) ⟨549888, by rfl⟩ : syracuseStep 1466369 = 1099777) B1099777
theorem B1466383 : Blo 385764 1466383 := bstep (se 1 (by rfl) ⟨1099787, by rfl⟩ : syracuseStep 1466383 = 2199575) B2199575
theorem B876563 : Blo 385764 876563 := bstep (se 1 (by rfl) ⟨657422, by rfl⟩ : syracuseStep 876563 = 1314845) B1314845
theorem B3203101 : Blo 385764 3203101 := bstep (se 3 (by rfl) ⟨600581, by rfl⟩ : syracuseStep 3203101 = 1201163) B1201163
theorem B581711 : Blo 385764 581711 := bstep (se 1 (by rfl) ⟨436283, by rfl⟩ : syracuseStep 581711 = 872567) B872567
theorem B581831 : Blo 385764 581831 := bstep (se 1 (by rfl) ⟨436373, by rfl⟩ : syracuseStep 581831 = 872747) B872747
theorem B6283493 : Blo 385764 6283493 := bstep (se 4 (by rfl) ⟨589077, by rfl⟩ : syracuseStep 6283493 = 1178155) B1178155
theorem B2941271 : Blo 385764 2941271 := bstep (se 1 (by rfl) ⟨2205953, by rfl⟩ : syracuseStep 2941271 = 4411907) B4411907
theorem B581993 : Blo 385764 581993 := bstep (se 2 (by rfl) ⟨218247, by rfl⟩ : syracuseStep 581993 = 436495) B436495
theorem B876905 : Blo 385764 876905 := bstep (se 2 (by rfl) ⟨328839, by rfl⟩ : syracuseStep 876905 = 657679) B657679
theorem B582071 : Blo 385764 582071 := bstep (se 1 (by rfl) ⟨436553, by rfl⟩ : syracuseStep 582071 = 873107) B873107
theorem B582107 : Blo 385764 582107 := bstep (se 1 (by rfl) ⟨436580, by rfl⟩ : syracuseStep 582107 = 873161) B873161
theorem B1303073 : Blo 385764 1303073 := bstep (se 2 (by rfl) ⟨488652, by rfl⟩ : syracuseStep 1303073 = 977305) B977305
theorem B647851 : Blo 385764 647851 := bstep (se 1 (by rfl) ⟨485888, by rfl⟩ : syracuseStep 647851 = 971777) B971777
theorem B1303289 : Blo 385764 1303289 := bstep (se 2 (by rfl) ⟨488733, by rfl⟩ : syracuseStep 1303289 = 977467) B977467
theorem B385831 : Blo 385764 385831 := bstep (se 1 (by rfl) ⟨289373, by rfl⟩ : syracuseStep 385831 = 578747) B578747
theorem B385871 : Blo 385764 385871 := bstep (se 1 (by rfl) ⟨289403, by rfl⟩ : syracuseStep 385871 = 578807) B578807
theorem B385887 : Blo 385764 385887 := bstep (se 1 (by rfl) ⟨289415, by rfl⟩ : syracuseStep 385887 = 578831) B578831
theorem B418655 : Blo 385764 418655 := bstep (se 1 (by rfl) ⟨313991, by rfl⟩ : syracuseStep 418655 = 627983) B627983
theorem B385915 : Blo 385764 385915 := bstep (se 1 (by rfl) ⟨289436, by rfl⟩ : syracuseStep 385915 = 578873) B578873
theorem B385967 : Blo 385764 385967 := bstep (se 1 (by rfl) ⟨289475, by rfl⟩ : syracuseStep 385967 = 578951) B578951
theorem B582575 : Blo 385764 582575 := bstep (se 1 (by rfl) ⟨436931, by rfl⟩ : syracuseStep 582575 = 873863) B873863
theorem B385991 : Blo 385764 385991 := bstep (se 1 (by rfl) ⟨289493, by rfl⟩ : syracuseStep 385991 = 578987) B578987
theorem B386011 : Blo 385764 386011 := bstep (se 1 (by rfl) ⟨289508, by rfl⟩ : syracuseStep 386011 = 579017) B579017
theorem B1303559 : Blo 385764 1303559 := bstep (se 1 (by rfl) ⟨977669, by rfl⟩ : syracuseStep 1303559 = 1955339) B1955339
theorem B582665 : Blo 385764 582665 := bstep (se 2 (by rfl) ⟨218499, by rfl⟩ : syracuseStep 582665 = 436999) B436999
theorem B386087 : Blo 385764 386087 := bstep (se 1 (by rfl) ⟨289565, by rfl⟩ : syracuseStep 386087 = 579131) B579131
theorem B582695 : Blo 385764 582695 := bstep (se 1 (by rfl) ⟨437021, by rfl⟩ : syracuseStep 582695 = 874043) B874043
theorem B12248113 : Blo 385764 12248113 := bstep (se 2 (by rfl) ⟨4593042, by rfl⟩ : syracuseStep 12248113 = 9186085) B9186085
theorem B1860659 : Blo 385764 1860659 := bstep (se 1 (by rfl) ⟨1395494, by rfl⟩ : syracuseStep 1860659 = 2790989) B2790989
theorem B386127 : Blo 385764 386127 := bstep (se 1 (by rfl) ⟨289595, by rfl⟩ : syracuseStep 386127 = 579191) B579191
theorem B386143 : Blo 385764 386143 := bstep (se 1 (by rfl) ⟨289607, by rfl⟩ : syracuseStep 386143 = 579215) B579215
theorem B1303667 : Blo 385764 1303667 := bstep (se 1 (by rfl) ⟨977750, by rfl⟩ : syracuseStep 1303667 = 1955501) B1955501
theorem B386171 : Blo 385764 386171 := bstep (se 1 (by rfl) ⟨289628, by rfl⟩ : syracuseStep 386171 = 579257) B579257
theorem B582779 : Blo 385764 582779 := bstep (se 1 (by rfl) ⟨437084, by rfl⟩ : syracuseStep 582779 = 874169) B874169
theorem B1959065 : Blo 385764 1959065 := bstep (se 2 (by rfl) ⟨734649, by rfl⟩ : syracuseStep 1959065 = 1469299) B1469299
theorem B1107101 : Blo 385764 1107101 := bstep (se 3 (by rfl) ⟨207581, by rfl⟩ : syracuseStep 1107101 = 415163) B415163
theorem B1664171 : Blo 385764 1664171 := bstep (se 1 (by rfl) ⟨1248128, by rfl⟩ : syracuseStep 1664171 = 2496257) B2496257
theorem B386223 : Blo 385764 386223 := bstep (se 1 (by rfl) ⟨289667, by rfl⟩ : syracuseStep 386223 = 579335) B579335
theorem B386247 : Blo 385764 386247 := bstep (se 1 (by rfl) ⟨289685, by rfl⟩ : syracuseStep 386247 = 579371) B579371
theorem B386267 : Blo 385764 386267 := bstep (se 1 (by rfl) ⟨289700, by rfl⟩ : syracuseStep 386267 = 579401) B579401
theorem B582905 : Blo 385764 582905 := bstep (se 2 (by rfl) ⟨218589, by rfl⟩ : syracuseStep 582905 = 437179) B437179
theorem B1467659 : Blo 385764 1467659 := bstep (se 1 (by rfl) ⟨1100744, by rfl⟩ : syracuseStep 1467659 = 2201489) B2201489
theorem B386343 : Blo 385764 386343 := bstep (se 1 (by rfl) ⟨289757, by rfl⟩ : syracuseStep 386343 = 579515) B579515
theorem B386383 : Blo 385764 386383 := bstep (se 1 (by rfl) ⟨289787, by rfl⟩ : syracuseStep 386383 = 579575) B579575
theorem B386399 : Blo 385764 386399 := bstep (se 1 (by rfl) ⟨289799, by rfl⟩ : syracuseStep 386399 = 579599) B579599
theorem B583007 : Blo 385764 583007 := bstep (se 1 (by rfl) ⟨437255, by rfl⟩ : syracuseStep 583007 = 874511) B874511
theorem B583019 : Blo 385764 583019 := bstep (se 1 (by rfl) ⟨437264, by rfl⟩ : syracuseStep 583019 = 874529) B874529
theorem B386427 : Blo 385764 386427 := bstep (se 1 (by rfl) ⟨289820, by rfl⟩ : syracuseStep 386427 = 579641) B579641
theorem B1303937 : Blo 385764 1303937 := bstep (se 2 (by rfl) ⟨488976, by rfl⟩ : syracuseStep 1303937 = 977953) B977953
theorem B386479 : Blo 385764 386479 := bstep (se 1 (by rfl) ⟨289859, by rfl⟩ : syracuseStep 386479 = 579719) B579719
theorem B550327 : Blo 385764 550327 := bstep (se 1 (by rfl) ⟨412745, by rfl⟩ : syracuseStep 550327 = 825491) B825491
theorem B386503 : Blo 385764 386503 := bstep (se 1 (by rfl) ⟨289877, by rfl⟩ : syracuseStep 386503 = 579755) B579755
theorem B386523 : Blo 385764 386523 := bstep (se 1 (by rfl) ⟨289892, by rfl⟩ : syracuseStep 386523 = 579785) B579785
theorem B386599 : Blo 385764 386599 := bstep (se 1 (by rfl) ⟨289949, by rfl⟩ : syracuseStep 386599 = 579899) B579899
theorem B386639 : Blo 385764 386639 := bstep (se 1 (by rfl) ⟨289979, by rfl⟩ : syracuseStep 386639 = 579959) B579959
theorem B583247 : Blo 385764 583247 := bstep (se 1 (by rfl) ⟨437435, by rfl⟩ : syracuseStep 583247 = 874871) B874871
theorem B386655 : Blo 385764 386655 := bstep (se 1 (by rfl) ⟨289991, by rfl⟩ : syracuseStep 386655 = 579983) B579983
theorem B386683 : Blo 385764 386683 := bstep (se 1 (by rfl) ⟨290012, by rfl⟩ : syracuseStep 386683 = 580025) B580025
theorem B386735 : Blo 385764 386735 := bstep (se 1 (by rfl) ⟨290051, by rfl⟩ : syracuseStep 386735 = 580103) B580103
theorem B386759 : Blo 385764 386759 := bstep (se 1 (by rfl) ⟨290069, by rfl⟩ : syracuseStep 386759 = 580139) B580139
theorem B583367 : Blo 385764 583367 := bstep (se 1 (by rfl) ⟨437525, by rfl⟩ : syracuseStep 583367 = 875051) B875051
theorem B1468115 : Blo 385764 1468115 := bstep (se 1 (by rfl) ⟨1101086, by rfl⟩ : syracuseStep 1468115 = 2202173) B2202173
theorem B386779 : Blo 385764 386779 := bstep (se 1 (by rfl) ⟨290084, by rfl⟩ : syracuseStep 386779 = 580169) B580169
theorem B386855 : Blo 385764 386855 := bstep (se 1 (by rfl) ⟨290141, by rfl⟩ : syracuseStep 386855 = 580283) B580283
theorem B386895 : Blo 385764 386895 := bstep (se 1 (by rfl) ⟨290171, by rfl⟩ : syracuseStep 386895 = 580343) B580343
theorem B386911 : Blo 385764 386911 := bstep (se 1 (by rfl) ⟨290183, by rfl⟩ : syracuseStep 386911 = 580367) B580367
theorem B583529 : Blo 385764 583529 := bstep (se 2 (by rfl) ⟨218823, by rfl⟩ : syracuseStep 583529 = 437647) B437647
theorem B386939 : Blo 385764 386939 := bstep (se 1 (by rfl) ⟨290204, by rfl⟩ : syracuseStep 386939 = 580409) B580409
theorem B386991 : Blo 385764 386991 := bstep (se 1 (by rfl) ⟨290243, by rfl⟩ : syracuseStep 386991 = 580487) B580487
theorem B583607 : Blo 385764 583607 := bstep (se 1 (by rfl) ⟨437705, by rfl⟩ : syracuseStep 583607 = 875411) B875411
theorem B387015 : Blo 385764 387015 := bstep (se 1 (by rfl) ⟨290261, by rfl⟩ : syracuseStep 387015 = 580523) B580523
theorem B387035 : Blo 385764 387035 := bstep (se 1 (by rfl) ⟨290276, by rfl⟩ : syracuseStep 387035 = 580553) B580553
theorem B583643 : Blo 385764 583643 := bstep (se 1 (by rfl) ⟨437732, by rfl⟩ : syracuseStep 583643 = 875465) B875465
theorem B387111 : Blo 385764 387111 := bstep (se 1 (by rfl) ⟨290333, by rfl⟩ : syracuseStep 387111 = 580667) B580667
theorem B387151 : Blo 385764 387151 := bstep (se 1 (by rfl) ⟨290363, by rfl⟩ : syracuseStep 387151 = 580727) B580727
theorem B387167 : Blo 385764 387167 := bstep (se 1 (by rfl) ⟨290375, by rfl⟩ : syracuseStep 387167 = 580751) B580751
theorem B387195 : Blo 385764 387195 := bstep (se 1 (by rfl) ⟨290396, by rfl⟩ : syracuseStep 387195 = 580793) B580793
theorem B1304747 : Blo 385764 1304747 := bstep (se 1 (by rfl) ⟨978560, by rfl⟩ : syracuseStep 1304747 = 1957121) B1957121
theorem B387247 : Blo 385764 387247 := bstep (se 1 (by rfl) ⟨290435, by rfl⟩ : syracuseStep 387247 = 580871) B580871
theorem B387271 : Blo 385764 387271 := bstep (se 1 (by rfl) ⟨290453, by rfl⟩ : syracuseStep 387271 = 580907) B580907
theorem B387291 : Blo 385764 387291 := bstep (se 1 (by rfl) ⟨290468, by rfl⟩ : syracuseStep 387291 = 580937) B580937
theorem B977143 : Blo 385764 977143 := bstep (se 1 (by rfl) ⟨732857, by rfl⟩ : syracuseStep 977143 = 1465715) B1465715
theorem B387367 : Blo 385764 387367 := bstep (se 1 (by rfl) ⟨290525, by rfl⟩ : syracuseStep 387367 = 581051) B581051
theorem B387407 : Blo 385764 387407 := bstep (se 1 (by rfl) ⟨290555, by rfl⟩ : syracuseStep 387407 = 581111) B581111
theorem B387423 : Blo 385764 387423 := bstep (se 1 (by rfl) ⟨290567, by rfl⟩ : syracuseStep 387423 = 581135) B581135
theorem B387451 : Blo 385764 387451 := bstep (se 1 (by rfl) ⟨290588, by rfl⟩ : syracuseStep 387451 = 581177) B581177
theorem B387503 : Blo 385764 387503 := bstep (se 1 (by rfl) ⟨290627, by rfl⟩ : syracuseStep 387503 = 581255) B581255
theorem B584111 : Blo 385764 584111 := bstep (se 1 (by rfl) ⟨438083, by rfl⟩ : syracuseStep 584111 = 876167) B876167
theorem B387527 : Blo 385764 387527 := bstep (se 1 (by rfl) ⟨290645, by rfl⟩ : syracuseStep 387527 = 581291) B581291
theorem B387547 : Blo 385764 387547 := bstep (se 1 (by rfl) ⟨290660, by rfl⟩ : syracuseStep 387547 = 581321) B581321
theorem B977417 : Blo 385764 977417 := bstep (se 2 (by rfl) ⟨366531, by rfl⟩ : syracuseStep 977417 = 733063) B733063
theorem B584201 : Blo 385764 584201 := bstep (se 2 (by rfl) ⟨219075, by rfl⟩ : syracuseStep 584201 = 438151) B438151
theorem B977447 : Blo 385764 977447 := bstep (se 1 (by rfl) ⟨733085, by rfl⟩ : syracuseStep 977447 = 1466171) B1466171
theorem B387623 : Blo 385764 387623 := bstep (se 1 (by rfl) ⟨290717, by rfl⟩ : syracuseStep 387623 = 581435) B581435
theorem B584231 : Blo 385764 584231 := bstep (se 1 (by rfl) ⟨438173, by rfl⟩ : syracuseStep 584231 = 876347) B876347
theorem B387663 : Blo 385764 387663 := bstep (se 1 (by rfl) ⟨290747, by rfl⟩ : syracuseStep 387663 = 581495) B581495
theorem B387679 : Blo 385764 387679 := bstep (se 1 (by rfl) ⟨290759, by rfl⟩ : syracuseStep 387679 = 581519) B581519
theorem B387707 : Blo 385764 387707 := bstep (se 1 (by rfl) ⟨290780, by rfl⟩ : syracuseStep 387707 = 581561) B581561
theorem B584315 : Blo 385764 584315 := bstep (se 1 (by rfl) ⟨438236, by rfl⟩ : syracuseStep 584315 = 876473) B876473
theorem B387759 : Blo 385764 387759 := bstep (se 1 (by rfl) ⟨290819, by rfl⟩ : syracuseStep 387759 = 581639) B581639
theorem B4975289 : Blo 385764 4975289 := bstep (se 2 (by rfl) ⟨1865733, by rfl⟩ : syracuseStep 4975289 = 3731467) B3731467
theorem B1469117 : Blo 385764 1469117 := bstep (se 3 (by rfl) ⟨275459, by rfl⟩ : syracuseStep 1469117 = 550919) B550919
theorem B1305287 : Blo 385764 1305287 := bstep (se 1 (by rfl) ⟨978965, by rfl⟩ : syracuseStep 1305287 = 1957931) B1957931
theorem B387783 : Blo 385764 387783 := bstep (se 1 (by rfl) ⟨290837, by rfl⟩ : syracuseStep 387783 = 581675) B581675
theorem B387803 : Blo 385764 387803 := bstep (se 1 (by rfl) ⟨290852, by rfl⟩ : syracuseStep 387803 = 581705) B581705
theorem B584441 : Blo 385764 584441 := bstep (se 2 (by rfl) ⟨219165, by rfl⟩ : syracuseStep 584441 = 438331) B438331
theorem B387879 : Blo 385764 387879 := bstep (se 1 (by rfl) ⟨290909, by rfl⟩ : syracuseStep 387879 = 581819) B581819
theorem B387919 : Blo 385764 387919 := bstep (se 1 (by rfl) ⟨290939, by rfl⟩ : syracuseStep 387919 = 581879) B581879
theorem B387935 : Blo 385764 387935 := bstep (se 1 (by rfl) ⟨290951, by rfl⟩ : syracuseStep 387935 = 581903) B581903
theorem B584543 : Blo 385764 584543 := bstep (se 1 (by rfl) ⟨438407, by rfl⟩ : syracuseStep 584543 = 876815) B876815
theorem B551785 : Blo 385764 551785 := bstep (se 2 (by rfl) ⟨206919, by rfl⟩ : syracuseStep 551785 = 413839) B413839
theorem B977771 : Blo 385764 977771 := bstep (se 1 (by rfl) ⟨733328, by rfl⟩ : syracuseStep 977771 = 1466657) B1466657
theorem B584555 : Blo 385764 584555 := bstep (se 1 (by rfl) ⟨438416, by rfl⟩ : syracuseStep 584555 = 876833) B876833
theorem B387963 : Blo 385764 387963 := bstep (se 1 (by rfl) ⟨290972, by rfl⟩ : syracuseStep 387963 = 581945) B581945
theorem B388015 : Blo 385764 388015 := bstep (se 1 (by rfl) ⟨291011, by rfl⟩ : syracuseStep 388015 = 582023) B582023
theorem B388039 : Blo 385764 388039 := bstep (se 1 (by rfl) ⟨291029, by rfl⟩ : syracuseStep 388039 = 582059) B582059
theorem B388059 : Blo 385764 388059 := bstep (se 1 (by rfl) ⟨291044, by rfl⟩ : syracuseStep 388059 = 582089) B582089
theorem B3304421 : Blo 385764 3304421 := bstep (se 4 (by rfl) ⟨309789, by rfl⟩ : syracuseStep 3304421 = 619579) B619579
theorem B388135 : Blo 385764 388135 := bstep (se 1 (by rfl) ⟨291101, by rfl⟩ : syracuseStep 388135 = 582203) B582203
theorem B388175 : Blo 385764 388175 := bstep (se 1 (by rfl) ⟨291131, by rfl⟩ : syracuseStep 388175 = 582263) B582263
theorem B388191 : Blo 385764 388191 := bstep (se 1 (by rfl) ⟨291143, by rfl⟩ : syracuseStep 388191 = 582287) B582287
theorem B388219 : Blo 385764 388219 := bstep (se 1 (by rfl) ⟨291164, by rfl⟩ : syracuseStep 388219 = 582329) B582329
theorem B1240235 : Blo 385764 1240235 := bstep (se 1 (by rfl) ⟨930176, by rfl⟩ : syracuseStep 1240235 = 1860353) B1860353
theorem B388271 : Blo 385764 388271 := bstep (se 1 (by rfl) ⟨291203, by rfl⟩ : syracuseStep 388271 = 582407) B582407
theorem B388295 : Blo 385764 388295 := bstep (se 1 (by rfl) ⟨291221, by rfl⟩ : syracuseStep 388295 = 582443) B582443
theorem B388315 : Blo 385764 388315 := bstep (se 1 (by rfl) ⟨291236, by rfl⟩ : syracuseStep 388315 = 582473) B582473
theorem B388391 : Blo 385764 388391 := bstep (se 1 (by rfl) ⟨291293, by rfl⟩ : syracuseStep 388391 = 582587) B582587
theorem B388431 : Blo 385764 388431 := bstep (se 1 (by rfl) ⟨291323, by rfl⟩ : syracuseStep 388431 = 582647) B582647
theorem B388447 : Blo 385764 388447 := bstep (se 1 (by rfl) ⟨291335, by rfl⟩ : syracuseStep 388447 = 582671) B582671
theorem B388475 : Blo 385764 388475 := bstep (se 1 (by rfl) ⟨291356, by rfl⟩ : syracuseStep 388475 = 582713) B582713
theorem B388527 : Blo 385764 388527 := bstep (se 1 (by rfl) ⟨291395, by rfl⟩ : syracuseStep 388527 = 582791) B582791
theorem B388551 : Blo 385764 388551 := bstep (se 1 (by rfl) ⟨291413, by rfl⟩ : syracuseStep 388551 = 582827) B582827
theorem B388571 : Blo 385764 388571 := bstep (se 1 (by rfl) ⟨291428, by rfl⟩ : syracuseStep 388571 = 582857) B582857
theorem B978419 : Blo 385764 978419 := bstep (se 1 (by rfl) ⟨733814, by rfl⟩ : syracuseStep 978419 = 1467629) B1467629
theorem B3730931 : Blo 385764 3730931 := bstep (se 1 (by rfl) ⟨2798198, by rfl⟩ : syracuseStep 3730931 = 5596397) B5596397
theorem B552457 : Blo 385764 552457 := bstep (se 2 (by rfl) ⟨207171, by rfl⟩ : syracuseStep 552457 = 414343) B414343
theorem B1306151 : Blo 385764 1306151 := bstep (se 1 (by rfl) ⟨979613, by rfl⟩ : syracuseStep 1306151 = 1959227) B1959227
theorem B2485799 : Blo 385764 2485799 := bstep (se 1 (by rfl) ⟨1864349, by rfl⟩ : syracuseStep 2485799 = 3728699) B3728699
theorem B388647 : Blo 385764 388647 := bstep (se 1 (by rfl) ⟨291485, by rfl⟩ : syracuseStep 388647 = 582971) B582971
theorem B388687 : Blo 385764 388687 := bstep (se 1 (by rfl) ⟨291515, by rfl⟩ : syracuseStep 388687 = 583031) B583031
theorem B388703 : Blo 385764 388703 := bstep (se 1 (by rfl) ⟨291527, by rfl⟩ : syracuseStep 388703 = 583055) B583055
theorem B388731 : Blo 385764 388731 := bstep (se 1 (by rfl) ⟨291548, by rfl⟩ : syracuseStep 388731 = 583097) B583097
theorem B1306259 : Blo 385764 1306259 := bstep (se 1 (by rfl) ⟨979694, by rfl⟩ : syracuseStep 1306259 = 1959389) B1959389
theorem B388783 : Blo 385764 388783 := bstep (se 1 (by rfl) ⟨291587, by rfl⟩ : syracuseStep 388783 = 583175) B583175
theorem B388807 : Blo 385764 388807 := bstep (se 1 (by rfl) ⟨291605, by rfl⟩ : syracuseStep 388807 = 583211) B583211
theorem B388827 : Blo 385764 388827 := bstep (se 1 (by rfl) ⟨291620, by rfl⟩ : syracuseStep 388827 = 583241) B583241
theorem B1404665 : Blo 385764 1404665 := bstep (se 2 (by rfl) ⟨526749, by rfl⟩ : syracuseStep 1404665 = 1053499) B1053499
theorem B388903 : Blo 385764 388903 := bstep (se 1 (by rfl) ⟨291677, by rfl⟩ : syracuseStep 388903 = 583355) B583355
theorem B388943 : Blo 385764 388943 := bstep (se 1 (by rfl) ⟨291707, by rfl⟩ : syracuseStep 388943 = 583415) B583415
theorem B388959 : Blo 385764 388959 := bstep (se 1 (by rfl) ⟨291719, by rfl⟩ : syracuseStep 388959 = 583439) B583439
theorem B1306475 : Blo 385764 1306475 := bstep (se 1 (by rfl) ⟨979856, by rfl⟩ : syracuseStep 1306475 = 1959713) B1959713
theorem B388987 : Blo 385764 388987 := bstep (se 1 (by rfl) ⟨291740, by rfl⟩ : syracuseStep 388987 = 583481) B583481
theorem B1306529 : Blo 385764 1306529 := bstep (se 2 (by rfl) ⟨489948, by rfl⟩ : syracuseStep 1306529 = 979897) B979897
theorem B389039 : Blo 385764 389039 := bstep (se 1 (by rfl) ⟨291779, by rfl⟩ : syracuseStep 389039 = 583559) B583559
theorem B978875 : Blo 385764 978875 := bstep (se 1 (by rfl) ⟨734156, by rfl⟩ : syracuseStep 978875 = 1468313) B1468313
theorem B2486209 : Blo 385764 2486209 := bstep (se 2 (by rfl) ⟨932328, by rfl⟩ : syracuseStep 2486209 = 1864657) B1864657
theorem B389063 : Blo 385764 389063 := bstep (se 1 (by rfl) ⟨291797, by rfl⟩ : syracuseStep 389063 = 583595) B583595
theorem B389083 : Blo 385764 389083 := bstep (se 1 (by rfl) ⟨291812, by rfl⟩ : syracuseStep 389083 = 583625) B583625
theorem B389159 : Blo 385764 389159 := bstep (se 1 (by rfl) ⟨291869, by rfl⟩ : syracuseStep 389159 = 583739) B583739
theorem B389199 : Blo 385764 389199 := bstep (se 1 (by rfl) ⟨291899, by rfl⟩ : syracuseStep 389199 = 583799) B583799
theorem B1470545 : Blo 385764 1470545 := bstep (se 2 (by rfl) ⟨551454, by rfl⟩ : syracuseStep 1470545 = 1102909) B1102909
theorem B389215 : Blo 385764 389215 := bstep (se 1 (by rfl) ⟨291911, by rfl⟩ : syracuseStep 389215 = 583823) B583823
theorem B389243 : Blo 385764 389243 := bstep (se 1 (by rfl) ⟨291932, by rfl⟩ : syracuseStep 389243 = 583865) B583865
theorem B389295 : Blo 385764 389295 := bstep (se 1 (by rfl) ⟨291971, by rfl⟩ : syracuseStep 389295 = 583943) B583943
theorem B389319 : Blo 385764 389319 := bstep (se 1 (by rfl) ⟨291989, by rfl⟩ : syracuseStep 389319 = 583979) B583979
theorem B389339 : Blo 385764 389339 := bstep (se 1 (by rfl) ⟨292004, by rfl⟩ : syracuseStep 389339 = 584009) B584009
theorem B389415 : Blo 385764 389415 := bstep (se 1 (by rfl) ⟨292061, by rfl⟩ : syracuseStep 389415 = 584123) B584123
theorem B389455 : Blo 385764 389455 := bstep (se 1 (by rfl) ⟨292091, by rfl⟩ : syracuseStep 389455 = 584183) B584183
theorem B389471 : Blo 385764 389471 := bstep (se 1 (by rfl) ⟨292103, by rfl⟩ : syracuseStep 389471 = 584207) B584207
theorem B389499 : Blo 385764 389499 := bstep (se 1 (by rfl) ⟨292124, by rfl⟩ : syracuseStep 389499 = 584249) B584249
theorem B389551 : Blo 385764 389551 := bstep (se 1 (by rfl) ⟨292163, by rfl⟩ : syracuseStep 389551 = 584327) B584327
theorem B782779 : Blo 385764 782779 := bstep (se 1 (by rfl) ⟨587084, by rfl⟩ : syracuseStep 782779 = 1174169) B1174169
theorem B389575 : Blo 385764 389575 := bstep (se 1 (by rfl) ⟨292181, by rfl⟩ : syracuseStep 389575 = 584363) B584363
theorem B651739 : Blo 385764 651739 := bstep (se 1 (by rfl) ⟨488804, by rfl⟩ : syracuseStep 651739 = 977609) B977609
theorem B389595 : Blo 385764 389595 := bstep (se 1 (by rfl) ⟨292196, by rfl⟩ : syracuseStep 389595 = 584393) B584393
theorem B1307123 : Blo 385764 1307123 := bstep (se 1 (by rfl) ⟨980342, by rfl⟩ : syracuseStep 1307123 = 1960685) B1960685
theorem B389671 : Blo 385764 389671 := bstep (se 1 (by rfl) ⟨292253, by rfl⟩ : syracuseStep 389671 = 584507) B584507
theorem B389711 : Blo 385764 389711 := bstep (se 1 (by rfl) ⟨292283, by rfl⟩ : syracuseStep 389711 = 584567) B584567
theorem B389727 : Blo 385764 389727 := bstep (se 1 (by rfl) ⟨292295, by rfl⟩ : syracuseStep 389727 = 584591) B584591
theorem B979553 : Blo 385764 979553 := bstep (se 2 (by rfl) ⟨367332, by rfl⟩ : syracuseStep 979553 = 734665) B734665
theorem B389755 : Blo 385764 389755 := bstep (se 1 (by rfl) ⟨292316, by rfl⟩ : syracuseStep 389755 = 584633) B584633
theorem B717511 : Blo 385764 717511 := bstep (se 1 (by rfl) ⟨538133, by rfl⟩ : syracuseStep 717511 = 1076267) B1076267
theorem B553721 : Blo 385764 553721 := bstep (se 2 (by rfl) ⟨207645, by rfl⟩ : syracuseStep 553721 = 415291) B415291
theorem B553835 : Blo 385764 553835 := bstep (se 1 (by rfl) ⟨415376, by rfl⟩ : syracuseStep 553835 = 830753) B830753
theorem B1307663 : Blo 385764 1307663 := bstep (se 1 (by rfl) ⟨980747, by rfl⟩ : syracuseStep 1307663 = 1961495) B1961495
theorem B652367 : Blo 385764 652367 := bstep (se 1 (by rfl) ⟨489275, by rfl⟩ : syracuseStep 652367 = 978551) B978551
theorem B1045583 : Blo 385764 1045583 := bstep (se 1 (by rfl) ⟨784187, by rfl⟩ : syracuseStep 1045583 = 1568375) B1568375
theorem B14840981 : Blo 385764 14840981 := bstep (se 6 (by rfl) ⟨347835, by rfl⟩ : syracuseStep 14840981 = 695671) B695671
theorem B4945049 : Blo 385764 4945049 := bstep (se 2 (by rfl) ⟨1854393, by rfl⟩ : syracuseStep 4945049 = 3708787) B3708787
theorem B2717093 : Blo 385764 2717093 := bstep (se 4 (by rfl) ⟨254727, by rfl⟩ : syracuseStep 2717093 = 509455) B509455
theorem B1177051 : Blo 385764 1177051 := bstep (se 1 (by rfl) ⟨882788, by rfl⟩ : syracuseStep 1177051 = 1765577) B1765577
theorem B1472033 : Blo 385764 1472033 := bstep (se 2 (by rfl) ⟨552012, by rfl⟩ : syracuseStep 1472033 = 1104025) B1104025
theorem B1308257 : Blo 385764 1308257 := bstep (se 2 (by rfl) ⟨490596, by rfl⟩ : syracuseStep 1308257 = 981193) B981193
theorem B2094781 : Blo 385764 2094781 := bstep (se 3 (by rfl) ⟨392771, by rfl⟩ : syracuseStep 2094781 = 785543) B785543
theorem B1472215 : Blo 385764 1472215 := bstep (se 1 (by rfl) ⟨1104161, by rfl⟩ : syracuseStep 1472215 = 2208323) B2208323
theorem B5994283 : Blo 385764 5994283 := bstep (se 1 (by rfl) ⟨4495712, by rfl⟩ : syracuseStep 5994283 = 8991425) B8991425
theorem B653231 : Blo 385764 653231 := bstep (se 1 (by rfl) ⟨489923, by rfl⟩ : syracuseStep 653231 = 979847) B979847
theorem B1472519 : Blo 385764 1472519 := bstep (se 1 (by rfl) ⟨1104389, by rfl⟩ : syracuseStep 1472519 = 2208779) B2208779
theorem B981011 : Blo 385764 981011 := bstep (se 1 (by rfl) ⟨735758, by rfl⟩ : syracuseStep 981011 = 1471517) B1471517
theorem B653663 : Blo 385764 653663 := bstep (se 1 (by rfl) ⟨490247, by rfl⟩ : syracuseStep 653663 = 980495) B980495
theorem B620983 : Blo 385764 620983 := bstep (se 1 (by rfl) ⟨465737, by rfl⟩ : syracuseStep 620983 = 931475) B931475
theorem B981467 : Blo 385764 981467 := bstep (se 1 (by rfl) ⟨736100, by rfl⟩ : syracuseStep 981467 = 1472201) B1472201
theorem B1473005 : Blo 385764 1473005 := bstep (se 3 (by rfl) ⟨276188, by rfl⟩ : syracuseStep 1473005 = 552377) B552377
theorem B1047163 : Blo 385764 1047163 := bstep (se 1 (by rfl) ⟨785372, by rfl⟩ : syracuseStep 1047163 = 1570745) B1570745
theorem B1178327 : Blo 385764 1178327 := bstep (se 1 (by rfl) ⟨883745, by rfl⟩ : syracuseStep 1178327 = 1767491) B1767491
theorem B1145707 : Blo 385764 1145707 := bstep (se 1 (by rfl) ⟨859280, by rfl⟩ : syracuseStep 1145707 = 1718561) B1718561
theorem B654223 : Blo 385764 654223 := bstep (se 1 (by rfl) ⟨490667, by rfl⟩ : syracuseStep 654223 = 981335) B981335
theorem B5307281 : Blo 385764 5307281 := bstep (se 2 (by rfl) ⟨1990230, by rfl⟩ : syracuseStep 5307281 = 3980461) B3980461
theorem B4717541 : Blo 385764 4717541 := bstep (se 4 (by rfl) ⟨442269, by rfl⟩ : syracuseStep 4717541 = 884539) B884539
theorem B1309715 : Blo 385764 1309715 := bstep (se 1 (by rfl) ⟨982286, by rfl⟩ : syracuseStep 1309715 = 1964573) B1964573
theorem B1310039 : Blo 385764 1310039 := bstep (se 1 (by rfl) ⟨982529, by rfl⟩ : syracuseStep 1310039 = 1965059) B1965059
theorem B654905 : Blo 385764 654905 := bstep (se 2 (by rfl) ⟨245589, by rfl⟩ : syracuseStep 654905 = 491179) B491179
theorem B1474145 : Blo 385764 1474145 := bstep (se 2 (by rfl) ⟨552804, by rfl⟩ : syracuseStep 1474145 = 1105609) B1105609
theorem B982651 : Blo 385764 982651 := bstep (se 1 (by rfl) ⟨736988, by rfl⟩ : syracuseStep 982651 = 1473977) B1473977
theorem B1965707 : Blo 385764 1965707 := bstep (se 1 (by rfl) ⟨1474280, by rfl⟩ : syracuseStep 1965707 = 2948561) B2948561
theorem B2096855 : Blo 385764 2096855 := bstep (se 1 (by rfl) ⟨1572641, by rfl⟩ : syracuseStep 2096855 = 3145283) B3145283
theorem B491447 : Blo 385764 491447 := bstep (se 1 (by rfl) ⟨368585, by rfl⟩ : syracuseStep 491447 = 737171) B737171
theorem B62357521 : Blo 385764 62357521 := bstep (se 2 (by rfl) ⟨23384070, by rfl⟩ : syracuseStep 62357521 = 46768141) B46768141
theorem B45547541 : Blo 385764 45547541 := bstep (se 6 (by rfl) ⟨1067520, by rfl⟩ : syracuseStep 45547541 = 2135041) B2135041
theorem B15728717 : Blo 385764 15728717 := bstep (se 3 (by rfl) ⟨2949134, by rfl⟩ : syracuseStep 15728717 = 5898269) B5898269
theorem B655465 : Blo 385764 655465 := bstep (se 2 (by rfl) ⟨245799, by rfl⟩ : syracuseStep 655465 = 491599) B491599
theorem B524863 : Blo 385764 524863 := bstep (se 1 (by rfl) ⟨393647, by rfl⟩ : syracuseStep 524863 = 787295) B787295
theorem B492095 : Blo 385764 492095 := bstep (se 1 (by rfl) ⟨369071, by rfl⟩ : syracuseStep 492095 = 738143) B738143
theorem B983623 : Blo 385764 983623 := bstep (se 1 (by rfl) ⟨737717, by rfl⟩ : syracuseStep 983623 = 1475435) B1475435
theorem B983735 : Blo 385764 983735 := bstep (se 1 (by rfl) ⟨737801, by rfl⟩ : syracuseStep 983735 = 1475603) B1475603
theorem B1966841 : Blo 385764 1966841 := bstep (se 2 (by rfl) ⟨737565, by rfl⟩ : syracuseStep 1966841 = 1475131) B1475131
theorem B886153 : Blo 385764 886153 := bstep (se 2 (by rfl) ⟨332307, by rfl⟩ : syracuseStep 886153 = 664615) B664615
theorem B1476103 : Blo 385764 1476103 := bstep (se 1 (by rfl) ⟨1107077, by rfl⟩ : syracuseStep 1476103 = 2214155) B2214155
theorem B984737 : Blo 385764 984737 := bstep (se 2 (by rfl) ⟨369276, by rfl⟩ : syracuseStep 984737 = 738553) B738553
theorem B657193 : Blo 385764 657193 := bstep (se 2 (by rfl) ⟨246447, by rfl⟩ : syracuseStep 657193 = 492895) B492895
theorem B1476407 : Blo 385764 1476407 := bstep (se 1 (by rfl) ⟨1107305, by rfl⟩ : syracuseStep 1476407 = 2214611) B2214611
theorem B1476589 : Blo 385764 1476589 := bstep (se 3 (by rfl) ⟨276860, by rfl⟩ : syracuseStep 1476589 = 553721) B553721
theorem B985193 : Blo 385764 985193 := bstep (se 2 (by rfl) ⟨369447, by rfl⟩ : syracuseStep 985193 = 738895) B738895
theorem B1116413 : Blo 385764 1116413 := bstep (se 3 (by rfl) ⟨209327, by rfl⟩ : syracuseStep 1116413 = 418655) B418655
theorem B1476893 : Blo 385764 1476893 := bstep (se 3 (by rfl) ⟨276917, by rfl⟩ : syracuseStep 1476893 = 553835) B553835
theorem B2984359 : Blo 385764 2984359 := bstep (se 1 (by rfl) ⟨2238269, by rfl⟩ : syracuseStep 2984359 = 4476539) B4476539
theorem B2099623 : Blo 385764 2099623 := bstep (se 1 (by rfl) ⟨1574717, by rfl⟩ : syracuseStep 2099623 = 3149435) B3149435
theorem B1477075 : Blo 385764 1477075 := bstep (se 1 (by rfl) ⟨1107806, by rfl⟩ : syracuseStep 1477075 = 2215613) B2215613
theorem B2689523 : Blo 385764 2689523 := bstep (se 1 (by rfl) ⟨2017142, by rfl⟩ : syracuseStep 2689523 = 4034285) B4034285
theorem B985679 : Blo 385764 985679 := bstep (se 1 (by rfl) ⟨739259, by rfl⟩ : syracuseStep 985679 = 1478519) B1478519
theorem B1313387 : Blo 385764 1313387 := bstep (se 1 (by rfl) ⟨985040, by rfl⟩ : syracuseStep 1313387 = 1970081) B1970081
theorem B4426487 : Blo 385764 4426487 := bstep (se 1 (by rfl) ⟨3319865, by rfl⟩ : syracuseStep 4426487 = 6639731) B6639731
theorem B1248155 : Blo 385764 1248155 := bstep (se 1 (by rfl) ⟨936116, by rfl⟩ : syracuseStep 1248155 = 1872233) B1872233
theorem B1477547 : Blo 385764 1477547 := bstep (se 1 (by rfl) ⟨1108160, by rfl⟩ : syracuseStep 1477547 = 2216321) B2216321
theorem B887723 : Blo 385764 887723 := bstep (se 1 (by rfl) ⟨665792, by rfl⟩ : syracuseStep 887723 = 1331585) B1331585
theorem B1313981 : Blo 385764 1313981 := bstep (se 3 (by rfl) ⟨246371, by rfl⟩ : syracuseStep 1313981 = 492743) B492743
theorem B986327 : Blo 385764 986327 := bstep (se 1 (by rfl) ⟨739745, by rfl⟩ : syracuseStep 986327 = 1479491) B1479491
theorem B2100599 : Blo 385764 2100599 := bstep (se 1 (by rfl) ⟨1575449, by rfl⟩ : syracuseStep 2100599 = 3150899) B3150899
theorem B1969595 : Blo 385764 1969595 := bstep (se 1 (by rfl) ⟨1477196, by rfl⟩ : syracuseStep 1969595 = 2954393) B2954393
theorem B3149725 : Blo 385764 3149725 := bstep (se 3 (by rfl) ⟨590573, by rfl⟩ : syracuseStep 3149725 = 1181147) B1181147
theorem B7475165 : Blo 385764 7475165 := bstep (se 3 (by rfl) ⟨1401593, by rfl⟩ : syracuseStep 7475165 = 2803187) B2803187
theorem B15044579 : Blo 385764 15044579 := bstep (se 1 (by rfl) ⟨11283434, by rfl⟩ : syracuseStep 15044579 = 22566869) B22566869
theorem B2363755 : Blo 385764 2363755 := bstep (se 1 (by rfl) ⟨1772816, by rfl⟩ : syracuseStep 2363755 = 3545633) B3545633
theorem B1479019 : Blo 385764 1479019 := bstep (se 1 (by rfl) ⟨1109264, by rfl⟩ : syracuseStep 1479019 = 2218529) B2218529
theorem B3314195 : Blo 385764 3314195 := bstep (se 1 (by rfl) ⟨2485646, by rfl⟩ : syracuseStep 3314195 = 4971293) B4971293
theorem B1970891 : Blo 385764 1970891 := bstep (se 1 (by rfl) ⟨1478168, by rfl⟩ : syracuseStep 1970891 = 2956337) B2956337
theorem B4395869 : Blo 385764 4395869 := bstep (se 3 (by rfl) ⟨824225, by rfl⟩ : syracuseStep 4395869 = 1648451) B1648451
theorem B2102111 : Blo 385764 2102111 := bstep (se 1 (by rfl) ⟨1576583, by rfl⟩ : syracuseStep 2102111 = 3153167) B3153167
theorem B1971053 : Blo 385764 1971053 := bstep (se 3 (by rfl) ⟨369572, by rfl⟩ : syracuseStep 1971053 = 739145) B739145
theorem B13407437 : Blo 385764 13407437 := bstep (se 3 (by rfl) ⟨2513894, by rfl⟩ : syracuseStep 13407437 = 5027789) B5027789
theorem B3314945 : Blo 385764 3314945 := bstep (se 2 (by rfl) ⟨1243104, by rfl⟩ : syracuseStep 3314945 = 2486209) B2486209
theorem B628105 : Blo 385764 628105 := bstep (se 2 (by rfl) ⟨235539, by rfl⟩ : syracuseStep 628105 = 471079) B471079
theorem B956681 : Blo 385764 956681 := bstep (se 2 (by rfl) ⟨358755, by rfl⟩ : syracuseStep 956681 = 717511) B717511
theorem B8395109 : Blo 385764 8395109 := bstep (se 4 (by rfl) ⟨787041, by rfl⟩ : syracuseStep 8395109 = 1574083) B1574083
theorem B1776323 : Blo 385764 1776323 := bstep (se 1 (by rfl) ⟨1332242, by rfl⟩ : syracuseStep 1776323 = 2664485) B2664485
theorem B3316859 : Blo 385764 3316859 := bstep (se 1 (by rfl) ⟨2487644, by rfl⟩ : syracuseStep 3316859 = 4975289) B4975289
theorem B2202947 : Blo 385764 2202947 := bstep (se 1 (by rfl) ⟨1652210, by rfl⟩ : syracuseStep 2202947 = 3304421) B3304421
theorem B826823 : Blo 385764 826823 := bstep (se 1 (by rfl) ⟨620117, by rfl⟩ : syracuseStep 826823 = 1240235) B1240235
theorem B2956823 : Blo 385764 2956823 := bstep (se 1 (by rfl) ⟨2217617, by rfl⟩ : syracuseStep 2956823 = 4435235) B4435235
theorem B2793041 : Blo 385764 2793041 := bstep (se 2 (by rfl) ⟨1047390, by rfl⟩ : syracuseStep 2793041 = 2094781) B2094781
theorem B466607 : Blo 385764 466607 := bstep (se 1 (by rfl) ⟨349955, by rfl⟩ : syracuseStep 466607 = 699911) B699911
theorem B466895 : Blo 385764 466895 := bstep (se 1 (by rfl) ⟨350171, by rfl⟩ : syracuseStep 466895 = 700343) B700343
theorem B28712981 : Blo 385764 28712981 := bstep (se 6 (by rfl) ⟨672960, by rfl⟩ : syracuseStep 28712981 = 1345921) B1345921
theorem B991361 : Blo 385764 991361 := bstep (se 2 (by rfl) ⟨371760, by rfl⟩ : syracuseStep 991361 = 743521) B743521
theorem B1056979 : Blo 385764 1056979 := bstep (se 1 (by rfl) ⟨792734, by rfl⟩ : syracuseStep 1056979 = 1585469) B1585469
theorem B827977 : Blo 385764 827977 := bstep (se 2 (by rfl) ⟨310491, by rfl⟩ : syracuseStep 827977 = 620983) B620983
theorem B434911 : Blo 385764 434911 := bstep (se 1 (by rfl) ⟨326183, by rfl⟩ : syracuseStep 434911 = 652367) B652367
theorem B697055 : Blo 385764 697055 := bstep (se 1 (by rfl) ⟨522791, by rfl⟩ : syracuseStep 697055 = 1045583) B1045583
theorem B1811395 : Blo 385764 1811395 := bstep (se 1 (by rfl) ⟨1358546, by rfl⟩ : syracuseStep 1811395 = 2717093) B2717093
theorem B926939 : Blo 385764 926939 := bstep (se 1 (by rfl) ⟨695204, by rfl⟩ : syracuseStep 926939 = 1390409) B1390409
theorem B435487 : Blo 385764 435487 := bstep (se 1 (by rfl) ⟨326615, by rfl⟩ : syracuseStep 435487 = 653231) B653231
theorem B121185679 : Blo 385764 121185679 := bstep (se 1 (by rfl) ⟨90889259, by rfl⟩ : syracuseStep 121185679 = 181778519) B181778519
theorem B435775 : Blo 385764 435775 := bstep (se 1 (by rfl) ⟨326831, by rfl⟩ : syracuseStep 435775 = 653663) B653663
theorem B3745921 : Blo 385764 3745921 := bstep (se 2 (by rfl) ⟨1404720, by rfl⟩ : syracuseStep 3745921 = 2809441) B2809441
theorem B436603 : Blo 385764 436603 := bstep (se 1 (by rfl) ⟨327452, by rfl⟩ : syracuseStep 436603 = 654905) B654905
theorem B928427 : Blo 385764 928427 := bstep (se 1 (by rfl) ⟨696320, by rfl⟩ : syracuseStep 928427 = 1392641) B1392641
theorem B4270801 : Blo 385764 4270801 := bstep (se 2 (by rfl) ⟨1601550, by rfl⟩ : syracuseStep 4270801 = 3203101) B3203101
theorem B8366915 : Blo 385764 8366915 := bstep (se 1 (by rfl) ⟨6275186, by rfl⟩ : syracuseStep 8366915 = 12550373) B12550373
theorem B797519 : Blo 385764 797519 := bstep (se 1 (by rfl) ⟨598139, by rfl⟩ : syracuseStep 797519 = 1196279) B1196279
theorem B437071 : Blo 385764 437071 := bstep (se 1 (by rfl) ⟨327803, by rfl⟩ : syracuseStep 437071 = 655607) B655607
theorem B621849635 : Blo 385764 621849635 := bstep (se 1 (by rfl) ⟨466387226, by rfl⟩ : syracuseStep 621849635 = 932774453) B932774453
theorem B437467 : Blo 385764 437467 := bstep (se 1 (by rfl) ⟨328100, by rfl⟩ : syracuseStep 437467 = 656201) B656201
theorem B732539 : Blo 385764 732539 := bstep (se 1 (by rfl) ⟨549404, by rfl⟩ : syracuseStep 732539 = 1098809) B1098809
theorem B437755 : Blo 385764 437755 := bstep (se 1 (by rfl) ⟨328316, by rfl⟩ : syracuseStep 437755 = 656633) B656633
theorem B863801 : Blo 385764 863801 := bstep (se 2 (by rfl) ⟨323925, by rfl⟩ : syracuseStep 863801 = 647851) B647851
theorem B437935 : Blo 385764 437935 := bstep (se 1 (by rfl) ⟨328451, by rfl⟩ : syracuseStep 437935 = 656903) B656903
theorem B831163 : Blo 385764 831163 := bstep (se 1 (by rfl) ⟨623372, by rfl⟩ : syracuseStep 831163 = 1246745) B1246745
theorem B438223 : Blo 385764 438223 := bstep (se 1 (by rfl) ⟨328667, by rfl⟩ : syracuseStep 438223 = 657335) B657335
theorem B15052825 : Blo 385764 15052825 := bstep (se 2 (by rfl) ⟨5644809, by rfl⟩ : syracuseStep 15052825 = 11289619) B11289619
theorem B16330817 : Blo 385764 16330817 := bstep (se 2 (by rfl) ⟨6124056, by rfl⟩ : syracuseStep 16330817 = 12248113) B12248113
theorem B3551321 : Blo 385764 3551321 := bstep (se 2 (by rfl) ⟨1331745, by rfl⟩ : syracuseStep 3551321 = 2663491) B2663491
theorem B733769 : Blo 385764 733769 := bstep (se 2 (by rfl) ⟨275163, by rfl⟩ : syracuseStep 733769 = 550327) B550327
theorem B2142935 : Blo 385764 2142935 := bstep (se 1 (by rfl) ⟨1607201, by rfl⟩ : syracuseStep 2142935 = 3214403) B3214403
theorem B930791 : Blo 385764 930791 := bstep (se 1 (by rfl) ⟨698093, by rfl⟩ : syracuseStep 930791 = 1396187) B1396187
theorem B3356293 : Blo 385764 3356293 := bstep (se 4 (by rfl) ⟨314652, by rfl⟩ : syracuseStep 3356293 = 629305) B629305
theorem B4962167 : Blo 385764 4962167 := bstep (se 1 (by rfl) ⟨3721625, by rfl⟩ : syracuseStep 4962167 = 7443251) B7443251
theorem B931945 : Blo 385764 931945 := bstep (se 2 (by rfl) ⟨349479, by rfl⟩ : syracuseStep 931945 = 698959) B698959
theorem B4438151 : Blo 385764 4438151 := bstep (se 1 (by rfl) ⟨3328613, by rfl⟩ : syracuseStep 4438151 = 6657227) B6657227
theorem B735713 : Blo 385764 735713 := bstep (se 2 (by rfl) ⟨275892, by rfl⟩ : syracuseStep 735713 = 551785) B551785
theorem B6110437 : Blo 385764 6110437 := bstep (se 4 (by rfl) ⟨572853, by rfl⟩ : syracuseStep 6110437 = 1145707) B1145707
theorem B736609 : Blo 385764 736609 := bstep (se 2 (by rfl) ⟨276228, by rfl⟩ : syracuseStep 736609 = 552457) B552457
theorem B1621367 : Blo 385764 1621367 := bstep (se 1 (by rfl) ⟨1216025, by rfl⟩ : syracuseStep 1621367 = 2432051) B2432051
theorem B5291513 : Blo 385764 5291513 := bstep (se 2 (by rfl) ⟨1984317, by rfl⟩ : syracuseStep 5291513 = 3968635) B3968635
theorem B868103 : Blo 385764 868103 := bstep (se 1 (by rfl) ⟨651077, by rfl⟩ : syracuseStep 868103 = 1302155) B1302155
theorem B60702605 : Blo 385764 60702605 := bstep (se 3 (by rfl) ⟨11381738, by rfl⟩ : syracuseStep 60702605 = 22763477) B22763477
theorem B868715 : Blo 385764 868715 := bstep (se 1 (by rfl) ⟨651536, by rfl⟩ : syracuseStep 868715 = 1303073) B1303073
theorem B868859 : Blo 385764 868859 := bstep (se 1 (by rfl) ⟨651644, by rfl⟩ : syracuseStep 868859 = 1303289) B1303289
theorem B868985 : Blo 385764 868985 := bstep (se 2 (by rfl) ⟨325869, by rfl⟩ : syracuseStep 868985 = 651739) B651739
theorem B869039 : Blo 385764 869039 := bstep (se 1 (by rfl) ⟨651779, by rfl⟩ : syracuseStep 869039 = 1303559) B1303559
theorem B869111 : Blo 385764 869111 := bstep (se 1 (by rfl) ⟨651833, by rfl⟩ : syracuseStep 869111 = 1303667) B1303667
theorem B738067 : Blo 385764 738067 := bstep (se 1 (by rfl) ⟨553550, by rfl⟩ : syracuseStep 738067 = 1107101) B1107101
theorem B869291 : Blo 385764 869291 := bstep (se 1 (by rfl) ⟨651968, by rfl⟩ : syracuseStep 869291 = 1303937) B1303937
theorem B836857 : Blo 385764 836857 := bstep (se 2 (by rfl) ⟨313821, by rfl⟩ : syracuseStep 836857 = 627643) B627643
theorem B869831 : Blo 385764 869831 := bstep (se 1 (by rfl) ⟨652373, by rfl⟩ : syracuseStep 869831 = 1304747) B1304747
theorem B870191 : Blo 385764 870191 := bstep (se 1 (by rfl) ⟨652643, by rfl⟩ : syracuseStep 870191 = 1305287) B1305287
theorem B2509093 : Blo 385764 2509093 := bstep (se 4 (by rfl) ⟨235227, by rfl⟩ : syracuseStep 2509093 = 470455) B470455
theorem B870767 : Blo 385764 870767 := bstep (se 1 (by rfl) ⟨653075, by rfl⟩ : syracuseStep 870767 = 1306151) B1306151
theorem B1657199 : Blo 385764 1657199 := bstep (se 1 (by rfl) ⟨1242899, by rfl⟩ : syracuseStep 1657199 = 2485799) B2485799
theorem B870839 : Blo 385764 870839 := bstep (se 1 (by rfl) ⟨653129, by rfl⟩ : syracuseStep 870839 = 1306259) B1306259
theorem B1100243 : Blo 385764 1100243 := bstep (se 1 (by rfl) ⟨825182, by rfl⟩ : syracuseStep 1100243 = 1650365) B1650365
theorem B936443 : Blo 385764 936443 := bstep (se 1 (by rfl) ⟨702332, by rfl⟩ : syracuseStep 936443 = 1404665) B1404665
theorem B870983 : Blo 385764 870983 := bstep (se 1 (by rfl) ⟨653237, by rfl⟩ : syracuseStep 870983 = 1306475) B1306475
theorem B871019 : Blo 385764 871019 := bstep (se 1 (by rfl) ⟨653264, by rfl⟩ : syracuseStep 871019 = 1306529) B1306529
theorem B1100699 : Blo 385764 1100699 := bstep (se 1 (by rfl) ⟨825524, by rfl⟩ : syracuseStep 1100699 = 1651049) B1651049
theorem B871415 : Blo 385764 871415 := bstep (se 1 (by rfl) ⟨653561, by rfl⟩ : syracuseStep 871415 = 1307123) B1307123
theorem B871775 : Blo 385764 871775 := bstep (se 1 (by rfl) ⟨653831, by rfl⟩ : syracuseStep 871775 = 1307663) B1307663
theorem B3296699 : Blo 385764 3296699 := bstep (se 1 (by rfl) ⟨2472524, by rfl⟩ : syracuseStep 3296699 = 4945049) B4945049
theorem B1396217 : Blo 385764 1396217 := bstep (se 2 (by rfl) ⟨523581, by rfl⟩ : syracuseStep 1396217 = 1047163) B1047163
theorem B6868547 : Blo 385764 6868547 := bstep (se 1 (by rfl) ⟨5151410, by rfl⟩ : syracuseStep 6868547 = 10302821) B10302821
theorem B1953395 : Blo 385764 1953395 := bstep (se 1 (by rfl) ⟨1465046, by rfl⟩ : syracuseStep 1953395 = 2930093) B2930093
theorem B2477803 : Blo 385764 2477803 := bstep (se 1 (by rfl) ⟨1858352, by rfl⟩ : syracuseStep 2477803 = 3716705) B3716705
theorem B872171 : Blo 385764 872171 := bstep (se 1 (by rfl) ⟨654128, by rfl⟩ : syracuseStep 872171 = 1308257) B1308257
theorem B872297 : Blo 385764 872297 := bstep (se 2 (by rfl) ⟨327111, by rfl⟩ : syracuseStep 872297 = 654223) B654223
theorem B1101725 : Blo 385764 1101725 := bstep (se 3 (by rfl) ⟨206573, by rfl⟩ : syracuseStep 1101725 = 413147) B413147
theorem B125751523 : Blo 385764 125751523 := bstep (se 1 (by rfl) ⟨94313642, by rfl⟩ : syracuseStep 125751523 = 188627285) B188627285
theorem B873143 : Blo 385764 873143 := bstep (se 1 (by rfl) ⟨654857, by rfl⟩ : syracuseStep 873143 = 1309715) B1309715
theorem B873359 : Blo 385764 873359 := bstep (se 1 (by rfl) ⟨655019, by rfl⟩ : syracuseStep 873359 = 1310039) B1310039
theorem B1397903 : Blo 385764 1397903 := bstep (se 1 (by rfl) ⟨1048427, by rfl⟩ : syracuseStep 1397903 = 2096855) B2096855
theorem B1955015 : Blo 385764 1955015 := bstep (se 1 (by rfl) ⟨1466261, by rfl⟩ : syracuseStep 1955015 = 2932523) B2932523
theorem B578855 : Blo 385764 578855 := bstep (se 1 (by rfl) ⟨434141, by rfl⟩ : syracuseStep 578855 = 868283) B868283
theorem B3986783 : Blo 385764 3986783 := bstep (se 1 (by rfl) ⟨2990087, by rfl⟩ : syracuseStep 3986783 = 5980175) B5980175
theorem B1955177 : Blo 385764 1955177 := bstep (se 2 (by rfl) ⟨733191, by rfl⟩ : syracuseStep 1955177 = 1466383) B1466383
theorem B578939 : Blo 385764 578939 := bstep (se 1 (by rfl) ⟨434204, by rfl⟩ : syracuseStep 578939 = 868409) B868409
theorem B579065 : Blo 385764 579065 := bstep (se 2 (by rfl) ⟨217149, by rfl⟩ : syracuseStep 579065 = 434299) B434299
theorem B13391381 : Blo 385764 13391381 := bstep (se 6 (by rfl) ⟨313860, by rfl⟩ : syracuseStep 13391381 = 627721) B627721
theorem B579167 : Blo 385764 579167 := bstep (se 1 (by rfl) ⟨434375, by rfl⟩ : syracuseStep 579167 = 868751) B868751
theorem B874079 : Blo 385764 874079 := bstep (se 1 (by rfl) ⟨655559, by rfl⟩ : syracuseStep 874079 = 1311119) B1311119
theorem B1660601 : Blo 385764 1660601 := bstep (se 2 (by rfl) ⟨622725, by rfl⟩ : syracuseStep 1660601 = 1245451) B1245451
theorem B579383 : Blo 385764 579383 := bstep (se 1 (by rfl) ⟨434537, by rfl⟩ : syracuseStep 579383 = 869075) B869075
theorem B874295 : Blo 385764 874295 := bstep (se 1 (by rfl) ⟨655721, by rfl⟩ : syracuseStep 874295 = 1311443) B1311443
theorem B1660753 : Blo 385764 1660753 := bstep (se 2 (by rfl) ⟨622782, by rfl⟩ : syracuseStep 1660753 = 1245565) B1245565
theorem B743375 : Blo 385764 743375 := bstep (se 1 (by rfl) ⟨557531, by rfl⟩ : syracuseStep 743375 = 1115063) B1115063
theorem B579689 : Blo 385764 579689 := bstep (se 2 (by rfl) ⟨217383, by rfl⟩ : syracuseStep 579689 = 434767) B434767
theorem B874601 : Blo 385764 874601 := bstep (se 2 (by rfl) ⟨327975, by rfl⟩ : syracuseStep 874601 = 655951) B655951
theorem B416111 : Blo 385764 416111 := bstep (se 1 (by rfl) ⟨312083, by rfl⟩ : syracuseStep 416111 = 624167) B624167
theorem B1464743 : Blo 385764 1464743 := bstep (se 1 (by rfl) ⟨1098557, by rfl⟩ : syracuseStep 1464743 = 2197115) B2197115
theorem B580007 : Blo 385764 580007 := bstep (se 1 (by rfl) ⟨435005, by rfl⟩ : syracuseStep 580007 = 870011) B870011
theorem B580091 : Blo 385764 580091 := bstep (se 1 (by rfl) ⟨435068, by rfl⟩ : syracuseStep 580091 = 870137) B870137
theorem B1464911 : Blo 385764 1464911 := bstep (se 1 (by rfl) ⟨1098683, by rfl⟩ : syracuseStep 1464911 = 2197367) B2197367
theorem B875087 : Blo 385764 875087 := bstep (se 1 (by rfl) ⟨656315, by rfl⟩ : syracuseStep 875087 = 1312631) B1312631
theorem B580217 : Blo 385764 580217 := bstep (se 2 (by rfl) ⟨217581, by rfl⟩ : syracuseStep 580217 = 435163) B435163
theorem B580271 : Blo 385764 580271 := bstep (se 1 (by rfl) ⟨435203, by rfl⟩ : syracuseStep 580271 = 870407) B870407
theorem B580319 : Blo 385764 580319 := bstep (se 1 (by rfl) ⟨435239, by rfl⟩ : syracuseStep 580319 = 870479) B870479
theorem B875231 : Blo 385764 875231 := bstep (se 1 (by rfl) ⟨656423, by rfl⟩ : syracuseStep 875231 = 1312847) B1312847
theorem B711595 : Blo 385764 711595 := bstep (se 1 (by rfl) ⟨533696, by rfl⟩ : syracuseStep 711595 = 1067393) B1067393
theorem B875483 : Blo 385764 875483 := bstep (se 1 (by rfl) ⟨656612, by rfl⟩ : syracuseStep 875483 = 1313225) B1313225
theorem B580583 : Blo 385764 580583 := bstep (se 1 (by rfl) ⟨435437, by rfl⟩ : syracuseStep 580583 = 870875) B870875
theorem B875663 : Blo 385764 875663 := bstep (se 1 (by rfl) ⟨656747, by rfl⟩ : syracuseStep 875663 = 1313495) B1313495
theorem B580841 : Blo 385764 580841 := bstep (se 2 (by rfl) ⟨217815, by rfl⟩ : syracuseStep 580841 = 435631) B435631
theorem B875753 : Blo 385764 875753 := bstep (se 2 (by rfl) ⟨328407, by rfl⟩ : syracuseStep 875753 = 656815) B656815
theorem B580895 : Blo 385764 580895 := bstep (se 1 (by rfl) ⟨435671, by rfl⟩ : syracuseStep 580895 = 871343) B871343
theorem B875807 : Blo 385764 875807 := bstep (se 1 (by rfl) ⟨656855, by rfl⟩ : syracuseStep 875807 = 1313711) B1313711
theorem B581063 : Blo 385764 581063 := bstep (se 1 (by rfl) ⟨435797, by rfl⟩ : syracuseStep 581063 = 871595) B871595
theorem B1105643 : Blo 385764 1105643 := bstep (se 1 (by rfl) ⟨829232, by rfl⟩ : syracuseStep 1105643 = 1658465) B1658465
theorem B581417 : Blo 385764 581417 := bstep (se 2 (by rfl) ⟨218031, by rfl⟩ : syracuseStep 581417 = 436063) B436063
theorem B876329 : Blo 385764 876329 := bstep (se 2 (by rfl) ⟨328623, by rfl⟩ : syracuseStep 876329 = 657247) B657247
theorem B581423 : Blo 385764 581423 := bstep (se 1 (by rfl) ⟨436067, by rfl⟩ : syracuseStep 581423 = 872135) B872135
theorem B1302587 : Blo 385764 1302587 := bstep (se 1 (by rfl) ⟨976940, by rfl⟩ : syracuseStep 1302587 = 1953881) B1953881
theorem B7561349 : Blo 385764 7561349 := bstep (se 4 (by rfl) ⟨708876, by rfl⟩ : syracuseStep 7561349 = 1417753) B1417753
theorem B581897 : Blo 385764 581897 := bstep (se 2 (by rfl) ⟨218211, by rfl⟩ : syracuseStep 581897 = 436423) B436423
theorem B1302857 : Blo 385764 1302857 := bstep (se 2 (by rfl) ⟨488571, by rfl⟩ : syracuseStep 1302857 = 977143) B977143
theorem B581999 : Blo 385764 581999 := bstep (se 1 (by rfl) ⟨436499, by rfl⟩ : syracuseStep 581999 = 872999) B872999
theorem B582215 : Blo 385764 582215 := bstep (se 1 (by rfl) ⟨436661, by rfl⟩ : syracuseStep 582215 = 873323) B873323
theorem B582251 : Blo 385764 582251 := bstep (se 1 (by rfl) ⟨436688, by rfl⟩ : syracuseStep 582251 = 873377) B873377
theorem B385839 : Blo 385764 385839 := bstep (se 1 (by rfl) ⟨289379, by rfl⟩ : syracuseStep 385839 = 578759) B578759
theorem B582479 : Blo 385764 582479 := bstep (se 1 (by rfl) ⟨436859, by rfl⟩ : syracuseStep 582479 = 873719) B873719
theorem B385947 : Blo 385764 385947 := bstep (se 1 (by rfl) ⟨289460, by rfl⟩ : syracuseStep 385947 = 578921) B578921
theorem B1860545 : Blo 385764 1860545 := bstep (se 2 (by rfl) ⟨697704, by rfl⟩ : syracuseStep 1860545 = 1395409) B1395409
theorem B385999 : Blo 385764 385999 := bstep (se 1 (by rfl) ⟨289499, by rfl⟩ : syracuseStep 385999 = 578999) B578999
theorem B1237979 : Blo 385764 1237979 := bstep (se 1 (by rfl) ⟨928484, by rfl⟩ : syracuseStep 1237979 = 1856969) B1856969
theorem B1467355 : Blo 385764 1467355 := bstep (se 1 (by rfl) ⟨1100516, by rfl⟩ : syracuseStep 1467355 = 2201033) B2201033
theorem B386023 : Blo 385764 386023 := bstep (se 1 (by rfl) ⟨289517, by rfl⟩ : syracuseStep 386023 = 579035) B579035
theorem B1860583 : Blo 385764 1860583 := bstep (se 1 (by rfl) ⟨1395437, by rfl⟩ : syracuseStep 1860583 = 2790875) B2790875
theorem B1958903 : Blo 385764 1958903 := bstep (se 1 (by rfl) ⟨1469177, by rfl⟩ : syracuseStep 1958903 = 2938355) B2938355
theorem B2483237 : Blo 385764 2483237 := bstep (se 4 (by rfl) ⟨232803, by rfl⟩ : syracuseStep 2483237 = 465607) B465607
theorem B582875 : Blo 385764 582875 := bstep (se 1 (by rfl) ⟨437156, by rfl⟩ : syracuseStep 582875 = 874313) B874313
theorem B386335 : Blo 385764 386335 := bstep (se 1 (by rfl) ⟨289751, by rfl⟩ : syracuseStep 386335 = 579503) B579503
theorem B1992023 : Blo 385764 1992023 := bstep (se 1 (by rfl) ⟨1494017, by rfl⟩ : syracuseStep 1992023 = 2988035) B2988035
theorem B386395 : Blo 385764 386395 := bstep (se 1 (by rfl) ⟨289796, by rfl⟩ : syracuseStep 386395 = 579593) B579593
theorem B386415 : Blo 385764 386415 := bstep (se 1 (by rfl) ⟨289811, by rfl⟩ : syracuseStep 386415 = 579623) B579623
theorem B583049 : Blo 385764 583049 := bstep (se 2 (by rfl) ⟨218643, by rfl⟩ : syracuseStep 583049 = 437287) B437287
theorem B386471 : Blo 385764 386471 := bstep (se 1 (by rfl) ⟨289853, by rfl⟩ : syracuseStep 386471 = 579707) B579707
theorem B386555 : Blo 385764 386555 := bstep (se 1 (by rfl) ⟨289916, by rfl⟩ : syracuseStep 386555 = 579833) B579833
theorem B386623 : Blo 385764 386623 := bstep (se 1 (by rfl) ⟨289967, by rfl⟩ : syracuseStep 386623 = 579935) B579935
theorem B386631 : Blo 385764 386631 := bstep (se 1 (by rfl) ⟨289973, by rfl⟩ : syracuseStep 386631 = 579947) B579947
theorem B386783 : Blo 385764 386783 := bstep (se 1 (by rfl) ⟨290087, by rfl⟩ : syracuseStep 386783 = 580175) B580175
theorem B583403 : Blo 385764 583403 := bstep (se 1 (by rfl) ⟨437552, by rfl⟩ : syracuseStep 583403 = 875105) B875105
theorem B386863 : Blo 385764 386863 := bstep (se 1 (by rfl) ⟨290147, by rfl⟩ : syracuseStep 386863 = 580295) B580295
theorem B976769 : Blo 385764 976769 := bstep (se 2 (by rfl) ⟨366288, by rfl⟩ : syracuseStep 976769 = 732577) B732577
theorem B386971 : Blo 385764 386971 := bstep (se 1 (by rfl) ⟨290228, by rfl⟩ : syracuseStep 386971 = 580457) B580457
theorem B387023 : Blo 385764 387023 := bstep (se 1 (by rfl) ⟨290267, by rfl⟩ : syracuseStep 387023 = 580535) B580535
theorem B583631 : Blo 385764 583631 := bstep (se 1 (by rfl) ⟨437723, by rfl⟩ : syracuseStep 583631 = 875447) B875447
theorem B387047 : Blo 385764 387047 := bstep (se 1 (by rfl) ⟨290285, by rfl⟩ : syracuseStep 387047 = 580571) B580571
theorem B1468601 : Blo 385764 1468601 := bstep (se 2 (by rfl) ⟨550725, by rfl⟩ : syracuseStep 1468601 = 1101451) B1101451
theorem B387359 : Blo 385764 387359 := bstep (se 1 (by rfl) ⟨290519, by rfl⟩ : syracuseStep 387359 = 581039) B581039
theorem B387419 : Blo 385764 387419 := bstep (se 1 (by rfl) ⟨290564, by rfl⟩ : syracuseStep 387419 = 581129) B581129
theorem B584027 : Blo 385764 584027 := bstep (se 1 (by rfl) ⟨438020, by rfl⟩ : syracuseStep 584027 = 876041) B876041
theorem B387439 : Blo 385764 387439 := bstep (se 1 (by rfl) ⟨290579, by rfl⟩ : syracuseStep 387439 = 581159) B581159
theorem B387495 : Blo 385764 387495 := bstep (se 1 (by rfl) ⟨290621, by rfl⟩ : syracuseStep 387495 = 581243) B581243
theorem B387579 : Blo 385764 387579 := bstep (se 1 (by rfl) ⟨290684, by rfl⟩ : syracuseStep 387579 = 581369) B581369
theorem B387647 : Blo 385764 387647 := bstep (se 1 (by rfl) ⟨290735, by rfl⟩ : syracuseStep 387647 = 581471) B581471
theorem B584255 : Blo 385764 584255 := bstep (se 1 (by rfl) ⟨438191, by rfl⟩ : syracuseStep 584255 = 876383) B876383
theorem B387655 : Blo 385764 387655 := bstep (se 1 (by rfl) ⟨290741, by rfl⟩ : syracuseStep 387655 = 581483) B581483
theorem B1108559 : Blo 385764 1108559 := bstep (se 1 (by rfl) ⟨831419, by rfl⟩ : syracuseStep 1108559 = 1662839) B1662839
theorem B977579 : Blo 385764 977579 := bstep (se 1 (by rfl) ⟨733184, by rfl⟩ : syracuseStep 977579 = 1466369) B1466369
theorem B584375 : Blo 385764 584375 := bstep (se 1 (by rfl) ⟨438281, by rfl⟩ : syracuseStep 584375 = 876563) B876563
theorem B387807 : Blo 385764 387807 := bstep (se 1 (by rfl) ⟨290855, by rfl⟩ : syracuseStep 387807 = 581711) B581711
theorem B748307 : Blo 385764 748307 := bstep (se 1 (by rfl) ⟨561230, by rfl⟩ : syracuseStep 748307 = 1122461) B1122461
theorem B387887 : Blo 385764 387887 := bstep (se 1 (by rfl) ⟨290915, by rfl⟩ : syracuseStep 387887 = 581831) B581831
theorem B4188995 : Blo 385764 4188995 := bstep (se 1 (by rfl) ⟨3141746, by rfl⟩ : syracuseStep 4188995 = 6283493) B6283493
theorem B1960847 : Blo 385764 1960847 := bstep (se 1 (by rfl) ⟨1470635, by rfl⟩ : syracuseStep 1960847 = 2941271) B2941271
theorem B387995 : Blo 385764 387995 := bstep (se 1 (by rfl) ⟨290996, by rfl⟩ : syracuseStep 387995 = 581993) B581993
theorem B584603 : Blo 385764 584603 := bstep (se 1 (by rfl) ⟨438452, by rfl⟩ : syracuseStep 584603 = 876905) B876905
theorem B388047 : Blo 385764 388047 := bstep (se 1 (by rfl) ⟨291035, by rfl⟩ : syracuseStep 388047 = 582071) B582071
theorem B388071 : Blo 385764 388071 := bstep (se 1 (by rfl) ⟨291053, by rfl⟩ : syracuseStep 388071 = 582107) B582107
theorem B1043705 : Blo 385764 1043705 := bstep (se 2 (by rfl) ⟨391389, by rfl⟩ : syracuseStep 1043705 = 782779) B782779
theorem B388383 : Blo 385764 388383 := bstep (se 1 (by rfl) ⟨291287, by rfl⟩ : syracuseStep 388383 = 582575) B582575
theorem B388443 : Blo 385764 388443 := bstep (se 1 (by rfl) ⟨291332, by rfl⟩ : syracuseStep 388443 = 582665) B582665
theorem B388463 : Blo 385764 388463 := bstep (se 1 (by rfl) ⟨291347, by rfl⟩ : syracuseStep 388463 = 582695) B582695
theorem B1240439 : Blo 385764 1240439 := bstep (se 1 (by rfl) ⟨930329, by rfl⟩ : syracuseStep 1240439 = 1860659) B1860659
theorem B388519 : Blo 385764 388519 := bstep (se 1 (by rfl) ⟨291389, by rfl⟩ : syracuseStep 388519 = 582779) B582779
theorem B1306043 : Blo 385764 1306043 := bstep (se 1 (by rfl) ⟨979532, by rfl⟩ : syracuseStep 1306043 = 1959065) B1959065
theorem B1109447 : Blo 385764 1109447 := bstep (se 1 (by rfl) ⟨832085, by rfl⟩ : syracuseStep 1109447 = 1664171) B1664171
theorem B388603 : Blo 385764 388603 := bstep (se 1 (by rfl) ⟨291452, by rfl⟩ : syracuseStep 388603 = 582905) B582905
theorem B978439 : Blo 385764 978439 := bstep (se 1 (by rfl) ⟨733829, by rfl⟩ : syracuseStep 978439 = 1467659) B1467659
theorem B388671 : Blo 385764 388671 := bstep (se 1 (by rfl) ⟨291503, by rfl⟩ : syracuseStep 388671 = 583007) B583007
theorem B388679 : Blo 385764 388679 := bstep (se 1 (by rfl) ⟨291509, by rfl⟩ : syracuseStep 388679 = 583019) B583019
theorem B388831 : Blo 385764 388831 := bstep (se 1 (by rfl) ⟨291623, by rfl⟩ : syracuseStep 388831 = 583247) B583247
theorem B1863427 : Blo 385764 1863427 := bstep (se 1 (by rfl) ⟨1397570, by rfl⟩ : syracuseStep 1863427 = 2795141) B2795141
theorem B1109801 : Blo 385764 1109801 := bstep (se 2 (by rfl) ⟨416175, by rfl⟩ : syracuseStep 1109801 = 832351) B832351
theorem B388911 : Blo 385764 388911 := bstep (se 1 (by rfl) ⟨291683, by rfl⟩ : syracuseStep 388911 = 583367) B583367
theorem B978743 : Blo 385764 978743 := bstep (se 1 (by rfl) ⟨734057, by rfl⟩ : syracuseStep 978743 = 1468115) B1468115
theorem B389019 : Blo 385764 389019 := bstep (se 1 (by rfl) ⟨291764, by rfl⟩ : syracuseStep 389019 = 583529) B583529
theorem B389071 : Blo 385764 389071 := bstep (se 1 (by rfl) ⟨291803, by rfl⟩ : syracuseStep 389071 = 583607) B583607
theorem B389095 : Blo 385764 389095 := bstep (se 1 (by rfl) ⟨291821, by rfl⟩ : syracuseStep 389095 = 583643) B583643
theorem B27324533 : Blo 385764 27324533 := bstep (se 5 (by rfl) ⟨1280837, by rfl⟩ : syracuseStep 27324533 = 2561675) B2561675
theorem B389407 : Blo 385764 389407 := bstep (se 1 (by rfl) ⟨292055, by rfl⟩ : syracuseStep 389407 = 584111) B584111
theorem B651611 : Blo 385764 651611 := bstep (se 1 (by rfl) ⟨488708, by rfl⟩ : syracuseStep 651611 = 977417) B977417
theorem B389467 : Blo 385764 389467 := bstep (se 1 (by rfl) ⟨292100, by rfl⟩ : syracuseStep 389467 = 584201) B584201
theorem B1864043 : Blo 385764 1864043 := bstep (se 1 (by rfl) ⟨1398032, by rfl⟩ : syracuseStep 1864043 = 2796065) B2796065
theorem B651631 : Blo 385764 651631 := bstep (se 1 (by rfl) ⟨488723, by rfl⟩ : syracuseStep 651631 = 977447) B977447
theorem B389487 : Blo 385764 389487 := bstep (se 1 (by rfl) ⟨292115, by rfl⟩ : syracuseStep 389487 = 584231) B584231
theorem B389543 : Blo 385764 389543 := bstep (se 1 (by rfl) ⟨292157, by rfl⟩ : syracuseStep 389543 = 584315) B584315
theorem B979411 : Blo 385764 979411 := bstep (se 1 (by rfl) ⟨734558, by rfl⟩ : syracuseStep 979411 = 1469117) B1469117
theorem B389627 : Blo 385764 389627 := bstep (se 1 (by rfl) ⟨292220, by rfl⟩ : syracuseStep 389627 = 584441) B584441
theorem B389695 : Blo 385764 389695 := bstep (se 1 (by rfl) ⟨292271, by rfl⟩ : syracuseStep 389695 = 584543) B584543
theorem B651847 : Blo 385764 651847 := bstep (se 1 (by rfl) ⟨488885, by rfl⟩ : syracuseStep 651847 = 977771) B977771
theorem B389703 : Blo 385764 389703 := bstep (se 1 (by rfl) ⟨292277, by rfl⟩ : syracuseStep 389703 = 584555) B584555
theorem B1569401 : Blo 385764 1569401 := bstep (se 2 (by rfl) ⟨588525, by rfl⟩ : syracuseStep 1569401 = 1177051) B1177051
theorem B619343 : Blo 385764 619343 := bstep (se 1 (by rfl) ⟨464507, by rfl⟩ : syracuseStep 619343 = 929015) B929015
theorem B553807 : Blo 385764 553807 := bstep (se 1 (by rfl) ⟨415355, by rfl⟩ : syracuseStep 553807 = 830711) B830711
theorem B3732389 : Blo 385764 3732389 := bstep (se 4 (by rfl) ⟨349911, by rfl⟩ : syracuseStep 3732389 = 699823) B699823
theorem B1962953 : Blo 385764 1962953 := bstep (se 2 (by rfl) ⟨736107, by rfl⟩ : syracuseStep 1962953 = 1472215) B1472215
theorem B652279 : Blo 385764 652279 := bstep (se 1 (by rfl) ⟨489209, by rfl⟩ : syracuseStep 652279 = 978419) B978419
theorem B2487287 : Blo 385764 2487287 := bstep (se 1 (by rfl) ⟨1865465, by rfl⟩ : syracuseStep 2487287 = 3730931) B3730931
theorem B7992377 : Blo 385764 7992377 := bstep (se 2 (by rfl) ⟨2997141, by rfl⟩ : syracuseStep 7992377 = 5994283) B5994283
theorem B1242209 : Blo 385764 1242209 := bstep (se 2 (by rfl) ⟨465828, by rfl⟩ : syracuseStep 1242209 = 931657) B931657
theorem B619753 : Blo 385764 619753 := bstep (se 2 (by rfl) ⟨232407, by rfl⟩ : syracuseStep 619753 = 464815) B464815
theorem B980201 : Blo 385764 980201 := bstep (se 2 (by rfl) ⟨367575, by rfl⟩ : syracuseStep 980201 = 735151) B735151
theorem B1996019 : Blo 385764 1996019 := bstep (se 1 (by rfl) ⟨1497014, by rfl⟩ : syracuseStep 1996019 = 2994029) B2994029
theorem B2782457 : Blo 385764 2782457 := bstep (se 2 (by rfl) ⟨1043421, by rfl⟩ : syracuseStep 2782457 = 2086843) B2086843
theorem B652583 : Blo 385764 652583 := bstep (se 1 (by rfl) ⟨489437, by rfl⟩ : syracuseStep 652583 = 978875) B978875
theorem B980363 : Blo 385764 980363 := bstep (se 1 (by rfl) ⟨735272, by rfl⟩ : syracuseStep 980363 = 1470545) B1470545
theorem B653035 : Blo 385764 653035 := bstep (se 1 (by rfl) ⟨489776, by rfl⟩ : syracuseStep 653035 = 979553) B979553
theorem B9893987 : Blo 385764 9893987 := bstep (se 1 (by rfl) ⟨7420490, by rfl⟩ : syracuseStep 9893987 = 14840981) B14840981
theorem B981355 : Blo 385764 981355 := bstep (se 1 (by rfl) ⟨736016, by rfl⟩ : syracuseStep 981355 = 1472033) B1472033
theorem B489979 : Blo 385764 489979 := bstep (se 1 (by rfl) ⟨367484, by rfl⟩ : syracuseStep 489979 = 734969) B734969
theorem B883271 : Blo 385764 883271 := bstep (se 1 (by rfl) ⟨662453, by rfl⟩ : syracuseStep 883271 = 1324907) B1324907
theorem B5306953 : Blo 385764 5306953 := bstep (se 2 (by rfl) ⟨1990107, by rfl⟩ : syracuseStep 5306953 = 3980215) B3980215
theorem B981679 : Blo 385764 981679 := bstep (se 1 (by rfl) ⟨736259, by rfl⟩ : syracuseStep 981679 = 1472519) B1472519
theorem B654007 : Blo 385764 654007 := bstep (se 1 (by rfl) ⟨490505, by rfl⟩ : syracuseStep 654007 = 981011) B981011
theorem B490207 : Blo 385764 490207 := bstep (se 1 (by rfl) ⟨367655, by rfl⟩ : syracuseStep 490207 = 735311) B735311
theorem B654311 : Blo 385764 654311 := bstep (se 1 (by rfl) ⟨490733, by rfl⟩ : syracuseStep 654311 = 981467) B981467
theorem B982003 : Blo 385764 982003 := bstep (se 1 (by rfl) ⟨736502, by rfl⟩ : syracuseStep 982003 = 1473005) B1473005
theorem B1473659 : Blo 385764 1473659 := bstep (se 1 (by rfl) ⟨1105244, by rfl⟩ : syracuseStep 1473659 = 2210489) B2210489
theorem B785551 : Blo 385764 785551 := bstep (se 1 (by rfl) ⟨589163, by rfl⟩ : syracuseStep 785551 = 1178327) B1178327
theorem B7044259 : Blo 385764 7044259 := bstep (se 1 (by rfl) ⟨5283194, by rfl⟩ : syracuseStep 7044259 = 10566389) B10566389
theorem B3538187 : Blo 385764 3538187 := bstep (se 1 (by rfl) ⟨2653640, by rfl⟩ : syracuseStep 3538187 = 5307281) B5307281
theorem B3145027 : Blo 385764 3145027 := bstep (se 1 (by rfl) ⟨2358770, by rfl⟩ : syracuseStep 3145027 = 4717541) B4717541
theorem B490951 : Blo 385764 490951 := bstep (se 1 (by rfl) ⟨368213, by rfl⟩ : syracuseStep 490951 = 736427) B736427
theorem B1310201 : Blo 385764 1310201 := bstep (se 2 (by rfl) ⟨491325, by rfl⟩ : syracuseStep 1310201 = 982651) B982651
theorem B982763 : Blo 385764 982763 := bstep (se 1 (by rfl) ⟨737072, by rfl⟩ : syracuseStep 982763 = 1474145) B1474145
theorem B1310471 : Blo 385764 1310471 := bstep (se 1 (by rfl) ⟨982853, by rfl⟩ : syracuseStep 1310471 = 1965707) B1965707
theorem B1310525 : Blo 385764 1310525 := bstep (se 3 (by rfl) ⟨245723, by rfl⟩ : syracuseStep 1310525 = 491447) B491447
theorem B1474433 : Blo 385764 1474433 := bstep (se 2 (by rfl) ⟨552912, by rfl⟩ : syracuseStep 1474433 = 1105825) B1105825
theorem B10485811 : Blo 385764 10485811 := bstep (se 1 (by rfl) ⟨7864358, by rfl⟩ : syracuseStep 10485811 = 15728717) B15728717
theorem B9470189 : Blo 385764 9470189 := bstep (se 3 (by rfl) ⟨1775660, by rfl⟩ : syracuseStep 9470189 = 3551321) B3551321
theorem B655823 : Blo 385764 655823 := bstep (se 1 (by rfl) ⟨491867, by rfl⟩ : syracuseStep 655823 = 983735) B983735
theorem B1311227 : Blo 385764 1311227 := bstep (se 1 (by rfl) ⟨983420, by rfl⟩ : syracuseStep 1311227 = 1966841) B1966841
theorem B1311497 : Blo 385764 1311497 := bstep (se 2 (by rfl) ⟨491811, by rfl⟩ : syracuseStep 1311497 = 983623) B983623
theorem B984089 : Blo 385764 984089 := bstep (se 2 (by rfl) ⟨369033, by rfl⟩ : syracuseStep 984089 = 738067) B738067
theorem B5637221 : Blo 385764 5637221 := bstep (se 4 (by rfl) ⟨528489, by rfl⟩ : syracuseStep 5637221 = 1056979) B1056979
theorem B656491 : Blo 385764 656491 := bstep (se 1 (by rfl) ⟨492368, by rfl⟩ : syracuseStep 656491 = 984737) B984737
theorem B984271 : Blo 385764 984271 := bstep (se 1 (by rfl) ⟨738203, by rfl⟩ : syracuseStep 984271 = 1476407) B1476407
theorem B656795 : Blo 385764 656795 := bstep (se 1 (by rfl) ⟨492596, by rfl⟩ : syracuseStep 656795 = 985193) B985193
theorem B1312253 : Blo 385764 1312253 := bstep (se 3 (by rfl) ⟨246047, by rfl⟩ : syracuseStep 1312253 = 492095) B492095
theorem B984595 : Blo 385764 984595 := bstep (se 1 (by rfl) ⟨738446, by rfl⟩ : syracuseStep 984595 = 1476893) B1476893
theorem B624295 : Blo 385764 624295 := bstep (se 1 (by rfl) ⟨468221, by rfl⟩ : syracuseStep 624295 = 936443) B936443
theorem B657119 : Blo 385764 657119 := bstep (se 1 (by rfl) ⟨492839, by rfl⟩ : syracuseStep 657119 = 985679) B985679
theorem B2950991 : Blo 385764 2950991 := bstep (se 1 (by rfl) ⟨2213243, by rfl⟩ : syracuseStep 2950991 = 4426487) B4426487
theorem B1181537 : Blo 385764 1181537 := bstep (se 2 (by rfl) ⟨443076, by rfl⟩ : syracuseStep 1181537 = 886153) B886153
theorem B161580905 : Blo 385764 161580905 := bstep (se 2 (by rfl) ⟨60592839, by rfl⟩ : syracuseStep 161580905 = 121185679) B121185679
theorem B985031 : Blo 385764 985031 := bstep (se 1 (by rfl) ⟨738773, by rfl⟩ : syracuseStep 985031 = 1477547) B1477547
theorem B591815 : Blo 385764 591815 := bstep (se 1 (by rfl) ⟨443861, by rfl⟩ : syracuseStep 591815 = 887723) B887723
theorem B1968137 : Blo 385764 1968137 := bstep (se 2 (by rfl) ⟨738051, by rfl⟩ : syracuseStep 1968137 = 1476103) B1476103
theorem B657551 : Blo 385764 657551 := bstep (se 1 (by rfl) ⟨493163, by rfl⟩ : syracuseStep 657551 = 986327) B986327
theorem B2197799 : Blo 385764 2197799 := bstep (se 1 (by rfl) ⟨1648349, by rfl⟩ : syracuseStep 2197799 = 3296699) B3296699
theorem B1313063 : Blo 385764 1313063 := bstep (se 1 (by rfl) ⟨984797, by rfl⟩ : syracuseStep 1313063 = 1969595) B1969595
theorem B1968785 : Blo 385764 1968785 := bstep (se 2 (by rfl) ⟨738294, by rfl⟩ : syracuseStep 1968785 = 1476589) B1476589
theorem B4983443 : Blo 385764 4983443 := bstep (se 1 (by rfl) ⟨3737582, by rfl⟩ : syracuseStep 4983443 = 7475165) B7475165
theorem B10029719 : Blo 385764 10029719 := bstep (se 1 (by rfl) ⟨7522289, by rfl⟩ : syracuseStep 10029719 = 15044579) B15044579
theorem B3345457 : Blo 385764 3345457 := bstep (se 2 (by rfl) ⟨1254546, by rfl⟩ : syracuseStep 3345457 = 2509093) B2509093
theorem B1313927 : Blo 385764 1313927 := bstep (se 1 (by rfl) ⟨985445, by rfl⟩ : syracuseStep 1313927 = 1970891) B1970891
theorem B1314035 : Blo 385764 1314035 := bstep (se 1 (by rfl) ⟨985526, by rfl⟩ : syracuseStep 1314035 = 1971053) B1971053
theorem B1969433 : Blo 385764 1969433 := bstep (se 2 (by rfl) ⟨738537, by rfl⟩ : syracuseStep 1969433 = 1477075) B1477075
theorem B2657855 : Blo 385764 2657855 := bstep (se 1 (by rfl) ⟨1993391, by rfl⟩ : syracuseStep 2657855 = 3986783) B3986783
theorem B1184215 : Blo 385764 1184215 := bstep (se 1 (by rfl) ⟨888161, by rfl⟩ : syracuseStep 1184215 = 1776323) B1776323
theorem B1971215 : Blo 385764 1971215 := bstep (se 1 (by rfl) ⟨1478411, by rfl⟩ : syracuseStep 1971215 = 2956823) B2956823
theorem B4199633 : Blo 385764 4199633 := bstep (se 2 (by rfl) ⟨1574862, by rfl⟩ : syracuseStep 4199633 = 3149725) B3149725
theorem B660907 : Blo 385764 660907 := bstep (se 1 (by rfl) ⟨495680, by rfl⟩ : syracuseStep 660907 = 991361) B991361
theorem B3151673 : Blo 385764 3151673 := bstep (se 2 (by rfl) ⟨1181877, by rfl⟩ : syracuseStep 3151673 = 2363755) B2363755
theorem B1972025 : Blo 385764 1972025 := bstep (se 2 (by rfl) ⟨739509, by rfl⟩ : syracuseStep 1972025 = 1479019) B1479019
theorem B825319 : Blo 385764 825319 := bstep (se 1 (by rfl) ⟨618989, by rfl⟩ : syracuseStep 825319 = 1237979) B1237979
theorem B4463237 : Blo 385764 4463237 := bstep (se 4 (by rfl) ⟨418428, by rfl⟩ : syracuseStep 4463237 = 836857) B836857
theorem B826337 : Blo 385764 826337 := bstep (se 2 (by rfl) ⟨309876, by rfl⟩ : syracuseStep 826337 = 619753) B619753
theorem B498871 : Blo 385764 498871 := bstep (se 1 (by rfl) ⟨374153, by rfl⟩ : syracuseStep 498871 = 748307) B748307
theorem B5577943 : Blo 385764 5577943 := bstep (se 1 (by rfl) ⟨4183457, by rfl⟩ : syracuseStep 5577943 = 8366915) B8366915
theorem B2792663 : Blo 385764 2792663 := bstep (se 1 (by rfl) ⟨2094497, by rfl⟩ : syracuseStep 2792663 = 4188995) B4188995
theorem B531679 : Blo 385764 531679 := bstep (se 1 (by rfl) ⟨398759, by rfl⟩ : syracuseStep 531679 = 797519) B797519
theorem B695803 : Blo 385764 695803 := bstep (se 1 (by rfl) ⟨521852, by rfl⟩ : syracuseStep 695803 = 1043705) B1043705
theorem B10887211 : Blo 385764 10887211 := bstep (se 1 (by rfl) ⟨8165408, by rfl⟩ : syracuseStep 10887211 = 16330817) B16330817
theorem B434407 : Blo 385764 434407 := bstep (se 1 (by rfl) ⟨325805, by rfl⟩ : syracuseStep 434407 = 651611) B651611
theorem B828139 : Blo 385764 828139 := bstep (se 1 (by rfl) ⟨621104, by rfl⟩ : syracuseStep 828139 = 1242209) B1242209
theorem B435055 : Blo 385764 435055 := bstep (se 1 (by rfl) ⟨326291, by rfl⟩ : syracuseStep 435055 = 652583) B652583
theorem B6595991 : Blo 385764 6595991 := bstep (se 1 (by rfl) ⟨4946993, by rfl⟩ : syracuseStep 6595991 = 9893987) B9893987
theorem B2958767 : Blo 385764 2958767 := bstep (se 1 (by rfl) ⟨2219075, by rfl⟩ : syracuseStep 2958767 = 4438151) B4438151
theorem B436207 : Blo 385764 436207 := bstep (se 1 (by rfl) ⟨327155, by rfl⟩ : syracuseStep 436207 = 654311) B654311
theorem B83143361 : Blo 385764 83143361 := bstep (se 2 (by rfl) ⟨31178760, by rfl⟩ : syracuseStep 83143361 = 62357521) B62357521
theorem B733799 : Blo 385764 733799 := bstep (se 1 (by rfl) ⟨550349, by rfl⟩ : syracuseStep 733799 = 1100699) B1100699
theorem B832103 : Blo 385764 832103 := bstep (se 1 (by rfl) ⟨624077, by rfl⟩ : syracuseStep 832103 = 1248155) B1248155
theorem B734483 : Blo 385764 734483 := bstep (se 1 (by rfl) ⟨550862, by rfl⟩ : syracuseStep 734483 = 1101725) B1101725
theorem B4994561 : Blo 385764 4994561 := bstep (se 2 (by rfl) ⟨1872960, by rfl⟩ : syracuseStep 4994561 = 3745921) B3745921
theorem B2799269 : Blo 385764 2799269 := bstep (se 4 (by rfl) ⟨262431, by rfl⟩ : syracuseStep 2799269 = 524863) B524863
theorem B2209463 : Blo 385764 2209463 := bstep (se 1 (by rfl) ⟨1657097, by rfl⟩ : syracuseStep 2209463 = 3314195) B3314195
theorem B3979145 : Blo 385764 3979145 := bstep (se 2 (by rfl) ⟨1492179, by rfl⟩ : syracuseStep 3979145 = 2984359) B2984359
theorem B2799497 : Blo 385764 2799497 := bstep (se 2 (by rfl) ⟨1049811, by rfl⟩ : syracuseStep 2799497 = 2099623) B2099623
theorem B2930579 : Blo 385764 2930579 := bstep (se 1 (by rfl) ⟨2197934, by rfl⟩ : syracuseStep 2930579 = 4395869) B4395869
theorem B2209963 : Blo 385764 2209963 := bstep (se 1 (by rfl) ⟨1657472, by rfl⟩ : syracuseStep 2209963 = 3314945) B3314945
theorem B8927587 : Blo 385764 8927587 := bstep (se 1 (by rfl) ⟨6695690, by rfl⟩ : syracuseStep 8927587 = 13391381) B13391381
theorem B637787 : Blo 385764 637787 := bstep (se 1 (by rfl) ⟨478340, by rfl⟩ : syracuseStep 637787 = 956681) B956681
theorem B2211239 : Blo 385764 2211239 := bstep (se 1 (by rfl) ⟨1658429, by rfl⟩ : syracuseStep 2211239 = 3316859) B3316859
theorem B737095 : Blo 385764 737095 := bstep (se 1 (by rfl) ⟨552821, by rfl⟩ : syracuseStep 737095 = 1105643) B1105643
theorem B1982333 : Blo 385764 1982333 := bstep (se 3 (by rfl) ⟨371687, by rfl⟩ : syracuseStep 1982333 = 743375) B743375
theorem B20070433 : Blo 385764 20070433 := bstep (se 2 (by rfl) ⟨7526412, by rfl⟩ : syracuseStep 20070433 = 15052825) B15052825
theorem B868391 : Blo 385764 868391 := bstep (se 1 (by rfl) ⟨651293, by rfl⟩ : syracuseStep 868391 = 1302587) B1302587
theorem B868571 : Blo 385764 868571 := bstep (se 1 (by rfl) ⟨651428, by rfl⟩ : syracuseStep 868571 = 1302857) B1302857
theorem B868841 : Blo 385764 868841 := bstep (se 2 (by rfl) ⟨325815, by rfl⟩ : syracuseStep 868841 = 651631) B651631
theorem B1655491 : Blo 385764 1655491 := bstep (se 1 (by rfl) ⟨1241618, by rfl⟩ : syracuseStep 1655491 = 2483237) B2483237
theorem B869129 : Blo 385764 869129 := bstep (se 2 (by rfl) ⟨325923, by rfl⟩ : syracuseStep 869129 = 651847) B651847
theorem B1328015 : Blo 385764 1328015 := bstep (se 1 (by rfl) ⟨996011, by rfl⟩ : syracuseStep 1328015 = 1992023) B1992023
theorem B738409 : Blo 385764 738409 := bstep (se 2 (by rfl) ⟨276903, by rfl⟩ : syracuseStep 738409 = 553807) B553807
theorem B2933981 : Blo 385764 2933981 := bstep (se 3 (by rfl) ⟨550121, by rfl⟩ : syracuseStep 2933981 = 1100243) B1100243
theorem B869705 : Blo 385764 869705 := bstep (se 2 (by rfl) ⟨326139, by rfl⟩ : syracuseStep 869705 = 652279) B652279
theorem B739039 : Blo 385764 739039 := bstep (se 1 (by rfl) ⟨554279, by rfl⟩ : syracuseStep 739039 = 1108559) B1108559
theorem B2475805 : Blo 385764 2475805 := bstep (se 3 (by rfl) ⟨464213, by rfl⟩ : syracuseStep 2475805 = 928427) B928427
theorem B837473 : Blo 385764 837473 := bstep (se 2 (by rfl) ⟨314052, by rfl⟩ : syracuseStep 837473 = 628105) B628105
theorem B414566423 : Blo 385764 414566423 := bstep (se 1 (by rfl) ⟨310924817, by rfl⟩ : syracuseStep 414566423 = 621849635) B621849635
theorem B4475057 : Blo 385764 4475057 := bstep (se 2 (by rfl) ⟨1678146, by rfl⟩ : syracuseStep 4475057 = 3356293) B3356293
theorem B870695 : Blo 385764 870695 := bstep (se 1 (by rfl) ⟨653021, by rfl⟩ : syracuseStep 870695 = 1306043) B1306043
theorem B739631 : Blo 385764 739631 := bstep (se 1 (by rfl) ⟨554723, by rfl⟩ : syracuseStep 739631 = 1109447) B1109447
theorem B870713 : Blo 385764 870713 := bstep (se 2 (by rfl) ⟨326517, by rfl⟩ : syracuseStep 870713 = 653035) B653035
theorem B575867 : Blo 385764 575867 := bstep (se 1 (by rfl) ⟨431900, by rfl⟩ : syracuseStep 575867 = 863801) B863801
theorem B2214337 : Blo 385764 2214337 := bstep (se 2 (by rfl) ⟨830376, by rfl⟩ : syracuseStep 2214337 = 1660753) B1660753
theorem B739867 : Blo 385764 739867 := bstep (se 1 (by rfl) ⟨554900, by rfl⟩ : syracuseStep 739867 = 1109801) B1109801
theorem B1428623 : Blo 385764 1428623 := bstep (se 1 (by rfl) ⟨1071467, by rfl⟩ : syracuseStep 1428623 = 2142935) B2142935
theorem B412895 : Blo 385764 412895 := bstep (se 1 (by rfl) ⟨309671, by rfl⟩ : syracuseStep 412895 = 619343) B619343
theorem B1658191 : Blo 385764 1658191 := bstep (se 1 (by rfl) ⟨1243643, by rfl⟩ : syracuseStep 1658191 = 2487287) B2487287
theorem B5328251 : Blo 385764 5328251 := bstep (se 1 (by rfl) ⟨3996188, by rfl⟩ : syracuseStep 5328251 = 7992377) B7992377
theorem B1330679 : Blo 385764 1330679 := bstep (se 1 (by rfl) ⟨998009, by rfl⟩ : syracuseStep 1330679 = 1996019) B1996019
theorem B1854971 : Blo 385764 1854971 := bstep (se 1 (by rfl) ⟨1391228, by rfl⟩ : syracuseStep 1854971 = 2782457) B2782457
theorem B872009 : Blo 385764 872009 := bstep (se 2 (by rfl) ⟨327003, by rfl⟩ : syracuseStep 872009 = 654007) B654007
theorem B3723245 : Blo 385764 3723245 := bstep (se 3 (by rfl) ⟨698108, by rfl⟩ : syracuseStep 3723245 = 1396217) B1396217
theorem B9392345 : Blo 385764 9392345 := bstep (se 2 (by rfl) ⟨3522129, by rfl⟩ : syracuseStep 9392345 = 7044259) B7044259
theorem B8147249 : Blo 385764 8147249 := bstep (se 2 (by rfl) ⟨3055218, by rfl⟩ : syracuseStep 8147249 = 6110437) B6110437
theorem B3527675 : Blo 385764 3527675 := bstep (se 1 (by rfl) ⟨2645756, by rfl⟩ : syracuseStep 3527675 = 5291513) B5291513
theorem B873467 : Blo 385764 873467 := bstep (se 1 (by rfl) ⟨655100, by rfl⟩ : syracuseStep 873467 = 1310201) B1310201
theorem B578735 : Blo 385764 578735 := bstep (se 1 (by rfl) ⟨434051, by rfl⟩ : syracuseStep 578735 = 868103) B868103
theorem B873647 : Blo 385764 873647 := bstep (se 1 (by rfl) ⟨655235, by rfl⟩ : syracuseStep 873647 = 1310471) B1310471
theorem B873683 : Blo 385764 873683 := bstep (se 1 (by rfl) ⟨655262, by rfl⟩ : syracuseStep 873683 = 1310525) B1310525
theorem B30365027 : Blo 385764 30365027 := bstep (se 1 (by rfl) ⟨22773770, by rfl⟩ : syracuseStep 30365027 = 45547541) B45547541
theorem B76567949 : Blo 385764 76567949 := bstep (se 3 (by rfl) ⟨14356490, by rfl⟩ : syracuseStep 76567949 = 28712981) B28712981
theorem B873953 : Blo 385764 873953 := bstep (se 2 (by rfl) ⟨327732, by rfl⟩ : syracuseStep 873953 = 655465) B655465
theorem B579143 : Blo 385764 579143 := bstep (se 1 (by rfl) ⟨434357, by rfl⟩ : syracuseStep 579143 = 868715) B868715
theorem B579239 : Blo 385764 579239 := bstep (se 1 (by rfl) ⟨434429, by rfl⟩ : syracuseStep 579239 = 868859) B868859
theorem B579323 : Blo 385764 579323 := bstep (se 1 (by rfl) ⟨434492, by rfl⟩ : syracuseStep 579323 = 868985) B868985
theorem B579359 : Blo 385764 579359 := bstep (se 1 (by rfl) ⟨434519, by rfl⟩ : syracuseStep 579359 = 869039) B869039
theorem B579407 : Blo 385764 579407 := bstep (se 1 (by rfl) ⟨434555, by rfl⟩ : syracuseStep 579407 = 869111) B869111
theorem B579527 : Blo 385764 579527 := bstep (se 1 (by rfl) ⟨434645, by rfl⟩ : syracuseStep 579527 = 869291) B869291
theorem B1103969 : Blo 385764 1103969 := bstep (se 2 (by rfl) ⟨413988, by rfl⟩ : syracuseStep 1103969 = 827977) B827977
theorem B579881 : Blo 385764 579881 := bstep (se 2 (by rfl) ⟨217455, by rfl⟩ : syracuseStep 579881 = 434911) B434911
theorem B579887 : Blo 385764 579887 := bstep (se 1 (by rfl) ⟨434915, by rfl⟩ : syracuseStep 579887 = 869831) B869831
theorem B580127 : Blo 385764 580127 := bstep (se 1 (by rfl) ⟨435095, by rfl⟩ : syracuseStep 580127 = 870191) B870191
theorem B2415193 : Blo 385764 2415193 := bstep (se 2 (by rfl) ⟨905697, by rfl⟩ : syracuseStep 2415193 = 1811395) B1811395
theorem B1956473 : Blo 385764 1956473 := bstep (se 2 (by rfl) ⟨733677, by rfl⟩ : syracuseStep 1956473 = 1467355) B1467355
theorem B2480777 : Blo 385764 2480777 := bstep (se 2 (by rfl) ⟨930291, by rfl⟩ : syracuseStep 2480777 = 1860583) B1860583
theorem B744275 : Blo 385764 744275 := bstep (se 1 (by rfl) ⟨558206, by rfl⟩ : syracuseStep 744275 = 1116413) B1116413
theorem B580511 : Blo 385764 580511 := bstep (se 1 (by rfl) ⟨435383, by rfl⟩ : syracuseStep 580511 = 870767) B870767
theorem B580559 : Blo 385764 580559 := bstep (se 1 (by rfl) ⟨435419, by rfl⟩ : syracuseStep 580559 = 870839) B870839
theorem B1793015 : Blo 385764 1793015 := bstep (se 1 (by rfl) ⟨1344761, by rfl⟩ : syracuseStep 1793015 = 2689523) B2689523
theorem B580649 : Blo 385764 580649 := bstep (se 2 (by rfl) ⟨217743, by rfl⟩ : syracuseStep 580649 = 435487) B435487
theorem B580655 : Blo 385764 580655 := bstep (se 1 (by rfl) ⟨435491, by rfl⟩ : syracuseStep 580655 = 870983) B870983
theorem B580679 : Blo 385764 580679 := bstep (se 1 (by rfl) ⟨435509, by rfl⟩ : syracuseStep 580679 = 871019) B871019
theorem B875591 : Blo 385764 875591 := bstep (se 1 (by rfl) ⟨656693, by rfl⟩ : syracuseStep 875591 = 1313387) B1313387
theorem B580943 : Blo 385764 580943 := bstep (se 1 (by rfl) ⟨435707, by rfl⟩ : syracuseStep 580943 = 871415) B871415
theorem B581033 : Blo 385764 581033 := bstep (se 2 (by rfl) ⟨217887, by rfl⟩ : syracuseStep 581033 = 435775) B435775
theorem B875987 : Blo 385764 875987 := bstep (se 1 (by rfl) ⟨656990, by rfl⟩ : syracuseStep 875987 = 1313981) B1313981
theorem B581183 : Blo 385764 581183 := bstep (se 1 (by rfl) ⟨435887, by rfl⟩ : syracuseStep 581183 = 871775) B871775
theorem B1400399 : Blo 385764 1400399 := bstep (se 1 (by rfl) ⟨1050299, by rfl⟩ : syracuseStep 1400399 = 2100599) B2100599
theorem B4579031 : Blo 385764 4579031 := bstep (se 1 (by rfl) ⟨3434273, by rfl⟩ : syracuseStep 4579031 = 6868547) B6868547
theorem B876257 : Blo 385764 876257 := bstep (se 2 (by rfl) ⟨328596, by rfl⟩ : syracuseStep 876257 = 657193) B657193
theorem B1302263 : Blo 385764 1302263 := bstep (se 1 (by rfl) ⟨976697, by rfl⟩ : syracuseStep 1302263 = 1953395) B1953395
theorem B581447 : Blo 385764 581447 := bstep (se 1 (by rfl) ⟨436085, by rfl⟩ : syracuseStep 581447 = 872171) B872171
theorem B581531 : Blo 385764 581531 := bstep (se 1 (by rfl) ⟨436148, by rfl⟩ : syracuseStep 581531 = 872297) B872297
theorem B2482109 : Blo 385764 2482109 := bstep (se 3 (by rfl) ⟨465395, by rfl⟩ : syracuseStep 2482109 = 930791) B930791
theorem B3727741 : Blo 385764 3727741 := bstep (se 3 (by rfl) ⟨698951, by rfl⟩ : syracuseStep 3727741 = 1397903) B1397903
theorem B582095 : Blo 385764 582095 := bstep (se 1 (by rfl) ⟨436571, by rfl⟩ : syracuseStep 582095 = 873143) B873143
theorem B582137 : Blo 385764 582137 := bstep (se 2 (by rfl) ⟨218301, by rfl⟩ : syracuseStep 582137 = 436603) B436603
theorem B1401407 : Blo 385764 1401407 := bstep (se 1 (by rfl) ⟨1051055, by rfl⟩ : syracuseStep 1401407 = 2102111) B2102111
theorem B582239 : Blo 385764 582239 := bstep (se 1 (by rfl) ⟨436679, by rfl⟩ : syracuseStep 582239 = 873359) B873359
theorem B1303343 : Blo 385764 1303343 := bstep (se 1 (by rfl) ⟨977507, by rfl⟩ : syracuseStep 1303343 = 1955015) B1955015
theorem B8938291 : Blo 385764 8938291 := bstep (se 1 (by rfl) ⟨6703718, by rfl⟩ : syracuseStep 8938291 = 13407437) B13407437
theorem B385903 : Blo 385764 385903 := bstep (se 1 (by rfl) ⟨289427, by rfl⟩ : syracuseStep 385903 = 578855) B578855
theorem B1303451 : Blo 385764 1303451 := bstep (se 1 (by rfl) ⟨977588, by rfl⟩ : syracuseStep 1303451 = 1955177) B1955177
theorem B385959 : Blo 385764 385959 := bstep (se 1 (by rfl) ⟨289469, by rfl⟩ : syracuseStep 385959 = 578939) B578939
theorem B5694401 : Blo 385764 5694401 := bstep (se 2 (by rfl) ⟨2135400, by rfl⟩ : syracuseStep 5694401 = 4270801) B4270801
theorem B386043 : Blo 385764 386043 := bstep (se 1 (by rfl) ⟨289532, by rfl⟩ : syracuseStep 386043 = 579065) B579065
theorem B386111 : Blo 385764 386111 := bstep (se 1 (by rfl) ⟨289583, by rfl⟩ : syracuseStep 386111 = 579167) B579167
theorem B582719 : Blo 385764 582719 := bstep (se 1 (by rfl) ⟨437039, by rfl⟩ : syracuseStep 582719 = 874079) B874079
theorem B582761 : Blo 385764 582761 := bstep (se 2 (by rfl) ⟨218535, by rfl⟩ : syracuseStep 582761 = 437071) B437071
theorem B1107067 : Blo 385764 1107067 := bstep (se 1 (by rfl) ⟨830300, by rfl⟩ : syracuseStep 1107067 = 1660601) B1660601
theorem B386255 : Blo 385764 386255 := bstep (se 1 (by rfl) ⟨289691, by rfl⟩ : syracuseStep 386255 = 579383) B579383
theorem B582863 : Blo 385764 582863 := bstep (se 1 (by rfl) ⟨437147, by rfl⟩ : syracuseStep 582863 = 874295) B874295
theorem B386459 : Blo 385764 386459 := bstep (se 1 (by rfl) ⟨289844, by rfl⟩ : syracuseStep 386459 = 579689) B579689
theorem B583067 : Blo 385764 583067 := bstep (se 1 (by rfl) ⟨437300, by rfl⟩ : syracuseStep 583067 = 874601) B874601
theorem B5596739 : Blo 385764 5596739 := bstep (se 1 (by rfl) ⟨4197554, by rfl⟩ : syracuseStep 5596739 = 8395109) B8395109
theorem B976495 : Blo 385764 976495 := bstep (se 1 (by rfl) ⟨732371, by rfl⟩ : syracuseStep 976495 = 1464743) B1464743
theorem B386671 : Blo 385764 386671 := bstep (se 1 (by rfl) ⟨290003, by rfl⟩ : syracuseStep 386671 = 580007) B580007
theorem B583289 : Blo 385764 583289 := bstep (se 2 (by rfl) ⟨218733, by rfl⟩ : syracuseStep 583289 = 437467) B437467
theorem B386727 : Blo 385764 386727 := bstep (se 1 (by rfl) ⟨290045, by rfl⟩ : syracuseStep 386727 = 580091) B580091
theorem B976607 : Blo 385764 976607 := bstep (se 1 (by rfl) ⟨732455, by rfl⟩ : syracuseStep 976607 = 1464911) B1464911
theorem B583391 : Blo 385764 583391 := bstep (se 1 (by rfl) ⟨437543, by rfl⟩ : syracuseStep 583391 = 875087) B875087
theorem B386811 : Blo 385764 386811 := bstep (se 1 (by rfl) ⟨290108, by rfl⟩ : syracuseStep 386811 = 580217) B580217
theorem B386847 : Blo 385764 386847 := bstep (se 1 (by rfl) ⟨290135, by rfl⟩ : syracuseStep 386847 = 580271) B580271
theorem B386879 : Blo 385764 386879 := bstep (se 1 (by rfl) ⟨290159, by rfl⟩ : syracuseStep 386879 = 580319) B580319
theorem B583487 : Blo 385764 583487 := bstep (se 1 (by rfl) ⟨437615, by rfl⟩ : syracuseStep 583487 = 875231) B875231
theorem B583655 : Blo 385764 583655 := bstep (se 1 (by rfl) ⟨437741, by rfl⟩ : syracuseStep 583655 = 875483) B875483
theorem B387055 : Blo 385764 387055 := bstep (se 1 (by rfl) ⟨290291, by rfl⟩ : syracuseStep 387055 = 580583) B580583
theorem B583673 : Blo 385764 583673 := bstep (se 2 (by rfl) ⟨218877, by rfl⟩ : syracuseStep 583673 = 437755) B437755
theorem B1304585 : Blo 385764 1304585 := bstep (se 2 (by rfl) ⟨489219, by rfl⟩ : syracuseStep 1304585 = 978439) B978439
theorem B583775 : Blo 385764 583775 := bstep (se 1 (by rfl) ⟨437831, by rfl⟩ : syracuseStep 583775 = 875663) B875663
theorem B387227 : Blo 385764 387227 := bstep (se 1 (by rfl) ⟨290420, by rfl⟩ : syracuseStep 387227 = 580841) B580841
theorem B583835 : Blo 385764 583835 := bstep (se 1 (by rfl) ⟨437876, by rfl⟩ : syracuseStep 583835 = 875753) B875753
theorem B387263 : Blo 385764 387263 := bstep (se 1 (by rfl) ⟨290447, by rfl⟩ : syracuseStep 387263 = 580895) B580895
theorem B583871 : Blo 385764 583871 := bstep (se 1 (by rfl) ⟨437903, by rfl⟩ : syracuseStep 583871 = 875807) B875807
theorem B1468631 : Blo 385764 1468631 := bstep (se 1 (by rfl) ⟨1101473, by rfl⟩ : syracuseStep 1468631 = 2202947) B2202947
theorem B3795173 : Blo 385764 3795173 := bstep (se 4 (by rfl) ⟨355797, by rfl⟩ : syracuseStep 3795173 = 711595) B711595
theorem B583913 : Blo 385764 583913 := bstep (se 2 (by rfl) ⟨218967, by rfl⟩ : syracuseStep 583913 = 437935) B437935
theorem B1108217 : Blo 385764 1108217 := bstep (se 2 (by rfl) ⟨415581, by rfl⟩ : syracuseStep 1108217 = 831163) B831163
theorem B551215 : Blo 385764 551215 := bstep (se 1 (by rfl) ⟨413411, by rfl⟩ : syracuseStep 551215 = 826823) B826823
theorem B387375 : Blo 385764 387375 := bstep (se 1 (by rfl) ⟨290531, by rfl⟩ : syracuseStep 387375 = 581063) B581063
theorem B3303737 : Blo 385764 3303737 := bstep (se 2 (by rfl) ⟨1238901, by rfl⟩ : syracuseStep 3303737 = 2477803) B2477803
theorem B2484569 : Blo 385764 2484569 := bstep (se 2 (by rfl) ⟨931713, by rfl⟩ : syracuseStep 2484569 = 1863427) B1863427
theorem B1862027 : Blo 385764 1862027 := bstep (se 1 (by rfl) ⟨1396520, by rfl⟩ : syracuseStep 1862027 = 2793041) B2793041
theorem B387611 : Blo 385764 387611 := bstep (se 1 (by rfl) ⟨290708, by rfl⟩ : syracuseStep 387611 = 581417) B581417
theorem B584219 : Blo 385764 584219 := bstep (se 1 (by rfl) ⟨438164, by rfl⟩ : syracuseStep 584219 = 876329) B876329
theorem B387615 : Blo 385764 387615 := bstep (se 1 (by rfl) ⟨290711, by rfl⟩ : syracuseStep 387615 = 581423) B581423
theorem B584297 : Blo 385764 584297 := bstep (se 2 (by rfl) ⟨219111, by rfl⟩ : syracuseStep 584297 = 438223) B438223
theorem B5040899 : Blo 385764 5040899 := bstep (se 1 (by rfl) ⟨3780674, by rfl⟩ : syracuseStep 5040899 = 7561349) B7561349
theorem B387931 : Blo 385764 387931 := bstep (se 1 (by rfl) ⟨290948, by rfl⟩ : syracuseStep 387931 = 581897) B581897
theorem B387999 : Blo 385764 387999 := bstep (se 1 (by rfl) ⟨290999, by rfl⟩ : syracuseStep 387999 = 581999) B581999
theorem B167668697 : Blo 385764 167668697 := bstep (se 2 (by rfl) ⟨62875761, by rfl⟩ : syracuseStep 167668697 = 125751523) B125751523
theorem B388143 : Blo 385764 388143 := bstep (se 1 (by rfl) ⟨291107, by rfl⟩ : syracuseStep 388143 = 582215) B582215
theorem B388167 : Blo 385764 388167 := bstep (se 1 (by rfl) ⟨291125, by rfl⟩ : syracuseStep 388167 = 582251) B582251
theorem B388319 : Blo 385764 388319 := bstep (se 1 (by rfl) ⟨291239, by rfl⟩ : syracuseStep 388319 = 582479) B582479
theorem B1305881 : Blo 385764 1305881 := bstep (se 2 (by rfl) ⟨489705, by rfl⟩ : syracuseStep 1305881 = 979411) B979411
theorem B1240363 : Blo 385764 1240363 := bstep (se 1 (by rfl) ⟨930272, by rfl⟩ : syracuseStep 1240363 = 1860545) B1860545
theorem B1305935 : Blo 385764 1305935 := bstep (se 1 (by rfl) ⟨979451, by rfl⟩ : syracuseStep 1305935 = 1958903) B1958903
theorem B617959 : Blo 385764 617959 := bstep (se 1 (by rfl) ⟨463469, by rfl⟩ : syracuseStep 617959 = 926939) B926939
theorem B388583 : Blo 385764 388583 := bstep (se 1 (by rfl) ⟨291437, by rfl⟩ : syracuseStep 388583 = 582875) B582875
theorem B388699 : Blo 385764 388699 := bstep (se 1 (by rfl) ⟨291524, by rfl⟩ : syracuseStep 388699 = 583049) B583049
theorem B4419197 : Blo 385764 4419197 := bstep (se 3 (by rfl) ⟨828599, by rfl⟩ : syracuseStep 4419197 = 1657199) B1657199
theorem B1109629 : Blo 385764 1109629 := bstep (se 3 (by rfl) ⟨208055, by rfl⟩ : syracuseStep 1109629 = 416111) B416111
theorem B388935 : Blo 385764 388935 := bstep (se 1 (by rfl) ⟨291701, by rfl⟩ : syracuseStep 388935 = 583403) B583403
theorem B651179 : Blo 385764 651179 := bstep (se 1 (by rfl) ⟨488384, by rfl⟩ : syracuseStep 651179 = 976769) B976769
theorem B389087 : Blo 385764 389087 := bstep (se 1 (by rfl) ⟨291815, by rfl⟩ : syracuseStep 389087 = 583631) B583631
theorem B979067 : Blo 385764 979067 := bstep (se 1 (by rfl) ⟨734300, by rfl⟩ : syracuseStep 979067 = 1468601) B1468601
theorem B2355389 : Blo 385764 2355389 := bstep (se 3 (by rfl) ⟨441635, by rfl⟩ : syracuseStep 2355389 = 883271) B883271
theorem B389351 : Blo 385764 389351 := bstep (se 1 (by rfl) ⟨292013, by rfl⟩ : syracuseStep 389351 = 584027) B584027
theorem B389503 : Blo 385764 389503 := bstep (se 1 (by rfl) ⟨292127, by rfl⟩ : syracuseStep 389503 = 584255) B584255
theorem B651719 : Blo 385764 651719 := bstep (se 1 (by rfl) ⟨488789, by rfl⟩ : syracuseStep 651719 = 977579) B977579
theorem B389583 : Blo 385764 389583 := bstep (se 1 (by rfl) ⟨292187, by rfl⟩ : syracuseStep 389583 = 584375) B584375
theorem B1307231 : Blo 385764 1307231 := bstep (se 1 (by rfl) ⟨980423, by rfl⟩ : syracuseStep 1307231 = 1960847) B1960847
theorem B389735 : Blo 385764 389735 := bstep (se 1 (by rfl) ⟨292301, by rfl⟩ : syracuseStep 389735 = 584603) B584603
theorem B488359 : Blo 385764 488359 := bstep (se 1 (by rfl) ⟨366269, by rfl⟩ : syracuseStep 488359 = 732539) B732539
theorem B7435253 : Blo 385764 7435253 := bstep (se 5 (by rfl) ⟨348527, by rfl⟩ : syracuseStep 7435253 = 697055) B697055
theorem B652495 : Blo 385764 652495 := bstep (se 1 (by rfl) ⟨489371, by rfl⟩ : syracuseStep 652495 = 978743) B978743
theorem B18216355 : Blo 385764 18216355 := bstep (se 1 (by rfl) ⟨13662266, by rfl⟩ : syracuseStep 18216355 = 27324533) B27324533
theorem B1242593 : Blo 385764 1242593 := bstep (se 2 (by rfl) ⟨465972, by rfl⟩ : syracuseStep 1242593 = 931945) B931945
theorem B1242695 : Blo 385764 1242695 := bstep (se 1 (by rfl) ⟨932021, by rfl⟩ : syracuseStep 1242695 = 1864043) B1864043
theorem B489179 : Blo 385764 489179 := bstep (se 1 (by rfl) ⟨366884, by rfl⟩ : syracuseStep 489179 = 733769) B733769
theorem B1046267 : Blo 385764 1046267 := bstep (se 1 (by rfl) ⟨784700, by rfl⟩ : syracuseStep 1046267 = 1569401) B1569401
theorem B1308473 : Blo 385764 1308473 := bstep (se 2 (by rfl) ⟨490677, by rfl⟩ : syracuseStep 1308473 = 981355) B981355
theorem B2488259 : Blo 385764 2488259 := bstep (se 1 (by rfl) ⟨1866194, by rfl⟩ : syracuseStep 2488259 = 3732389) B3732389
theorem B1308635 : Blo 385764 1308635 := bstep (se 1 (by rfl) ⟨981476, by rfl⟩ : syracuseStep 1308635 = 1962953) B1962953
theorem B653305 : Blo 385764 653305 := bstep (se 2 (by rfl) ⟨244989, by rfl⟩ : syracuseStep 653305 = 489979) B489979
theorem B7075937 : Blo 385764 7075937 := bstep (se 2 (by rfl) ⟨2653476, by rfl⟩ : syracuseStep 7075937 = 5306953) B5306953
theorem B653467 : Blo 385764 653467 := bstep (se 1 (by rfl) ⟨490100, by rfl⟩ : syracuseStep 653467 = 980201) B980201
theorem B1308905 : Blo 385764 1308905 := bstep (se 2 (by rfl) ⟨490839, by rfl⟩ : syracuseStep 1308905 = 981679) B981679
theorem B653575 : Blo 385764 653575 := bstep (se 1 (by rfl) ⟨490181, by rfl⟩ : syracuseStep 653575 = 980363) B980363
theorem B653609 : Blo 385764 653609 := bstep (se 2 (by rfl) ⟨245103, by rfl⟩ : syracuseStep 653609 = 490207) B490207
theorem B3307837 : Blo 385764 3307837 := bstep (se 3 (by rfl) ⟨620219, by rfl⟩ : syracuseStep 3307837 = 1240439) B1240439
theorem B3308111 : Blo 385764 3308111 := bstep (se 1 (by rfl) ⟨2481083, by rfl⟩ : syracuseStep 3308111 = 4962167) B4962167
theorem B1309337 : Blo 385764 1309337 := bstep (se 2 (by rfl) ⟨491001, by rfl⟩ : syracuseStep 1309337 = 982003) B982003
theorem B1047401 : Blo 385764 1047401 := bstep (se 2 (by rfl) ⟨392775, by rfl⟩ : syracuseStep 1047401 = 785551) B785551
theorem B490475 : Blo 385764 490475 := bstep (se 1 (by rfl) ⟨367856, by rfl⟩ : syracuseStep 490475 = 735713) B735713
theorem B4193369 : Blo 385764 4193369 := bstep (se 2 (by rfl) ⟨1572513, by rfl⟩ : syracuseStep 4193369 = 3145027) B3145027
theorem B1244285 : Blo 385764 1244285 := bstep (se 3 (by rfl) ⟨233303, by rfl⟩ : syracuseStep 1244285 = 466607) B466607
theorem B982145 : Blo 385764 982145 := bstep (se 2 (by rfl) ⟨368304, by rfl⟩ : syracuseStep 982145 = 736609) B736609
theorem B654601 : Blo 385764 654601 := bstep (se 2 (by rfl) ⟨245475, by rfl⟩ : syracuseStep 654601 = 490951) B490951
theorem B982439 : Blo 385764 982439 := bstep (se 1 (by rfl) ⟨736829, by rfl⟩ : syracuseStep 982439 = 1473659) B1473659
theorem B2358791 : Blo 385764 2358791 := bstep (se 1 (by rfl) ⟨1769093, by rfl⟩ : syracuseStep 2358791 = 3538187) B3538187
theorem B1080911 : Blo 385764 1080911 := bstep (se 1 (by rfl) ⟨810683, by rfl⟩ : syracuseStep 1080911 = 1621367) B1621367
theorem B655175 : Blo 385764 655175 := bstep (se 1 (by rfl) ⟨491381, by rfl⟩ : syracuseStep 655175 = 982763) B982763
theorem B1245053 : Blo 385764 1245053 := bstep (se 3 (by rfl) ⟨233447, by rfl⟩ : syracuseStep 1245053 = 466895) B466895
theorem B982955 : Blo 385764 982955 := bstep (se 1 (by rfl) ⟨737216, by rfl⟩ : syracuseStep 982955 = 1474433) B1474433
theorem B40468403 : Blo 385764 40468403 := bstep (se 1 (by rfl) ⟨30351302, by rfl⟩ : syracuseStep 40468403 = 60702605) B60702605
theorem B14516281 : Blo 385764 14516281 := bstep (se 2 (by rfl) ⟨5443605, by rfl⟩ : syracuseStep 14516281 = 10887211) B10887211
theorem B885343 : Blo 385764 885343 := bstep (se 1 (by rfl) ⟨664007, by rfl⟩ : syracuseStep 885343 = 1328015) B1328015
theorem B656059 : Blo 385764 656059 := bstep (se 1 (by rfl) ⟨492044, by rfl⟩ : syracuseStep 656059 = 984089) B984089
theorem B1967327 : Blo 385764 1967327 := bstep (se 1 (by rfl) ⟨1475495, by rfl⟩ : syracuseStep 1967327 = 2950991) B2950991
theorem B787691 : Blo 385764 787691 := bstep (se 1 (by rfl) ⟨590768, by rfl⟩ : syracuseStep 787691 = 1181537) B1181537
theorem B656687 : Blo 385764 656687 := bstep (se 1 (by rfl) ⟨492515, by rfl⟩ : syracuseStep 656687 = 985031) B985031
theorem B394543 : Blo 385764 394543 := bstep (se 1 (by rfl) ⟨295907, by rfl⟩ : syracuseStep 394543 = 591815) B591815
theorem B1312091 : Blo 385764 1312091 := bstep (se 1 (by rfl) ⟨984068, by rfl⟩ : syracuseStep 1312091 = 1968137) B1968137
theorem B984545 : Blo 385764 984545 := bstep (se 2 (by rfl) ⟨369204, by rfl⟩ : syracuseStep 984545 = 738409) B738409
theorem B1476089 : Blo 385764 1476089 := bstep (se 2 (by rfl) ⟨553533, by rfl⟩ : syracuseStep 1476089 = 1107067) B1107067
theorem B1312361 : Blo 385764 1312361 := bstep (se 2 (by rfl) ⟨492135, by rfl⟩ : syracuseStep 1312361 = 984271) B984271
theorem B1312523 : Blo 385764 1312523 := bstep (se 1 (by rfl) ⟨984392, by rfl⟩ : syracuseStep 1312523 = 1968785) B1968785
theorem B6686479 : Blo 385764 6686479 := bstep (se 1 (by rfl) ⟨5014859, by rfl⟩ : syracuseStep 6686479 = 10029719) B10029719
theorem B1312793 : Blo 385764 1312793 := bstep (se 2 (by rfl) ⟨492297, by rfl⟩ : syracuseStep 1312793 = 984595) B984595
theorem B952415 : Blo 385764 952415 := bstep (se 1 (by rfl) ⟨714311, by rfl⟩ : syracuseStep 952415 = 1428623) B1428623
theorem B1312955 : Blo 385764 1312955 := bstep (se 1 (by rfl) ⟨984716, by rfl⟩ : syracuseStep 1312955 = 1969433) B1969433
theorem B985385 : Blo 385764 985385 := bstep (se 2 (by rfl) ⟨369519, by rfl⟩ : syracuseStep 985385 = 739039) B739039
theorem B887119 : Blo 385764 887119 := bstep (se 1 (by rfl) ⟨665339, by rfl⟩ : syracuseStep 887119 = 1330679) B1330679
theorem B1771903 : Blo 385764 1771903 := bstep (se 1 (by rfl) ⟨1328927, by rfl⟩ : syracuseStep 1771903 = 2657855) B2657855
theorem B6261563 : Blo 385764 6261563 := bstep (se 1 (by rfl) ⟨4696172, by rfl⟩ : syracuseStep 6261563 = 9392345) B9392345
theorem B12881029 : Blo 385764 12881029 := bstep (se 4 (by rfl) ⟨1207596, by rfl⟩ : syracuseStep 12881029 = 2415193) B2415193
theorem B2952449 : Blo 385764 2952449 := bstep (se 2 (by rfl) ⟨1107168, by rfl⟩ : syracuseStep 2952449 = 2214337) B2214337
theorem B1314143 : Blo 385764 1314143 := bstep (se 1 (by rfl) ⟨985607, by rfl⟩ : syracuseStep 1314143 = 1971215) B1971215
theorem B986489 : Blo 385764 986489 := bstep (se 2 (by rfl) ⟨369933, by rfl⟩ : syracuseStep 986489 = 739867) B739867
theorem B2101115 : Blo 385764 2101115 := bstep (se 1 (by rfl) ⟨1575836, by rfl⟩ : syracuseStep 2101115 = 3151673) B3151673
theorem B1314683 : Blo 385764 1314683 := bstep (se 1 (by rfl) ⟨986012, by rfl⟩ : syracuseStep 1314683 = 1972025) B1972025
theorem B4460609 : Blo 385764 4460609 := bstep (se 2 (by rfl) ⟨1672728, by rfl⟩ : syracuseStep 4460609 = 3345457) B3345457
theorem B823945 : Blo 385764 823945 := bstep (se 2 (by rfl) ⟨308979, by rfl⟩ : syracuseStep 823945 = 617959) B617959
theorem B1479505 : Blo 385764 1479505 := bstep (se 2 (by rfl) ⟨554814, by rfl⟩ : syracuseStep 1479505 = 1109629) B1109629
theorem B2233261 : Blo 385764 2233261 := bstep (se 3 (by rfl) ⟨418736, by rfl⟩ : syracuseStep 2233261 = 837473) B837473
theorem B3052687 : Blo 385764 3052687 := bstep (se 1 (by rfl) ⟨2289515, by rfl⟩ : syracuseStep 3052687 = 4579031) B4579031
theorem B1578953 : Blo 385764 1578953 := bstep (se 2 (by rfl) ⟨592107, by rfl⟩ : syracuseStep 1578953 = 1184215) B1184215
theorem B1972349 : Blo 385764 1972349 := bstep (se 3 (by rfl) ⟨369815, by rfl⟩ : syracuseStep 1972349 = 739631) B739631
theorem B4397327 : Blo 385764 4397327 := bstep (se 1 (by rfl) ⟨3297995, by rfl⟩ : syracuseStep 4397327 = 6595991) B6595991
theorem B1972511 : Blo 385764 1972511 := bstep (se 1 (by rfl) ⟨1479383, by rfl⟩ : syracuseStep 1972511 = 2958767) B2958767
theorem B2530115 : Blo 385764 2530115 := bstep (se 1 (by rfl) ⟨1897586, by rfl⟩ : syracuseStep 2530115 = 3795173) B3795173
theorem B2202491 : Blo 385764 2202491 := bstep (se 1 (by rfl) ⟨1651868, by rfl⟩ : syracuseStep 2202491 = 3303737) B3303737
theorem B24288473 : Blo 385764 24288473 := bstep (se 2 (by rfl) ⟨9108177, by rfl⟩ : syracuseStep 24288473 = 18216355) B18216355
theorem B111779131 : Blo 385764 111779131 := bstep (se 1 (by rfl) ⟨83834348, by rfl⟩ : syracuseStep 111779131 = 167668697) B167668697
theorem B434119 : Blo 385764 434119 := bstep (se 1 (by rfl) ⟨325589, by rfl⟩ : syracuseStep 434119 = 651179) B651179
theorem B434479 : Blo 385764 434479 := bstep (se 1 (by rfl) ⟨325859, by rfl⟩ : syracuseStep 434479 = 651719) B651719
theorem B11903449 : Blo 385764 11903449 := bstep (se 2 (by rfl) ⟨4463793, by rfl⟩ : syracuseStep 11903449 = 8927587) B8927587
theorem B4956835 : Blo 385764 4956835 := bstep (se 1 (by rfl) ⟨3717626, by rfl⟩ : syracuseStep 4956835 = 7435253) B7435253
theorem B828395 : Blo 385764 828395 := bstep (se 1 (by rfl) ⟨621296, by rfl⟩ : syracuseStep 828395 = 1242593) B1242593
theorem B828463 : Blo 385764 828463 := bstep (se 1 (by rfl) ⟨621347, by rfl⟩ : syracuseStep 828463 = 1242695) B1242695
theorem B697511 : Blo 385764 697511 := bstep (se 1 (by rfl) ⟨523133, by rfl⟩ : syracuseStep 697511 = 1046267) B1046267
theorem B435739 : Blo 385764 435739 := bstep (se 1 (by rfl) ⟨326804, by rfl⟩ : syracuseStep 435739 = 653609) B653609
theorem B665161 : Blo 385764 665161 := bstep (se 2 (by rfl) ⟨249435, by rfl⟩ : syracuseStep 665161 = 498871) B498871
theorem B2205407 : Blo 385764 2205407 := bstep (se 1 (by rfl) ⟨1654055, by rfl⟩ : syracuseStep 2205407 = 3308111) B3308111
theorem B698267 : Blo 385764 698267 := bstep (se 1 (by rfl) ⟨523700, by rfl⟩ : syracuseStep 698267 = 1047401) B1047401
theorem B927737 : Blo 385764 927737 := bstep (se 2 (by rfl) ⟨347901, by rfl⟩ : syracuseStep 927737 = 695803) B695803
theorem B2795579 : Blo 385764 2795579 := bstep (se 1 (by rfl) ⟨2096684, by rfl⟩ : syracuseStep 2795579 = 4193369) B4193369
theorem B829523 : Blo 385764 829523 := bstep (se 1 (by rfl) ⟨622142, by rfl⟩ : syracuseStep 829523 = 1244285) B1244285
theorem B5286221 : Blo 385764 5286221 := bstep (se 3 (by rfl) ⟨991166, by rfl⟩ : syracuseStep 5286221 = 1982333) B1982333
theorem B4401701 : Blo 385764 4401701 := bstep (se 4 (by rfl) ⟨412659, by rfl⟩ : syracuseStep 4401701 = 825319) B825319
theorem B436783 : Blo 385764 436783 := bstep (se 1 (by rfl) ⟨327587, by rfl⟩ : syracuseStep 436783 = 655175) B655175
theorem B830035 : Blo 385764 830035 := bstep (se 1 (by rfl) ⟨622526, by rfl⟩ : syracuseStep 830035 = 1245053) B1245053
theorem B26978935 : Blo 385764 26978935 := bstep (se 1 (by rfl) ⟨20234201, by rfl⟩ : syracuseStep 26978935 = 40468403) B40468403
theorem B437215 : Blo 385764 437215 := bstep (se 1 (by rfl) ⟨327911, by rfl⟩ : syracuseStep 437215 = 655823) B655823
theorem B2207321 : Blo 385764 2207321 := bstep (se 2 (by rfl) ⟨827745, by rfl⟩ : syracuseStep 2207321 = 1655491) B1655491
theorem B437863 : Blo 385764 437863 := bstep (se 1 (by rfl) ⟨328397, by rfl⟩ : syracuseStep 437863 = 656795) B656795
theorem B438079 : Blo 385764 438079 := bstep (se 1 (by rfl) ⟨328559, by rfl⟩ : syracuseStep 438079 = 657119) B657119
theorem B107720603 : Blo 385764 107720603 := bstep (se 1 (by rfl) ⟨80790452, by rfl⟩ : syracuseStep 107720603 = 161580905) B161580905
theorem B276377615 : Blo 385764 276377615 := bstep (se 1 (by rfl) ⟨207283211, by rfl⟩ : syracuseStep 276377615 = 414566423) B414566423
theorem B438367 : Blo 385764 438367 := bstep (se 1 (by rfl) ⟨328775, by rfl⟩ : syracuseStep 438367 = 657551) B657551
theorem B3322295 : Blo 385764 3322295 := bstep (se 1 (by rfl) ⟨2491721, by rfl⟩ : syracuseStep 3322295 = 4983443) B4983443
theorem B832393 : Blo 385764 832393 := bstep (se 2 (by rfl) ⟨312147, by rfl⟩ : syracuseStep 832393 = 624295) B624295
theorem B3552167 : Blo 385764 3552167 := bstep (se 1 (by rfl) ⟨2664125, by rfl⟩ : syracuseStep 3552167 = 5328251) B5328251
theorem B2799755 : Blo 385764 2799755 := bstep (se 1 (by rfl) ⟨2099816, by rfl⟩ : syracuseStep 2799755 = 4199633) B4199633
theorem B735979 : Blo 385764 735979 := bstep (se 1 (by rfl) ⟨551984, by rfl⟩ : syracuseStep 735979 = 1103969) B1103969
theorem B1653817 : Blo 385764 1653817 := bstep (se 2 (by rfl) ⟨620181, by rfl⟩ : syracuseStep 1653817 = 1240363) B1240363
theorem B1653851 : Blo 385764 1653851 := bstep (se 1 (by rfl) ⟨1240388, by rfl⟩ : syracuseStep 1653851 = 2480777) B2480777
theorem B2210921 : Blo 385764 2210921 := bstep (se 2 (by rfl) ⟨829095, by rfl⟩ : syracuseStep 2210921 = 1658191) B1658191
theorem B1195343 : Blo 385764 1195343 := bstep (se 1 (by rfl) ⟨896507, by rfl⟩ : syracuseStep 1195343 = 1793015) B1793015
theorem B933599 : Blo 385764 933599 := bstep (se 1 (by rfl) ⟨700199, by rfl⟩ : syracuseStep 933599 = 1400399) B1400399
theorem B868175 : Blo 385764 868175 := bstep (se 1 (by rfl) ⟨651131, by rfl⟩ : syracuseStep 868175 = 1302263) B1302263
theorem B6635357 : Blo 385764 6635357 := bstep (se 3 (by rfl) ⟨1244129, by rfl⟩ : syracuseStep 6635357 = 2488259) B2488259
theorem B1654739 : Blo 385764 1654739 := bstep (se 1 (by rfl) ⟨1241054, by rfl⟩ : syracuseStep 1654739 = 2482109) B2482109
theorem B934271 : Blo 385764 934271 := bstep (se 1 (by rfl) ⟨700703, by rfl⟩ : syracuseStep 934271 = 1401407) B1401407
theorem B868895 : Blo 385764 868895 := bstep (se 1 (by rfl) ⟨651671, by rfl⟩ : syracuseStep 868895 = 1303343) B1303343
theorem B868967 : Blo 385764 868967 := bstep (se 1 (by rfl) ⟨651725, by rfl⟩ : syracuseStep 868967 = 1303451) B1303451
theorem B869723 : Blo 385764 869723 := bstep (se 1 (by rfl) ⟨652292, by rfl⟩ : syracuseStep 869723 = 1304585) B1304585
theorem B738811 : Blo 385764 738811 := bstep (se 1 (by rfl) ⟨554108, by rfl⟩ : syracuseStep 738811 = 1108217) B1108217
theorem B1656379 : Blo 385764 1656379 := bstep (se 1 (by rfl) ⟨1242284, by rfl⟩ : syracuseStep 1656379 = 2484569) B2484569
theorem B869993 : Blo 385764 869993 := bstep (se 2 (by rfl) ⟨326247, by rfl⟩ : syracuseStep 869993 = 652495) B652495
theorem B55428907 : Blo 385764 55428907 := bstep (se 1 (by rfl) ⟨41571680, by rfl⟩ : syracuseStep 55428907 = 83143361) B83143361
theorem B3360599 : Blo 385764 3360599 := bstep (se 1 (by rfl) ⟨2520449, by rfl⟩ : syracuseStep 3360599 = 5040899) B5040899
theorem B870587 : Blo 385764 870587 := bstep (se 1 (by rfl) ⟨652940, by rfl⟩ : syracuseStep 870587 = 1305881) B1305881
theorem B1984733 : Blo 385764 1984733 := bstep (se 3 (by rfl) ⟨372137, by rfl⟩ : syracuseStep 1984733 = 744275) B744275
theorem B870623 : Blo 385764 870623 := bstep (se 1 (by rfl) ⟨652967, by rfl⟩ : syracuseStep 870623 = 1305935) B1305935
theorem B871073 : Blo 385764 871073 := bstep (se 2 (by rfl) ⟨326652, by rfl⟩ : syracuseStep 871073 = 653305) B653305
theorem B871289 : Blo 385764 871289 := bstep (se 2 (by rfl) ⟨326733, by rfl⟩ : syracuseStep 871289 = 653467) B653467
theorem B871433 : Blo 385764 871433 := bstep (se 2 (by rfl) ⟨326787, by rfl⟩ : syracuseStep 871433 = 653575) B653575
theorem B871487 : Blo 385764 871487 := bstep (se 1 (by rfl) ⟨653615, by rfl⟩ : syracuseStep 871487 = 1307231) B1307231
theorem B4410449 : Blo 385764 4410449 := bstep (se 2 (by rfl) ⟨1653918, by rfl⟩ : syracuseStep 4410449 = 3307837) B3307837
theorem B1101053 : Blo 385764 1101053 := bstep (se 3 (by rfl) ⟨206447, by rfl⟩ : syracuseStep 1101053 = 412895) B412895
theorem B3329707 : Blo 385764 3329707 := bstep (se 1 (by rfl) ⟨2497280, by rfl⟩ : syracuseStep 3329707 = 4994561) B4994561
theorem B872315 : Blo 385764 872315 := bstep (se 1 (by rfl) ⟨654236, by rfl⟩ : syracuseStep 872315 = 1308473) B1308473
theorem B1953719 : Blo 385764 1953719 := bstep (se 1 (by rfl) ⟨1465289, by rfl⟩ : syracuseStep 1953719 = 2930579) B2930579
theorem B872423 : Blo 385764 872423 := bstep (se 1 (by rfl) ⟨654317, by rfl⟩ : syracuseStep 872423 = 1308635) B1308635
theorem B872603 : Blo 385764 872603 := bstep (se 1 (by rfl) ⟨654452, by rfl⟩ : syracuseStep 872603 = 1308905) B1308905
theorem B708905 : Blo 385764 708905 := bstep (se 2 (by rfl) ⟨265839, by rfl⟩ : syracuseStep 708905 = 531679) B531679
theorem B872801 : Blo 385764 872801 := bstep (se 2 (by rfl) ⟨327300, by rfl⟩ : syracuseStep 872801 = 654601) B654601
theorem B872891 : Blo 385764 872891 := bstep (se 1 (by rfl) ⟨654668, by rfl⟩ : syracuseStep 872891 = 1309337) B1309337
theorem B578927 : Blo 385764 578927 := bstep (se 1 (by rfl) ⟨434195, by rfl⟩ : syracuseStep 578927 = 868391) B868391
theorem B26760577 : Blo 385764 26760577 := bstep (se 2 (by rfl) ⟨10035216, by rfl⟩ : syracuseStep 26760577 = 20070433) B20070433
theorem B13981081 : Blo 385764 13981081 := bstep (se 2 (by rfl) ⟨5242905, by rfl⟩ : syracuseStep 13981081 = 10485811) B10485811
theorem B579047 : Blo 385764 579047 := bstep (se 1 (by rfl) ⟨434285, by rfl⟩ : syracuseStep 579047 = 868571) B868571
theorem B6313459 : Blo 385764 6313459 := bstep (se 1 (by rfl) ⟨4735094, by rfl⟩ : syracuseStep 6313459 = 9470189) B9470189
theorem B579209 : Blo 385764 579209 := bstep (se 2 (by rfl) ⟨217203, by rfl⟩ : syracuseStep 579209 = 434407) B434407
theorem B579227 : Blo 385764 579227 := bstep (se 1 (by rfl) ⟨434420, by rfl⟩ : syracuseStep 579227 = 868841) B868841
theorem B874151 : Blo 385764 874151 := bstep (se 1 (by rfl) ⟨655613, by rfl⟩ : syracuseStep 874151 = 1311227) B1311227
theorem B4970321 : Blo 385764 4970321 := bstep (se 2 (by rfl) ⟨1863870, by rfl⟩ : syracuseStep 4970321 = 3727741) B3727741
theorem B579419 : Blo 385764 579419 := bstep (se 1 (by rfl) ⟨434564, by rfl⟩ : syracuseStep 579419 = 869129) B869129
theorem B874331 : Blo 385764 874331 := bstep (se 1 (by rfl) ⟨655748, by rfl⟩ : syracuseStep 874331 = 1311497) B1311497
theorem B3758147 : Blo 385764 3758147 := bstep (se 1 (by rfl) ⟨2818610, by rfl⟩ : syracuseStep 3758147 = 5637221) B5637221
theorem B1955987 : Blo 385764 1955987 := bstep (se 1 (by rfl) ⟨1466990, by rfl⟩ : syracuseStep 1955987 = 2933981) B2933981
theorem B579803 : Blo 385764 579803 := bstep (se 1 (by rfl) ⟨434852, by rfl⟩ : syracuseStep 579803 = 869705) B869705
theorem B1104185 : Blo 385764 1104185 := bstep (se 2 (by rfl) ⟨414069, by rfl⟩ : syracuseStep 1104185 = 828139) B828139
theorem B874835 : Blo 385764 874835 := bstep (se 1 (by rfl) ⟨656126, by rfl⟩ : syracuseStep 874835 = 1312253) B1312253
theorem B11917721 : Blo 385764 11917721 := bstep (se 2 (by rfl) ⟨4469145, by rfl⟩ : syracuseStep 11917721 = 8938291) B8938291
theorem B580073 : Blo 385764 580073 := bstep (se 2 (by rfl) ⟨217527, by rfl⟩ : syracuseStep 580073 = 435055) B435055
theorem B875321 : Blo 385764 875321 := bstep (se 2 (by rfl) ⟨328245, by rfl⟩ : syracuseStep 875321 = 656491) B656491
theorem B1465199 : Blo 385764 1465199 := bstep (se 1 (by rfl) ⟨1098899, by rfl⟩ : syracuseStep 1465199 = 2197799) B2197799
theorem B580463 : Blo 385764 580463 := bstep (se 1 (by rfl) ⟨435347, by rfl⟩ : syracuseStep 580463 = 870695) B870695
theorem B875375 : Blo 385764 875375 := bstep (se 1 (by rfl) ⟨656531, by rfl⟩ : syracuseStep 875375 = 1313063) B1313063
theorem B580475 : Blo 385764 580475 := bstep (se 1 (by rfl) ⟨435356, by rfl⟩ : syracuseStep 580475 = 870713) B870713
theorem B2939813 : Blo 385764 2939813 := bstep (se 4 (by rfl) ⟨275607, by rfl⟩ : syracuseStep 2939813 = 551215) B551215
theorem B1956797 : Blo 385764 1956797 := bstep (se 3 (by rfl) ⟨366899, by rfl⟩ : syracuseStep 1956797 = 733799) B733799
theorem B47733941 : Blo 385764 47733941 := bstep (se 5 (by rfl) ⟨2237528, by rfl⟩ : syracuseStep 47733941 = 4475057) B4475057
theorem B875951 : Blo 385764 875951 := bstep (se 1 (by rfl) ⟨656963, by rfl⟩ : syracuseStep 875951 = 1313927) B1313927
theorem B1301993 : Blo 385764 1301993 := bstep (se 2 (by rfl) ⟨488247, by rfl⟩ : syracuseStep 1301993 = 976495) B976495
theorem B876023 : Blo 385764 876023 := bstep (se 1 (by rfl) ⟨657017, by rfl⟩ : syracuseStep 876023 = 1314035) B1314035
theorem B1236647 : Blo 385764 1236647 := bstep (se 1 (by rfl) ⟨927485, by rfl⟩ : syracuseStep 1236647 = 1854971) B1854971
theorem B3301073 : Blo 385764 3301073 := bstep (se 2 (by rfl) ⟨1237902, by rfl⟩ : syracuseStep 3301073 = 2475805) B2475805
theorem B581339 : Blo 385764 581339 := bstep (se 1 (by rfl) ⟨436004, by rfl⟩ : syracuseStep 581339 = 872009) B872009
theorem B581609 : Blo 385764 581609 := bstep (se 2 (by rfl) ⟨218103, by rfl⟩ : syracuseStep 581609 = 436207) B436207
theorem B2482163 : Blo 385764 2482163 := bstep (se 1 (by rfl) ⟨1861622, by rfl⟩ : syracuseStep 2482163 = 3723245) B3723245
theorem B5431499 : Blo 385764 5431499 := bstep (se 1 (by rfl) ⟨4073624, by rfl⟩ : syracuseStep 5431499 = 8147249) B8147249
theorem B2351783 : Blo 385764 2351783 := bstep (se 1 (by rfl) ⟨1763837, by rfl⟩ : syracuseStep 2351783 = 3527675) B3527675
theorem B582311 : Blo 385764 582311 := bstep (se 1 (by rfl) ⟨436733, by rfl⟩ : syracuseStep 582311 = 873467) B873467
theorem B385823 : Blo 385764 385823 := bstep (se 1 (by rfl) ⟨289367, by rfl⟩ : syracuseStep 385823 = 578735) B578735
theorem B582431 : Blo 385764 582431 := bstep (se 1 (by rfl) ⟨436823, by rfl⟩ : syracuseStep 582431 = 873647) B873647
theorem B582455 : Blo 385764 582455 := bstep (se 1 (by rfl) ⟨436841, by rfl⟩ : syracuseStep 582455 = 873683) B873683
theorem B20243351 : Blo 385764 20243351 := bstep (se 1 (by rfl) ⟨15182513, by rfl⟩ : syracuseStep 20243351 = 30365027) B30365027
theorem B51045299 : Blo 385764 51045299 := bstep (se 1 (by rfl) ⟨38283974, by rfl⟩ : syracuseStep 51045299 = 76567949) B76567949
theorem B582635 : Blo 385764 582635 := bstep (se 1 (by rfl) ⟨436976, by rfl⟩ : syracuseStep 582635 = 873953) B873953
theorem B386095 : Blo 385764 386095 := bstep (se 1 (by rfl) ⟨289571, by rfl⟩ : syracuseStep 386095 = 579143) B579143
theorem B386159 : Blo 385764 386159 := bstep (se 1 (by rfl) ⟨289619, by rfl⟩ : syracuseStep 386159 = 579239) B579239
theorem B386215 : Blo 385764 386215 := bstep (se 1 (by rfl) ⟨289661, by rfl⟩ : syracuseStep 386215 = 579323) B579323
theorem B386239 : Blo 385764 386239 := bstep (se 1 (by rfl) ⟨289679, by rfl⟩ : syracuseStep 386239 = 579359) B579359
theorem B386271 : Blo 385764 386271 := bstep (se 1 (by rfl) ⟨289703, by rfl⟩ : syracuseStep 386271 = 579407) B579407
theorem B386351 : Blo 385764 386351 := bstep (se 1 (by rfl) ⟨289763, by rfl⟩ : syracuseStep 386351 = 579527) B579527
theorem B386587 : Blo 385764 386587 := bstep (se 1 (by rfl) ⟨289940, by rfl⟩ : syracuseStep 386587 = 579881) B579881
theorem B386591 : Blo 385764 386591 := bstep (se 1 (by rfl) ⟨289943, by rfl⟩ : syracuseStep 386591 = 579887) B579887
theorem B386751 : Blo 385764 386751 := bstep (se 1 (by rfl) ⟨290063, by rfl⟩ : syracuseStep 386751 = 580127) B580127
theorem B1304315 : Blo 385764 1304315 := bstep (se 1 (by rfl) ⟨978236, by rfl⟩ : syracuseStep 1304315 = 1956473) B1956473
theorem B2975491 : Blo 385764 2975491 := bstep (se 1 (by rfl) ⟨2231618, by rfl⟩ : syracuseStep 2975491 = 4463237) B4463237
theorem B1304477 : Blo 385764 1304477 := bstep (se 3 (by rfl) ⟨244589, by rfl⟩ : syracuseStep 1304477 = 489179) B489179
theorem B387007 : Blo 385764 387007 := bstep (se 1 (by rfl) ⟨290255, by rfl⟩ : syracuseStep 387007 = 580511) B580511
theorem B387039 : Blo 385764 387039 := bstep (se 1 (by rfl) ⟨290279, by rfl⟩ : syracuseStep 387039 = 580559) B580559
theorem B550891 : Blo 385764 550891 := bstep (se 1 (by rfl) ⟨413168, by rfl⟩ : syracuseStep 550891 = 826337) B826337
theorem B387099 : Blo 385764 387099 := bstep (se 1 (by rfl) ⟨290324, by rfl⟩ : syracuseStep 387099 = 580649) B580649
theorem B387103 : Blo 385764 387103 := bstep (se 1 (by rfl) ⟨290327, by rfl⟩ : syracuseStep 387103 = 580655) B580655
theorem B387119 : Blo 385764 387119 := bstep (se 1 (by rfl) ⟨290339, by rfl⟩ : syracuseStep 387119 = 580679) B580679
theorem B583727 : Blo 385764 583727 := bstep (se 1 (by rfl) ⟨437795, by rfl⟩ : syracuseStep 583727 = 875591) B875591
theorem B1861775 : Blo 385764 1861775 := bstep (se 1 (by rfl) ⟨1396331, by rfl⟩ : syracuseStep 1861775 = 2792663) B2792663
theorem B387295 : Blo 385764 387295 := bstep (se 1 (by rfl) ⟨290471, by rfl⟩ : syracuseStep 387295 = 580943) B580943
theorem B387355 : Blo 385764 387355 := bstep (se 1 (by rfl) ⟨290516, by rfl⟩ : syracuseStep 387355 = 581033) B581033
theorem B583991 : Blo 385764 583991 := bstep (se 1 (by rfl) ⟨437993, by rfl⟩ : syracuseStep 583991 = 875987) B875987
theorem B387455 : Blo 385764 387455 := bstep (se 1 (by rfl) ⟨290591, by rfl⟩ : syracuseStep 387455 = 581183) B581183
theorem B584171 : Blo 385764 584171 := bstep (se 1 (by rfl) ⟨438128, by rfl⟩ : syracuseStep 584171 = 876257) B876257
theorem B387631 : Blo 385764 387631 := bstep (se 1 (by rfl) ⟨290723, by rfl⟩ : syracuseStep 387631 = 581447) B581447
theorem B387687 : Blo 385764 387687 := bstep (se 1 (by rfl) ⟨290765, by rfl⟩ : syracuseStep 387687 = 581531) B581531
theorem B388063 : Blo 385764 388063 := bstep (se 1 (by rfl) ⟨291047, by rfl⟩ : syracuseStep 388063 = 582095) B582095
theorem B388091 : Blo 385764 388091 := bstep (se 1 (by rfl) ⟨291068, by rfl⟩ : syracuseStep 388091 = 582137) B582137
theorem B388159 : Blo 385764 388159 := bstep (se 1 (by rfl) ⟨291119, by rfl⟩ : syracuseStep 388159 = 582239) B582239
theorem B3796267 : Blo 385764 3796267 := bstep (se 1 (by rfl) ⟨2847200, by rfl⟩ : syracuseStep 3796267 = 5694401) B5694401
theorem B388479 : Blo 385764 388479 := bstep (se 1 (by rfl) ⟨291359, by rfl⟩ : syracuseStep 388479 = 582719) B582719
theorem B388507 : Blo 385764 388507 := bstep (se 1 (by rfl) ⟨291380, by rfl⟩ : syracuseStep 388507 = 582761) B582761
theorem B388575 : Blo 385764 388575 := bstep (se 1 (by rfl) ⟨291431, by rfl⟩ : syracuseStep 388575 = 582863) B582863
theorem B388711 : Blo 385764 388711 := bstep (se 1 (by rfl) ⟨291533, by rfl⟩ : syracuseStep 388711 = 583067) B583067
theorem B1535645 : Blo 385764 1535645 := bstep (se 3 (by rfl) ⟨287933, by rfl⟩ : syracuseStep 1535645 = 575867) B575867
theorem B3731159 : Blo 385764 3731159 := bstep (se 1 (by rfl) ⟨2798369, by rfl⟩ : syracuseStep 3731159 = 5596739) B5596739
theorem B388859 : Blo 385764 388859 := bstep (se 1 (by rfl) ⟨291644, by rfl⟩ : syracuseStep 388859 = 583289) B583289
theorem B651071 : Blo 385764 651071 := bstep (se 1 (by rfl) ⟨488303, by rfl⟩ : syracuseStep 651071 = 976607) B976607
theorem B388927 : Blo 385764 388927 := bstep (se 1 (by rfl) ⟨291695, by rfl⟩ : syracuseStep 388927 = 583391) B583391
theorem B388991 : Blo 385764 388991 := bstep (se 1 (by rfl) ⟨291743, by rfl⟩ : syracuseStep 388991 = 583487) B583487
theorem B651145 : Blo 385764 651145 := bstep (se 2 (by rfl) ⟨244179, by rfl⟩ : syracuseStep 651145 = 488359) B488359
theorem B389103 : Blo 385764 389103 := bstep (se 1 (by rfl) ⟨291827, by rfl⟩ : syracuseStep 389103 = 583655) B583655
theorem B389115 : Blo 385764 389115 := bstep (se 1 (by rfl) ⟨291836, by rfl⟩ : syracuseStep 389115 = 583673) B583673
theorem B389183 : Blo 385764 389183 := bstep (se 1 (by rfl) ⟨291887, by rfl⟩ : syracuseStep 389183 = 583775) B583775
theorem B389223 : Blo 385764 389223 := bstep (se 1 (by rfl) ⟨291917, by rfl⟩ : syracuseStep 389223 = 583835) B583835
theorem B389247 : Blo 385764 389247 := bstep (se 1 (by rfl) ⟨291935, by rfl⟩ : syracuseStep 389247 = 583871) B583871
theorem B979087 : Blo 385764 979087 := bstep (se 1 (by rfl) ⟨734315, by rfl⟩ : syracuseStep 979087 = 1468631) B1468631
theorem B389275 : Blo 385764 389275 := bstep (se 1 (by rfl) ⟨291956, by rfl⟩ : syracuseStep 389275 = 583913) B583913
theorem B1241351 : Blo 385764 1241351 := bstep (se 1 (by rfl) ⟨931013, by rfl⟩ : syracuseStep 1241351 = 1862027) B1862027
theorem B389479 : Blo 385764 389479 := bstep (se 1 (by rfl) ⟨292109, by rfl⟩ : syracuseStep 389479 = 584219) B584219
theorem B389531 : Blo 385764 389531 := bstep (se 1 (by rfl) ⟨292148, by rfl⟩ : syracuseStep 389531 = 584297) B584297
theorem B881209 : Blo 385764 881209 := bstep (se 2 (by rfl) ⟨330453, by rfl⟩ : syracuseStep 881209 = 660907) B660907
theorem B1700765 : Blo 385764 1700765 := bstep (se 3 (by rfl) ⟨318893, by rfl⟩ : syracuseStep 1700765 = 637787) B637787
theorem B2946131 : Blo 385764 2946131 := bstep (se 1 (by rfl) ⟨2209598, by rfl⟩ : syracuseStep 2946131 = 4419197) B4419197
theorem B1307933 : Blo 385764 1307933 := bstep (se 3 (by rfl) ⟨245237, by rfl⟩ : syracuseStep 1307933 = 490475) B490475
theorem B652711 : Blo 385764 652711 := bstep (se 1 (by rfl) ⟨489533, by rfl⟩ : syracuseStep 652711 = 979067) B979067
theorem B1570259 : Blo 385764 1570259 := bstep (se 1 (by rfl) ⟨1177694, by rfl⟩ : syracuseStep 1570259 = 2355389) B2355389
theorem B2946617 : Blo 385764 2946617 := bstep (se 2 (by rfl) ⟨1104981, by rfl⟩ : syracuseStep 2946617 = 2209963) B2209963
theorem B554735 : Blo 385764 554735 := bstep (se 1 (by rfl) ⟨416051, by rfl⟩ : syracuseStep 554735 = 832103) B832103
theorem B489655 : Blo 385764 489655 := bstep (se 1 (by rfl) ⟨367241, by rfl⟩ : syracuseStep 489655 = 734483) B734483
theorem B1866179 : Blo 385764 1866179 := bstep (se 1 (by rfl) ⟨1399634, by rfl⟩ : syracuseStep 1866179 = 2799269) B2799269
theorem B1472975 : Blo 385764 1472975 := bstep (se 1 (by rfl) ⟨1104731, by rfl⟩ : syracuseStep 1472975 = 2209463) B2209463
theorem B2652763 : Blo 385764 2652763 := bstep (se 1 (by rfl) ⟨1989572, by rfl⟩ : syracuseStep 2652763 = 3979145) B3979145
theorem B1866331 : Blo 385764 1866331 := bstep (se 1 (by rfl) ⟨1399748, by rfl⟩ : syracuseStep 1866331 = 2799497) B2799497
theorem B4717291 : Blo 385764 4717291 := bstep (se 1 (by rfl) ⟨3537968, by rfl⟩ : syracuseStep 4717291 = 7075937) B7075937
theorem B2882429 : Blo 385764 2882429 := bstep (se 3 (by rfl) ⟨540455, by rfl⟩ : syracuseStep 2882429 = 1080911) B1080911
theorem B7437257 : Blo 385764 7437257 := bstep (se 2 (by rfl) ⟨2788971, by rfl⟩ : syracuseStep 7437257 = 5577943) B5577943
theorem B654763 : Blo 385764 654763 := bstep (se 1 (by rfl) ⟨491072, by rfl⟩ : syracuseStep 654763 = 982145) B982145
theorem B654959 : Blo 385764 654959 := bstep (se 1 (by rfl) ⟨491219, by rfl⟩ : syracuseStep 654959 = 982439) B982439
theorem B1474159 : Blo 385764 1474159 := bstep (se 1 (by rfl) ⟨1105619, by rfl⟩ : syracuseStep 1474159 = 2211239) B2211239
theorem B1572527 : Blo 385764 1572527 := bstep (se 1 (by rfl) ⟨1179395, by rfl⟩ : syracuseStep 1572527 = 2358791) B2358791
theorem B982793 : Blo 385764 982793 := bstep (se 2 (by rfl) ⟨368547, by rfl⟩ : syracuseStep 982793 = 737095) B737095
theorem B655303 : Blo 385764 655303 := bstep (se 1 (by rfl) ⟨491477, by rfl⟩ : syracuseStep 655303 = 982955) B982955
theorem B11894957 : Blo 385764 11894957 := bstep (se 3 (by rfl) ⟨2230304, by rfl⟩ : syracuseStep 11894957 = 4460609) B4460609
theorem B622847 : Blo 385764 622847 := bstep (se 1 (by rfl) ⟨467135, by rfl⟩ : syracuseStep 622847 = 934271) B934271
theorem B1180457 : Blo 385764 1180457 := bstep (se 2 (by rfl) ⟨442671, by rfl⟩ : syracuseStep 1180457 = 885343) B885343
theorem B1311551 : Blo 385764 1311551 := bstep (se 1 (by rfl) ⟨983663, by rfl⟩ : syracuseStep 1311551 = 1967327) B1967327
theorem B525127 : Blo 385764 525127 := bstep (se 1 (by rfl) ⟨393845, by rfl⟩ : syracuseStep 525127 = 787691) B787691
theorem B656363 : Blo 385764 656363 := bstep (se 1 (by rfl) ⟨492272, by rfl⟩ : syracuseStep 656363 = 984545) B984545
theorem B984059 : Blo 385764 984059 := bstep (se 1 (by rfl) ⟨738044, by rfl⟩ : syracuseStep 984059 = 1476089) B1476089
theorem B656923 : Blo 385764 656923 := bstep (se 1 (by rfl) ⟨492692, by rfl⟩ : syracuseStep 656923 = 985385) B985385
theorem B526057 : Blo 385764 526057 := bstep (se 2 (by rfl) ⟨197271, by rfl⟩ : syracuseStep 526057 = 394543) B394543
theorem B985081 : Blo 385764 985081 := bstep (se 2 (by rfl) ⟨369405, by rfl⟩ : syracuseStep 985081 = 738811) B738811
theorem B1968299 : Blo 385764 1968299 := bstep (se 1 (by rfl) ⟨1476224, by rfl⟩ : syracuseStep 1968299 = 2952449) B2952449
theorem B657659 : Blo 385764 657659 := bstep (se 1 (by rfl) ⟨493244, by rfl⟩ : syracuseStep 657659 = 986489) B986489
theorem B3967321 : Blo 385764 3967321 := bstep (se 2 (by rfl) ⟨1487745, by rfl⟩ : syracuseStep 3967321 = 2975491) B2975491
theorem B2362537 : Blo 385764 2362537 := bstep (se 2 (by rfl) ⟨885951, by rfl⟩ : syracuseStep 2362537 = 1771903) B1771903
theorem B3313547 : Blo 385764 3313547 := bstep (se 1 (by rfl) ⟨2485160, by rfl⟩ : syracuseStep 3313547 = 4970321) B4970321
theorem B1052635 : Blo 385764 1052635 := bstep (se 1 (by rfl) ⟨789476, by rfl⟩ : syracuseStep 1052635 = 1578953) B1578953
theorem B1314899 : Blo 385764 1314899 := bstep (se 1 (by rfl) ⟨986174, by rfl⟩ : syracuseStep 1314899 = 1972349) B1972349
theorem B17174705 : Blo 385764 17174705 := bstep (se 2 (by rfl) ⟨6440514, by rfl⟩ : syracuseStep 17174705 = 12881029) B12881029
theorem B1315007 : Blo 385764 1315007 := bstep (se 1 (by rfl) ⟨986255, by rfl⟩ : syracuseStep 1315007 = 1972511) B1972511
theorem B1479293 : Blo 385764 1479293 := bstep (se 3 (by rfl) ⟨277367, by rfl⟩ : syracuseStep 1479293 = 554735) B554735
theorem B31822627 : Blo 385764 31822627 := bstep (se 1 (by rfl) ⟨23866970, by rfl⟩ : syracuseStep 31822627 = 47733941) B47733941
theorem B16192315 : Blo 385764 16192315 := bstep (se 1 (by rfl) ⟨12144236, by rfl⟩ : syracuseStep 16192315 = 24288473) B24288473
theorem B824431 : Blo 385764 824431 := bstep (se 1 (by rfl) ⟨618323, by rfl⟩ : syracuseStep 824431 = 1236647) B1236647
theorem B2200715 : Blo 385764 2200715 := bstep (se 1 (by rfl) ⟨1650536, by rfl⟩ : syracuseStep 2200715 = 3301073) B3301073
theorem B1972673 : Blo 385764 1972673 := bstep (se 2 (by rfl) ⟨739752, by rfl⟩ : syracuseStep 1972673 = 1479505) B1479505
theorem B465511 : Blo 385764 465511 := bstep (se 1 (by rfl) ⟨349133, by rfl⟩ : syracuseStep 465511 = 698267) B698267
theorem B4070249 : Blo 385764 4070249 := bstep (se 2 (by rfl) ⟨1526343, by rfl⟩ : syracuseStep 4070249 = 3052687) B3052687
theorem B1023763 : Blo 385764 1023763 := bstep (se 1 (by rfl) ⟨767822, by rfl⟩ : syracuseStep 1023763 = 1535645) B1535645
theorem B434047 : Blo 385764 434047 := bstep (se 1 (by rfl) ⟨325535, by rfl⟩ : syracuseStep 434047 = 651071) B651071
theorem B827567 : Blo 385764 827567 := bstep (se 1 (by rfl) ⟨620675, by rfl⟩ : syracuseStep 827567 = 1241351) B1241351
theorem B3547525 : Blo 385764 3547525 := bstep (se 4 (by rfl) ⟨332580, by rfl⟩ : syracuseStep 3547525 = 665161) B665161
theorem B2368111 : Blo 385764 2368111 := bstep (se 1 (by rfl) ⟨1776083, by rfl⟩ : syracuseStep 2368111 = 3552167) B3552167
theorem B2205089 : Blo 385764 2205089 := bstep (se 2 (by rfl) ⟨826908, by rfl⟩ : syracuseStep 2205089 = 1653817) B1653817
theorem B35661221 : Blo 385764 35661221 := bstep (se 4 (by rfl) ⟨3343239, by rfl⟩ : syracuseStep 35661221 = 6686479) B6686479
theorem B149038841 : Blo 385764 149038841 := bstep (se 2 (by rfl) ⟨55889565, by rfl⟩ : syracuseStep 149038841 = 111779131) B111779131
theorem B4958171 : Blo 385764 4958171 := bstep (se 1 (by rfl) ⟨3718628, by rfl⟩ : syracuseStep 4958171 = 7437257) B7437257
theorem B796895 : Blo 385764 796895 := bstep (se 1 (by rfl) ⟨597671, by rfl⟩ : syracuseStep 796895 = 1195343) B1195343
theorem B436639 : Blo 385764 436639 := bstep (se 1 (by rfl) ⟨327479, by rfl⟩ : syracuseStep 436639 = 654959) B654959
theorem B15871265 : Blo 385764 15871265 := bstep (se 2 (by rfl) ⟨5951724, by rfl⟩ : syracuseStep 15871265 = 11903449) B11903449
theorem B437791 : Blo 385764 437791 := bstep (se 1 (by rfl) ⟨328343, by rfl⟩ : syracuseStep 437791 = 656687) B656687
theorem B2240399 : Blo 385764 2240399 := bstep (se 1 (by rfl) ⟨1680299, by rfl⟩ : syracuseStep 2240399 = 3360599) B3360599
theorem B634943 : Blo 385764 634943 := bstep (se 1 (by rfl) ⟨476207, by rfl⟩ : syracuseStep 634943 = 952415) B952415
theorem B1323155 : Blo 385764 1323155 := bstep (se 1 (by rfl) ⟨992366, by rfl⟩ : syracuseStep 1323155 = 1984733) B1984733
theorem B4731301 : Blo 385764 4731301 := bstep (se 4 (by rfl) ⟨443559, by rfl⟩ : syracuseStep 4731301 = 887119) B887119
theorem B4174375 : Blo 385764 4174375 := bstep (se 1 (by rfl) ⟨3130781, by rfl⟩ : syracuseStep 4174375 = 6261563) B6261563
theorem B2208505 : Blo 385764 2208505 := bstep (se 2 (by rfl) ⟨828189, by rfl⟩ : syracuseStep 2208505 = 1656379) B1656379
theorem B734035 : Blo 385764 734035 := bstep (se 1 (by rfl) ⟨550526, by rfl⟩ : syracuseStep 734035 = 1101053) B1101053
theorem B73905209 : Blo 385764 73905209 := bstep (se 2 (by rfl) ⟨27714453, by rfl⟩ : syracuseStep 73905209 = 55428907) B55428907
theorem B734521 : Blo 385764 734521 := bstep (se 2 (by rfl) ⟨275445, by rfl⟩ : syracuseStep 734521 = 550891) B550891
theorem B472603 : Blo 385764 472603 := bstep (se 1 (by rfl) ⟨354452, by rfl⟩ : syracuseStep 472603 = 708905) B708905
theorem B4699781 : Blo 385764 4699781 := bstep (se 4 (by rfl) ⟨440604, by rfl⟩ : syracuseStep 4699781 = 881209) B881209
theorem B2505431 : Blo 385764 2505431 := bstep (se 1 (by rfl) ⟨1879073, by rfl⟩ : syracuseStep 2505431 = 3758147) B3758147
theorem B2931551 : Blo 385764 2931551 := bstep (se 1 (by rfl) ⟨2198663, by rfl⟩ : syracuseStep 2931551 = 4397327) B4397327
theorem B736123 : Blo 385764 736123 := bstep (se 1 (by rfl) ⟨552092, by rfl⟩ : syracuseStep 736123 = 1104185) B1104185
theorem B7945147 : Blo 385764 7945147 := bstep (se 1 (by rfl) ⟨5958860, by rfl⟩ : syracuseStep 7945147 = 11917721) B11917721
theorem B5061689 : Blo 385764 5061689 := bstep (se 2 (by rfl) ⟨1898133, by rfl⟩ : syracuseStep 5061689 = 3796267) B3796267
theorem B1686743 : Blo 385764 1686743 := bstep (se 1 (by rfl) ⟨1265057, by rfl⟩ : syracuseStep 1686743 = 2530115) B2530115
theorem B4439609 : Blo 385764 4439609 := bstep (se 2 (by rfl) ⟨1664853, by rfl⟩ : syracuseStep 4439609 = 3329707) B3329707
theorem B867995 : Blo 385764 867995 := bstep (se 1 (by rfl) ⟨650996, by rfl⟩ : syracuseStep 867995 = 1301993) B1301993
theorem B868193 : Blo 385764 868193 := bstep (se 2 (by rfl) ⟨325572, by rfl⟩ : syracuseStep 868193 = 651145) B651145
theorem B1654775 : Blo 385764 1654775 := bstep (se 1 (by rfl) ⟨1241081, by rfl⟩ : syracuseStep 1654775 = 2482163) B2482163
theorem B3620999 : Blo 385764 3620999 := bstep (se 1 (by rfl) ⟨2715749, by rfl⟩ : syracuseStep 3620999 = 5431499) B5431499
theorem B34030199 : Blo 385764 34030199 := bstep (se 1 (by rfl) ⟨25522649, by rfl⟩ : syracuseStep 34030199 = 51045299) B51045299
theorem B1098593 : Blo 385764 1098593 := bstep (se 2 (by rfl) ⟨411972, by rfl⟩ : syracuseStep 1098593 = 823945) B823945
theorem B869543 : Blo 385764 869543 := bstep (se 1 (by rfl) ⟨652157, by rfl⟩ : syracuseStep 869543 = 1304315) B1304315
theorem B869651 : Blo 385764 869651 := bstep (se 1 (by rfl) ⟨652238, by rfl⟩ : syracuseStep 869651 = 1304477) B1304477
theorem B3524147 : Blo 385764 3524147 := bstep (se 1 (by rfl) ⟨2643110, by rfl⟩ : syracuseStep 3524147 = 5286221) B5286221
theorem B2934467 : Blo 385764 2934467 := bstep (se 1 (by rfl) ⟨2200850, by rfl⟩ : syracuseStep 2934467 = 4401701) B4401701
theorem B870281 : Blo 385764 870281 := bstep (se 2 (by rfl) ⟨326355, by rfl⟩ : syracuseStep 870281 = 652711) B652711
theorem B71813735 : Blo 385764 71813735 := bstep (se 1 (by rfl) ⟨53860301, by rfl⟩ : syracuseStep 71813735 = 107720603) B107720603
theorem B2214863 : Blo 385764 2214863 := bstep (se 1 (by rfl) ⟨1661147, by rfl⟩ : syracuseStep 2214863 = 3322295) B3322295
theorem B1133843 : Blo 385764 1133843 := bstep (se 1 (by rfl) ⟨850382, by rfl⟩ : syracuseStep 1133843 = 1700765) B1700765
theorem B871955 : Blo 385764 871955 := bstep (se 1 (by rfl) ⟨653966, by rfl⟩ : syracuseStep 871955 = 1307933) B1307933
theorem B873017 : Blo 385764 873017 := bstep (se 2 (by rfl) ⟨327381, by rfl⟩ : syracuseStep 873017 = 654763) B654763
theorem B1921619 : Blo 385764 1921619 := bstep (se 1 (by rfl) ⟨1441214, by rfl⟩ : syracuseStep 1921619 = 2882429) B2882429
theorem B1102567 : Blo 385764 1102567 := bstep (se 1 (by rfl) ⟨826925, by rfl⟩ : syracuseStep 1102567 = 1653851) B1653851
theorem B578783 : Blo 385764 578783 := bstep (se 1 (by rfl) ⟨434087, by rfl⟩ : syracuseStep 578783 = 868175) B868175
theorem B578825 : Blo 385764 578825 := bstep (se 2 (by rfl) ⟨217059, by rfl⟩ : syracuseStep 578825 = 434119) B434119
theorem B873737 : Blo 385764 873737 := bstep (se 2 (by rfl) ⟨327651, by rfl⟩ : syracuseStep 873737 = 655303) B655303
theorem B1103159 : Blo 385764 1103159 := bstep (se 1 (by rfl) ⟨827369, by rfl⟩ : syracuseStep 1103159 = 1654739) B1654739
theorem B19355041 : Blo 385764 19355041 := bstep (se 2 (by rfl) ⟨7258140, by rfl⟩ : syracuseStep 19355041 = 14516281) B14516281
theorem B579263 : Blo 385764 579263 := bstep (se 1 (by rfl) ⟨434447, by rfl⟩ : syracuseStep 579263 = 868895) B868895
theorem B579305 : Blo 385764 579305 := bstep (se 2 (by rfl) ⟨217239, by rfl⟩ : syracuseStep 579305 = 434479) B434479
theorem B579311 : Blo 385764 579311 := bstep (se 1 (by rfl) ⟨434483, by rfl⟩ : syracuseStep 579311 = 868967) B868967
theorem B6609113 : Blo 385764 6609113 := bstep (se 2 (by rfl) ⟨2478417, by rfl⟩ : syracuseStep 6609113 = 4956835) B4956835
theorem B579815 : Blo 385764 579815 := bstep (se 1 (by rfl) ⟨434861, by rfl⟩ : syracuseStep 579815 = 869723) B869723
theorem B874727 : Blo 385764 874727 := bstep (se 1 (by rfl) ⟨656045, by rfl⟩ : syracuseStep 874727 = 1312091) B1312091
theorem B874745 : Blo 385764 874745 := bstep (se 2 (by rfl) ⟨328029, by rfl⟩ : syracuseStep 874745 = 656059) B656059
theorem B579995 : Blo 385764 579995 := bstep (se 1 (by rfl) ⟨434996, by rfl⟩ : syracuseStep 579995 = 869993) B869993
theorem B874907 : Blo 385764 874907 := bstep (se 1 (by rfl) ⟨656180, by rfl⟩ : syracuseStep 874907 = 1312361) B1312361
theorem B875015 : Blo 385764 875015 := bstep (se 1 (by rfl) ⟨656261, by rfl⟩ : syracuseStep 875015 = 1312523) B1312523
theorem B875195 : Blo 385764 875195 := bstep (se 1 (by rfl) ⟨656396, by rfl⟩ : syracuseStep 875195 = 1312793) B1312793
theorem B1104617 : Blo 385764 1104617 := bstep (se 2 (by rfl) ⟨414231, by rfl⟩ : syracuseStep 1104617 = 828463) B828463
theorem B580391 : Blo 385764 580391 := bstep (se 1 (by rfl) ⟨435293, by rfl⟩ : syracuseStep 580391 = 870587) B870587
theorem B875303 : Blo 385764 875303 := bstep (se 1 (by rfl) ⟨656477, by rfl⟩ : syracuseStep 875303 = 1312955) B1312955
theorem B580415 : Blo 385764 580415 := bstep (se 1 (by rfl) ⟨435311, by rfl⟩ : syracuseStep 580415 = 870623) B870623
theorem B580715 : Blo 385764 580715 := bstep (se 1 (by rfl) ⟨435536, by rfl⟩ : syracuseStep 580715 = 871073) B871073
theorem B580859 : Blo 385764 580859 := bstep (se 1 (by rfl) ⟨435644, by rfl⟩ : syracuseStep 580859 = 871289) B871289
theorem B580955 : Blo 385764 580955 := bstep (se 1 (by rfl) ⟨435716, by rfl⟩ : syracuseStep 580955 = 871433) B871433
theorem B580985 : Blo 385764 580985 := bstep (se 2 (by rfl) ⟨217869, by rfl⟩ : syracuseStep 580985 = 435739) B435739
theorem B580991 : Blo 385764 580991 := bstep (se 1 (by rfl) ⟨435743, by rfl⟩ : syracuseStep 580991 = 871487) B871487
theorem B2940299 : Blo 385764 2940299 := bstep (se 1 (by rfl) ⟨2205224, by rfl⟩ : syracuseStep 2940299 = 4410449) B4410449
theorem B876095 : Blo 385764 876095 := bstep (se 1 (by rfl) ⟨657071, by rfl⟩ : syracuseStep 876095 = 1314143) B1314143
theorem B581543 : Blo 385764 581543 := bstep (se 1 (by rfl) ⟨436157, by rfl⟩ : syracuseStep 581543 = 872315) B872315
theorem B1400743 : Blo 385764 1400743 := bstep (se 1 (by rfl) ⟨1050557, by rfl⟩ : syracuseStep 1400743 = 2101115) B2101115
theorem B876455 : Blo 385764 876455 := bstep (se 1 (by rfl) ⟨657341, by rfl⟩ : syracuseStep 876455 = 1314683) B1314683
theorem B1302479 : Blo 385764 1302479 := bstep (se 1 (by rfl) ⟨976859, by rfl⟩ : syracuseStep 1302479 = 1953719) B1953719
theorem B581615 : Blo 385764 581615 := bstep (se 1 (by rfl) ⟨436211, by rfl⟩ : syracuseStep 581615 = 872423) B872423
theorem B581735 : Blo 385764 581735 := bstep (se 1 (by rfl) ⟨436301, by rfl⟩ : syracuseStep 581735 = 872603) B872603
theorem B581867 : Blo 385764 581867 := bstep (se 1 (by rfl) ⟨436400, by rfl⟩ : syracuseStep 581867 = 872801) B872801
theorem B581927 : Blo 385764 581927 := bstep (se 1 (by rfl) ⟨436445, by rfl⟩ : syracuseStep 581927 = 872891) B872891
theorem B1860029 : Blo 385764 1860029 := bstep (se 3 (by rfl) ⟨348755, by rfl⟩ : syracuseStep 1860029 = 697511) B697511
theorem B582377 : Blo 385764 582377 := bstep (se 2 (by rfl) ⟨218391, by rfl⟩ : syracuseStep 582377 = 436783) B436783
theorem B1106713 : Blo 385764 1106713 := bstep (se 2 (by rfl) ⟨415017, by rfl⟩ : syracuseStep 1106713 = 830035) B830035
theorem B35971913 : Blo 385764 35971913 := bstep (se 2 (by rfl) ⟨13489467, by rfl⟩ : syracuseStep 35971913 = 26978935) B26978935
theorem B385951 : Blo 385764 385951 := bstep (se 1 (by rfl) ⟨289463, by rfl⟩ : syracuseStep 385951 = 578927) B578927
theorem B386031 : Blo 385764 386031 := bstep (se 1 (by rfl) ⟨289523, by rfl⟩ : syracuseStep 386031 = 579047) B579047
theorem B386139 : Blo 385764 386139 := bstep (se 1 (by rfl) ⟨289604, by rfl⟩ : syracuseStep 386139 = 579209) B579209
theorem B386151 : Blo 385764 386151 := bstep (se 1 (by rfl) ⟨289613, by rfl⟩ : syracuseStep 386151 = 579227) B579227
theorem B582767 : Blo 385764 582767 := bstep (se 1 (by rfl) ⟨437075, by rfl⟩ : syracuseStep 582767 = 874151) B874151
theorem B386279 : Blo 385764 386279 := bstep (se 1 (by rfl) ⟨289709, by rfl⟩ : syracuseStep 386279 = 579419) B579419
theorem B582887 : Blo 385764 582887 := bstep (se 1 (by rfl) ⟨437165, by rfl⟩ : syracuseStep 582887 = 874331) B874331
theorem B582953 : Blo 385764 582953 := bstep (se 2 (by rfl) ⟨218607, by rfl⟩ : syracuseStep 582953 = 437215) B437215
theorem B1303991 : Blo 385764 1303991 := bstep (se 1 (by rfl) ⟨977993, by rfl⟩ : syracuseStep 1303991 = 1955987) B1955987
theorem B386535 : Blo 385764 386535 := bstep (se 1 (by rfl) ⟨289901, by rfl⟩ : syracuseStep 386535 = 579803) B579803
theorem B583223 : Blo 385764 583223 := bstep (se 1 (by rfl) ⟨437417, by rfl⟩ : syracuseStep 583223 = 874835) B874835
theorem B386715 : Blo 385764 386715 := bstep (se 1 (by rfl) ⟨290036, by rfl⟩ : syracuseStep 386715 = 580073) B580073
theorem B583547 : Blo 385764 583547 := bstep (se 1 (by rfl) ⟨437660, by rfl⟩ : syracuseStep 583547 = 875321) B875321
theorem B976799 : Blo 385764 976799 := bstep (se 1 (by rfl) ⟨732599, by rfl⟩ : syracuseStep 976799 = 1465199) B1465199
theorem B386975 : Blo 385764 386975 := bstep (se 1 (by rfl) ⟨290231, by rfl⟩ : syracuseStep 386975 = 580463) B580463
theorem B583583 : Blo 385764 583583 := bstep (se 1 (by rfl) ⟨437687, by rfl⟩ : syracuseStep 583583 = 875375) B875375
theorem B1468327 : Blo 385764 1468327 := bstep (se 1 (by rfl) ⟨1101245, by rfl⟩ : syracuseStep 1468327 = 2202491) B2202491
theorem B386983 : Blo 385764 386983 := bstep (se 1 (by rfl) ⟨290237, by rfl⟩ : syracuseStep 386983 = 580475) B580475
theorem B1959875 : Blo 385764 1959875 := bstep (se 1 (by rfl) ⟨1469906, by rfl⟩ : syracuseStep 1959875 = 2939813) B2939813
theorem B1304531 : Blo 385764 1304531 := bstep (se 1 (by rfl) ⟨978398, by rfl⟩ : syracuseStep 1304531 = 1956797) B1956797
theorem B583817 : Blo 385764 583817 := bstep (se 2 (by rfl) ⟨218931, by rfl⟩ : syracuseStep 583817 = 437863) B437863
theorem B583967 : Blo 385764 583967 := bstep (se 1 (by rfl) ⟨437975, by rfl⟩ : syracuseStep 583967 = 875951) B875951
theorem B584015 : Blo 385764 584015 := bstep (se 1 (by rfl) ⟨438011, by rfl⟩ : syracuseStep 584015 = 876023) B876023
theorem B584105 : Blo 385764 584105 := bstep (se 2 (by rfl) ⟨219039, by rfl⟩ : syracuseStep 584105 = 438079) B438079
theorem B387559 : Blo 385764 387559 := bstep (se 1 (by rfl) ⟨290669, by rfl⟩ : syracuseStep 387559 = 581339) B581339
theorem B387739 : Blo 385764 387739 := bstep (se 1 (by rfl) ⟨290804, by rfl⟩ : syracuseStep 387739 = 581609) B581609
theorem B584489 : Blo 385764 584489 := bstep (se 2 (by rfl) ⟨219183, by rfl⟩ : syracuseStep 584489 = 438367) B438367
theorem B1305449 : Blo 385764 1305449 := bstep (se 2 (by rfl) ⟨489543, by rfl⟩ : syracuseStep 1305449 = 979087) B979087
theorem B1567855 : Blo 385764 1567855 := bstep (se 1 (by rfl) ⟨1175891, by rfl⟩ : syracuseStep 1567855 = 2351783) B2351783
theorem B388207 : Blo 385764 388207 := bstep (se 1 (by rfl) ⟨291155, by rfl⟩ : syracuseStep 388207 = 582311) B582311
theorem B388287 : Blo 385764 388287 := bstep (se 1 (by rfl) ⟨291215, by rfl⟩ : syracuseStep 388287 = 582431) B582431
theorem B388303 : Blo 385764 388303 := bstep (se 1 (by rfl) ⟨291227, by rfl⟩ : syracuseStep 388303 = 582455) B582455
theorem B13495567 : Blo 385764 13495567 := bstep (se 1 (by rfl) ⟨10121675, by rfl⟩ : syracuseStep 13495567 = 20243351) B20243351
theorem B552263 : Blo 385764 552263 := bstep (se 1 (by rfl) ⟨414197, by rfl⟩ : syracuseStep 552263 = 828395) B828395
theorem B388423 : Blo 385764 388423 := bstep (se 1 (by rfl) ⟨291317, by rfl⟩ : syracuseStep 388423 = 582635) B582635
theorem B1470271 : Blo 385764 1470271 := bstep (se 1 (by rfl) ⟨1102703, by rfl⟩ : syracuseStep 1470271 = 2205407) B2205407
theorem B1109857 : Blo 385764 1109857 := bstep (se 2 (by rfl) ⟨416196, by rfl⟩ : syracuseStep 1109857 = 832393) B832393
theorem B2977681 : Blo 385764 2977681 := bstep (se 2 (by rfl) ⟨1116630, by rfl⟩ : syracuseStep 2977681 = 2233261) B2233261
theorem B618491 : Blo 385764 618491 := bstep (se 1 (by rfl) ⟨463868, by rfl⟩ : syracuseStep 618491 = 927737) B927737
theorem B389151 : Blo 385764 389151 := bstep (se 1 (by rfl) ⟨291863, by rfl⟩ : syracuseStep 389151 = 583727) B583727
theorem B1863719 : Blo 385764 1863719 := bstep (se 1 (by rfl) ⟨1397789, by rfl⟩ : syracuseStep 1863719 = 2795579) B2795579
theorem B553015 : Blo 385764 553015 := bstep (se 1 (by rfl) ⟨414761, by rfl⟩ : syracuseStep 553015 = 829523) B829523
theorem B1241183 : Blo 385764 1241183 := bstep (se 1 (by rfl) ⟨930887, by rfl⟩ : syracuseStep 1241183 = 1861775) B1861775
theorem B389327 : Blo 385764 389327 := bstep (se 1 (by rfl) ⟨291995, by rfl⟩ : syracuseStep 389327 = 583991) B583991
theorem B389447 : Blo 385764 389447 := bstep (se 1 (by rfl) ⟨292085, by rfl⟩ : syracuseStep 389447 = 584171) B584171
theorem B35680769 : Blo 385764 35680769 := bstep (se 2 (by rfl) ⟨13380288, by rfl⟩ : syracuseStep 35680769 = 26760577) B26760577
theorem B18641441 : Blo 385764 18641441 := bstep (se 2 (by rfl) ⟨6990540, by rfl⟩ : syracuseStep 18641441 = 13981081) B13981081
theorem B8417945 : Blo 385764 8417945 := bstep (se 2 (by rfl) ⟨3156729, by rfl⟩ : syracuseStep 8417945 = 6313459) B6313459
theorem B1471547 : Blo 385764 1471547 := bstep (se 1 (by rfl) ⟨1103660, by rfl⟩ : syracuseStep 1471547 = 2207321) B2207321
theorem B2487439 : Blo 385764 2487439 := bstep (se 1 (by rfl) ⟨1865579, by rfl⟩ : syracuseStep 2487439 = 3731159) B3731159
theorem B184251743 : Blo 385764 184251743 := bstep (se 1 (by rfl) ⟨138188807, by rfl⟩ : syracuseStep 184251743 = 276377615) B276377615
theorem B652873 : Blo 385764 652873 := bstep (se 2 (by rfl) ⟨244827, by rfl⟩ : syracuseStep 652873 = 489655) B489655
theorem B1964087 : Blo 385764 1964087 := bstep (se 1 (by rfl) ⟨1473065, by rfl⟩ : syracuseStep 1964087 = 2946131) B2946131
theorem B3537017 : Blo 385764 3537017 := bstep (se 2 (by rfl) ⟨1326381, by rfl⟩ : syracuseStep 3537017 = 2652763) B2652763
theorem B2488441 : Blo 385764 2488441 := bstep (se 2 (by rfl) ⟨933165, by rfl⟩ : syracuseStep 2488441 = 1866331) B1866331
theorem B1046839 : Blo 385764 1046839 := bstep (se 1 (by rfl) ⟨785129, by rfl⟩ : syracuseStep 1046839 = 1570259) B1570259
theorem B981305 : Blo 385764 981305 := bstep (se 2 (by rfl) ⟨367989, by rfl⟩ : syracuseStep 981305 = 735979) B735979
theorem B6289721 : Blo 385764 6289721 := bstep (se 2 (by rfl) ⟨2358645, by rfl⟩ : syracuseStep 6289721 = 4717291) B4717291
theorem B1964411 : Blo 385764 1964411 := bstep (se 1 (by rfl) ⟨1473308, by rfl⟩ : syracuseStep 1964411 = 2946617) B2946617
theorem B1866503 : Blo 385764 1866503 := bstep (se 1 (by rfl) ⟨1399877, by rfl⟩ : syracuseStep 1866503 = 2799755) B2799755
theorem B1244119 : Blo 385764 1244119 := bstep (se 1 (by rfl) ⟨933089, by rfl⟩ : syracuseStep 1244119 = 1866179) B1866179
theorem B981983 : Blo 385764 981983 := bstep (se 1 (by rfl) ⟨736487, by rfl⟩ : syracuseStep 981983 = 1472975) B1472975
theorem B1473947 : Blo 385764 1473947 := bstep (se 1 (by rfl) ⟨1105460, by rfl⟩ : syracuseStep 1473947 = 2210921) B2210921
theorem B1965545 : Blo 385764 1965545 := bstep (se 2 (by rfl) ⟨737079, by rfl⟩ : syracuseStep 1965545 = 1474159) B1474159
theorem B1048351 : Blo 385764 1048351 := bstep (se 1 (by rfl) ⟨786263, by rfl⟩ : syracuseStep 1048351 = 1572527) B1572527
theorem B622399 : Blo 385764 622399 := bstep (se 1 (by rfl) ⟨466799, by rfl⟩ : syracuseStep 622399 = 933599) B933599
theorem B655195 : Blo 385764 655195 := bstep (se 1 (by rfl) ⟨491396, by rfl⟩ : syracuseStep 655195 = 982793) B982793
theorem B4423571 : Blo 385764 4423571 := bstep (se 1 (by rfl) ⟨3317678, by rfl⟩ : syracuseStep 4423571 = 6635357) B6635357
theorem B7929971 : Blo 385764 7929971 := bstep (se 1 (by rfl) ⟨5947478, by rfl⟩ : syracuseStep 7929971 = 11894957) B11894957
theorem B3309821 : Blo 385764 3309821 := bstep (se 3 (by rfl) ⟨620591, by rfl⟩ : syracuseStep 3309821 = 1241183) B1241183
theorem B786971 : Blo 385764 786971 := bstep (se 1 (by rfl) ⟨590228, by rfl⟩ : syracuseStep 786971 = 1180457) B1180457
theorem B656039 : Blo 385764 656039 := bstep (se 1 (by rfl) ⟨492029, by rfl⟩ : syracuseStep 656039 = 984059) B984059
theorem B1475617 : Blo 385764 1475617 := bstep (se 2 (by rfl) ⟨553356, by rfl⟩ : syracuseStep 1475617 = 1106713) B1106713
theorem B1312199 : Blo 385764 1312199 := bstep (se 1 (by rfl) ⟨984149, by rfl⟩ : syracuseStep 1312199 = 1968299) B1968299
theorem B47875823 : Blo 385764 47875823 := bstep (se 1 (by rfl) ⟨35906867, by rfl⟩ : syracuseStep 47875823 = 71813735) B71813735
theorem B1476575 : Blo 385764 1476575 := bstep (se 1 (by rfl) ⟨1107431, by rfl⟩ : syracuseStep 1476575 = 2214863) B2214863
theorem B25233605 : Blo 385764 25233605 := bstep (se 4 (by rfl) ⟨2365650, by rfl⟩ : syracuseStep 25233605 = 4731301) B4731301
theorem B1313441 : Blo 385764 1313441 := bstep (se 2 (by rfl) ⟨492540, by rfl⟩ : syracuseStep 1313441 = 985081) B985081
theorem B1281079 : Blo 385764 1281079 := bstep (se 1 (by rfl) ⟨960809, by rfl⟩ : syracuseStep 1281079 = 1921619) B1921619
theorem B986195 : Blo 385764 986195 := bstep (se 1 (by rfl) ⟨739646, by rfl⟩ : syracuseStep 986195 = 1479293) B1479293
theorem B1315115 : Blo 385764 1315115 := bstep (se 1 (by rfl) ⟨986336, by rfl⟩ : syracuseStep 1315115 = 1972673) B1972673
theorem B17994089 : Blo 385764 17994089 := bstep (se 2 (by rfl) ⟨6747783, by rfl⟩ : syracuseStep 17994089 = 13495567) B13495567
theorem B42374117 : Blo 385764 42374117 := bstep (se 4 (by rfl) ⟨3972573, by rfl⟩ : syracuseStep 42374117 = 7945147) B7945147
theorem B1479809 : Blo 385764 1479809 := bstep (se 2 (by rfl) ⟨554928, by rfl⟩ : syracuseStep 1479809 = 1109857) B1109857
theorem B3970241 : Blo 385764 3970241 := bstep (se 2 (by rfl) ⟨1488840, by rfl⟩ : syracuseStep 3970241 = 2977681) B2977681
theorem B8361893 : Blo 385764 8361893 := bstep (se 4 (by rfl) ⟨783927, by rfl⟩ : syracuseStep 8361893 = 1567855) B1567855
theorem B99359227 : Blo 385764 99359227 := bstep (se 1 (by rfl) ⟨74519420, by rfl⟩ : syracuseStep 99359227 = 149038841) B149038841
theorem B531263 : Blo 385764 531263 := bstep (se 1 (by rfl) ⟨398447, by rfl⟩ : syracuseStep 531263 = 796895) B796895
theorem B3316585 : Blo 385764 3316585 := bstep (se 2 (by rfl) ⟨1243719, by rfl⟩ : syracuseStep 3316585 = 2487439) B2487439
theorem B630137 : Blo 385764 630137 := bstep (se 2 (by rfl) ⟨236301, by rfl⟩ : syracuseStep 630137 = 472603) B472603
theorem B3317921 : Blo 385764 3317921 := bstep (se 2 (by rfl) ⟨1244220, by rfl⟩ : syracuseStep 3317921 = 2488441) B2488441
theorem B12427627 : Blo 385764 12427627 := bstep (se 1 (by rfl) ⟨9320720, by rfl⟩ : syracuseStep 12427627 = 18641441) B18641441
theorem B5611963 : Blo 385764 5611963 := bstep (se 1 (by rfl) ⟨4208972, by rfl⟩ : syracuseStep 5611963 = 8417945) B8417945
theorem B3023581 : Blo 385764 3023581 := bstep (se 3 (by rfl) ⟨566921, by rfl⟩ : syracuseStep 3023581 = 1133843) B1133843
theorem B1124495 : Blo 385764 1124495 := bstep (se 1 (by rfl) ⟨843371, by rfl⟩ : syracuseStep 1124495 = 1686743) B1686743
theorem B2959739 : Blo 385764 2959739 := bstep (se 1 (by rfl) ⟨2219804, by rfl⟩ : syracuseStep 2959739 = 4439609) B4439609
theorem B829865 : Blo 385764 829865 := bstep (se 2 (by rfl) ⟨311199, by rfl⟩ : syracuseStep 829865 = 622399) B622399
theorem B22686799 : Blo 385764 22686799 := bstep (se 1 (by rfl) ⟨17015099, by rfl⟩ : syracuseStep 22686799 = 34030199) B34030199
theorem B4730033 : Blo 385764 4730033 := bstep (se 2 (by rfl) ⟨1773762, by rfl⟩ : syracuseStep 4730033 = 3547525) B3547525
theorem B732395 : Blo 385764 732395 := bstep (se 1 (by rfl) ⟨549296, by rfl⟩ : syracuseStep 732395 = 1098593) B1098593
theorem B437575 : Blo 385764 437575 := bstep (se 1 (by rfl) ⟨328181, by rfl⟩ : syracuseStep 437575 = 656363) B656363
theorem B3157481 : Blo 385764 3157481 := bstep (se 2 (by rfl) ⟨1184055, by rfl⟩ : syracuseStep 3157481 = 2368111) B2368111
theorem B700169 : Blo 385764 700169 := bstep (se 2 (by rfl) ⟨262563, by rfl⟩ : syracuseStep 700169 = 525127) B525127
theorem B438439 : Blo 385764 438439 := bstep (se 1 (by rfl) ⟨328829, by rfl⟩ : syracuseStep 438439 = 657659) B657659
theorem B2209031 : Blo 385764 2209031 := bstep (se 1 (by rfl) ⟨1656773, by rfl⟩ : syracuseStep 2209031 = 3313547) B3313547
theorem B5289761 : Blo 385764 5289761 := bstep (se 2 (by rfl) ⟨1983660, by rfl⟩ : syracuseStep 5289761 = 3967321) B3967321
theorem B4406075 : Blo 385764 4406075 := bstep (se 1 (by rfl) ⟨3304556, by rfl⟩ : syracuseStep 4406075 = 6609113) B6609113
theorem B868319 : Blo 385764 868319 := bstep (se 1 (by rfl) ⟨651239, by rfl⟩ : syracuseStep 868319 = 1302479) B1302479
theorem B737353 : Blo 385764 737353 := bstep (se 2 (by rfl) ⟨276507, by rfl⟩ : syracuseStep 737353 = 553015) B553015
theorem B12600197 : Blo 385764 12600197 := bstep (se 4 (by rfl) ⟨1181268, by rfl⟩ : syracuseStep 12600197 = 2362537) B2362537
theorem B23774147 : Blo 385764 23774147 := bstep (se 1 (by rfl) ⟨17830610, by rfl⟩ : syracuseStep 23774147 = 35661221) B35661221
theorem B869327 : Blo 385764 869327 := bstep (se 1 (by rfl) ⟨651995, by rfl⟩ : syracuseStep 869327 = 1303991) B1303991
theorem B869687 : Blo 385764 869687 := bstep (se 1 (by rfl) ⟨652265, by rfl⟩ : syracuseStep 869687 = 1304531) B1304531
theorem B1099241 : Blo 385764 1099241 := bstep (se 2 (by rfl) ⟨412215, by rfl⟩ : syracuseStep 1099241 = 824431) B824431
theorem B25806721 : Blo 385764 25806721 := bstep (se 2 (by rfl) ⟨9677520, by rfl⟩ : syracuseStep 25806721 = 19355041) B19355041
theorem B870299 : Blo 385764 870299 := bstep (se 1 (by rfl) ⟨652724, by rfl⟩ : syracuseStep 870299 = 1305449) B1305449
theorem B870497 : Blo 385764 870497 := bstep (se 2 (by rfl) ⟨326436, by rfl⟩ : syracuseStep 870497 = 652873) B652873
theorem B1493599 : Blo 385764 1493599 := bstep (se 1 (by rfl) ⟨1120199, by rfl⟩ : syracuseStep 1493599 = 2240399) B2240399
theorem B412327 : Blo 385764 412327 := bstep (se 1 (by rfl) ⟨309245, by rfl⟩ : syracuseStep 412327 = 618491) B618491
theorem B1395785 : Blo 385764 1395785 := bstep (se 2 (by rfl) ⟨523419, by rfl⟩ : syracuseStep 1395785 = 1046839) B1046839
theorem B49270139 : Blo 385764 49270139 := bstep (se 1 (by rfl) ⟨36952604, by rfl⟩ : syracuseStep 49270139 = 73905209) B73905209
theorem B122834495 : Blo 385764 122834495 := bstep (se 1 (by rfl) ⟨92125871, by rfl⟩ : syracuseStep 122834495 = 184251743) B184251743
theorem B3133187 : Blo 385764 3133187 := bstep (se 1 (by rfl) ⟨2349890, by rfl⟩ : syracuseStep 3133187 = 4699781) B4699781
theorem B2805637 : Blo 385764 2805637 := bstep (se 4 (by rfl) ⟨263028, by rfl⟩ : syracuseStep 2805637 = 526057) B526057
theorem B1658825 : Blo 385764 1658825 := bstep (se 2 (by rfl) ⟨622059, by rfl⟩ : syracuseStep 1658825 = 1244119) B1244119
theorem B1954367 : Blo 385764 1954367 := bstep (se 1 (by rfl) ⟨1465775, by rfl⟩ : syracuseStep 1954367 = 2931551) B2931551
theorem B1365017 : Blo 385764 1365017 := bstep (se 2 (by rfl) ⟨511881, by rfl⟩ : syracuseStep 1365017 = 1023763) B1023763
theorem B1397801 : Blo 385764 1397801 := bstep (se 2 (by rfl) ⟨524175, by rfl⟩ : syracuseStep 1397801 = 1048351) B1048351
theorem B578663 : Blo 385764 578663 := bstep (se 1 (by rfl) ⟨433997, by rfl⟩ : syracuseStep 578663 = 867995) B867995
theorem B873593 : Blo 385764 873593 := bstep (se 2 (by rfl) ⟨327597, by rfl⟩ : syracuseStep 873593 = 655195) B655195
theorem B578729 : Blo 385764 578729 := bstep (se 2 (by rfl) ⟨217023, by rfl⟩ : syracuseStep 578729 = 434047) B434047
theorem B578795 : Blo 385764 578795 := bstep (se 1 (by rfl) ⟨434096, by rfl⟩ : syracuseStep 578795 = 868193) B868193
theorem B1103183 : Blo 385764 1103183 := bstep (se 1 (by rfl) ⟨827387, by rfl⟩ : syracuseStep 1103183 = 1654775) B1654775
theorem B2413999 : Blo 385764 2413999 := bstep (se 1 (by rfl) ⟨1810499, by rfl⟩ : syracuseStep 2413999 = 3620999) B3620999
theorem B874367 : Blo 385764 874367 := bstep (se 1 (by rfl) ⟨655775, by rfl⟩ : syracuseStep 874367 = 1311551) B1311551
theorem B1660925 : Blo 385764 1660925 := bstep (se 3 (by rfl) ⟨311423, by rfl⟩ : syracuseStep 1660925 = 622847) B622847
theorem B579695 : Blo 385764 579695 := bstep (se 1 (by rfl) ⟨434771, by rfl⟩ : syracuseStep 579695 = 869543) B869543
theorem B579767 : Blo 385764 579767 := bstep (se 1 (by rfl) ⟨434825, by rfl⟩ : syracuseStep 579767 = 869651) B869651
theorem B2349431 : Blo 385764 2349431 := bstep (se 1 (by rfl) ⟨1762073, by rfl⟩ : syracuseStep 2349431 = 3524147) B3524147
theorem B1956311 : Blo 385764 1956311 := bstep (se 1 (by rfl) ⟨1467233, by rfl⟩ : syracuseStep 1956311 = 2934467) B2934467
theorem B580187 : Blo 385764 580187 := bstep (se 1 (by rfl) ⟨435140, by rfl⟩ : syracuseStep 580187 = 870281) B870281
theorem B183196853 : Blo 385764 183196853 := bstep (se 5 (by rfl) ⟨8587352, by rfl⟩ : syracuseStep 183196853 = 17174705) B17174705
theorem B875897 : Blo 385764 875897 := bstep (se 2 (by rfl) ⟨328461, by rfl⟩ : syracuseStep 875897 = 656923) B656923
theorem B581303 : Blo 385764 581303 := bstep (se 1 (by rfl) ⟨435977, by rfl⟩ : syracuseStep 581303 = 871955) B871955
theorem B1957769 : Blo 385764 1957769 := bstep (se 2 (by rfl) ⟨734163, by rfl⟩ : syracuseStep 1957769 = 1468327) B1468327
theorem B876599 : Blo 385764 876599 := bstep (se 1 (by rfl) ⟨657449, by rfl⟩ : syracuseStep 876599 = 1314899) B1314899
theorem B876671 : Blo 385764 876671 := bstep (se 1 (by rfl) ⟨657503, by rfl⟩ : syracuseStep 876671 = 1315007) B1315007
theorem B582011 : Blo 385764 582011 := bstep (se 1 (by rfl) ⟨436508, by rfl⟩ : syracuseStep 582011 = 873017) B873017
theorem B582185 : Blo 385764 582185 := bstep (se 2 (by rfl) ⟨218319, by rfl⟩ : syracuseStep 582185 = 436639) B436639
theorem B1467143 : Blo 385764 1467143 := bstep (se 1 (by rfl) ⟨1100357, by rfl⟩ : syracuseStep 1467143 = 2200715) B2200715
theorem B2941757 : Blo 385764 2941757 := bstep (se 3 (by rfl) ⟨551579, by rfl⟩ : syracuseStep 2941757 = 1103159) B1103159
theorem B385855 : Blo 385764 385855 := bstep (se 1 (by rfl) ⟨289391, by rfl⟩ : syracuseStep 385855 = 578783) B578783
theorem B385883 : Blo 385764 385883 := bstep (se 1 (by rfl) ⟨289412, by rfl⟩ : syracuseStep 385883 = 578825) B578825
theorem B582491 : Blo 385764 582491 := bstep (se 1 (by rfl) ⟨436868, by rfl⟩ : syracuseStep 582491 = 873737) B873737
theorem B386175 : Blo 385764 386175 := bstep (se 1 (by rfl) ⟨289631, by rfl⟩ : syracuseStep 386175 = 579263) B579263
theorem B386203 : Blo 385764 386203 := bstep (se 1 (by rfl) ⟨289652, by rfl⟩ : syracuseStep 386203 = 579305) B579305
theorem B386207 : Blo 385764 386207 := bstep (se 1 (by rfl) ⟨289655, by rfl⟩ : syracuseStep 386207 = 579311) B579311
theorem B386543 : Blo 385764 386543 := bstep (se 1 (by rfl) ⟨289907, by rfl⟩ : syracuseStep 386543 = 579815) B579815
theorem B583151 : Blo 385764 583151 := bstep (se 1 (by rfl) ⟨437363, by rfl⟩ : syracuseStep 583151 = 874727) B874727
theorem B583163 : Blo 385764 583163 := bstep (se 1 (by rfl) ⟨437372, by rfl⟩ : syracuseStep 583163 = 874745) B874745
theorem B386663 : Blo 385764 386663 := bstep (se 1 (by rfl) ⟨289997, by rfl⟩ : syracuseStep 386663 = 579995) B579995
theorem B583271 : Blo 385764 583271 := bstep (se 1 (by rfl) ⟨437453, by rfl⟩ : syracuseStep 583271 = 874907) B874907
theorem B583343 : Blo 385764 583343 := bstep (se 1 (by rfl) ⟨437507, by rfl⟩ : syracuseStep 583343 = 875015) B875015
theorem B583463 : Blo 385764 583463 := bstep (se 1 (by rfl) ⟨437597, by rfl⟩ : syracuseStep 583463 = 875195) B875195
theorem B386927 : Blo 385764 386927 := bstep (se 1 (by rfl) ⟨290195, by rfl⟩ : syracuseStep 386927 = 580391) B580391
theorem B583535 : Blo 385764 583535 := bstep (se 1 (by rfl) ⟨437651, by rfl⟩ : syracuseStep 583535 = 875303) B875303
theorem B386943 : Blo 385764 386943 := bstep (se 1 (by rfl) ⟨290207, by rfl⟩ : syracuseStep 386943 = 580415) B580415
theorem B2713499 : Blo 385764 2713499 := bstep (se 1 (by rfl) ⟨2035124, by rfl⟩ : syracuseStep 2713499 = 4070249) B4070249
theorem B583721 : Blo 385764 583721 := bstep (se 2 (by rfl) ⟨218895, by rfl⟩ : syracuseStep 583721 = 437791) B437791
theorem B387143 : Blo 385764 387143 := bstep (se 1 (by rfl) ⟨290357, by rfl⟩ : syracuseStep 387143 = 580715) B580715
theorem B387239 : Blo 385764 387239 := bstep (se 1 (by rfl) ⟨290429, by rfl⟩ : syracuseStep 387239 = 580859) B580859
theorem B387303 : Blo 385764 387303 := bstep (se 1 (by rfl) ⟨290477, by rfl⟩ : syracuseStep 387303 = 580955) B580955
theorem B387323 : Blo 385764 387323 := bstep (se 1 (by rfl) ⟨290492, by rfl⟩ : syracuseStep 387323 = 580985) B580985
theorem B387327 : Blo 385764 387327 := bstep (se 1 (by rfl) ⟨290495, by rfl⟩ : syracuseStep 387327 = 580991) B580991
theorem B1960199 : Blo 385764 1960199 := bstep (se 1 (by rfl) ⟨1470149, by rfl⟩ : syracuseStep 1960199 = 2940299) B2940299
theorem B584063 : Blo 385764 584063 := bstep (se 1 (by rfl) ⟨438047, by rfl⟩ : syracuseStep 584063 = 876095) B876095
theorem B1960361 : Blo 385764 1960361 := bstep (se 2 (by rfl) ⟨735135, by rfl⟩ : syracuseStep 1960361 = 1470271) B1470271
theorem B387695 : Blo 385764 387695 := bstep (se 1 (by rfl) ⟨290771, by rfl⟩ : syracuseStep 387695 = 581543) B581543
theorem B584303 : Blo 385764 584303 := bstep (se 1 (by rfl) ⟨438227, by rfl⟩ : syracuseStep 584303 = 876455) B876455
theorem B1403513 : Blo 385764 1403513 := bstep (se 2 (by rfl) ⟨526317, by rfl⟩ : syracuseStep 1403513 = 1052635) B1052635
theorem B387743 : Blo 385764 387743 := bstep (se 1 (by rfl) ⟨290807, by rfl⟩ : syracuseStep 387743 = 581615) B581615
theorem B387823 : Blo 385764 387823 := bstep (se 1 (by rfl) ⟨290867, by rfl⟩ : syracuseStep 387823 = 581735) B581735
theorem B551711 : Blo 385764 551711 := bstep (se 1 (by rfl) ⟨413783, by rfl⟩ : syracuseStep 551711 = 827567) B827567
theorem B387911 : Blo 385764 387911 := bstep (se 1 (by rfl) ⟨290933, by rfl⟩ : syracuseStep 387911 = 581867) B581867
theorem B387951 : Blo 385764 387951 := bstep (se 1 (by rfl) ⟨290963, by rfl⟩ : syracuseStep 387951 = 581927) B581927
theorem B1240019 : Blo 385764 1240019 := bstep (se 1 (by rfl) ⟨930014, by rfl⟩ : syracuseStep 1240019 = 1860029) B1860029
theorem B388251 : Blo 385764 388251 := bstep (se 1 (by rfl) ⟨291188, by rfl⟩ : syracuseStep 388251 = 582377) B582377
theorem B23981275 : Blo 385764 23981275 := bstep (se 1 (by rfl) ⟨17985956, by rfl⟩ : syracuseStep 23981275 = 35971913) B35971913
theorem B5565833 : Blo 385764 5565833 := bstep (se 2 (by rfl) ⟨2087187, by rfl⟩ : syracuseStep 5565833 = 4174375) B4174375
theorem B388511 : Blo 385764 388511 := bstep (se 1 (by rfl) ⟨291383, by rfl⟩ : syracuseStep 388511 = 582767) B582767
theorem B388591 : Blo 385764 388591 := bstep (se 1 (by rfl) ⟨291443, by rfl⟩ : syracuseStep 388591 = 582887) B582887
theorem B388635 : Blo 385764 388635 := bstep (se 1 (by rfl) ⟨291476, by rfl⟩ : syracuseStep 388635 = 582953) B582953
theorem B1470059 : Blo 385764 1470059 := bstep (se 1 (by rfl) ⟨1102544, by rfl⟩ : syracuseStep 1470059 = 2205089) B2205089
theorem B1470089 : Blo 385764 1470089 := bstep (se 2 (by rfl) ⟨551283, by rfl⟩ : syracuseStep 1470089 = 1102567) B1102567
theorem B2944673 : Blo 385764 2944673 := bstep (se 2 (by rfl) ⟨1104252, by rfl⟩ : syracuseStep 2944673 = 2208505) B2208505
theorem B388815 : Blo 385764 388815 := bstep (se 1 (by rfl) ⟨291611, by rfl⟩ : syracuseStep 388815 = 583223) B583223
theorem B42430169 : Blo 385764 42430169 := bstep (se 2 (by rfl) ⟨15911313, by rfl⟩ : syracuseStep 42430169 = 31822627) B31822627
theorem B21589753 : Blo 385764 21589753 := bstep (se 2 (by rfl) ⟨8096157, by rfl⟩ : syracuseStep 21589753 = 16192315) B16192315
theorem B978713 : Blo 385764 978713 := bstep (se 2 (by rfl) ⟨367017, by rfl⟩ : syracuseStep 978713 = 734035) B734035
theorem B389031 : Blo 385764 389031 := bstep (se 1 (by rfl) ⟨291773, by rfl⟩ : syracuseStep 389031 = 583547) B583547
theorem B651199 : Blo 385764 651199 := bstep (se 1 (by rfl) ⟨488399, by rfl⟩ : syracuseStep 651199 = 976799) B976799
theorem B389055 : Blo 385764 389055 := bstep (se 1 (by rfl) ⟨291791, by rfl⟩ : syracuseStep 389055 = 583583) B583583
theorem B1306583 : Blo 385764 1306583 := bstep (se 1 (by rfl) ⟨979937, by rfl⟩ : syracuseStep 1306583 = 1959875) B1959875
theorem B3305447 : Blo 385764 3305447 := bstep (se 1 (by rfl) ⟨2479085, by rfl⟩ : syracuseStep 3305447 = 4958171) B4958171
theorem B389211 : Blo 385764 389211 := bstep (se 1 (by rfl) ⟨291908, by rfl⟩ : syracuseStep 389211 = 583817) B583817
theorem B389311 : Blo 385764 389311 := bstep (se 1 (by rfl) ⟨291983, by rfl⟩ : syracuseStep 389311 = 583967) B583967
theorem B389343 : Blo 385764 389343 := bstep (se 1 (by rfl) ⟨292007, by rfl⟩ : syracuseStep 389343 = 584015) B584015
theorem B389403 : Blo 385764 389403 := bstep (se 1 (by rfl) ⟨292052, by rfl⟩ : syracuseStep 389403 = 584105) B584105
theorem B979361 : Blo 385764 979361 := bstep (se 2 (by rfl) ⟨367260, by rfl⟩ : syracuseStep 979361 = 734521) B734521
theorem B389659 : Blo 385764 389659 := bstep (se 1 (by rfl) ⟨292244, by rfl⟩ : syracuseStep 389659 = 584489) B584489
theorem B6681149 : Blo 385764 6681149 := bstep (se 3 (by rfl) ⟨1252715, by rfl⟩ : syracuseStep 6681149 = 2505431) B2505431
theorem B2945645 : Blo 385764 2945645 := bstep (se 3 (by rfl) ⟨552308, by rfl⟩ : syracuseStep 2945645 = 1104617) B1104617
theorem B10580843 : Blo 385764 10580843 := bstep (se 1 (by rfl) ⟨7935632, by rfl⟩ : syracuseStep 10580843 = 15871265) B15871265
theorem B1242479 : Blo 385764 1242479 := bstep (se 1 (by rfl) ⟨931859, by rfl⟩ : syracuseStep 1242479 = 1863719) B1863719
theorem B423295 : Blo 385764 423295 := bstep (se 1 (by rfl) ⟨317471, by rfl⟩ : syracuseStep 423295 = 634943) B634943
theorem B882103 : Blo 385764 882103 := bstep (se 1 (by rfl) ⟨661577, by rfl⟩ : syracuseStep 882103 = 1323155) B1323155
theorem B23787179 : Blo 385764 23787179 := bstep (se 1 (by rfl) ⟨17840384, by rfl⟩ : syracuseStep 23787179 = 35680769) B35680769
theorem B981031 : Blo 385764 981031 := bstep (se 1 (by rfl) ⟨735773, by rfl⟩ : syracuseStep 981031 = 1471547) B1471547
theorem B620681 : Blo 385764 620681 := bstep (se 2 (by rfl) ⟨232755, by rfl⟩ : syracuseStep 620681 = 465511) B465511
theorem B1472701 : Blo 385764 1472701 := bstep (se 3 (by rfl) ⟨276131, by rfl⟩ : syracuseStep 1472701 = 552263) B552263
theorem B981497 : Blo 385764 981497 := bstep (se 2 (by rfl) ⟨368061, by rfl⟩ : syracuseStep 981497 = 736123) B736123
theorem B1309391 : Blo 385764 1309391 := bstep (se 1 (by rfl) ⟨982043, by rfl⟩ : syracuseStep 1309391 = 1964087) B1964087
theorem B2358011 : Blo 385764 2358011 := bstep (se 1 (by rfl) ⟨1768508, by rfl⟩ : syracuseStep 2358011 = 3537017) B3537017
theorem B654203 : Blo 385764 654203 := bstep (se 1 (by rfl) ⟨490652, by rfl⟩ : syracuseStep 654203 = 981305) B981305
theorem B4193147 : Blo 385764 4193147 := bstep (se 1 (by rfl) ⟨3144860, by rfl⟩ : syracuseStep 4193147 = 6289721) B6289721
theorem B1309607 : Blo 385764 1309607 := bstep (se 1 (by rfl) ⟨982205, by rfl⟩ : syracuseStep 1309607 = 1964411) B1964411
theorem B1244335 : Blo 385764 1244335 := bstep (se 1 (by rfl) ⟨933251, by rfl⟩ : syracuseStep 1244335 = 1866503) B1866503
theorem B654655 : Blo 385764 654655 := bstep (se 1 (by rfl) ⟨490991, by rfl⟩ : syracuseStep 654655 = 981983) B981983
theorem B3374459 : Blo 385764 3374459 := bstep (se 1 (by rfl) ⟨2530844, by rfl⟩ : syracuseStep 3374459 = 5061689) B5061689
theorem B982631 : Blo 385764 982631 := bstep (se 1 (by rfl) ⟨736973, by rfl⟩ : syracuseStep 982631 = 1473947) B1473947
theorem B1310363 : Blo 385764 1310363 := bstep (se 1 (by rfl) ⟨982772, by rfl⟩ : syracuseStep 1310363 = 1965545) B1965545
theorem B1867657 : Blo 385764 1867657 := bstep (se 2 (by rfl) ⟨700371, by rfl⟩ : syracuseStep 1867657 = 1400743) B1400743
theorem B2949047 : Blo 385764 2949047 := bstep (se 1 (by rfl) ⟨2211785, by rfl⟩ : syracuseStep 2949047 = 4423571) B4423571
theorem B983137 : Blo 385764 983137 := bstep (se 2 (by rfl) ⟨368676, by rfl⟩ : syracuseStep 983137 = 737353) B737353
theorem B524647 : Blo 385764 524647 := bstep (se 1 (by rfl) ⟨393485, by rfl⟩ : syracuseStep 524647 = 786971) B786971
theorem B4031441 : Blo 385764 4031441 := bstep (se 2 (by rfl) ⟨1511790, by rfl⟩ : syracuseStep 4031441 = 3023581) B3023581
theorem B31917215 : Blo 385764 31917215 := bstep (se 1 (by rfl) ⟨23937911, by rfl⟩ : syracuseStep 31917215 = 47875823) B47875823
theorem B984383 : Blo 385764 984383 := bstep (se 1 (by rfl) ⟨738287, by rfl⟩ : syracuseStep 984383 = 1476575) B1476575
theorem B1967489 : Blo 385764 1967489 := bstep (se 2 (by rfl) ⟨737808, by rfl⟩ : syracuseStep 1967489 = 1475617) B1475617
theorem B657463 : Blo 385764 657463 := bstep (se 1 (by rfl) ⟨493097, by rfl⟩ : syracuseStep 657463 = 986195) B986195
theorem B81889663 : Blo 385764 81889663 := bstep (se 1 (by rfl) ⟨61417247, by rfl⟩ : syracuseStep 81889663 = 122834495) B122834495
theorem B34408961 : Blo 385764 34408961 := bstep (se 2 (by rfl) ⟨12903360, by rfl⟩ : syracuseStep 34408961 = 25806721) B25806721
theorem B28249411 : Blo 385764 28249411 := bstep (se 1 (by rfl) ⟨21187058, by rfl⟩ : syracuseStep 28249411 = 42374117) B42374117
theorem B986539 : Blo 385764 986539 := bstep (se 1 (by rfl) ⟨739904, by rfl⟩ : syracuseStep 986539 = 1479809) B1479809
theorem B5574595 : Blo 385764 5574595 := bstep (se 1 (by rfl) ⟨4180946, by rfl⟩ : syracuseStep 5574595 = 8361893) B8361893
theorem B30249065 : Blo 385764 30249065 := bstep (se 2 (by rfl) ⟨11343399, by rfl⟩ : syracuseStep 30249065 = 22686799) B22686799
theorem B122131235 : Blo 385764 122131235 := bstep (se 1 (by rfl) ⟨91598426, by rfl⟩ : syracuseStep 122131235 = 183196853) B183196853
theorem B3740849 : Blo 385764 3740849 := bstep (se 2 (by rfl) ⟨1402818, by rfl⟩ : syracuseStep 3740849 = 2805637) B2805637
theorem B1808999 : Blo 385764 1808999 := bstep (se 1 (by rfl) ⟨1356749, by rfl⟩ : syracuseStep 1808999 = 2713499) B2713499
theorem B1973159 : Blo 385764 1973159 := bstep (se 1 (by rfl) ⟨1479869, by rfl⟩ : syracuseStep 1973159 = 2959739) B2959739
theorem B3218665 : Blo 385764 3218665 := bstep (se 2 (by rfl) ⟨1206999, by rfl⟩ : syracuseStep 3218665 = 2413999) B2413999
theorem B826679 : Blo 385764 826679 := bstep (se 1 (by rfl) ⟨620009, by rfl⟩ : syracuseStep 826679 = 1240019) B1240019
theorem B1416701 : Blo 385764 1416701 := bstep (se 3 (by rfl) ⟨265631, by rfl⟩ : syracuseStep 1416701 = 531263) B531263
theorem B3710555 : Blo 385764 3710555 := bstep (se 1 (by rfl) ⟨2782916, by rfl⟩ : syracuseStep 3710555 = 5565833) B5565833
theorem B28286779 : Blo 385764 28286779 := bstep (se 1 (by rfl) ⟨21215084, by rfl⟩ : syracuseStep 28286779 = 42430169) B42430169
theorem B2203631 : Blo 385764 2203631 := bstep (se 1 (by rfl) ⟨1652723, by rfl⟩ : syracuseStep 2203631 = 3305447) B3305447
theorem B7053895 : Blo 385764 7053895 := bstep (se 1 (by rfl) ⟨5290421, by rfl⟩ : syracuseStep 7053895 = 10580843) B10580843
theorem B828319 : Blo 385764 828319 := bstep (se 1 (by rfl) ⟨621239, by rfl⟩ : syracuseStep 828319 = 1242479) B1242479
theorem B1680365 : Blo 385764 1680365 := bstep (se 3 (by rfl) ⟨315068, by rfl⟩ : syracuseStep 1680365 = 630137) B630137
theorem B436135 : Blo 385764 436135 := bstep (se 1 (by rfl) ⟨327101, by rfl⟩ : syracuseStep 436135 = 654203) B654203
theorem B2795431 : Blo 385764 2795431 := bstep (se 1 (by rfl) ⟨2096573, by rfl⟩ : syracuseStep 2795431 = 4193147) B4193147
theorem B5286647 : Blo 385764 5286647 := bstep (se 1 (by rfl) ⟨3964985, by rfl⟩ : syracuseStep 5286647 = 7929971) B7929971
theorem B2206547 : Blo 385764 2206547 := bstep (se 1 (by rfl) ⟨1654910, by rfl⟩ : syracuseStep 2206547 = 3309821) B3309821
theorem B14560181 : Blo 385764 14560181 := bstep (se 5 (by rfl) ⟨682508, by rfl⟩ : syracuseStep 14560181 = 1365017) B1365017
theorem B437359 : Blo 385764 437359 := bstep (se 1 (by rfl) ⟨328019, by rfl⟩ : syracuseStep 437359 = 656039) B656039
theorem B7482617 : Blo 385764 7482617 := bstep (se 2 (by rfl) ⟨2805981, by rfl⟩ : syracuseStep 7482617 = 5611963) B5611963
theorem B8400131 : Blo 385764 8400131 := bstep (se 1 (by rfl) ⟨6300098, by rfl⟩ : syracuseStep 8400131 = 12600197) B12600197
theorem B47984237 : Blo 385764 47984237 := bstep (se 3 (by rfl) ⟨8997044, by rfl⟩ : syracuseStep 47984237 = 17994089) B17994089
theorem B732827 : Blo 385764 732827 := bstep (se 1 (by rfl) ⟨549620, by rfl⟩ : syracuseStep 732827 = 1099241) B1099241
theorem B16822403 : Blo 385764 16822403 := bstep (se 1 (by rfl) ⟨12616802, by rfl⟩ : syracuseStep 16822403 = 25233605) B25233605
theorem B930523 : Blo 385764 930523 := bstep (se 1 (by rfl) ⟨697892, by rfl⟩ : syracuseStep 930523 = 1395785) B1395785
theorem B32846759 : Blo 385764 32846759 := bstep (se 1 (by rfl) ⟨24635069, by rfl⟩ : syracuseStep 32846759 = 49270139) B49270139
theorem B931867 : Blo 385764 931867 := bstep (se 1 (by rfl) ⟨698900, by rfl⟩ : syracuseStep 931867 = 1397801) B1397801
theorem B735455 : Blo 385764 735455 := bstep (se 1 (by rfl) ⟨551591, by rfl⟩ : syracuseStep 735455 = 1103183) B1103183
theorem B28786337 : Blo 385764 28786337 := bstep (se 2 (by rfl) ⟨10794876, by rfl⟩ : syracuseStep 28786337 = 21589753) B21589753
theorem B868265 : Blo 385764 868265 := bstep (se 2 (by rfl) ⟨325599, by rfl⟩ : syracuseStep 868265 = 651199) B651199
theorem B2211947 : Blo 385764 2211947 := bstep (se 1 (by rfl) ⟨1658960, by rfl⟩ : syracuseStep 2211947 = 3317921) B3317921
theorem B6832421 : Blo 385764 6832421 := bstep (se 4 (by rfl) ⟨640539, by rfl⟩ : syracuseStep 6832421 = 1281079) B1281079
theorem B1655149 : Blo 385764 1655149 := bstep (se 3 (by rfl) ⟨310340, by rfl⟩ : syracuseStep 1655149 = 620681) B620681
theorem B935675 : Blo 385764 935675 := bstep (se 1 (by rfl) ⟨701756, by rfl⟩ : syracuseStep 935675 = 1403513) B1403513
theorem B871055 : Blo 385764 871055 := bstep (se 1 (by rfl) ⟨653291, by rfl⟩ : syracuseStep 871055 = 1306583) B1306583
theorem B3526507 : Blo 385764 3526507 := bstep (se 1 (by rfl) ⟨2644880, by rfl⟩ : syracuseStep 3526507 = 5289761) B5289761
theorem B1659113 : Blo 385764 1659113 := bstep (se 2 (by rfl) ⟨622167, by rfl⟩ : syracuseStep 1659113 = 1244335) B1244335
theorem B872873 : Blo 385764 872873 := bstep (se 2 (by rfl) ⟨327327, by rfl⟩ : syracuseStep 872873 = 654655) B654655
theorem B872927 : Blo 385764 872927 := bstep (se 1 (by rfl) ⟨654695, by rfl⟩ : syracuseStep 872927 = 1309391) B1309391
theorem B2937383 : Blo 385764 2937383 := bstep (se 1 (by rfl) ⟨2203037, by rfl⟩ : syracuseStep 2937383 = 4406075) B4406075
theorem B873071 : Blo 385764 873071 := bstep (se 1 (by rfl) ⟨654803, by rfl⟩ : syracuseStep 873071 = 1309607) B1309607
theorem B2249639 : Blo 385764 2249639 := bstep (se 1 (by rfl) ⟨1687229, by rfl⟩ : syracuseStep 2249639 = 3374459) B3374459
theorem B873575 : Blo 385764 873575 := bstep (se 1 (by rfl) ⟨655181, by rfl⟩ : syracuseStep 873575 = 1310363) B1310363
theorem B578879 : Blo 385764 578879 := bstep (se 1 (by rfl) ⟨434159, by rfl⟩ : syracuseStep 578879 = 868319) B868319
theorem B16570169 : Blo 385764 16570169 := bstep (se 2 (by rfl) ⟨6213813, by rfl⟩ : syracuseStep 16570169 = 12427627) B12427627
theorem B15849431 : Blo 385764 15849431 := bstep (se 1 (by rfl) ⟨11887073, by rfl⟩ : syracuseStep 15849431 = 23774147) B23774147
theorem B579551 : Blo 385764 579551 := bstep (se 1 (by rfl) ⟨434663, by rfl⟩ : syracuseStep 579551 = 869327) B869327
theorem B579791 : Blo 385764 579791 := bstep (se 1 (by rfl) ⟨434843, by rfl⟩ : syracuseStep 579791 = 869687) B869687
theorem B874799 : Blo 385764 874799 := bstep (se 1 (by rfl) ⟨656099, by rfl⟩ : syracuseStep 874799 = 1312199) B1312199
theorem B580199 : Blo 385764 580199 := bstep (se 1 (by rfl) ⟨435149, by rfl⟩ : syracuseStep 580199 = 870299) B870299
theorem B580331 : Blo 385764 580331 := bstep (se 1 (by rfl) ⟨435248, by rfl⟩ : syracuseStep 580331 = 870497) B870497
theorem B875627 : Blo 385764 875627 := bstep (se 1 (by rfl) ⟨656720, by rfl⟩ : syracuseStep 875627 = 1313441) B1313441
theorem B2088791 : Blo 385764 2088791 := bstep (se 1 (by rfl) ⟨1566593, by rfl⟩ : syracuseStep 2088791 = 3133187) B3133187
theorem B1105883 : Blo 385764 1105883 := bstep (se 1 (by rfl) ⟨829412, by rfl⟩ : syracuseStep 1105883 = 1658825) B1658825
theorem B529915877 : Blo 385764 529915877 := bstep (se 4 (by rfl) ⟨49679613, by rfl⟩ : syracuseStep 529915877 = 99359227) B99359227
theorem B876743 : Blo 385764 876743 := bstep (se 1 (by rfl) ⟨657557, by rfl⟩ : syracuseStep 876743 = 1315115) B1315115
theorem B1302911 : Blo 385764 1302911 := bstep (se 1 (by rfl) ⟨977183, by rfl⟩ : syracuseStep 1302911 = 1954367) B1954367
theorem B385775 : Blo 385764 385775 := bstep (se 1 (by rfl) ⟨289331, by rfl⟩ : syracuseStep 385775 = 578663) B578663
theorem B582395 : Blo 385764 582395 := bstep (se 1 (by rfl) ⟨436796, by rfl⟩ : syracuseStep 582395 = 873593) B873593
theorem B385819 : Blo 385764 385819 := bstep (se 1 (by rfl) ⟨289364, by rfl⟩ : syracuseStep 385819 = 578729) B578729
theorem B1991465 : Blo 385764 1991465 := bstep (se 2 (by rfl) ⟨746799, by rfl⟩ : syracuseStep 1991465 = 1493599) B1493599
theorem B2646827 : Blo 385764 2646827 := bstep (se 1 (by rfl) ⟨1985120, by rfl⟩ : syracuseStep 2646827 = 3970241) B3970241
theorem B385863 : Blo 385764 385863 := bstep (se 1 (by rfl) ⟨289397, by rfl⟩ : syracuseStep 385863 = 578795) B578795
theorem B549769 : Blo 385764 549769 := bstep (se 2 (by rfl) ⟨206163, by rfl⟩ : syracuseStep 549769 = 412327) B412327
theorem B582911 : Blo 385764 582911 := bstep (se 1 (by rfl) ⟨437183, by rfl⟩ : syracuseStep 582911 = 874367) B874367
theorem B1107283 : Blo 385764 1107283 := bstep (se 1 (by rfl) ⟨830462, by rfl⟩ : syracuseStep 1107283 = 1660925) B1660925
theorem B386463 : Blo 385764 386463 := bstep (se 1 (by rfl) ⟨289847, by rfl⟩ : syracuseStep 386463 = 579695) B579695
theorem B386511 : Blo 385764 386511 := bstep (se 1 (by rfl) ⟨289883, by rfl⟩ : syracuseStep 386511 = 579767) B579767
theorem B1566287 : Blo 385764 1566287 := bstep (se 1 (by rfl) ⟨1174715, by rfl⟩ : syracuseStep 1566287 = 2349431) B2349431
theorem B31975033 : Blo 385764 31975033 := bstep (se 2 (by rfl) ⟨11990637, by rfl⟩ : syracuseStep 31975033 = 23981275) B23981275
theorem B1304207 : Blo 385764 1304207 := bstep (se 1 (by rfl) ⟨978155, by rfl⟩ : syracuseStep 1304207 = 1956311) B1956311
theorem B386791 : Blo 385764 386791 := bstep (se 1 (by rfl) ⟨290093, by rfl⟩ : syracuseStep 386791 = 580187) B580187
theorem B583433 : Blo 385764 583433 := bstep (se 2 (by rfl) ⟨218787, by rfl⟩ : syracuseStep 583433 = 437575) B437575
theorem B583931 : Blo 385764 583931 := bstep (se 1 (by rfl) ⟨437948, by rfl⟩ : syracuseStep 583931 = 875897) B875897
theorem B387535 : Blo 385764 387535 := bstep (se 1 (by rfl) ⟨290651, by rfl⟩ : syracuseStep 387535 = 581303) B581303
theorem B1305179 : Blo 385764 1305179 := bstep (se 1 (by rfl) ⟨978884, by rfl⟩ : syracuseStep 1305179 = 1957769) B1957769
theorem B584399 : Blo 385764 584399 := bstep (se 1 (by rfl) ⟨438299, by rfl⟩ : syracuseStep 584399 = 876599) B876599
theorem B584447 : Blo 385764 584447 := bstep (se 1 (by rfl) ⟨438335, by rfl⟩ : syracuseStep 584447 = 876671) B876671
theorem B584585 : Blo 385764 584585 := bstep (se 2 (by rfl) ⟨219219, by rfl⟩ : syracuseStep 584585 = 438439) B438439
theorem B388007 : Blo 385764 388007 := bstep (se 1 (by rfl) ⟨291005, by rfl⟩ : syracuseStep 388007 = 582011) B582011
theorem B388123 : Blo 385764 388123 := bstep (se 1 (by rfl) ⟨291092, by rfl⟩ : syracuseStep 388123 = 582185) B582185
theorem B978095 : Blo 385764 978095 := bstep (se 1 (by rfl) ⟨733571, by rfl⟩ : syracuseStep 978095 = 1467143) B1467143
theorem B1961171 : Blo 385764 1961171 := bstep (se 1 (by rfl) ⟨1470878, by rfl⟩ : syracuseStep 1961171 = 2941757) B2941757
theorem B388327 : Blo 385764 388327 := bstep (se 1 (by rfl) ⟨291245, by rfl⟩ : syracuseStep 388327 = 582491) B582491
theorem B388767 : Blo 385764 388767 := bstep (se 1 (by rfl) ⟨291575, by rfl⟩ : syracuseStep 388767 = 583151) B583151
theorem B388775 : Blo 385764 388775 := bstep (se 1 (by rfl) ⟨291581, by rfl⟩ : syracuseStep 388775 = 583163) B583163
theorem B388847 : Blo 385764 388847 := bstep (se 1 (by rfl) ⟨291635, by rfl⟩ : syracuseStep 388847 = 583271) B583271
theorem B388895 : Blo 385764 388895 := bstep (se 1 (by rfl) ⟨291671, by rfl⟩ : syracuseStep 388895 = 583343) B583343
theorem B388975 : Blo 385764 388975 := bstep (se 1 (by rfl) ⟨291731, by rfl⟩ : syracuseStep 388975 = 583463) B583463
theorem B389023 : Blo 385764 389023 := bstep (se 1 (by rfl) ⟨291767, by rfl⟩ : syracuseStep 389023 = 583535) B583535
theorem B389147 : Blo 385764 389147 := bstep (se 1 (by rfl) ⟨291860, by rfl⟩ : syracuseStep 389147 = 583721) B583721
theorem B749663 : Blo 385764 749663 := bstep (se 1 (by rfl) ⟨562247, by rfl⟩ : syracuseStep 749663 = 1124495) B1124495
theorem B1306799 : Blo 385764 1306799 := bstep (se 1 (by rfl) ⟨980099, by rfl⟩ : syracuseStep 1306799 = 1960199) B1960199
theorem B389375 : Blo 385764 389375 := bstep (se 1 (by rfl) ⟨292031, by rfl⟩ : syracuseStep 389375 = 584063) B584063
theorem B1306907 : Blo 385764 1306907 := bstep (se 1 (by rfl) ⟨980180, by rfl⟩ : syracuseStep 1306907 = 1960361) B1960361
theorem B553243 : Blo 385764 553243 := bstep (se 1 (by rfl) ⟨414932, by rfl⟩ : syracuseStep 553243 = 829865) B829865
theorem B389535 : Blo 385764 389535 := bstep (se 1 (by rfl) ⟨292151, by rfl⟩ : syracuseStep 389535 = 584303) B584303
theorem B1176137 : Blo 385764 1176137 := bstep (se 2 (by rfl) ⟨441051, by rfl⟩ : syracuseStep 1176137 = 882103) B882103
theorem B6288029 : Blo 385764 6288029 := bstep (se 3 (by rfl) ⟨1179005, by rfl⟩ : syracuseStep 6288029 = 2358011) B2358011
theorem B2257573 : Blo 385764 2257573 := bstep (se 4 (by rfl) ⟨211647, by rfl⟩ : syracuseStep 2257573 = 423295) B423295
theorem B1471229 : Blo 385764 1471229 := bstep (se 3 (by rfl) ⟨275855, by rfl⟩ : syracuseStep 1471229 = 551711) B551711
theorem B488263 : Blo 385764 488263 := bstep (se 1 (by rfl) ⟨366197, by rfl⟩ : syracuseStep 488263 = 732395) B732395
theorem B980039 : Blo 385764 980039 := bstep (se 1 (by rfl) ⟨735029, by rfl⟩ : syracuseStep 980039 = 1470059) B1470059
theorem B980059 : Blo 385764 980059 := bstep (se 1 (by rfl) ⟨735044, by rfl⟩ : syracuseStep 980059 = 1470089) B1470089
theorem B1963115 : Blo 385764 1963115 := bstep (se 1 (by rfl) ⟨1472336, by rfl⟩ : syracuseStep 1963115 = 2944673) B2944673
theorem B652475 : Blo 385764 652475 := bstep (se 1 (by rfl) ⟨489356, by rfl⟩ : syracuseStep 652475 = 978713) B978713
theorem B1308041 : Blo 385764 1308041 := bstep (se 2 (by rfl) ⟨490515, by rfl⟩ : syracuseStep 1308041 = 981031) B981031
theorem B7468469 : Blo 385764 7468469 := bstep (se 5 (by rfl) ⟨350084, by rfl⟩ : syracuseStep 7468469 = 700169) B700169
theorem B1963601 : Blo 385764 1963601 := bstep (se 2 (by rfl) ⟨736350, by rfl⟩ : syracuseStep 1963601 = 1472701) B1472701
theorem B652907 : Blo 385764 652907 := bstep (se 1 (by rfl) ⟨489680, by rfl⟩ : syracuseStep 652907 = 979361) B979361
theorem B4454099 : Blo 385764 4454099 := bstep (se 1 (by rfl) ⟨3340574, by rfl⟩ : syracuseStep 4454099 = 6681149) B6681149
theorem B1963763 : Blo 385764 1963763 := bstep (se 1 (by rfl) ⟨1472822, by rfl⟩ : syracuseStep 1963763 = 2945645) B2945645
theorem B12613421 : Blo 385764 12613421 := bstep (se 3 (by rfl) ⟨2365016, by rfl⟩ : syracuseStep 12613421 = 4730033) B4730033
theorem B1472687 : Blo 385764 1472687 := bstep (se 1 (by rfl) ⟨1104515, by rfl⟩ : syracuseStep 1472687 = 2209031) B2209031
theorem B15858119 : Blo 385764 15858119 := bstep (se 1 (by rfl) ⟨11893589, by rfl⟩ : syracuseStep 15858119 = 23787179) B23787179
theorem B4422113 : Blo 385764 4422113 := bstep (se 2 (by rfl) ⟨1658292, by rfl⟩ : syracuseStep 4422113 = 3316585) B3316585
theorem B8419949 : Blo 385764 8419949 := bstep (se 3 (by rfl) ⟨1578740, by rfl⟩ : syracuseStep 8419949 = 3157481) B3157481
theorem B654331 : Blo 385764 654331 := bstep (se 1 (by rfl) ⟨490748, by rfl⟩ : syracuseStep 654331 = 981497) B981497
theorem B655087 : Blo 385764 655087 := bstep (se 1 (by rfl) ⟨491315, by rfl⟩ : syracuseStep 655087 = 982631) B982631
theorem B2490209 : Blo 385764 2490209 := bstep (se 2 (by rfl) ⟨933828, by rfl⟩ : syracuseStep 2490209 = 1867657) B1867657
theorem B1966031 : Blo 385764 1966031 := bstep (se 1 (by rfl) ⟨1474523, by rfl⟩ : syracuseStep 1966031 = 2949047) B2949047
theorem B1474631 : Blo 385764 1474631 := bstep (se 1 (by rfl) ⟨1105973, by rfl⟩ : syracuseStep 1474631 = 2211947) B2211947
theorem B1310849 : Blo 385764 1310849 := bstep (se 2 (by rfl) ⟨491568, by rfl⟩ : syracuseStep 1310849 = 983137) B983137
theorem B4554947 : Blo 385764 4554947 := bstep (se 1 (by rfl) ⟨3416210, by rfl⟩ : syracuseStep 4554947 = 6832421) B6832421
theorem B2687627 : Blo 385764 2687627 := bstep (se 1 (by rfl) ⟨2015720, by rfl⟩ : syracuseStep 2687627 = 4031441) B4031441
theorem B9405193 : Blo 385764 9405193 := bstep (se 2 (by rfl) ⟨3526947, by rfl⟩ : syracuseStep 9405193 = 7053895) B7053895
theorem B656255 : Blo 385764 656255 := bstep (se 1 (by rfl) ⟨492191, by rfl⟩ : syracuseStep 656255 = 984383) B984383
theorem B1311659 : Blo 385764 1311659 := bstep (se 1 (by rfl) ⟨983744, by rfl⟩ : syracuseStep 1311659 = 1967489) B1967489
theorem B623783 : Blo 385764 623783 := bstep (se 1 (by rfl) ⟨467837, by rfl⟩ : syracuseStep 623783 = 935675) B935675
theorem B22939307 : Blo 385764 22939307 := bstep (se 1 (by rfl) ⟨17204480, by rfl⟩ : syracuseStep 22939307 = 34408961) B34408961
theorem B1476377 : Blo 385764 1476377 := bstep (se 2 (by rfl) ⟨553641, by rfl⟩ : syracuseStep 1476377 = 1107283) B1107283
theorem B42633377 : Blo 385764 42633377 := bstep (se 2 (by rfl) ⟨15987516, by rfl⟩ : syracuseStep 42633377 = 31975033) B31975033
theorem B109186217 : Blo 385764 109186217 := bstep (se 2 (by rfl) ⟨40944831, by rfl⟩ : syracuseStep 109186217 = 81889663) B81889663
theorem B2493899 : Blo 385764 2493899 := bstep (se 1 (by rfl) ⟨1870424, by rfl⟩ : syracuseStep 2493899 = 3740849) B3740849
theorem B11046779 : Blo 385764 11046779 := bstep (se 1 (by rfl) ⟨8285084, by rfl⟩ : syracuseStep 11046779 = 16570169) B16570169
theorem B1315385 : Blo 385764 1315385 := bstep (se 2 (by rfl) ⟨493269, by rfl⟩ : syracuseStep 1315385 = 986539) B986539
theorem B1315439 : Blo 385764 1315439 := bstep (se 1 (by rfl) ⟨986579, by rfl⟩ : syracuseStep 1315439 = 1973159) B1973159
theorem B353277251 : Blo 385764 353277251 := bstep (se 1 (by rfl) ⟨264957938, by rfl⟩ : syracuseStep 353277251 = 529915877) B529915877
theorem B1120243 : Blo 385764 1120243 := bstep (se 1 (by rfl) ⟨840182, by rfl⟩ : syracuseStep 1120243 = 1680365) B1680365
theorem B9706787 : Blo 385764 9706787 := bstep (se 1 (by rfl) ⟨7280090, by rfl⟩ : syracuseStep 9706787 = 14560181) B14560181
theorem B4988411 : Blo 385764 4988411 := bstep (se 1 (by rfl) ⟨3741308, by rfl⟩ : syracuseStep 4988411 = 7482617) B7482617
theorem B31989491 : Blo 385764 31989491 := bstep (se 1 (by rfl) ⟨23992118, by rfl⟩ : syracuseStep 31989491 = 47984237) B47984237
theorem B499775 : Blo 385764 499775 := bstep (se 1 (by rfl) ⟨374831, by rfl⟩ : syracuseStep 499775 = 749663) B749663
theorem B11214935 : Blo 385764 11214935 := bstep (se 1 (by rfl) ⟨8411201, by rfl⟩ : syracuseStep 11214935 = 16822403) B16822403
theorem B21897839 : Blo 385764 21897839 := bstep (se 1 (by rfl) ⟨16423379, by rfl⟩ : syracuseStep 21897839 = 32846759) B32846759
theorem B434983 : Blo 385764 434983 := bstep (se 1 (by rfl) ⟨326237, by rfl⟩ : syracuseStep 434983 = 652475) B652475
theorem B435271 : Blo 385764 435271 := bstep (se 1 (by rfl) ⟨326453, by rfl⟩ : syracuseStep 435271 = 652907) B652907
theorem B5613299 : Blo 385764 5613299 := bstep (se 1 (by rfl) ⟨4209974, by rfl⟩ : syracuseStep 5613299 = 8419949) B8419949
theorem B699529 : Blo 385764 699529 := bstep (se 2 (by rfl) ⟨262323, by rfl⟩ : syracuseStep 699529 = 524647) B524647
theorem B2206865 : Blo 385764 2206865 := bstep (se 2 (by rfl) ⟨827574, by rfl⟩ : syracuseStep 2206865 = 1655149) B1655149
theorem B21278143 : Blo 385764 21278143 := bstep (se 1 (by rfl) ⟨15958607, by rfl⟩ : syracuseStep 21278143 = 31917215) B31917215
theorem B733025 : Blo 385764 733025 := bstep (se 2 (by rfl) ⟨274884, by rfl⟩ : syracuseStep 733025 = 549769) B549769
theorem B20166043 : Blo 385764 20166043 := bstep (se 1 (by rfl) ⟨15124532, by rfl⟩ : syracuseStep 20166043 = 30249065) B30249065
theorem B10566287 : Blo 385764 10566287 := bstep (se 1 (by rfl) ⟨7924715, by rfl⟩ : syracuseStep 10566287 = 15849431) B15849431
theorem B37665881 : Blo 385764 37665881 := bstep (se 2 (by rfl) ⟨14124705, by rfl⟩ : syracuseStep 37665881 = 28249411) B28249411
theorem B2473703 : Blo 385764 2473703 := bstep (se 1 (by rfl) ⟨1855277, by rfl⟩ : syracuseStep 2473703 = 3710555) B3710555
theorem B4702009 : Blo 385764 4702009 := bstep (se 2 (by rfl) ⟨1763253, by rfl⟩ : syracuseStep 4702009 = 3526507) B3526507
theorem B1392527 : Blo 385764 1392527 := bstep (se 1 (by rfl) ⟨1044395, by rfl⟩ : syracuseStep 1392527 = 2088791) B2088791
theorem B737255 : Blo 385764 737255 := bstep (se 1 (by rfl) ⟨552941, by rfl⟩ : syracuseStep 737255 = 1105883) B1105883
theorem B868607 : Blo 385764 868607 := bstep (se 1 (by rfl) ⟨651455, by rfl⟩ : syracuseStep 868607 = 1302911) B1302911
theorem B737657 : Blo 385764 737657 := bstep (se 2 (by rfl) ⟨276621, by rfl⟩ : syracuseStep 737657 = 553243) B553243
theorem B1327643 : Blo 385764 1327643 := bstep (se 1 (by rfl) ⟨995732, by rfl⟩ : syracuseStep 1327643 = 1991465) B1991465
theorem B869471 : Blo 385764 869471 := bstep (se 1 (by rfl) ⟨652103, by rfl⟩ : syracuseStep 869471 = 1304207) B1304207
theorem B870119 : Blo 385764 870119 := bstep (se 1 (by rfl) ⟨652589, by rfl⟩ : syracuseStep 870119 = 1305179) B1305179
theorem B3524431 : Blo 385764 3524431 := bstep (se 1 (by rfl) ⟨2643323, by rfl⟩ : syracuseStep 3524431 = 5286647) B5286647
theorem B871199 : Blo 385764 871199 := bstep (se 1 (by rfl) ⟨653399, by rfl⟩ : syracuseStep 871199 = 1306799) B1306799
theorem B871271 : Blo 385764 871271 := bstep (se 1 (by rfl) ⟨653453, by rfl⟩ : syracuseStep 871271 = 1306907) B1306907
theorem B872027 : Blo 385764 872027 := bstep (se 1 (by rfl) ⟨654020, by rfl⟩ : syracuseStep 872027 = 1308041) B1308041
theorem B2969399 : Blo 385764 2969399 := bstep (se 1 (by rfl) ⟨2227049, by rfl⟩ : syracuseStep 2969399 = 4454099) B4454099
theorem B8408947 : Blo 385764 8408947 := bstep (se 1 (by rfl) ⟨6306710, by rfl⟩ : syracuseStep 8408947 = 12613421) B12613421
theorem B872441 : Blo 385764 872441 := bstep (se 2 (by rfl) ⟨327165, by rfl⟩ : syracuseStep 872441 = 654331) B654331
theorem B10572079 : Blo 385764 10572079 := bstep (se 1 (by rfl) ⟨7929059, by rfl⟩ : syracuseStep 10572079 = 15858119) B15858119
theorem B1954205 : Blo 385764 1954205 := bstep (se 3 (by rfl) ⟨366413, by rfl⟩ : syracuseStep 1954205 = 732827) B732827
theorem B873449 : Blo 385764 873449 := bstep (se 2 (by rfl) ⟨327543, by rfl⟩ : syracuseStep 873449 = 655087) B655087
theorem B19190891 : Blo 385764 19190891 := bstep (se 1 (by rfl) ⟨14393168, by rfl⟩ : syracuseStep 19190891 = 28786337) B28786337
theorem B1660139 : Blo 385764 1660139 := bstep (se 1 (by rfl) ⟨1245104, by rfl⟩ : syracuseStep 1660139 = 2490209) B2490209
theorem B578843 : Blo 385764 578843 := bstep (se 1 (by rfl) ⟨434132, by rfl⟩ : syracuseStep 578843 = 868265) B868265
theorem B4969957 : Blo 385764 4969957 := bstep (se 4 (by rfl) ⟨465933, by rfl⟩ : syracuseStep 4969957 = 931867) B931867
theorem B1104425 : Blo 385764 1104425 := bstep (se 2 (by rfl) ⟨414159, by rfl⟩ : syracuseStep 1104425 = 828319) B828319
theorem B580703 : Blo 385764 580703 := bstep (se 1 (by rfl) ⟨435527, by rfl⟩ : syracuseStep 580703 = 871055) B871055
theorem B581513 : Blo 385764 581513 := bstep (se 2 (by rfl) ⟨218067, by rfl⟩ : syracuseStep 581513 = 436135) B436135
theorem B3727241 : Blo 385764 3727241 := bstep (se 2 (by rfl) ⟨1397715, by rfl⟩ : syracuseStep 3727241 = 2795431) B2795431
theorem B876617 : Blo 385764 876617 := bstep (se 2 (by rfl) ⟨328731, by rfl⟩ : syracuseStep 876617 = 657463) B657463
theorem B1106075 : Blo 385764 1106075 := bstep (se 1 (by rfl) ⟨829556, by rfl⟩ : syracuseStep 1106075 = 1659113) B1659113
theorem B581915 : Blo 385764 581915 := bstep (se 1 (by rfl) ⟨436436, by rfl⟩ : syracuseStep 581915 = 872873) B872873
theorem B581951 : Blo 385764 581951 := bstep (se 1 (by rfl) ⟨436463, by rfl⟩ : syracuseStep 581951 = 872927) B872927
theorem B1958255 : Blo 385764 1958255 := bstep (se 1 (by rfl) ⟨1468691, by rfl⟩ : syracuseStep 1958255 = 2937383) B2937383
theorem B582047 : Blo 385764 582047 := bstep (se 1 (by rfl) ⟨436535, by rfl⟩ : syracuseStep 582047 = 873071) B873071
theorem B81420823 : Blo 385764 81420823 := bstep (se 1 (by rfl) ⟨61065617, by rfl⟩ : syracuseStep 81420823 = 122131235) B122131235
theorem B1499759 : Blo 385764 1499759 := bstep (se 1 (by rfl) ⟨1124819, by rfl⟩ : syracuseStep 1499759 = 2249639) B2249639
theorem B582383 : Blo 385764 582383 := bstep (se 1 (by rfl) ⟨436787, by rfl⟩ : syracuseStep 582383 = 873575) B873575
theorem B385919 : Blo 385764 385919 := bstep (se 1 (by rfl) ⟨289439, by rfl⟩ : syracuseStep 385919 = 578879) B578879
theorem B386367 : Blo 385764 386367 := bstep (se 1 (by rfl) ⟨289775, by rfl⟩ : syracuseStep 386367 = 579551) B579551
theorem B386527 : Blo 385764 386527 := bstep (se 1 (by rfl) ⟨289895, by rfl⟩ : syracuseStep 386527 = 579791) B579791
theorem B583145 : Blo 385764 583145 := bstep (se 2 (by rfl) ⟨218679, by rfl⟩ : syracuseStep 583145 = 437359) B437359
theorem B583199 : Blo 385764 583199 := bstep (se 1 (by rfl) ⟨437399, by rfl⟩ : syracuseStep 583199 = 874799) B874799
theorem B1205999 : Blo 385764 1205999 := bstep (se 1 (by rfl) ⟨904499, by rfl⟩ : syracuseStep 1205999 = 1808999) B1808999
theorem B386799 : Blo 385764 386799 := bstep (se 1 (by rfl) ⟨290099, by rfl⟩ : syracuseStep 386799 = 580199) B580199
theorem B386887 : Blo 385764 386887 := bstep (se 1 (by rfl) ⟨290165, by rfl⟩ : syracuseStep 386887 = 580331) B580331
theorem B583751 : Blo 385764 583751 := bstep (se 1 (by rfl) ⟨437813, by rfl⟩ : syracuseStep 583751 = 875627) B875627
theorem B551119 : Blo 385764 551119 := bstep (se 1 (by rfl) ⟨413339, by rfl⟩ : syracuseStep 551119 = 826679) B826679
theorem B944467 : Blo 385764 944467 := bstep (se 1 (by rfl) ⟨708350, by rfl⟩ : syracuseStep 944467 = 1416701) B1416701
theorem B7432793 : Blo 385764 7432793 := bstep (se 2 (by rfl) ⟨2787297, by rfl⟩ : syracuseStep 7432793 = 5574595) B5574595
theorem B1469087 : Blo 385764 1469087 := bstep (se 1 (by rfl) ⟨1101815, by rfl⟩ : syracuseStep 1469087 = 2203631) B2203631
theorem B584495 : Blo 385764 584495 := bstep (se 1 (by rfl) ⟨438371, by rfl⟩ : syracuseStep 584495 = 876743) B876743
theorem B388263 : Blo 385764 388263 := bstep (se 1 (by rfl) ⟨291197, by rfl⟩ : syracuseStep 388263 = 582395) B582395
theorem B1764551 : Blo 385764 1764551 := bstep (se 1 (by rfl) ⟨1323413, by rfl⟩ : syracuseStep 1764551 = 2646827) B2646827
theorem B388607 : Blo 385764 388607 := bstep (se 1 (by rfl) ⟨291455, by rfl⟩ : syracuseStep 388607 = 582911) B582911
theorem B3010097 : Blo 385764 3010097 := bstep (se 2 (by rfl) ⟨1128786, by rfl⟩ : syracuseStep 3010097 = 2257573) B2257573
theorem B1240697 : Blo 385764 1240697 := bstep (se 2 (by rfl) ⟨465261, by rfl⟩ : syracuseStep 1240697 = 930523) B930523
theorem B1044191 : Blo 385764 1044191 := bstep (se 1 (by rfl) ⟨783143, by rfl⟩ : syracuseStep 1044191 = 1566287) B1566287
theorem B651017 : Blo 385764 651017 := bstep (se 2 (by rfl) ⟨244131, by rfl⟩ : syracuseStep 651017 = 488263) B488263
theorem B388955 : Blo 385764 388955 := bstep (se 1 (by rfl) ⟨291716, by rfl⟩ : syracuseStep 388955 = 583433) B583433
theorem B1306745 : Blo 385764 1306745 := bstep (se 2 (by rfl) ⟨490029, by rfl⟩ : syracuseStep 1306745 = 980059) B980059
theorem B389287 : Blo 385764 389287 := bstep (se 1 (by rfl) ⟨291965, by rfl⟩ : syracuseStep 389287 = 583931) B583931
theorem B389599 : Blo 385764 389599 := bstep (se 1 (by rfl) ⟨292199, by rfl⟩ : syracuseStep 389599 = 584399) B584399
theorem B389631 : Blo 385764 389631 := bstep (se 1 (by rfl) ⟨292223, by rfl⟩ : syracuseStep 389631 = 584447) B584447
theorem B1471031 : Blo 385764 1471031 := bstep (se 1 (by rfl) ⟨1103273, by rfl⟩ : syracuseStep 1471031 = 2206547) B2206547
theorem B389723 : Blo 385764 389723 := bstep (se 1 (by rfl) ⟨292292, by rfl⟩ : syracuseStep 389723 = 584585) B584585
theorem B652063 : Blo 385764 652063 := bstep (se 1 (by rfl) ⟨489047, by rfl⟩ : syracuseStep 652063 = 978095) B978095
theorem B1307447 : Blo 385764 1307447 := bstep (se 1 (by rfl) ⟨980585, by rfl⟩ : syracuseStep 1307447 = 1961171) B1961171
theorem B5600087 : Blo 385764 5600087 := bstep (se 1 (by rfl) ⟨4200065, by rfl⟩ : syracuseStep 5600087 = 8400131) B8400131
theorem B784091 : Blo 385764 784091 := bstep (se 1 (by rfl) ⟨588068, by rfl⟩ : syracuseStep 784091 = 1176137) B1176137
theorem B4192019 : Blo 385764 4192019 := bstep (se 1 (by rfl) ⟨3144014, by rfl⟩ : syracuseStep 4192019 = 6288029) B6288029
theorem B980819 : Blo 385764 980819 := bstep (se 1 (by rfl) ⟨735614, by rfl⟩ : syracuseStep 980819 = 1471229) B1471229
theorem B653359 : Blo 385764 653359 := bstep (se 1 (by rfl) ⟨490019, by rfl⟩ : syracuseStep 653359 = 980039) B980039
theorem B1308743 : Blo 385764 1308743 := bstep (se 1 (by rfl) ⟨981557, by rfl⟩ : syracuseStep 1308743 = 1963115) B1963115
theorem B4978979 : Blo 385764 4978979 := bstep (se 1 (by rfl) ⟨3734234, by rfl⟩ : syracuseStep 4978979 = 7468469) B7468469
theorem B1309067 : Blo 385764 1309067 := bstep (se 1 (by rfl) ⟨981800, by rfl⟩ : syracuseStep 1309067 = 1963601) B1963601
theorem B1309175 : Blo 385764 1309175 := bstep (se 1 (by rfl) ⟨981881, by rfl⟩ : syracuseStep 1309175 = 1963763) B1963763
theorem B981791 : Blo 385764 981791 := bstep (se 1 (by rfl) ⟨736343, by rfl⟩ : syracuseStep 981791 = 1472687) B1472687
theorem B490303 : Blo 385764 490303 := bstep (se 1 (by rfl) ⟨367727, by rfl⟩ : syracuseStep 490303 = 735455) B735455
theorem B4291553 : Blo 385764 4291553 := bstep (se 2 (by rfl) ⟨1609332, by rfl⟩ : syracuseStep 4291553 = 3218665) B3218665
theorem B2948075 : Blo 385764 2948075 := bstep (se 1 (by rfl) ⟨2211056, by rfl⟩ : syracuseStep 2948075 = 4422113) B4422113
theorem B37715705 : Blo 385764 37715705 := bstep (se 2 (by rfl) ⟨14143389, by rfl⟩ : syracuseStep 37715705 = 28286779) B28286779
theorem B1310687 : Blo 385764 1310687 := bstep (se 1 (by rfl) ⟨983015, by rfl⟩ : syracuseStep 1310687 = 1966031) B1966031
theorem B983087 : Blo 385764 983087 := bstep (se 1 (by rfl) ⟨737315, by rfl⟩ : syracuseStep 983087 = 1474631) B1474631
theorem B491771 : Blo 385764 491771 := bstep (se 1 (by rfl) ⟨368828, by rfl⟩ : syracuseStep 491771 = 737657) B737657
theorem B885095 : Blo 385764 885095 := bstep (se 1 (by rfl) ⟨663821, by rfl⟩ : syracuseStep 885095 = 1327643) B1327643
theorem B2949533 : Blo 385764 2949533 := bstep (se 3 (by rfl) ⟨553037, by rfl⟩ : syracuseStep 2949533 = 1106075) B1106075
theorem B108561097 : Blo 385764 108561097 := bstep (se 2 (by rfl) ⟨40710411, by rfl⟩ : syracuseStep 108561097 = 81420823) B81420823
theorem B984251 : Blo 385764 984251 := bstep (se 1 (by rfl) ⟨738188, by rfl⟩ : syracuseStep 984251 = 1476377) B1476377
theorem B11211929 : Blo 385764 11211929 := bstep (se 2 (by rfl) ⟨4204473, by rfl⟩ : syracuseStep 11211929 = 8408947) B8408947
theorem B7476623 : Blo 385764 7476623 := bstep (se 1 (by rfl) ⟨5607467, by rfl⟩ : syracuseStep 7476623 = 11214935) B11214935
theorem B14096105 : Blo 385764 14096105 := bstep (se 2 (by rfl) ⟨5286039, by rfl⟩ : syracuseStep 14096105 = 10572079) B10572079
theorem B3742199 : Blo 385764 3742199 := bstep (se 1 (by rfl) ⟨2806649, by rfl⟩ : syracuseStep 3742199 = 5613299) B5613299
theorem B4955195 : Blo 385764 4955195 := bstep (se 1 (by rfl) ⟨3716396, by rfl⟩ : syracuseStep 4955195 = 7432793) B7432793
theorem B6626609 : Blo 385764 6626609 := bstep (se 2 (by rfl) ⟨2484978, by rfl⟩ : syracuseStep 6626609 = 4969957) B4969957
theorem B2006731 : Blo 385764 2006731 := bstep (se 1 (by rfl) ⟨1505048, by rfl⟩ : syracuseStep 2006731 = 3010097) B3010097
theorem B827131 : Blo 385764 827131 := bstep (se 1 (by rfl) ⟨620348, by rfl⟩ : syracuseStep 827131 = 1240697) B1240697
theorem B696127 : Blo 385764 696127 := bstep (se 1 (by rfl) ⟨522095, by rfl⟩ : syracuseStep 696127 = 1044191) B1044191
theorem B434011 : Blo 385764 434011 := bstep (se 1 (by rfl) ⟨325508, by rfl⟩ : syracuseStep 434011 = 651017) B651017
theorem B11444141 : Blo 385764 11444141 := bstep (se 3 (by rfl) ⟨2145776, by rfl⟩ : syracuseStep 11444141 = 4291553) B4291553
theorem B2794679 : Blo 385764 2794679 := bstep (se 1 (by rfl) ⟨2096009, by rfl⟩ : syracuseStep 2794679 = 4192019) B4192019
theorem B3319319 : Blo 385764 3319319 := bstep (se 1 (by rfl) ⟨2489489, by rfl⟩ : syracuseStep 3319319 = 4978979) B4978979
theorem B25110587 : Blo 385764 25110587 := bstep (se 1 (by rfl) ⟨18832940, by rfl⟩ : syracuseStep 25110587 = 37665881) B37665881
theorem B6269345 : Blo 385764 6269345 := bstep (se 2 (by rfl) ⟨2351004, by rfl⟩ : syracuseStep 6269345 = 4702009) B4702009
theorem B1649135 : Blo 385764 1649135 := bstep (se 1 (by rfl) ⟨1236851, by rfl⟩ : syracuseStep 1649135 = 2473703) B2473703
theorem B25143803 : Blo 385764 25143803 := bstep (se 1 (by rfl) ⟨18857852, by rfl⟩ : syracuseStep 25143803 = 37715705) B37715705
theorem B928351 : Blo 385764 928351 := bstep (se 1 (by rfl) ⟨696263, by rfl⟩ : syracuseStep 928351 = 1392527) B1392527
theorem B437503 : Blo 385764 437503 := bstep (se 1 (by rfl) ⟨328127, by rfl⟩ : syracuseStep 437503 = 656255) B656255
theorem B28422251 : Blo 385764 28422251 := bstep (se 1 (by rfl) ⟨21316688, by rfl⟩ : syracuseStep 28422251 = 42633377) B42633377
theorem B72790811 : Blo 385764 72790811 := bstep (se 1 (by rfl) ⟨54593108, by rfl⟩ : syracuseStep 72790811 = 109186217) B109186217
theorem B4699241 : Blo 385764 4699241 := bstep (se 2 (by rfl) ⟨1762215, by rfl⟩ : syracuseStep 4699241 = 3524431) B3524431
theorem B734825 : Blo 385764 734825 := bstep (se 2 (by rfl) ⟨275559, by rfl⟩ : syracuseStep 734825 = 551119) B551119
theorem B235518167 : Blo 385764 235518167 := bstep (se 1 (by rfl) ⟨176638625, by rfl⟩ : syracuseStep 235518167 = 353277251) B353277251
theorem B932705 : Blo 385764 932705 := bstep (se 2 (by rfl) ⟨349764, by rfl⟩ : syracuseStep 932705 = 699529) B699529
theorem B736283 : Blo 385764 736283 := bstep (se 1 (by rfl) ⟨552212, by rfl⟩ : syracuseStep 736283 = 1104425) B1104425
theorem B6471191 : Blo 385764 6471191 := bstep (se 1 (by rfl) ⟨4853393, by rfl⟩ : syracuseStep 6471191 = 9706787) B9706787
theorem B3325607 : Blo 385764 3325607 := bstep (se 1 (by rfl) ⟨2494205, by rfl⟩ : syracuseStep 3325607 = 4988411) B4988411
theorem B14598559 : Blo 385764 14598559 := bstep (se 1 (by rfl) ⟨10948919, by rfl⟩ : syracuseStep 14598559 = 21897839) B21897839
theorem B999839 : Blo 385764 999839 := bstep (se 1 (by rfl) ⟨749879, by rfl⟩ : syracuseStep 999839 = 1499759) B1499759
theorem B869417 : Blo 385764 869417 := bstep (se 2 (by rfl) ⟨326031, by rfl⟩ : syracuseStep 869417 = 652063) B652063
theorem B803999 : Blo 385764 803999 := bstep (se 1 (by rfl) ⟨602999, by rfl⟩ : syracuseStep 803999 = 1205999) B1205999
theorem B26888057 : Blo 385764 26888057 := bstep (se 2 (by rfl) ⟨10083021, by rfl⟩ : syracuseStep 26888057 = 20166043) B20166043
theorem B1493657 : Blo 385764 1493657 := bstep (se 2 (by rfl) ⟨560121, by rfl⟩ : syracuseStep 1493657 = 1120243) B1120243
theorem B871145 : Blo 385764 871145 := bstep (se 2 (by rfl) ⟨326679, by rfl⟩ : syracuseStep 871145 = 653359) B653359
theorem B871163 : Blo 385764 871163 := bstep (se 1 (by rfl) ⟨653372, by rfl⟩ : syracuseStep 871163 = 1306745) B1306745
theorem B871631 : Blo 385764 871631 := bstep (se 1 (by rfl) ⟨653723, by rfl⟩ : syracuseStep 871631 = 1307447) B1307447
theorem B872495 : Blo 385764 872495 := bstep (se 1 (by rfl) ⟨654371, by rfl⟩ : syracuseStep 872495 = 1308743) B1308743
theorem B872711 : Blo 385764 872711 := bstep (se 1 (by rfl) ⟨654533, by rfl⟩ : syracuseStep 872711 = 1309067) B1309067
theorem B872783 : Blo 385764 872783 := bstep (se 1 (by rfl) ⟨654587, by rfl⟩ : syracuseStep 872783 = 1309175) B1309175
theorem B7918397 : Blo 385764 7918397 := bstep (se 3 (by rfl) ⟨1484699, by rfl⟩ : syracuseStep 7918397 = 2969399) B2969399
theorem B873791 : Blo 385764 873791 := bstep (se 1 (by rfl) ⟨655343, by rfl⟩ : syracuseStep 873791 = 1310687) B1310687
theorem B873899 : Blo 385764 873899 := bstep (se 1 (by rfl) ⟨655424, by rfl⟩ : syracuseStep 873899 = 1310849) B1310849
theorem B3036631 : Blo 385764 3036631 := bstep (se 1 (by rfl) ⟨2277473, by rfl⟩ : syracuseStep 3036631 = 4554947) B4554947
theorem B1332733 : Blo 385764 1332733 := bstep (se 3 (by rfl) ⟨249887, by rfl⟩ : syracuseStep 1332733 = 499775) B499775
theorem B579071 : Blo 385764 579071 := bstep (se 1 (by rfl) ⟨434303, by rfl⟩ : syracuseStep 579071 = 868607) B868607
theorem B874439 : Blo 385764 874439 := bstep (se 1 (by rfl) ⟨655829, by rfl⟩ : syracuseStep 874439 = 1311659) B1311659
theorem B579647 : Blo 385764 579647 := bstep (se 1 (by rfl) ⟨434735, by rfl⟩ : syracuseStep 579647 = 869471) B869471
theorem B415855 : Blo 385764 415855 := bstep (se 1 (by rfl) ⟨311891, by rfl⟩ : syracuseStep 415855 = 623783) B623783
theorem B12540257 : Blo 385764 12540257 := bstep (se 2 (by rfl) ⟨4702596, by rfl⟩ : syracuseStep 12540257 = 9405193) B9405193
theorem B579977 : Blo 385764 579977 := bstep (se 2 (by rfl) ⟨217491, by rfl⟩ : syracuseStep 579977 = 434983) B434983
theorem B15292871 : Blo 385764 15292871 := bstep (se 1 (by rfl) ⟨11469653, by rfl⟩ : syracuseStep 15292871 = 22939307) B22939307
theorem B580079 : Blo 385764 580079 := bstep (se 1 (by rfl) ⟨435059, by rfl⟩ : syracuseStep 580079 = 870119) B870119
theorem B580361 : Blo 385764 580361 := bstep (se 2 (by rfl) ⟨217635, by rfl⟩ : syracuseStep 580361 = 435271) B435271
theorem B7167005 : Blo 385764 7167005 := bstep (se 3 (by rfl) ⟨1343813, by rfl⟩ : syracuseStep 7167005 = 2687627) B2687627
theorem B5037157 : Blo 385764 5037157 := bstep (se 4 (by rfl) ⟨472233, by rfl⟩ : syracuseStep 5037157 = 944467) B944467
theorem B580799 : Blo 385764 580799 := bstep (se 1 (by rfl) ⟨435599, by rfl⟩ : syracuseStep 580799 = 871199) B871199
theorem B580847 : Blo 385764 580847 := bstep (se 1 (by rfl) ⟨435635, by rfl⟩ : syracuseStep 580847 = 871271) B871271
theorem B1662599 : Blo 385764 1662599 := bstep (se 1 (by rfl) ⟨1246949, by rfl⟩ : syracuseStep 1662599 = 2493899) B2493899
theorem B581351 : Blo 385764 581351 := bstep (se 1 (by rfl) ⟨436013, by rfl⟩ : syracuseStep 581351 = 872027) B872027
theorem B7364519 : Blo 385764 7364519 := bstep (se 1 (by rfl) ⟨5523389, by rfl⟩ : syracuseStep 7364519 = 11046779) B11046779
theorem B581627 : Blo 385764 581627 := bstep (se 1 (by rfl) ⟨436220, by rfl⟩ : syracuseStep 581627 = 872441) B872441
theorem B1302803 : Blo 385764 1302803 := bstep (se 1 (by rfl) ⟨977102, by rfl⟩ : syracuseStep 1302803 = 1954205) B1954205
theorem B51175709 : Blo 385764 51175709 := bstep (se 3 (by rfl) ⟨9595445, by rfl⟩ : syracuseStep 51175709 = 19190891) B19190891
theorem B876923 : Blo 385764 876923 := bstep (se 1 (by rfl) ⟨657692, by rfl⟩ : syracuseStep 876923 = 1315385) B1315385
theorem B876959 : Blo 385764 876959 := bstep (se 1 (by rfl) ⟨657719, by rfl⟩ : syracuseStep 876959 = 1315439) B1315439
theorem B582299 : Blo 385764 582299 := bstep (se 1 (by rfl) ⟨436724, by rfl⟩ : syracuseStep 582299 = 873449) B873449
theorem B1106759 : Blo 385764 1106759 := bstep (se 1 (by rfl) ⟨830069, by rfl⟩ : syracuseStep 1106759 = 1660139) B1660139
theorem B385895 : Blo 385764 385895 := bstep (se 1 (by rfl) ⟨289421, by rfl⟩ : syracuseStep 385895 = 578843) B578843
theorem B2090909 : Blo 385764 2090909 := bstep (se 3 (by rfl) ⟨392045, by rfl⟩ : syracuseStep 2090909 = 784091) B784091
theorem B28370857 : Blo 385764 28370857 := bstep (se 2 (by rfl) ⟨10639071, by rfl⟩ : syracuseStep 28370857 = 21278143) B21278143
theorem B387135 : Blo 385764 387135 := bstep (se 1 (by rfl) ⟨290351, by rfl⟩ : syracuseStep 387135 = 580703) B580703
theorem B21326327 : Blo 385764 21326327 := bstep (se 1 (by rfl) ⟨15994745, by rfl⟩ : syracuseStep 21326327 = 31989491) B31989491
theorem B387675 : Blo 385764 387675 := bstep (se 1 (by rfl) ⟨290756, by rfl⟩ : syracuseStep 387675 = 581513) B581513
theorem B2484827 : Blo 385764 2484827 := bstep (se 1 (by rfl) ⟨1863620, by rfl⟩ : syracuseStep 2484827 = 3727241) B3727241
theorem B584411 : Blo 385764 584411 := bstep (se 1 (by rfl) ⟨438308, by rfl⟩ : syracuseStep 584411 = 876617) B876617
theorem B387943 : Blo 385764 387943 := bstep (se 1 (by rfl) ⟨290957, by rfl⟩ : syracuseStep 387943 = 581915) B581915
theorem B387967 : Blo 385764 387967 := bstep (se 1 (by rfl) ⟨290975, by rfl⟩ : syracuseStep 387967 = 581951) B581951
theorem B1305503 : Blo 385764 1305503 := bstep (se 1 (by rfl) ⟨979127, by rfl⟩ : syracuseStep 1305503 = 1958255) B1958255
theorem B388031 : Blo 385764 388031 := bstep (se 1 (by rfl) ⟨291023, by rfl⟩ : syracuseStep 388031 = 582047) B582047
theorem B388255 : Blo 385764 388255 := bstep (se 1 (by rfl) ⟨291191, by rfl⟩ : syracuseStep 388255 = 582383) B582383
theorem B388763 : Blo 385764 388763 := bstep (se 1 (by rfl) ⟨291572, by rfl⟩ : syracuseStep 388763 = 583145) B583145
theorem B388799 : Blo 385764 388799 := bstep (se 1 (by rfl) ⟨291599, by rfl⟩ : syracuseStep 388799 = 583199) B583199
theorem B389167 : Blo 385764 389167 := bstep (se 1 (by rfl) ⟨291875, by rfl⟩ : syracuseStep 389167 = 583751) B583751
theorem B979391 : Blo 385764 979391 := bstep (se 1 (by rfl) ⟨734543, by rfl⟩ : syracuseStep 979391 = 1469087) B1469087
theorem B389663 : Blo 385764 389663 := bstep (se 1 (by rfl) ⟨292247, by rfl⟩ : syracuseStep 389663 = 584495) B584495
theorem B1471243 : Blo 385764 1471243 := bstep (se 1 (by rfl) ⟨1103432, by rfl⟩ : syracuseStep 1471243 = 2206865) B2206865
theorem B1176367 : Blo 385764 1176367 := bstep (se 1 (by rfl) ⟨882275, by rfl⟩ : syracuseStep 1176367 = 1764551) B1764551
theorem B488683 : Blo 385764 488683 := bstep (se 1 (by rfl) ⟨366512, by rfl⟩ : syracuseStep 488683 = 733025) B733025
theorem B980687 : Blo 385764 980687 := bstep (se 1 (by rfl) ⟨735515, by rfl⟩ : syracuseStep 980687 = 1471031) B1471031
theorem B3733391 : Blo 385764 3733391 := bstep (se 1 (by rfl) ⟨2800043, by rfl⟩ : syracuseStep 3733391 = 5600087) B5600087
theorem B653737 : Blo 385764 653737 := bstep (se 2 (by rfl) ⟨245151, by rfl⟩ : syracuseStep 653737 = 490303) B490303
theorem B653879 : Blo 385764 653879 := bstep (se 1 (by rfl) ⟨490409, by rfl⟩ : syracuseStep 653879 = 980819) B980819
theorem B7044191 : Blo 385764 7044191 := bstep (se 1 (by rfl) ⟨5283143, by rfl⟩ : syracuseStep 7044191 = 10566287) B10566287
theorem B654527 : Blo 385764 654527 := bstep (se 1 (by rfl) ⟨490895, by rfl⟩ : syracuseStep 654527 = 981791) B981791
theorem B1965383 : Blo 385764 1965383 := bstep (se 1 (by rfl) ⟨1474037, by rfl⟩ : syracuseStep 1965383 = 2948075) B2948075
theorem B491503 : Blo 385764 491503 := bstep (se 1 (by rfl) ⟨368627, by rfl⟩ : syracuseStep 491503 = 737255) B737255
theorem B655391 : Blo 385764 655391 := bstep (se 1 (by rfl) ⟨491543, by rfl⟩ : syracuseStep 655391 = 983087) B983087
theorem B590063 : Blo 385764 590063 := bstep (se 1 (by rfl) ⟨442547, by rfl⟩ : syracuseStep 590063 = 885095) B885095
theorem B1966355 : Blo 385764 1966355 := bstep (se 1 (by rfl) ⟨1474766, by rfl⟩ : syracuseStep 1966355 = 2949533) B2949533
theorem B19464745 : Blo 385764 19464745 := bstep (se 2 (by rfl) ⟨7299279, by rfl⟩ : syracuseStep 19464745 = 14598559) B14598559
theorem B1311389 : Blo 385764 1311389 := bstep (se 3 (by rfl) ⟨245885, by rfl⟩ : syracuseStep 1311389 = 491771) B491771
theorem B656167 : Blo 385764 656167 := bstep (se 1 (by rfl) ⟨492125, by rfl⟩ : syracuseStep 656167 = 984251) B984251
theorem B17925371 : Blo 385764 17925371 := bstep (se 1 (by rfl) ⟨13444028, by rfl⟩ : syracuseStep 17925371 = 26888057) B26888057
theorem B5278931 : Blo 385764 5278931 := bstep (se 1 (by rfl) ⟨3959198, by rfl⟩ : syracuseStep 5278931 = 7918397) B7918397
theorem B7474619 : Blo 385764 7474619 := bstep (se 1 (by rfl) ⟨5605964, by rfl⟩ : syracuseStep 7474619 = 11211929) B11211929
theorem B4984415 : Blo 385764 4984415 := bstep (se 1 (by rfl) ⟨3738311, by rfl⟩ : syracuseStep 4984415 = 7476623) B7476623
theorem B8360171 : Blo 385764 8360171 := bstep (se 1 (by rfl) ⟨6270128, by rfl⟩ : syracuseStep 8360171 = 12540257) B12540257
theorem B10195247 : Blo 385764 10195247 := bstep (se 1 (by rfl) ⟨7646435, by rfl⟩ : syracuseStep 10195247 = 15292871) B15292871
theorem B2494799 : Blo 385764 2494799 := bstep (se 1 (by rfl) ⟨1871099, by rfl⟩ : syracuseStep 2494799 = 3742199) B3742199
theorem B34117139 : Blo 385764 34117139 := bstep (se 1 (by rfl) ⟨25587854, by rfl⟩ : syracuseStep 34117139 = 51175709) B51175709
theorem B1776977 : Blo 385764 1776977 := bstep (se 2 (by rfl) ⟨666366, by rfl⟩ : syracuseStep 1776977 = 1332733) B1332733
theorem B18948167 : Blo 385764 18948167 := bstep (se 1 (by rfl) ⟨14211125, by rfl⟩ : syracuseStep 18948167 = 28422251) B28422251
theorem B435919 : Blo 385764 435919 := bstep (se 1 (by rfl) ⟨326939, by rfl⟩ : syracuseStep 435919 = 653879) B653879
theorem B4696127 : Blo 385764 4696127 := bstep (se 1 (by rfl) ⟨3522095, by rfl⟩ : syracuseStep 4696127 = 7044191) B7044191
theorem B436351 : Blo 385764 436351 := bstep (se 1 (by rfl) ⟨327263, by rfl⟩ : syracuseStep 436351 = 654527) B654527
theorem B928169 : Blo 385764 928169 := bstep (se 2 (by rfl) ⟨348063, by rfl⟩ : syracuseStep 928169 = 696127) B696127
theorem B666559 : Blo 385764 666559 := bstep (se 1 (by rfl) ⟨499919, by rfl⟩ : syracuseStep 666559 = 999839) B999839
theorem B144748129 : Blo 385764 144748129 := bstep (se 2 (by rfl) ⟨54280548, by rfl⟩ : syracuseStep 144748129 = 108561097) B108561097
theorem B995771 : Blo 385764 995771 := bstep (se 1 (by rfl) ⟨746828, by rfl⟩ : syracuseStep 995771 = 1493657) B1493657
theorem B37827809 : Blo 385764 37827809 := bstep (se 2 (by rfl) ⟨14185428, by rfl⟩ : syracuseStep 37827809 = 28370857) B28370857
theorem B2143997 : Blo 385764 2143997 := bstep (se 3 (by rfl) ⟨401999, by rfl⟩ : syracuseStep 2143997 = 803999) B803999
theorem B868535 : Blo 385764 868535 := bstep (se 1 (by rfl) ⟨651401, by rfl⟩ : syracuseStep 868535 = 1302803) B1302803
theorem B737839 : Blo 385764 737839 := bstep (se 1 (by rfl) ⟨553379, by rfl⟩ : syracuseStep 737839 = 1106759) B1106759
theorem B2212879 : Blo 385764 2212879 := bstep (se 1 (by rfl) ⟨1659659, by rfl⟩ : syracuseStep 2212879 = 3319319) B3319319
theorem B1393939 : Blo 385764 1393939 := bstep (se 1 (by rfl) ⟨1045454, by rfl⟩ : syracuseStep 1393939 = 2090909) B2090909
theorem B4179563 : Blo 385764 4179563 := bstep (se 1 (by rfl) ⟨3134672, by rfl⟩ : syracuseStep 4179563 = 6269345) B6269345
theorem B1099423 : Blo 385764 1099423 := bstep (se 1 (by rfl) ⟨824567, by rfl⟩ : syracuseStep 1099423 = 1649135) B1649135
theorem B16762535 : Blo 385764 16762535 := bstep (se 1 (by rfl) ⟨12571901, by rfl⟩ : syracuseStep 16762535 = 25143803) B25143803
theorem B1656551 : Blo 385764 1656551 := bstep (se 1 (by rfl) ⟨1242413, by rfl⟩ : syracuseStep 1656551 = 2484827) B2484827
theorem B870335 : Blo 385764 870335 := bstep (se 1 (by rfl) ⟨652751, by rfl⟩ : syracuseStep 870335 = 1305503) B1305503
theorem B4048841 : Blo 385764 4048841 := bstep (se 2 (by rfl) ⟨1518315, by rfl⟩ : syracuseStep 4048841 = 3036631) B3036631
theorem B871649 : Blo 385764 871649 := bstep (se 2 (by rfl) ⟨326868, by rfl⟩ : syracuseStep 871649 = 653737) B653737
theorem B3132827 : Blo 385764 3132827 := bstep (se 1 (by rfl) ⟨2349620, by rfl⟩ : syracuseStep 3132827 = 4699241) B4699241
theorem B17256509 : Blo 385764 17256509 := bstep (se 3 (by rfl) ⟨3235595, by rfl⟩ : syracuseStep 17256509 = 6471191) B6471191
theorem B157012111 : Blo 385764 157012111 := bstep (se 1 (by rfl) ⟨117759083, by rfl⟩ : syracuseStep 157012111 = 235518167) B235518167
theorem B2675641 : Blo 385764 2675641 := bstep (se 2 (by rfl) ⟨1003365, by rfl⟩ : syracuseStep 2675641 = 2006731) B2006731
theorem B1102841 : Blo 385764 1102841 := bstep (se 2 (by rfl) ⟨413565, by rfl⟩ : syracuseStep 1102841 = 827131) B827131
theorem B2217071 : Blo 385764 2217071 := bstep (se 1 (by rfl) ⟨1662803, by rfl⟩ : syracuseStep 2217071 = 3325607) B3325607
theorem B578681 : Blo 385764 578681 := bstep (se 2 (by rfl) ⟨217005, by rfl⟩ : syracuseStep 578681 = 434011) B434011
theorem B579611 : Blo 385764 579611 := bstep (se 1 (by rfl) ⟨434708, by rfl⟩ : syracuseStep 579611 = 869417) B869417
theorem B580763 : Blo 385764 580763 := bstep (se 1 (by rfl) ⟨435572, by rfl⟩ : syracuseStep 580763 = 871145) B871145
theorem B580775 : Blo 385764 580775 := bstep (se 1 (by rfl) ⟨435581, by rfl⟩ : syracuseStep 580775 = 871163) B871163
theorem B581087 : Blo 385764 581087 := bstep (se 1 (by rfl) ⟨435815, by rfl⟩ : syracuseStep 581087 = 871631) B871631
theorem B581663 : Blo 385764 581663 := bstep (se 1 (by rfl) ⟨436247, by rfl⟩ : syracuseStep 581663 = 872495) B872495
theorem B581807 : Blo 385764 581807 := bstep (se 1 (by rfl) ⟨436355, by rfl⟩ : syracuseStep 581807 = 872711) B872711
theorem B581855 : Blo 385764 581855 := bstep (se 1 (by rfl) ⟨436391, by rfl⟩ : syracuseStep 581855 = 872783) B872783
theorem B1237801 : Blo 385764 1237801 := bstep (se 2 (by rfl) ⟨464175, by rfl⟩ : syracuseStep 1237801 = 928351) B928351
theorem B582527 : Blo 385764 582527 := bstep (se 1 (by rfl) ⟨436895, by rfl⟩ : syracuseStep 582527 = 873791) B873791
theorem B582599 : Blo 385764 582599 := bstep (se 1 (by rfl) ⟨436949, by rfl⟩ : syracuseStep 582599 = 873899) B873899
theorem B386047 : Blo 385764 386047 := bstep (se 1 (by rfl) ⟨289535, by rfl⟩ : syracuseStep 386047 = 579071) B579071
theorem B9397403 : Blo 385764 9397403 := bstep (se 1 (by rfl) ⟨7048052, by rfl⟩ : syracuseStep 9397403 = 14096105) B14096105
theorem B582959 : Blo 385764 582959 := bstep (se 1 (by rfl) ⟨437219, by rfl⟩ : syracuseStep 582959 = 874439) B874439
theorem B386431 : Blo 385764 386431 := bstep (se 1 (by rfl) ⟨289823, by rfl⟩ : syracuseStep 386431 = 579647) B579647
theorem B386651 : Blo 385764 386651 := bstep (se 1 (by rfl) ⟨289988, by rfl⟩ : syracuseStep 386651 = 579977) B579977
theorem B386719 : Blo 385764 386719 := bstep (se 1 (by rfl) ⟨290039, by rfl⟩ : syracuseStep 386719 = 580079) B580079
theorem B583337 : Blo 385764 583337 := bstep (se 2 (by rfl) ⟨218751, by rfl⟩ : syracuseStep 583337 = 437503) B437503
theorem B386907 : Blo 385764 386907 := bstep (se 1 (by rfl) ⟨290180, by rfl⟩ : syracuseStep 386907 = 580361) B580361
theorem B4778003 : Blo 385764 4778003 := bstep (se 1 (by rfl) ⟨3583502, by rfl⟩ : syracuseStep 4778003 = 7167005) B7167005
theorem B3303463 : Blo 385764 3303463 := bstep (se 1 (by rfl) ⟨2477597, by rfl⟩ : syracuseStep 3303463 = 4955195) B4955195
theorem B387199 : Blo 385764 387199 := bstep (se 1 (by rfl) ⟨290399, by rfl⟩ : syracuseStep 387199 = 580799) B580799
theorem B387231 : Blo 385764 387231 := bstep (se 1 (by rfl) ⟨290423, by rfl⟩ : syracuseStep 387231 = 580847) B580847
theorem B4417739 : Blo 385764 4417739 := bstep (se 1 (by rfl) ⟨3313304, by rfl⟩ : syracuseStep 4417739 = 6626609) B6626609
theorem B1108399 : Blo 385764 1108399 := bstep (se 1 (by rfl) ⟨831299, by rfl⟩ : syracuseStep 1108399 = 1662599) B1662599
theorem B387567 : Blo 385764 387567 := bstep (se 1 (by rfl) ⟨290675, by rfl⟩ : syracuseStep 387567 = 581351) B581351
theorem B4909679 : Blo 385764 4909679 := bstep (se 1 (by rfl) ⟨3682259, by rfl⟩ : syracuseStep 4909679 = 7364519) B7364519
theorem B7629427 : Blo 385764 7629427 := bstep (se 1 (by rfl) ⟨5722070, by rfl⟩ : syracuseStep 7629427 = 11444141) B11444141
theorem B387751 : Blo 385764 387751 := bstep (se 1 (by rfl) ⟨290813, by rfl⟩ : syracuseStep 387751 = 581627) B581627
theorem B584615 : Blo 385764 584615 := bstep (se 1 (by rfl) ⟨438461, by rfl⟩ : syracuseStep 584615 = 876923) B876923
theorem B584639 : Blo 385764 584639 := bstep (se 1 (by rfl) ⟨438479, by rfl⟩ : syracuseStep 584639 = 876959) B876959
theorem B388199 : Blo 385764 388199 := bstep (se 1 (by rfl) ⟨291149, by rfl⟩ : syracuseStep 388199 = 582299) B582299
theorem B1863119 : Blo 385764 1863119 := bstep (se 1 (by rfl) ⟨1397339, by rfl⟩ : syracuseStep 1863119 = 2794679) B2794679
theorem B1961657 : Blo 385764 1961657 := bstep (se 2 (by rfl) ⟨735621, by rfl⟩ : syracuseStep 1961657 = 1471243) B1471243
theorem B1568489 : Blo 385764 1568489 := bstep (se 2 (by rfl) ⟨588183, by rfl⟩ : syracuseStep 1568489 = 1176367) B1176367
theorem B16740391 : Blo 385764 16740391 := bstep (se 1 (by rfl) ⟨12555293, by rfl⟩ : syracuseStep 16740391 = 25110587) B25110587
theorem B651577 : Blo 385764 651577 := bstep (se 2 (by rfl) ⟨244341, by rfl⟩ : syracuseStep 651577 = 488683) B488683
theorem B14217551 : Blo 385764 14217551 := bstep (se 1 (by rfl) ⟨10663163, by rfl⟩ : syracuseStep 14217551 = 21326327) B21326327
theorem B389607 : Blo 385764 389607 := bstep (se 1 (by rfl) ⟨292205, by rfl⟩ : syracuseStep 389607 = 584411) B584411
theorem B554473 : Blo 385764 554473 := bstep (se 2 (by rfl) ⟨207927, by rfl⟩ : syracuseStep 554473 = 415855) B415855
theorem B652927 : Blo 385764 652927 := bstep (se 1 (by rfl) ⟨489695, by rfl⟩ : syracuseStep 652927 = 979391) B979391
theorem B48527207 : Blo 385764 48527207 := bstep (se 1 (by rfl) ⟨36395405, by rfl⟩ : syracuseStep 48527207 = 72790811) B72790811
theorem B489883 : Blo 385764 489883 := bstep (se 1 (by rfl) ⟨367412, by rfl⟩ : syracuseStep 489883 = 734825) B734825
theorem B653791 : Blo 385764 653791 := bstep (se 1 (by rfl) ⟨490343, by rfl⟩ : syracuseStep 653791 = 980687) B980687
theorem B2488927 : Blo 385764 2488927 := bstep (se 1 (by rfl) ⟨1866695, by rfl⟩ : syracuseStep 2488927 = 3733391) B3733391
theorem B6716209 : Blo 385764 6716209 := bstep (se 2 (by rfl) ⟨2518578, by rfl⟩ : syracuseStep 6716209 = 5037157) B5037157
theorem B621803 : Blo 385764 621803 := bstep (se 1 (by rfl) ⟨466352, by rfl⟩ : syracuseStep 621803 = 932705) B932705
theorem B490855 : Blo 385764 490855 := bstep (se 1 (by rfl) ⟨368141, by rfl⟩ : syracuseStep 490855 = 736283) B736283
theorem B1310255 : Blo 385764 1310255 := bstep (se 1 (by rfl) ⟨982691, by rfl⟩ : syracuseStep 1310255 = 1965383) B1965383
theorem B655337 : Blo 385764 655337 := bstep (se 2 (by rfl) ⟨245751, by rfl⟩ : syracuseStep 655337 = 491503) B491503
theorem B1310903 : Blo 385764 1310903 := bstep (se 1 (by rfl) ⟨983177, by rfl⟩ : syracuseStep 1310903 = 1966355) B1966355
theorem B1573501 : Blo 385764 1573501 := bstep (se 3 (by rfl) ⟨295031, by rfl⟩ : syracuseStep 1573501 = 590063) B590063
theorem B25952993 : Blo 385764 25952993 := bstep (se 2 (by rfl) ⟨9732372, by rfl⟩ : syracuseStep 25952993 = 19464745) B19464745
theorem B983785 : Blo 385764 983785 := bstep (se 2 (by rfl) ⟨368919, by rfl⟩ : syracuseStep 983785 = 737839) B737839
theorem B2786375 : Blo 385764 2786375 := bstep (se 1 (by rfl) ⟨2089781, by rfl⟩ : syracuseStep 2786375 = 4179563) B4179563
theorem B11175023 : Blo 385764 11175023 := bstep (se 1 (by rfl) ⟨8381267, by rfl⟩ : syracuseStep 11175023 = 16762535) B16762535
theorem B2655389 : Blo 385764 2655389 := bstep (se 3 (by rfl) ⟨497885, by rfl⟩ : syracuseStep 2655389 = 995771) B995771
theorem B2950505 : Blo 385764 2950505 := bstep (se 2 (by rfl) ⟨1106439, by rfl⟩ : syracuseStep 2950505 = 2212879) B2212879
theorem B4983079 : Blo 385764 4983079 := bstep (se 1 (by rfl) ⟨3737309, by rfl⟩ : syracuseStep 4983079 = 7474619) B7474619
theorem B11504339 : Blo 385764 11504339 := bstep (se 1 (by rfl) ⟨8628254, by rfl⟩ : syracuseStep 11504339 = 17256509) B17256509
theorem B5573447 : Blo 385764 5573447 := bstep (se 1 (by rfl) ⟨4180085, by rfl⟩ : syracuseStep 5573447 = 8360171) B8360171
theorem B1477865 : Blo 385764 1477865 := bstep (se 2 (by rfl) ⟨554199, by rfl⟩ : syracuseStep 1477865 = 1108399) B1108399
theorem B1478047 : Blo 385764 1478047 := bstep (se 1 (by rfl) ⟨1108535, by rfl⟩ : syracuseStep 1478047 = 2217071) B2217071
theorem B22744759 : Blo 385764 22744759 := bstep (se 1 (by rfl) ⟨17058569, by rfl⟩ : syracuseStep 22744759 = 34117139) B34117139
theorem B888745 : Blo 385764 888745 := bstep (se 2 (by rfl) ⟨333279, by rfl⟩ : syracuseStep 888745 = 666559) B666559
theorem B1184651 : Blo 385764 1184651 := bstep (se 1 (by rfl) ⟨888488, by rfl⟩ : syracuseStep 1184651 = 1776977) B1776977
theorem B22320521 : Blo 385764 22320521 := bstep (se 2 (by rfl) ⟨8370195, by rfl⟩ : syracuseStep 22320521 = 16740391) B16740391
theorem B6264935 : Blo 385764 6264935 := bstep (se 1 (by rfl) ⟨4698701, by rfl⟩ : syracuseStep 6264935 = 9397403) B9397403
theorem B3185335 : Blo 385764 3185335 := bstep (se 1 (by rfl) ⟨2389001, by rfl⟩ : syracuseStep 3185335 = 4778003) B4778003
theorem B9478367 : Blo 385764 9478367 := bstep (se 1 (by rfl) ⟨7108775, by rfl⟩ : syracuseStep 9478367 = 14217551) B14217551
theorem B3318569 : Blo 385764 3318569 := bstep (se 2 (by rfl) ⟨1244463, by rfl⟩ : syracuseStep 3318569 = 2488927) B2488927
theorem B8954945 : Blo 385764 8954945 := bstep (se 2 (by rfl) ⟨3358104, by rfl⟩ : syracuseStep 8954945 = 6716209) B6716209
theorem B32351471 : Blo 385764 32351471 := bstep (se 1 (by rfl) ⟨24263603, by rfl⟩ : syracuseStep 32351471 = 48527207) B48527207
theorem B436891 : Blo 385764 436891 := bstep (se 1 (by rfl) ⟨327668, by rfl⟩ : syracuseStep 436891 = 655337) B655337
theorem B436927 : Blo 385764 436927 := bstep (se 1 (by rfl) ⟨327695, by rfl⟩ : syracuseStep 436927 = 655391) B655391
theorem B837397925 : Blo 385764 837397925 := bstep (se 4 (by rfl) ⟨78506055, by rfl⟩ : syracuseStep 837397925 = 157012111) B157012111
theorem B1650401 : Blo 385764 1650401 := bstep (se 2 (by rfl) ⟨618900, by rfl⟩ : syracuseStep 1650401 = 1237801) B1237801
theorem B2699227 : Blo 385764 2699227 := bstep (se 1 (by rfl) ⟨2024420, by rfl⟩ : syracuseStep 2699227 = 4048841) B4048841
theorem B3519287 : Blo 385764 3519287 := bstep (se 1 (by rfl) ⟨2639465, by rfl⟩ : syracuseStep 3519287 = 5278931) B5278931
theorem B3322943 : Blo 385764 3322943 := bstep (se 1 (by rfl) ⟨2492207, by rfl⟩ : syracuseStep 3322943 = 4984415) B4984415
theorem B4404617 : Blo 385764 4404617 := bstep (se 2 (by rfl) ⟨1651731, by rfl⟩ : syracuseStep 4404617 = 3303463) B3303463
theorem B6796831 : Blo 385764 6796831 := bstep (se 1 (by rfl) ⟨5097623, by rfl⟩ : syracuseStep 6796831 = 10195247) B10195247
theorem B735227 : Blo 385764 735227 := bstep (se 1 (by rfl) ⟨551420, by rfl⟩ : syracuseStep 735227 = 1102841) B1102841
theorem B10172569 : Blo 385764 10172569 := bstep (se 2 (by rfl) ⟨3814713, by rfl⟩ : syracuseStep 10172569 = 7629427) B7629427
theorem B12632111 : Blo 385764 12632111 := bstep (se 1 (by rfl) ⟨9474083, by rfl⟩ : syracuseStep 12632111 = 18948167) B18948167
theorem B868769 : Blo 385764 868769 := bstep (se 2 (by rfl) ⟨325788, by rfl⟩ : syracuseStep 868769 = 651577) B651577
theorem B3130751 : Blo 385764 3130751 := bstep (se 1 (by rfl) ⟨2348063, by rfl⟩ : syracuseStep 3130751 = 4696127) B4696127
theorem B739297 : Blo 385764 739297 := bstep (se 2 (by rfl) ⟨277236, by rfl⟩ : syracuseStep 739297 = 554473) B554473
theorem B870569 : Blo 385764 870569 := bstep (se 2 (by rfl) ⟨326463, by rfl⟩ : syracuseStep 870569 = 652927) B652927
theorem B16730549 : Blo 385764 16730549 := bstep (se 5 (by rfl) ⟨784244, by rfl⟩ : syracuseStep 16730549 = 1568489) B1568489
theorem B1658141 : Blo 385764 1658141 := bstep (se 3 (by rfl) ⟨310901, by rfl⟩ : syracuseStep 1658141 = 621803) B621803
theorem B871721 : Blo 385764 871721 := bstep (se 2 (by rfl) ⟨326895, by rfl⟩ : syracuseStep 871721 = 653791) B653791
theorem B25218539 : Blo 385764 25218539 := bstep (se 1 (by rfl) ⟨18913904, by rfl⟩ : syracuseStep 25218539 = 37827809) B37827809
theorem B1429331 : Blo 385764 1429331 := bstep (se 1 (by rfl) ⟨1071998, by rfl⟩ : syracuseStep 1429331 = 2143997) B2143997
theorem B4968317 : Blo 385764 4968317 := bstep (se 3 (by rfl) ⟨931559, by rfl⟩ : syracuseStep 4968317 = 1863119) B1863119
theorem B873503 : Blo 385764 873503 := bstep (se 1 (by rfl) ⟨655127, by rfl⟩ : syracuseStep 873503 = 1310255) B1310255
theorem B579023 : Blo 385764 579023 := bstep (se 1 (by rfl) ⟨434267, by rfl⟩ : syracuseStep 579023 = 868535) B868535
theorem B874259 : Blo 385764 874259 := bstep (se 1 (by rfl) ⟨655694, by rfl⟩ : syracuseStep 874259 = 1311389) B1311389
theorem B11950247 : Blo 385764 11950247 := bstep (se 1 (by rfl) ⟨8962685, by rfl⟩ : syracuseStep 11950247 = 17925371) B17925371
theorem B874889 : Blo 385764 874889 := bstep (se 2 (by rfl) ⟨328083, by rfl⟩ : syracuseStep 874889 = 656167) B656167
theorem B1104367 : Blo 385764 1104367 := bstep (se 1 (by rfl) ⟨828275, by rfl⟩ : syracuseStep 1104367 = 1656551) B1656551
theorem B580223 : Blo 385764 580223 := bstep (se 1 (by rfl) ⟨435167, by rfl⟩ : syracuseStep 580223 = 870335) B870335
theorem B1858585 : Blo 385764 1858585 := bstep (se 2 (by rfl) ⟨696969, by rfl⟩ : syracuseStep 1858585 = 1393939) B1393939
theorem B581099 : Blo 385764 581099 := bstep (se 1 (by rfl) ⟨435824, by rfl⟩ : syracuseStep 581099 = 871649) B871649
theorem B1465897 : Blo 385764 1465897 := bstep (se 2 (by rfl) ⟨549711, by rfl⟩ : syracuseStep 1465897 = 1099423) B1099423
theorem B2088551 : Blo 385764 2088551 := bstep (se 1 (by rfl) ⟨1566413, by rfl⟩ : syracuseStep 2088551 = 3132827) B3132827
theorem B581225 : Blo 385764 581225 := bstep (se 2 (by rfl) ⟨217959, by rfl⟩ : syracuseStep 581225 = 435919) B435919
theorem B581801 : Blo 385764 581801 := bstep (se 2 (by rfl) ⟨218175, by rfl⟩ : syracuseStep 581801 = 436351) B436351
theorem B1663199 : Blo 385764 1663199 := bstep (se 1 (by rfl) ⟨1247399, by rfl⟩ : syracuseStep 1663199 = 2494799) B2494799
theorem B385787 : Blo 385764 385787 := bstep (se 1 (by rfl) ⟨289340, by rfl⟩ : syracuseStep 385787 = 578681) B578681
theorem B386407 : Blo 385764 386407 := bstep (se 1 (by rfl) ⟨289805, by rfl⟩ : syracuseStep 386407 = 579611) B579611
theorem B387175 : Blo 385764 387175 := bstep (se 1 (by rfl) ⟨290381, by rfl⟩ : syracuseStep 387175 = 580763) B580763
theorem B387183 : Blo 385764 387183 := bstep (se 1 (by rfl) ⟨290387, by rfl⟩ : syracuseStep 387183 = 580775) B580775
theorem B192997505 : Blo 385764 192997505 := bstep (se 2 (by rfl) ⟨72374064, by rfl⟩ : syracuseStep 192997505 = 144748129) B144748129
theorem B387391 : Blo 385764 387391 := bstep (se 1 (by rfl) ⟨290543, by rfl⟩ : syracuseStep 387391 = 581087) B581087
theorem B387775 : Blo 385764 387775 := bstep (se 1 (by rfl) ⟨290831, by rfl⟩ : syracuseStep 387775 = 581663) B581663
theorem B387871 : Blo 385764 387871 := bstep (se 1 (by rfl) ⟨290903, by rfl⟩ : syracuseStep 387871 = 581807) B581807
theorem B387903 : Blo 385764 387903 := bstep (se 1 (by rfl) ⟨290927, by rfl⟩ : syracuseStep 387903 = 581855) B581855
theorem B388351 : Blo 385764 388351 := bstep (se 1 (by rfl) ⟨291263, by rfl⟩ : syracuseStep 388351 = 582527) B582527
theorem B388399 : Blo 385764 388399 := bstep (se 1 (by rfl) ⟨291299, by rfl⟩ : syracuseStep 388399 = 582599) B582599
theorem B388639 : Blo 385764 388639 := bstep (se 1 (by rfl) ⟨291479, by rfl⟩ : syracuseStep 388639 = 582959) B582959
theorem B388891 : Blo 385764 388891 := bstep (se 1 (by rfl) ⟨291668, by rfl⟩ : syracuseStep 388891 = 583337) B583337
theorem B3567521 : Blo 385764 3567521 := bstep (se 2 (by rfl) ⟨1337820, by rfl⟩ : syracuseStep 3567521 = 2675641) B2675641
theorem B2945159 : Blo 385764 2945159 := bstep (se 1 (by rfl) ⟨2208869, by rfl⟩ : syracuseStep 2945159 = 4417739) B4417739
theorem B618779 : Blo 385764 618779 := bstep (se 1 (by rfl) ⟨464084, by rfl⟩ : syracuseStep 618779 = 928169) B928169
theorem B3273119 : Blo 385764 3273119 := bstep (se 1 (by rfl) ⟨2454839, by rfl⟩ : syracuseStep 3273119 = 4909679) B4909679
theorem B389743 : Blo 385764 389743 := bstep (se 1 (by rfl) ⟨292307, by rfl⟩ : syracuseStep 389743 = 584615) B584615
theorem B389759 : Blo 385764 389759 := bstep (se 1 (by rfl) ⟨292319, by rfl⟩ : syracuseStep 389759 = 584639) B584639
theorem B1307771 : Blo 385764 1307771 := bstep (se 1 (by rfl) ⟨980828, by rfl⟩ : syracuseStep 1307771 = 1961657) B1961657
theorem B653177 : Blo 385764 653177 := bstep (se 2 (by rfl) ⟨244941, by rfl⟩ : syracuseStep 653177 = 489883) B489883
theorem B654473 : Blo 385764 654473 := bstep (se 2 (by rfl) ⟨245427, by rfl⟩ : syracuseStep 654473 = 490855) B490855
theorem B8421407 : Blo 385764 8421407 := bstep (se 1 (by rfl) ⟨6316055, by rfl⟩ : syracuseStep 8421407 = 12632111) B12632111
theorem B17301995 : Blo 385764 17301995 := bstep (se 1 (by rfl) ⟨12976496, by rfl⟩ : syracuseStep 17301995 = 25952993) B25952993
theorem B2098001 : Blo 385764 2098001 := bstep (se 2 (by rfl) ⟨786750, by rfl⟩ : syracuseStep 2098001 = 1573501) B1573501
theorem B1967003 : Blo 385764 1967003 := bstep (se 1 (by rfl) ⟨1475252, by rfl⟩ : syracuseStep 1967003 = 2950505) B2950505
theorem B1311713 : Blo 385764 1311713 := bstep (se 2 (by rfl) ⟨491892, by rfl⟩ : syracuseStep 1311713 = 983785) B983785
theorem B7669559 : Blo 385764 7669559 := bstep (se 1 (by rfl) ⟨5752169, by rfl⟩ : syracuseStep 7669559 = 11504339) B11504339
theorem B985243 : Blo 385764 985243 := bstep (se 1 (by rfl) ⟨738932, by rfl⟩ : syracuseStep 985243 = 1477865) B1477865
theorem B16812359 : Blo 385764 16812359 := bstep (se 1 (by rfl) ⟨12609269, by rfl⟩ : syracuseStep 16812359 = 25218539) B25218539
theorem B3312211 : Blo 385764 3312211 := bstep (se 1 (by rfl) ⟨2484158, by rfl⟩ : syracuseStep 3312211 = 4968317) B4968317
theorem B985729 : Blo 385764 985729 := bstep (se 2 (by rfl) ⟨369648, by rfl⟩ : syracuseStep 985729 = 739297) B739297
theorem B7081037 : Blo 385764 7081037 := bstep (se 3 (by rfl) ⟨1327694, by rfl⟩ : syracuseStep 7081037 = 2655389) B2655389
theorem B789767 : Blo 385764 789767 := bstep (se 1 (by rfl) ⟨592325, by rfl⟩ : syracuseStep 789767 = 1184651) B1184651
theorem B14880347 : Blo 385764 14880347 := bstep (se 1 (by rfl) ⟨11160260, by rfl⟩ : syracuseStep 14880347 = 22320521) B22320521
theorem B7966831 : Blo 385764 7966831 := bstep (se 1 (by rfl) ⟨5975123, by rfl⟩ : syracuseStep 7966831 = 11950247) B11950247
theorem B1970729 : Blo 385764 1970729 := bstep (se 2 (by rfl) ⟨739023, by rfl⟩ : syracuseStep 1970729 = 1478047) B1478047
theorem B1184993 : Blo 385764 1184993 := bstep (se 2 (by rfl) ⟨444372, by rfl⟩ : syracuseStep 1184993 = 888745) B888745
theorem B514660013 : Blo 385764 514660013 := bstep (se 3 (by rfl) ⟨96498752, by rfl⟩ : syracuseStep 514660013 = 192997505) B192997505
theorem B5969963 : Blo 385764 5969963 := bstep (se 1 (by rfl) ⟨4477472, by rfl⟩ : syracuseStep 5969963 = 8954945) B8954945
theorem B21567647 : Blo 385764 21567647 := bstep (se 1 (by rfl) ⟨16175735, by rfl⟩ : syracuseStep 21567647 = 32351471) B32351471
theorem B435451 : Blo 385764 435451 := bstep (se 1 (by rfl) ⟨326588, by rfl⟩ : syracuseStep 435451 = 653177) B653177
theorem B436315 : Blo 385764 436315 := bstep (se 1 (by rfl) ⟨327236, by rfl⟩ : syracuseStep 436315 = 654473) B654473
theorem B3811549 : Blo 385764 3811549 := bstep (se 3 (by rfl) ⟨714665, by rfl⟩ : syracuseStep 3811549 = 1429331) B1429331
theorem B9513389 : Blo 385764 9513389 := bstep (se 3 (by rfl) ⟨1783760, by rfl⟩ : syracuseStep 9513389 = 3567521) B3567521
theorem B14395877 : Blo 385764 14395877 := bstep (se 4 (by rfl) ⟨1349613, by rfl⟩ : syracuseStep 14395877 = 2699227) B2699227
theorem B1650077 : Blo 385764 1650077 := bstep (se 3 (by rfl) ⟨309389, by rfl⟩ : syracuseStep 1650077 = 618779) B618779
theorem B7450015 : Blo 385764 7450015 := bstep (se 1 (by rfl) ⟨5587511, by rfl⟩ : syracuseStep 7450015 = 11175023) B11175023
theorem B11153699 : Blo 385764 11153699 := bstep (se 1 (by rfl) ⟨8365274, by rfl⟩ : syracuseStep 11153699 = 16730549) B16730549
theorem B3715631 : Blo 385764 3715631 := bstep (se 1 (by rfl) ⟨2786723, by rfl⟩ : syracuseStep 3715631 = 5573447) B5573447
theorem B4176623 : Blo 385764 4176623 := bstep (se 1 (by rfl) ⟨3132467, by rfl⟩ : syracuseStep 4176623 = 6264935) B6264935
theorem B30326345 : Blo 385764 30326345 := bstep (se 2 (by rfl) ⟨11372379, by rfl⟩ : syracuseStep 30326345 = 22744759) B22744759
theorem B2212379 : Blo 385764 2212379 := bstep (se 1 (by rfl) ⟨1659284, by rfl⟩ : syracuseStep 2212379 = 3318569) B3318569
theorem B9062441 : Blo 385764 9062441 := bstep (se 2 (by rfl) ⟨3398415, by rfl⟩ : syracuseStep 9062441 = 6796831) B6796831
theorem B1100267 : Blo 385764 1100267 := bstep (se 1 (by rfl) ⟨825200, by rfl⟩ : syracuseStep 1100267 = 1650401) B1650401
theorem B2182079 : Blo 385764 2182079 := bstep (se 1 (by rfl) ⟨1636559, by rfl⟩ : syracuseStep 2182079 = 3273119) B3273119
theorem B2346191 : Blo 385764 2346191 := bstep (se 1 (by rfl) ⟨1759643, by rfl⟩ : syracuseStep 2346191 = 3519287) B3519287
theorem B2215295 : Blo 385764 2215295 := bstep (se 1 (by rfl) ⟨1661471, by rfl⟩ : syracuseStep 2215295 = 3322943) B3322943
theorem B871847 : Blo 385764 871847 := bstep (se 1 (by rfl) ⟨653885, by rfl⟩ : syracuseStep 871847 = 1307771) B1307771
theorem B4247113 : Blo 385764 4247113 := bstep (se 2 (by rfl) ⟨1592667, by rfl⟩ : syracuseStep 4247113 = 3185335) B3185335
theorem B2936411 : Blo 385764 2936411 := bstep (se 1 (by rfl) ⟨2202308, by rfl⟩ : syracuseStep 2936411 = 4404617) B4404617
theorem B2478113 : Blo 385764 2478113 := bstep (se 2 (by rfl) ⟨929292, by rfl⟩ : syracuseStep 2478113 = 1858585) B1858585
theorem B1954529 : Blo 385764 1954529 := bstep (se 2 (by rfl) ⟨732948, by rfl⟩ : syracuseStep 1954529 = 1465897) B1465897
theorem B873935 : Blo 385764 873935 := bstep (se 1 (by rfl) ⟨655451, by rfl⟩ : syracuseStep 873935 = 1310903) B1310903
theorem B579179 : Blo 385764 579179 := bstep (se 1 (by rfl) ⟨434384, by rfl⟩ : syracuseStep 579179 = 868769) B868769
theorem B1857583 : Blo 385764 1857583 := bstep (se 1 (by rfl) ⟨1393187, by rfl⟩ : syracuseStep 1857583 = 2786375) B2786375
theorem B580379 : Blo 385764 580379 := bstep (se 1 (by rfl) ⟨435284, by rfl⟩ : syracuseStep 580379 = 870569) B870569
theorem B1105427 : Blo 385764 1105427 := bstep (se 1 (by rfl) ⟨829070, by rfl⟩ : syracuseStep 1105427 = 1658141) B1658141
theorem B581147 : Blo 385764 581147 := bstep (se 1 (by rfl) ⟨435860, by rfl⟩ : syracuseStep 581147 = 871721) B871721
theorem B6644105 : Blo 385764 6644105 := bstep (se 2 (by rfl) ⟨2491539, by rfl⟩ : syracuseStep 6644105 = 4983079) B4983079
theorem B582335 : Blo 385764 582335 := bstep (se 1 (by rfl) ⟨436751, by rfl⟩ : syracuseStep 582335 = 873503) B873503
theorem B582521 : Blo 385764 582521 := bstep (se 2 (by rfl) ⟨218445, by rfl⟩ : syracuseStep 582521 = 436891) B436891
theorem B582569 : Blo 385764 582569 := bstep (se 2 (by rfl) ⟨218463, by rfl⟩ : syracuseStep 582569 = 436927) B436927
theorem B386015 : Blo 385764 386015 := bstep (se 1 (by rfl) ⟨289511, by rfl⟩ : syracuseStep 386015 = 579023) B579023
theorem B8348669 : Blo 385764 8348669 := bstep (se 3 (by rfl) ⟨1565375, by rfl⟩ : syracuseStep 8348669 = 3130751) B3130751
theorem B582839 : Blo 385764 582839 := bstep (se 1 (by rfl) ⟨437129, by rfl⟩ : syracuseStep 582839 = 874259) B874259
theorem B583259 : Blo 385764 583259 := bstep (se 1 (by rfl) ⟨437444, by rfl⟩ : syracuseStep 583259 = 874889) B874889
theorem B386815 : Blo 385764 386815 := bstep (se 1 (by rfl) ⟨290111, by rfl⟩ : syracuseStep 386815 = 580223) B580223
theorem B387399 : Blo 385764 387399 := bstep (se 1 (by rfl) ⟨290549, by rfl⟩ : syracuseStep 387399 = 581099) B581099
theorem B387483 : Blo 385764 387483 := bstep (se 1 (by rfl) ⟨290612, by rfl⟩ : syracuseStep 387483 = 581225) B581225
theorem B387867 : Blo 385764 387867 := bstep (se 1 (by rfl) ⟨290900, by rfl⟩ : syracuseStep 387867 = 581801) B581801
theorem B1108799 : Blo 385764 1108799 := bstep (se 1 (by rfl) ⟨831599, by rfl⟩ : syracuseStep 1108799 = 1663199) B1663199
theorem B6318911 : Blo 385764 6318911 := bstep (se 1 (by rfl) ⟨4739183, by rfl⟩ : syracuseStep 6318911 = 9478367) B9478367
theorem B558265283 : Blo 385764 558265283 := bstep (se 1 (by rfl) ⟨418698962, by rfl⟩ : syracuseStep 558265283 = 837397925) B837397925
theorem B1963439 : Blo 385764 1963439 := bstep (se 1 (by rfl) ⟨1472579, by rfl⟩ : syracuseStep 1963439 = 2945159) B2945159
theorem B13563425 : Blo 385764 13563425 := bstep (se 2 (by rfl) ⟨5086284, by rfl⟩ : syracuseStep 13563425 = 10172569) B10172569
theorem B1472489 : Blo 385764 1472489 := bstep (se 2 (by rfl) ⟨552183, by rfl⟩ : syracuseStep 1472489 = 1104367) B1104367
theorem B490151 : Blo 385764 490151 := bstep (se 1 (by rfl) ⟨367613, by rfl⟩ : syracuseStep 490151 = 735227) B735227
theorem B5569469 : Blo 385764 5569469 := bstep (se 3 (by rfl) ⟨1044275, by rfl⟩ : syracuseStep 5569469 = 2088551) B2088551
theorem B11534663 : Blo 385764 11534663 := bstep (se 1 (by rfl) ⟨8650997, by rfl⟩ : syracuseStep 11534663 = 17301995) B17301995
theorem B1474919 : Blo 385764 1474919 := bstep (se 1 (by rfl) ⟨1106189, by rfl⟩ : syracuseStep 1474919 = 2212379) B2212379
theorem B1311335 : Blo 385764 1311335 := bstep (se 1 (by rfl) ⟨983501, by rfl⟩ : syracuseStep 1311335 = 1967003) B1967003
theorem B5113039 : Blo 385764 5113039 := bstep (se 1 (by rfl) ⟨3834779, by rfl⟩ : syracuseStep 5113039 = 7669559) B7669559
theorem B11208239 : Blo 385764 11208239 := bstep (se 1 (by rfl) ⟨8406179, by rfl⟩ : syracuseStep 11208239 = 16812359) B16812359
theorem B4720691 : Blo 385764 4720691 := bstep (se 1 (by rfl) ⟨3540518, by rfl⟩ : syracuseStep 4720691 = 7081037) B7081037
theorem B526511 : Blo 385764 526511 := bstep (se 1 (by rfl) ⟨394883, by rfl⟩ : syracuseStep 526511 = 789767) B789767
theorem B1476863 : Blo 385764 1476863 := bstep (se 1 (by rfl) ⟨1107647, by rfl⟩ : syracuseStep 1476863 = 2215295) B2215295
theorem B1313657 : Blo 385764 1313657 := bstep (se 2 (by rfl) ⟨492621, by rfl⟩ : syracuseStep 1313657 = 985243) B985243
theorem B5082065 : Blo 385764 5082065 := bstep (se 2 (by rfl) ⟨1905774, by rfl⟩ : syracuseStep 5082065 = 3811549) B3811549
theorem B1313819 : Blo 385764 1313819 := bstep (se 1 (by rfl) ⟨985364, by rfl⟩ : syracuseStep 1313819 = 1970729) B1970729
theorem B789995 : Blo 385764 789995 := bstep (se 1 (by rfl) ⟨592496, by rfl⟩ : syracuseStep 789995 = 1184993) B1184993
theorem B1314305 : Blo 385764 1314305 := bstep (se 2 (by rfl) ⟨492864, by rfl⟩ : syracuseStep 1314305 = 985729) B985729
theorem B9933353 : Blo 385764 9933353 := bstep (se 2 (by rfl) ⟨3725007, by rfl⟩ : syracuseStep 9933353 = 7450015) B7450015
theorem B10622441 : Blo 385764 10622441 := bstep (se 2 (by rfl) ⟨3983415, by rfl⟩ : syracuseStep 10622441 = 7966831) B7966831
theorem B4429403 : Blo 385764 4429403 := bstep (se 1 (by rfl) ⟨3322052, by rfl⟩ : syracuseStep 4429403 = 6644105) B6644105
theorem B57513725 : Blo 385764 57513725 := bstep (se 3 (by rfl) ⟨10783823, by rfl⟩ : syracuseStep 57513725 = 21567647) B21567647
theorem B3712979 : Blo 385764 3712979 := bstep (se 1 (by rfl) ⟨2784734, by rfl⟩ : syracuseStep 3712979 = 5569469) B5569469
theorem B5614271 : Blo 385764 5614271 := bstep (se 1 (by rfl) ⟨4210703, by rfl⟩ : syracuseStep 5614271 = 8421407) B8421407
theorem B9907109 : Blo 385764 9907109 := bstep (se 4 (by rfl) ⟨928791, by rfl⟩ : syracuseStep 9907109 = 1857583) B1857583
theorem B6041627 : Blo 385764 6041627 := bstep (se 1 (by rfl) ⟨4531220, by rfl⟩ : syracuseStep 6041627 = 9062441) B9062441
theorem B733511 : Blo 385764 733511 := bstep (se 1 (by rfl) ⟨550133, by rfl⟩ : syracuseStep 733511 = 1100267) B1100267
theorem B1652075 : Blo 385764 1652075 := bstep (se 1 (by rfl) ⟨1239056, by rfl⟩ : syracuseStep 1652075 = 2478113) B2478113
theorem B3979975 : Blo 385764 3979975 := bstep (se 1 (by rfl) ⟨2984981, by rfl⟩ : syracuseStep 3979975 = 5969963) B5969963
theorem B736951 : Blo 385764 736951 := bstep (se 1 (by rfl) ⟨552713, by rfl⟩ : syracuseStep 736951 = 1105427) B1105427
theorem B6342259 : Blo 385764 6342259 := bstep (se 1 (by rfl) ⟨4756694, by rfl⟩ : syracuseStep 6342259 = 9513389) B9513389
theorem B739199 : Blo 385764 739199 := bstep (se 1 (by rfl) ⟨554399, by rfl⟩ : syracuseStep 739199 = 1108799) B1108799
theorem B4212607 : Blo 385764 4212607 := bstep (se 1 (by rfl) ⟨3159455, by rfl⟩ : syracuseStep 4212607 = 6318911) B6318911
theorem B1100051 : Blo 385764 1100051 := bstep (se 1 (by rfl) ⟨825038, by rfl⟩ : syracuseStep 1100051 = 1650077) B1650077
theorem B5818877 : Blo 385764 5818877 := bstep (se 3 (by rfl) ⟨1091039, by rfl⟩ : syracuseStep 5818877 = 2182079) B2182079
theorem B2477087 : Blo 385764 2477087 := bstep (se 1 (by rfl) ⟨1857815, by rfl⟩ : syracuseStep 2477087 = 3715631) B3715631
theorem B1398667 : Blo 385764 1398667 := bstep (se 1 (by rfl) ⟨1049000, by rfl⟩ : syracuseStep 1398667 = 2098001) B2098001
theorem B874475 : Blo 385764 874475 := bstep (se 1 (by rfl) ⟨655856, by rfl⟩ : syracuseStep 874475 = 1311713) B1311713
theorem B580601 : Blo 385764 580601 := bstep (se 2 (by rfl) ⟨217725, by rfl⟩ : syracuseStep 580601 = 435451) B435451
theorem B1564127 : Blo 385764 1564127 := bstep (se 1 (by rfl) ⟨1173095, by rfl⟩ : syracuseStep 1564127 = 2346191) B2346191
theorem B581231 : Blo 385764 581231 := bstep (se 1 (by rfl) ⟨435923, by rfl⟩ : syracuseStep 581231 = 871847) B871847
theorem B1957607 : Blo 385764 1957607 := bstep (se 1 (by rfl) ⟨1468205, by rfl⟩ : syracuseStep 1957607 = 2936411) B2936411
theorem B9920231 : Blo 385764 9920231 := bstep (se 1 (by rfl) ⟨7440173, by rfl⟩ : syracuseStep 9920231 = 14880347) B14880347
theorem B581753 : Blo 385764 581753 := bstep (se 2 (by rfl) ⟨218157, by rfl⟩ : syracuseStep 581753 = 436315) B436315
theorem B1303019 : Blo 385764 1303019 := bstep (se 1 (by rfl) ⟨977264, by rfl⟩ : syracuseStep 1303019 = 1954529) B1954529
theorem B4416281 : Blo 385764 4416281 := bstep (se 2 (by rfl) ⟨1656105, by rfl⟩ : syracuseStep 4416281 = 3312211) B3312211
theorem B582623 : Blo 385764 582623 := bstep (se 1 (by rfl) ⟨436967, by rfl⟩ : syracuseStep 582623 = 873935) B873935
theorem B386119 : Blo 385764 386119 := bstep (se 1 (by rfl) ⟨289589, by rfl⟩ : syracuseStep 386119 = 579179) B579179
theorem B343106675 : Blo 385764 343106675 := bstep (se 1 (by rfl) ⟨257330006, by rfl⟩ : syracuseStep 343106675 = 514660013) B514660013
theorem B386919 : Blo 385764 386919 := bstep (se 1 (by rfl) ⟨290189, by rfl⟩ : syracuseStep 386919 = 580379) B580379
theorem B5662817 : Blo 385764 5662817 := bstep (se 2 (by rfl) ⟨2123556, by rfl⟩ : syracuseStep 5662817 = 4247113) B4247113
theorem B387431 : Blo 385764 387431 := bstep (se 1 (by rfl) ⟨290573, by rfl⟩ : syracuseStep 387431 = 581147) B581147
theorem B388223 : Blo 385764 388223 := bstep (se 1 (by rfl) ⟨291167, by rfl⟩ : syracuseStep 388223 = 582335) B582335
theorem B388347 : Blo 385764 388347 := bstep (se 1 (by rfl) ⟨291260, by rfl⟩ : syracuseStep 388347 = 582521) B582521
theorem B388379 : Blo 385764 388379 := bstep (se 1 (by rfl) ⟨291284, by rfl⟩ : syracuseStep 388379 = 582569) B582569
theorem B5565779 : Blo 385764 5565779 := bstep (se 1 (by rfl) ⟨4174334, by rfl⟩ : syracuseStep 5565779 = 8348669) B8348669
theorem B388559 : Blo 385764 388559 := bstep (se 1 (by rfl) ⟨291419, by rfl⟩ : syracuseStep 388559 = 582839) B582839
theorem B388839 : Blo 385764 388839 := bstep (se 1 (by rfl) ⟨291629, by rfl⟩ : syracuseStep 388839 = 583259) B583259
theorem B9597251 : Blo 385764 9597251 := bstep (se 1 (by rfl) ⟨7197938, by rfl⟩ : syracuseStep 9597251 = 14395877) B14395877
theorem B1307069 : Blo 385764 1307069 := bstep (se 3 (by rfl) ⟨245075, by rfl⟩ : syracuseStep 1307069 = 490151) B490151
theorem B11137661 : Blo 385764 11137661 := bstep (se 3 (by rfl) ⟨2088311, by rfl⟩ : syracuseStep 11137661 = 4176623) B4176623
theorem B7435799 : Blo 385764 7435799 := bstep (se 1 (by rfl) ⟨5576849, by rfl⟩ : syracuseStep 7435799 = 11153699) B11153699
theorem B372176855 : Blo 385764 372176855 := bstep (se 1 (by rfl) ⟨279132641, by rfl⟩ : syracuseStep 372176855 = 558265283) B558265283
theorem B1308959 : Blo 385764 1308959 := bstep (se 1 (by rfl) ⟨981719, by rfl⟩ : syracuseStep 1308959 = 1963439) B1963439
theorem B9042283 : Blo 385764 9042283 := bstep (se 1 (by rfl) ⟨6781712, by rfl⟩ : syracuseStep 9042283 = 13563425) B13563425
theorem B981659 : Blo 385764 981659 := bstep (se 1 (by rfl) ⟨736244, by rfl⟩ : syracuseStep 981659 = 1472489) B1472489
theorem B20217563 : Blo 385764 20217563 := bstep (se 1 (by rfl) ⟨15163172, by rfl⟩ : syracuseStep 20217563 = 30326345) B30326345
theorem B983279 : Blo 385764 983279 := bstep (se 1 (by rfl) ⟨737459, by rfl⟩ : syracuseStep 983279 = 1474919) B1474919
theorem B25592669 : Blo 385764 25592669 := bstep (se 3 (by rfl) ⟨4798625, by rfl⟩ : syracuseStep 25592669 = 9597251) B9597251
theorem B7472159 : Blo 385764 7472159 := bstep (se 1 (by rfl) ⟨5604119, by rfl⟩ : syracuseStep 7472159 = 11208239) B11208239
theorem B492799 : Blo 385764 492799 := bstep (se 1 (by rfl) ⟨369599, by rfl⟩ : syracuseStep 492799 = 739199) B739199
theorem B984575 : Blo 385764 984575 := bstep (se 1 (by rfl) ⟨738431, by rfl⟩ : syracuseStep 984575 = 1476863) B1476863
theorem B6817385 : Blo 385764 6817385 := bstep (se 2 (by rfl) ⟨2556519, by rfl⟩ : syracuseStep 6817385 = 5113039) B5113039
theorem B8456345 : Blo 385764 8456345 := bstep (se 2 (by rfl) ⟨3171129, by rfl⟩ : syracuseStep 8456345 = 6342259) B6342259
theorem B526663 : Blo 385764 526663 := bstep (se 1 (by rfl) ⟨394997, by rfl⟩ : syracuseStep 526663 = 789995) B789995
theorem B6622235 : Blo 385764 6622235 := bstep (se 1 (by rfl) ⟨4966676, by rfl⟩ : syracuseStep 6622235 = 9933353) B9933353
theorem B7081627 : Blo 385764 7081627 := bstep (se 1 (by rfl) ⟨5311220, by rfl⟩ : syracuseStep 7081627 = 10622441) B10622441
theorem B2952935 : Blo 385764 2952935 := bstep (se 1 (by rfl) ⟨2214701, by rfl⟩ : syracuseStep 2952935 = 4429403) B4429403
theorem B38342483 : Blo 385764 38342483 := bstep (se 1 (by rfl) ⟨28756862, by rfl⟩ : syracuseStep 38342483 = 57513725) B57513725
theorem B12588509 : Blo 385764 12588509 := bstep (se 3 (by rfl) ⟨2360345, by rfl⟩ : syracuseStep 12588509 = 4720691) B4720691
theorem B3775211 : Blo 385764 3775211 := bstep (se 1 (by rfl) ⟨2831408, by rfl⟩ : syracuseStep 3775211 = 5662817) B5662817
theorem B3742847 : Blo 385764 3742847 := bstep (se 1 (by rfl) ⟨2807135, by rfl⟩ : syracuseStep 3742847 = 5614271) B5614271
theorem B3710519 : Blo 385764 3710519 := bstep (se 1 (by rfl) ⟨2782889, by rfl⟩ : syracuseStep 3710519 = 5565779) B5565779
theorem B4957199 : Blo 385764 4957199 := bstep (se 1 (by rfl) ⟨3717899, by rfl⟩ : syracuseStep 4957199 = 7435799) B7435799
theorem B13478375 : Blo 385764 13478375 := bstep (se 1 (by rfl) ⟨10108781, by rfl⟩ : syracuseStep 13478375 = 20217563) B20217563
theorem B733367 : Blo 385764 733367 := bstep (se 1 (by rfl) ⟨550025, by rfl⟩ : syracuseStep 733367 = 1100051) B1100051
theorem B3879251 : Blo 385764 3879251 := bstep (se 1 (by rfl) ⟨2909438, by rfl⟩ : syracuseStep 3879251 = 5818877) B5818877
theorem B3388043 : Blo 385764 3388043 := bstep (se 1 (by rfl) ⟨2541032, by rfl⟩ : syracuseStep 3388043 = 5082065) B5082065
theorem B1651391 : Blo 385764 1651391 := bstep (se 1 (by rfl) ⟨1238543, by rfl⟩ : syracuseStep 1651391 = 2477087) B2477087
theorem B5616809 : Blo 385764 5616809 := bstep (se 2 (by rfl) ⟨2106303, by rfl⟩ : syracuseStep 5616809 = 4212607) B4212607
theorem B868679 : Blo 385764 868679 := bstep (se 1 (by rfl) ⟨651509, by rfl⟩ : syracuseStep 868679 = 1303019) B1303019
theorem B228737783 : Blo 385764 228737783 := bstep (se 1 (by rfl) ⟨171553337, by rfl⟩ : syracuseStep 228737783 = 343106675) B343106675
theorem B2475319 : Blo 385764 2475319 := bstep (se 1 (by rfl) ⟨1856489, by rfl⟩ : syracuseStep 2475319 = 3712979) B3712979
theorem B6604739 : Blo 385764 6604739 := bstep (se 1 (by rfl) ⟨4953554, by rfl⟩ : syracuseStep 6604739 = 9907109) B9907109
theorem B871379 : Blo 385764 871379 := bstep (se 1 (by rfl) ⟨653534, by rfl⟩ : syracuseStep 871379 = 1307069) B1307069
theorem B7425107 : Blo 385764 7425107 := bstep (se 1 (by rfl) ⟨5568830, by rfl⟩ : syracuseStep 7425107 = 11137661) B11137661
theorem B1101383 : Blo 385764 1101383 := bstep (se 1 (by rfl) ⟨826037, by rfl⟩ : syracuseStep 1101383 = 1652075) B1652075
theorem B872639 : Blo 385764 872639 := bstep (se 1 (by rfl) ⟨654479, by rfl⟩ : syracuseStep 872639 = 1308959) B1308959
theorem B7689775 : Blo 385764 7689775 := bstep (se 1 (by rfl) ⟨5767331, by rfl⟩ : syracuseStep 7689775 = 11534663) B11534663
theorem B874223 : Blo 385764 874223 := bstep (se 1 (by rfl) ⟨655667, by rfl⟩ : syracuseStep 874223 = 1311335) B1311335
theorem B875771 : Blo 385764 875771 := bstep (se 1 (by rfl) ⟨656828, by rfl⟩ : syracuseStep 875771 = 1313657) B1313657
theorem B875879 : Blo 385764 875879 := bstep (se 1 (by rfl) ⟨656909, by rfl⟩ : syracuseStep 875879 = 1313819) B1313819
theorem B876203 : Blo 385764 876203 := bstep (se 1 (by rfl) ⟨657152, by rfl⟩ : syracuseStep 876203 = 1314305) B1314305
theorem B582983 : Blo 385764 582983 := bstep (se 1 (by rfl) ⟨437237, by rfl⟩ : syracuseStep 582983 = 874475) B874475
theorem B387067 : Blo 385764 387067 := bstep (se 1 (by rfl) ⟨290300, by rfl⟩ : syracuseStep 387067 = 580601) B580601
theorem B1042751 : Blo 385764 1042751 := bstep (se 1 (by rfl) ⟨782063, by rfl⟩ : syracuseStep 1042751 = 1564127) B1564127
theorem B387487 : Blo 385764 387487 := bstep (se 1 (by rfl) ⟨290615, by rfl⟩ : syracuseStep 387487 = 581231) B581231
theorem B1305071 : Blo 385764 1305071 := bstep (se 1 (by rfl) ⟨978803, by rfl⟩ : syracuseStep 1305071 = 1957607) B1957607
theorem B6613487 : Blo 385764 6613487 := bstep (se 1 (by rfl) ⟨4960115, by rfl⟩ : syracuseStep 6613487 = 9920231) B9920231
theorem B387835 : Blo 385764 387835 := bstep (se 1 (by rfl) ⟨290876, by rfl⟩ : syracuseStep 387835 = 581753) B581753
theorem B1404029 : Blo 385764 1404029 := bstep (se 3 (by rfl) ⟨263255, by rfl⟩ : syracuseStep 1404029 = 526511) B526511
theorem B2944187 : Blo 385764 2944187 := bstep (se 1 (by rfl) ⟨2208140, by rfl⟩ : syracuseStep 2944187 = 4416281) B4416281
theorem B388415 : Blo 385764 388415 := bstep (se 1 (by rfl) ⟨291311, by rfl⟩ : syracuseStep 388415 = 582623) B582623
theorem B1864889 : Blo 385764 1864889 := bstep (se 2 (by rfl) ⟨699333, by rfl⟩ : syracuseStep 1864889 = 1398667) B1398667
theorem B4027751 : Blo 385764 4027751 := bstep (se 1 (by rfl) ⟨3020813, by rfl⟩ : syracuseStep 4027751 = 6041627) B6041627
theorem B489007 : Blo 385764 489007 := bstep (se 1 (by rfl) ⟨366755, by rfl⟩ : syracuseStep 489007 = 733511) B733511
theorem B12056377 : Blo 385764 12056377 := bstep (se 2 (by rfl) ⟨4521141, by rfl⟩ : syracuseStep 12056377 = 9042283) B9042283
theorem B5306633 : Blo 385764 5306633 := bstep (se 2 (by rfl) ⟨1989987, by rfl⟩ : syracuseStep 5306633 = 3979975) B3979975
theorem B248117903 : Blo 385764 248117903 := bstep (se 1 (by rfl) ⟨186088427, by rfl⟩ : syracuseStep 248117903 = 372176855) B372176855
theorem B654439 : Blo 385764 654439 := bstep (se 1 (by rfl) ⟨490829, by rfl⟩ : syracuseStep 654439 = 981659) B981659
theorem B982601 : Blo 385764 982601 := bstep (se 2 (by rfl) ⟨368475, by rfl⟩ : syracuseStep 982601 = 736951) B736951
theorem B655519 : Blo 385764 655519 := bstep (se 1 (by rfl) ⟨491639, by rfl⟩ : syracuseStep 655519 = 983279) B983279
theorem B4981439 : Blo 385764 4981439 := bstep (se 1 (by rfl) ⟨3736079, by rfl⟩ : syracuseStep 4981439 = 7472159) B7472159
theorem B656383 : Blo 385764 656383 := bstep (se 1 (by rfl) ⟨492287, by rfl⟩ : syracuseStep 656383 = 984575) B984575
theorem B5637563 : Blo 385764 5637563 := bstep (se 1 (by rfl) ⟨4228172, by rfl⟩ : syracuseStep 5637563 = 8456345) B8456345
theorem B657065 : Blo 385764 657065 := bstep (se 2 (by rfl) ⟨246399, by rfl⟩ : syracuseStep 657065 = 492799) B492799
theorem B4950071 : Blo 385764 4950071 := bstep (se 1 (by rfl) ⟨3712553, by rfl⟩ : syracuseStep 4950071 = 7425107) B7425107
theorem B1968623 : Blo 385764 1968623 := bstep (se 1 (by rfl) ⟨1476467, by rfl⟩ : syracuseStep 1968623 = 2952935) B2952935
theorem B25561655 : Blo 385764 25561655 := bstep (se 1 (by rfl) ⟨19171241, by rfl⟩ : syracuseStep 25561655 = 38342483) B38342483
theorem B8392339 : Blo 385764 8392339 := bstep (se 1 (by rfl) ⟨6294254, by rfl⟩ : syracuseStep 8392339 = 12588509) B12588509
theorem B2495231 : Blo 385764 2495231 := bstep (se 1 (by rfl) ⟨1871423, by rfl⟩ : syracuseStep 2495231 = 3742847) B3742847
theorem B9442169 : Blo 385764 9442169 := bstep (se 2 (by rfl) ⟨3540813, by rfl⟩ : syracuseStep 9442169 = 7081627) B7081627
theorem B8985583 : Blo 385764 8985583 := bstep (se 1 (by rfl) ⟨6739187, by rfl⟩ : syracuseStep 8985583 = 13478375) B13478375
theorem B3744539 : Blo 385764 3744539 := bstep (se 1 (by rfl) ⟨2808404, by rfl⟩ : syracuseStep 3744539 = 5616809) B5616809
theorem B4403159 : Blo 385764 4403159 := bstep (se 1 (by rfl) ⟨3302369, by rfl⟩ : syracuseStep 4403159 = 6604739) B6604739
theorem B734255 : Blo 385764 734255 := bstep (se 1 (by rfl) ⟨550691, by rfl⟩ : syracuseStep 734255 = 1101383) B1101383
theorem B702217 : Blo 385764 702217 := bstep (se 2 (by rfl) ⟨263331, by rfl⟩ : syracuseStep 702217 = 526663) B526663
theorem B2473679 : Blo 385764 2473679 := bstep (se 1 (by rfl) ⟨1855259, by rfl⟩ : syracuseStep 2473679 = 3710519) B3710519
theorem B870047 : Blo 385764 870047 := bstep (se 1 (by rfl) ⟨652535, by rfl⟩ : syracuseStep 870047 = 1305071) B1305071
theorem B4408991 : Blo 385764 4408991 := bstep (se 1 (by rfl) ⟨3306743, by rfl⟩ : syracuseStep 4408991 = 6613487) B6613487
theorem B936019 : Blo 385764 936019 := bstep (se 1 (by rfl) ⟨702014, by rfl⟩ : syracuseStep 936019 = 1404029) B1404029
theorem B16075169 : Blo 385764 16075169 := bstep (se 2 (by rfl) ⟨6028188, by rfl⟩ : syracuseStep 16075169 = 12056377) B12056377
theorem B1100927 : Blo 385764 1100927 := bstep (se 1 (by rfl) ⟨825695, by rfl⟩ : syracuseStep 1100927 = 1651391) B1651391
theorem B872585 : Blo 385764 872585 := bstep (se 2 (by rfl) ⟨327219, by rfl⟩ : syracuseStep 872585 = 654439) B654439
theorem B579119 : Blo 385764 579119 := bstep (se 1 (by rfl) ⟨434339, by rfl⟩ : syracuseStep 579119 = 868679) B868679
theorem B152491855 : Blo 385764 152491855 := bstep (se 1 (by rfl) ⟨114368891, by rfl⟩ : syracuseStep 152491855 = 228737783) B228737783
theorem B17061779 : Blo 385764 17061779 := bstep (se 1 (by rfl) ⟨12796334, by rfl⟩ : syracuseStep 17061779 = 25592669) B25592669
theorem B4544923 : Blo 385764 4544923 := bstep (se 1 (by rfl) ⟨3408692, by rfl⟩ : syracuseStep 4544923 = 6817385) B6817385
theorem B3300425 : Blo 385764 3300425 := bstep (se 2 (by rfl) ⟨1237659, by rfl⟩ : syracuseStep 3300425 = 2475319) B2475319
theorem B580919 : Blo 385764 580919 := bstep (se 1 (by rfl) ⟨435689, by rfl⟩ : syracuseStep 580919 = 871379) B871379
theorem B4414823 : Blo 385764 4414823 := bstep (se 1 (by rfl) ⟨3311117, by rfl⟩ : syracuseStep 4414823 = 6622235) B6622235
theorem B581759 : Blo 385764 581759 := bstep (se 1 (by rfl) ⟨436319, by rfl⟩ : syracuseStep 581759 = 872639) B872639
theorem B582815 : Blo 385764 582815 := bstep (se 1 (by rfl) ⟨437111, by rfl⟩ : syracuseStep 582815 = 874223) B874223
theorem B2516807 : Blo 385764 2516807 := bstep (se 1 (by rfl) ⟨1887605, by rfl⟩ : syracuseStep 2516807 = 3775211) B3775211
theorem B583847 : Blo 385764 583847 := bstep (se 1 (by rfl) ⟨437885, by rfl⟩ : syracuseStep 583847 = 875771) B875771
theorem B583919 : Blo 385764 583919 := bstep (se 1 (by rfl) ⟨437939, by rfl⟩ : syracuseStep 583919 = 875879) B875879
theorem B584135 : Blo 385764 584135 := bstep (se 1 (by rfl) ⟨438101, by rfl⟩ : syracuseStep 584135 = 876203) B876203
theorem B3304799 : Blo 385764 3304799 := bstep (se 1 (by rfl) ⟨2478599, by rfl⟩ : syracuseStep 3304799 = 4957199) B4957199
theorem B2780669 : Blo 385764 2780669 := bstep (se 3 (by rfl) ⟨521375, by rfl⟩ : syracuseStep 2780669 = 1042751) B1042751
theorem B388655 : Blo 385764 388655 := bstep (se 1 (by rfl) ⟨291491, by rfl⟩ : syracuseStep 388655 = 582983) B582983
theorem B652009 : Blo 385764 652009 := bstep (se 2 (by rfl) ⟨244503, by rfl⟩ : syracuseStep 652009 = 489007) B489007
theorem B10253033 : Blo 385764 10253033 := bstep (se 2 (by rfl) ⟨3844887, by rfl⟩ : syracuseStep 10253033 = 7689775) B7689775
theorem B1962791 : Blo 385764 1962791 := bstep (se 1 (by rfl) ⟨1472093, by rfl⟩ : syracuseStep 1962791 = 2944187) B2944187
theorem B488911 : Blo 385764 488911 := bstep (se 1 (by rfl) ⟨366683, by rfl⟩ : syracuseStep 488911 = 733367) B733367
theorem B2586167 : Blo 385764 2586167 := bstep (se 1 (by rfl) ⟨1939625, by rfl⟩ : syracuseStep 2586167 = 3879251) B3879251
theorem B2258695 : Blo 385764 2258695 := bstep (se 1 (by rfl) ⟨1694021, by rfl⟩ : syracuseStep 2258695 = 3388043) B3388043
theorem B1243259 : Blo 385764 1243259 := bstep (se 1 (by rfl) ⟨932444, by rfl⟩ : syracuseStep 1243259 = 1864889) B1864889
theorem B2685167 : Blo 385764 2685167 := bstep (se 1 (by rfl) ⟨2013875, by rfl⟩ : syracuseStep 2685167 = 4027751) B4027751
theorem B3537755 : Blo 385764 3537755 := bstep (se 1 (by rfl) ⟨2653316, by rfl⟩ : syracuseStep 3537755 = 5306633) B5306633
theorem B165411935 : Blo 385764 165411935 := bstep (se 1 (by rfl) ⟨124058951, by rfl⟩ : syracuseStep 165411935 = 248117903) B248117903
theorem B655067 : Blo 385764 655067 := bstep (se 1 (by rfl) ⟨491300, by rfl⟩ : syracuseStep 655067 = 982601) B982601
theorem B10716779 : Blo 385764 10716779 := bstep (se 1 (by rfl) ⟨8037584, by rfl⟩ : syracuseStep 10716779 = 16075169) B16075169
theorem B1312415 : Blo 385764 1312415 := bstep (se 1 (by rfl) ⟨984311, by rfl⟩ : syracuseStep 1312415 = 1968623) B1968623
theorem B17041103 : Blo 385764 17041103 := bstep (se 1 (by rfl) ⟨12780827, by rfl⟩ : syracuseStep 17041103 = 25561655) B25561655
theorem B6294779 : Blo 385764 6294779 := bstep (se 1 (by rfl) ⟨4721084, by rfl⟩ : syracuseStep 6294779 = 9442169) B9442169
theorem B11374519 : Blo 385764 11374519 := bstep (se 1 (by rfl) ⟨8530889, by rfl⟩ : syracuseStep 11374519 = 17061779) B17061779
theorem B2200283 : Blo 385764 2200283 := bstep (se 1 (by rfl) ⟨1650212, by rfl⟩ : syracuseStep 2200283 = 3300425) B3300425
theorem B2496359 : Blo 385764 2496359 := bstep (se 1 (by rfl) ⟨1872269, by rfl⟩ : syracuseStep 2496359 = 3744539) B3744539
theorem B1677871 : Blo 385764 1677871 := bstep (se 1 (by rfl) ⟨1258403, by rfl⟩ : syracuseStep 1677871 = 2516807) B2516807
theorem B2203199 : Blo 385764 2203199 := bstep (se 1 (by rfl) ⟨1652399, by rfl⟩ : syracuseStep 2203199 = 3304799) B3304799
theorem B828839 : Blo 385764 828839 := bstep (se 1 (by rfl) ⟨621629, by rfl⟩ : syracuseStep 828839 = 1243259) B1243259
theorem B110274623 : Blo 385764 110274623 := bstep (se 1 (by rfl) ⟨82705967, by rfl⟩ : syracuseStep 110274623 = 165411935) B165411935
theorem B1649119 : Blo 385764 1649119 := bstep (se 1 (by rfl) ⟨1236839, by rfl⟩ : syracuseStep 1649119 = 2473679) B2473679
theorem B436711 : Blo 385764 436711 := bstep (se 1 (by rfl) ⟨327533, by rfl⟩ : syracuseStep 436711 = 655067) B655067
theorem B4992101 : Blo 385764 4992101 := bstep (se 4 (by rfl) ⟨468009, by rfl⟩ : syracuseStep 4992101 = 936019) B936019
theorem B3320959 : Blo 385764 3320959 := bstep (se 1 (by rfl) ⟨2490719, by rfl⟩ : syracuseStep 3320959 = 4981439) B4981439
theorem B438043 : Blo 385764 438043 := bstep (se 1 (by rfl) ⟨328532, by rfl⟩ : syracuseStep 438043 = 657065) B657065
theorem B733951 : Blo 385764 733951 := bstep (se 1 (by rfl) ⟨550463, by rfl⟩ : syracuseStep 733951 = 1100927) B1100927
theorem B11189785 : Blo 385764 11189785 := bstep (se 2 (by rfl) ⟨4196169, by rfl⟩ : syracuseStep 11189785 = 8392339) B8392339
theorem B47923109 : Blo 385764 47923109 := bstep (se 4 (by rfl) ⟨4492791, by rfl⟩ : syracuseStep 47923109 = 8985583) B8985583
theorem B869345 : Blo 385764 869345 := bstep (se 2 (by rfl) ⟨326004, by rfl⟩ : syracuseStep 869345 = 652009) B652009
theorem B1853779 : Blo 385764 1853779 := bstep (se 1 (by rfl) ⟨1390334, by rfl⟩ : syracuseStep 1853779 = 2780669) B2780669
theorem B936289 : Blo 385764 936289 := bstep (se 2 (by rfl) ⟨351108, by rfl⟩ : syracuseStep 936289 = 702217) B702217
theorem B2935439 : Blo 385764 2935439 := bstep (se 1 (by rfl) ⟨2201579, by rfl⟩ : syracuseStep 2935439 = 4403159) B4403159
theorem B6835355 : Blo 385764 6835355 := bstep (se 1 (by rfl) ⟨5126516, by rfl⟩ : syracuseStep 6835355 = 10253033) B10253033
theorem B1724111 : Blo 385764 1724111 := bstep (se 1 (by rfl) ⟨1293083, by rfl⟩ : syracuseStep 1724111 = 2586167) B2586167
theorem B12046373 : Blo 385764 12046373 := bstep (se 4 (by rfl) ⟨1129347, by rfl⟩ : syracuseStep 12046373 = 2258695) B2258695
theorem B1790111 : Blo 385764 1790111 := bstep (se 1 (by rfl) ⟨1342583, by rfl⟩ : syracuseStep 1790111 = 2685167) B2685167
theorem B874025 : Blo 385764 874025 := bstep (se 2 (by rfl) ⟨327759, by rfl⟩ : syracuseStep 874025 = 655519) B655519
theorem B3758375 : Blo 385764 3758375 := bstep (se 1 (by rfl) ⟨2818781, by rfl⟩ : syracuseStep 3758375 = 5637563) B5637563
theorem B580031 : Blo 385764 580031 := bstep (se 1 (by rfl) ⟨435023, by rfl⟩ : syracuseStep 580031 = 870047) B870047
theorem B2939327 : Blo 385764 2939327 := bstep (se 1 (by rfl) ⟨2204495, by rfl⟩ : syracuseStep 2939327 = 4408991) B4408991
theorem B875177 : Blo 385764 875177 := bstep (se 2 (by rfl) ⟨328191, by rfl⟩ : syracuseStep 875177 = 656383) B656383
theorem B3300047 : Blo 385764 3300047 := bstep (se 1 (by rfl) ⟨2475035, by rfl⟩ : syracuseStep 3300047 = 4950071) B4950071
theorem B581723 : Blo 385764 581723 := bstep (se 1 (by rfl) ⟨436292, by rfl⟩ : syracuseStep 581723 = 872585) B872585
theorem B1663487 : Blo 385764 1663487 := bstep (se 1 (by rfl) ⟨1247615, by rfl⟩ : syracuseStep 1663487 = 2495231) B2495231
theorem B386079 : Blo 385764 386079 := bstep (se 1 (by rfl) ⟨289559, by rfl⟩ : syracuseStep 386079 = 579119) B579119
theorem B387279 : Blo 385764 387279 := bstep (se 1 (by rfl) ⟨290459, by rfl⟩ : syracuseStep 387279 = 580919) B580919
theorem B2943215 : Blo 385764 2943215 := bstep (se 1 (by rfl) ⟨2207411, by rfl⟩ : syracuseStep 2943215 = 4414823) B4414823
theorem B387839 : Blo 385764 387839 := bstep (se 1 (by rfl) ⟨290879, by rfl⟩ : syracuseStep 387839 = 581759) B581759
theorem B388543 : Blo 385764 388543 := bstep (se 1 (by rfl) ⟨291407, by rfl⟩ : syracuseStep 388543 = 582815) B582815
theorem B389231 : Blo 385764 389231 := bstep (se 1 (by rfl) ⟨291923, by rfl⟩ : syracuseStep 389231 = 583847) B583847
theorem B389279 : Blo 385764 389279 := bstep (se 1 (by rfl) ⟨291959, by rfl⟩ : syracuseStep 389279 = 583919) B583919
theorem B389423 : Blo 385764 389423 := bstep (se 1 (by rfl) ⟨292067, by rfl⟩ : syracuseStep 389423 = 584135) B584135
theorem B651881 : Blo 385764 651881 := bstep (se 2 (by rfl) ⟨244455, by rfl⟩ : syracuseStep 651881 = 488911) B488911
theorem B203322473 : Blo 385764 203322473 := bstep (se 2 (by rfl) ⟨76245927, by rfl⟩ : syracuseStep 203322473 = 152491855) B152491855
theorem B1308527 : Blo 385764 1308527 := bstep (se 1 (by rfl) ⟨981395, by rfl⟩ : syracuseStep 1308527 = 1962791) B1962791
theorem B6059897 : Blo 385764 6059897 := bstep (se 2 (by rfl) ⟨2272461, by rfl⟩ : syracuseStep 6059897 = 4544923) B4544923
theorem B489503 : Blo 385764 489503 := bstep (se 1 (by rfl) ⟨367127, by rfl⟩ : syracuseStep 489503 = 734255) B734255
theorem B2358503 : Blo 385764 2358503 := bstep (se 1 (by rfl) ⟨1768877, by rfl⟩ : syracuseStep 2358503 = 3537755) B3537755
theorem B7144519 : Blo 385764 7144519 := bstep (se 1 (by rfl) ⟨5358389, by rfl⟩ : syracuseStep 7144519 = 10716779) B10716779
theorem B4556903 : Blo 385764 4556903 := bstep (se 1 (by rfl) ⟨3417677, by rfl⟩ : syracuseStep 4556903 = 6835355) B6835355
theorem B4196519 : Blo 385764 4196519 := bstep (se 1 (by rfl) ⟨3147389, by rfl⟩ : syracuseStep 4196519 = 6294779) B6294779
theorem B1149407 : Blo 385764 1149407 := bstep (se 1 (by rfl) ⟨862055, by rfl⟩ : syracuseStep 1149407 = 1724111) B1724111
theorem B8030915 : Blo 385764 8030915 := bstep (se 1 (by rfl) ⟨6023186, by rfl⟩ : syracuseStep 8030915 = 12046373) B12046373
theorem B1248385 : Blo 385764 1248385 := bstep (se 2 (by rfl) ⟨468144, by rfl⟩ : syracuseStep 1248385 = 936289) B936289
theorem B2198825 : Blo 385764 2198825 := bstep (se 2 (by rfl) ⟨824559, by rfl⟩ : syracuseStep 2198825 = 1649119) B1649119
theorem B4427945 : Blo 385764 4427945 := bstep (se 2 (by rfl) ⟨1660479, by rfl⟩ : syracuseStep 4427945 = 3320959) B3320959
theorem B2200031 : Blo 385764 2200031 := bstep (se 1 (by rfl) ⟨1650023, by rfl⟩ : syracuseStep 2200031 = 3300047) B3300047
theorem B434587 : Blo 385764 434587 := bstep (se 1 (by rfl) ⟨325940, by rfl⟩ : syracuseStep 434587 = 651881) B651881
theorem B2237161 : Blo 385764 2237161 := bstep (se 2 (by rfl) ⟨838935, by rfl⟩ : syracuseStep 2237161 = 1677871) B1677871
theorem B4039931 : Blo 385764 4039931 := bstep (se 1 (by rfl) ⟨3029948, by rfl⟩ : syracuseStep 4039931 = 6059897) B6059897
theorem B14919713 : Blo 385764 14919713 := bstep (se 2 (by rfl) ⟨5594892, by rfl⟩ : syracuseStep 14919713 = 11189785) B11189785
theorem B2471705 : Blo 385764 2471705 := bstep (se 2 (by rfl) ⟨926889, by rfl⟩ : syracuseStep 2471705 = 1853779) B1853779
theorem B2210237 : Blo 385764 2210237 := bstep (se 3 (by rfl) ⟨414419, by rfl⟩ : syracuseStep 2210237 = 828839) B828839
theorem B2505583 : Blo 385764 2505583 := bstep (se 1 (by rfl) ⟨1879187, by rfl⟩ : syracuseStep 2505583 = 3758375) B3758375
theorem B73516415 : Blo 385764 73516415 := bstep (se 1 (by rfl) ⟨55137311, by rfl⟩ : syracuseStep 73516415 = 110274623) B110274623
theorem B3328067 : Blo 385764 3328067 := bstep (se 1 (by rfl) ⟨2496050, by rfl⟩ : syracuseStep 3328067 = 4992101) B4992101
theorem B135548315 : Blo 385764 135548315 := bstep (se 1 (by rfl) ⟨101661236, by rfl⟩ : syracuseStep 135548315 = 203322473) B203322473
theorem B872351 : Blo 385764 872351 := bstep (se 1 (by rfl) ⟨654263, by rfl⟩ : syracuseStep 872351 = 1308527) B1308527
theorem B4773629 : Blo 385764 4773629 := bstep (se 3 (by rfl) ⟨895055, by rfl⟩ : syracuseStep 4773629 = 1790111) B1790111
theorem B579563 : Blo 385764 579563 := bstep (se 1 (by rfl) ⟨434672, by rfl⟩ : syracuseStep 579563 = 869345) B869345
theorem B874943 : Blo 385764 874943 := bstep (se 1 (by rfl) ⟨656207, by rfl⟩ : syracuseStep 874943 = 1312415) B1312415
theorem B11360735 : Blo 385764 11360735 := bstep (se 1 (by rfl) ⟨8520551, by rfl⟩ : syracuseStep 11360735 = 17041103) B17041103
theorem B1956959 : Blo 385764 1956959 := bstep (se 1 (by rfl) ⟨1467719, by rfl⟩ : syracuseStep 1956959 = 2935439) B2935439
theorem B1466855 : Blo 385764 1466855 := bstep (se 1 (by rfl) ⟨1100141, by rfl⟩ : syracuseStep 1466855 = 2200283) B2200283
theorem B582281 : Blo 385764 582281 := bstep (se 2 (by rfl) ⟨218355, by rfl⟩ : syracuseStep 582281 = 436711) B436711
theorem B582683 : Blo 385764 582683 := bstep (se 1 (by rfl) ⟨437012, by rfl⟩ : syracuseStep 582683 = 874025) B874025
theorem B1664239 : Blo 385764 1664239 := bstep (se 1 (by rfl) ⟨1248179, by rfl⟩ : syracuseStep 1664239 = 2496359) B2496359
theorem B386687 : Blo 385764 386687 := bstep (se 1 (by rfl) ⟨290015, by rfl⟩ : syracuseStep 386687 = 580031) B580031
theorem B1959551 : Blo 385764 1959551 := bstep (se 1 (by rfl) ⟨1469663, by rfl⟩ : syracuseStep 1959551 = 2939327) B2939327
theorem B583451 : Blo 385764 583451 := bstep (se 1 (by rfl) ⟨437588, by rfl⟩ : syracuseStep 583451 = 875177) B875177
theorem B584057 : Blo 385764 584057 := bstep (se 2 (by rfl) ⟨219021, by rfl⟩ : syracuseStep 584057 = 438043) B438043
theorem B1468799 : Blo 385764 1468799 := bstep (se 1 (by rfl) ⟨1101599, by rfl⟩ : syracuseStep 1468799 = 2203199) B2203199
theorem B15166025 : Blo 385764 15166025 := bstep (se 2 (by rfl) ⟨5687259, by rfl⟩ : syracuseStep 15166025 = 11374519) B11374519
theorem B387815 : Blo 385764 387815 := bstep (se 1 (by rfl) ⟨290861, by rfl⟩ : syracuseStep 387815 = 581723) B581723
theorem B1305341 : Blo 385764 1305341 := bstep (se 3 (by rfl) ⟨244751, by rfl⟩ : syracuseStep 1305341 = 489503) B489503
theorem B1108991 : Blo 385764 1108991 := bstep (se 1 (by rfl) ⟨831743, by rfl⟩ : syracuseStep 1108991 = 1663487) B1663487
theorem B978601 : Blo 385764 978601 := bstep (se 2 (by rfl) ⟨366975, by rfl⟩ : syracuseStep 978601 = 733951) B733951
theorem B1962143 : Blo 385764 1962143 := bstep (se 1 (by rfl) ⟨1471607, by rfl⟩ : syracuseStep 1962143 = 2943215) B2943215
theorem B1572335 : Blo 385764 1572335 := bstep (se 1 (by rfl) ⟨1179251, by rfl⟩ : syracuseStep 1572335 = 2358503) B2358503
theorem B31948739 : Blo 385764 31948739 := bstep (se 1 (by rfl) ⟨23961554, by rfl⟩ : syracuseStep 31948739 = 47923109) B47923109
theorem B2982881 : Blo 385764 2982881 := bstep (se 2 (by rfl) ⟨1118580, by rfl⟩ : syracuseStep 2982881 = 2237161) B2237161
theorem B2951963 : Blo 385764 2951963 := bstep (se 1 (by rfl) ⟨2213972, by rfl⟩ : syracuseStep 2951963 = 4427945) B4427945
theorem B3182419 : Blo 385764 3182419 := bstep (se 1 (by rfl) ⟨2386814, by rfl⟩ : syracuseStep 3182419 = 4773629) B4773629
theorem B7573823 : Blo 385764 7573823 := bstep (se 1 (by rfl) ⟨5680367, by rfl⟩ : syracuseStep 7573823 = 11360735) B11360735
theorem B2693287 : Blo 385764 2693287 := bstep (se 1 (by rfl) ⟨2019965, by rfl⟩ : syracuseStep 2693287 = 4039931) B4039931
theorem B2957309 : Blo 385764 2957309 := bstep (se 3 (by rfl) ⟨554495, by rfl⟩ : syracuseStep 2957309 = 1108991) B1108991
theorem B1647803 : Blo 385764 1647803 := bstep (se 1 (by rfl) ⟨1235852, by rfl⟩ : syracuseStep 1647803 = 2471705) B2471705
theorem B48606965 : Blo 385764 48606965 := bstep (se 5 (by rfl) ⟨2278451, by rfl⟩ : syracuseStep 48606965 = 4556903) B4556903
theorem B2797679 : Blo 385764 2797679 := bstep (se 1 (by rfl) ⟨2098259, by rfl⟩ : syracuseStep 2797679 = 4196519) B4196519
theorem B766271 : Blo 385764 766271 := bstep (se 1 (by rfl) ⟨574703, by rfl⟩ : syracuseStep 766271 = 1149407) B1149407
theorem B5353943 : Blo 385764 5353943 := bstep (se 1 (by rfl) ⟨4015457, by rfl⟩ : syracuseStep 5353943 = 8030915) B8030915
theorem B9946475 : Blo 385764 9946475 := bstep (se 1 (by rfl) ⟨7459856, by rfl⟩ : syracuseStep 9946475 = 14919713) B14919713
theorem B10110683 : Blo 385764 10110683 := bstep (se 1 (by rfl) ⟨7583012, by rfl⟩ : syracuseStep 10110683 = 15166025) B15166025
theorem B870227 : Blo 385764 870227 := bstep (se 1 (by rfl) ⟨652670, by rfl⟩ : syracuseStep 870227 = 1305341) B1305341
theorem B579449 : Blo 385764 579449 := bstep (se 2 (by rfl) ⟨217293, by rfl⟩ : syracuseStep 579449 = 434587) B434587
theorem B2218711 : Blo 385764 2218711 := bstep (se 1 (by rfl) ⟨1664033, by rfl⟩ : syracuseStep 2218711 = 3328067) B3328067
theorem B9526025 : Blo 385764 9526025 := bstep (se 2 (by rfl) ⟨3572259, by rfl⟩ : syracuseStep 9526025 = 7144519) B7144519
theorem B2218985 : Blo 385764 2218985 := bstep (se 2 (by rfl) ⟨832119, by rfl⟩ : syracuseStep 2218985 = 1664239) B1664239
theorem B1465883 : Blo 385764 1465883 := bstep (se 1 (by rfl) ⟨1099412, by rfl⟩ : syracuseStep 1465883 = 2198825) B2198825
theorem B90365543 : Blo 385764 90365543 := bstep (se 1 (by rfl) ⟨67774157, by rfl⟩ : syracuseStep 90365543 = 135548315) B135548315
theorem B581567 : Blo 385764 581567 := bstep (se 1 (by rfl) ⟨436175, by rfl⟩ : syracuseStep 581567 = 872351) B872351
theorem B1466687 : Blo 385764 1466687 := bstep (se 1 (by rfl) ⟨1100015, by rfl⟩ : syracuseStep 1466687 = 2200031) B2200031
theorem B196043773 : Blo 385764 196043773 := bstep (se 3 (by rfl) ⟨36758207, by rfl⟩ : syracuseStep 196043773 = 73516415) B73516415
theorem B386375 : Blo 385764 386375 := bstep (se 1 (by rfl) ⟨289781, by rfl⟩ : syracuseStep 386375 = 579563) B579563
theorem B1664513 : Blo 385764 1664513 := bstep (se 2 (by rfl) ⟨624192, by rfl⟩ : syracuseStep 1664513 = 1248385) B1248385
theorem B583295 : Blo 385764 583295 := bstep (se 1 (by rfl) ⟨437471, by rfl⟩ : syracuseStep 583295 = 874943) B874943
theorem B1304639 : Blo 385764 1304639 := bstep (se 1 (by rfl) ⟨978479, by rfl⟩ : syracuseStep 1304639 = 1956959) B1956959
theorem B1304801 : Blo 385764 1304801 := bstep (se 2 (by rfl) ⟨489300, by rfl⟩ : syracuseStep 1304801 = 978601) B978601
theorem B977903 : Blo 385764 977903 := bstep (se 1 (by rfl) ⟨733427, by rfl⟩ : syracuseStep 977903 = 1466855) B1466855
theorem B388187 : Blo 385764 388187 := bstep (se 1 (by rfl) ⟨291140, by rfl⟩ : syracuseStep 388187 = 582281) B582281
theorem B388455 : Blo 385764 388455 := bstep (se 1 (by rfl) ⟨291341, by rfl⟩ : syracuseStep 388455 = 582683) B582683
theorem B1306367 : Blo 385764 1306367 := bstep (se 1 (by rfl) ⟨979775, by rfl⟩ : syracuseStep 1306367 = 1959551) B1959551
theorem B388967 : Blo 385764 388967 := bstep (se 1 (by rfl) ⟨291725, by rfl⟩ : syracuseStep 388967 = 583451) B583451
theorem B389371 : Blo 385764 389371 := bstep (se 1 (by rfl) ⟨292028, by rfl⟩ : syracuseStep 389371 = 584057) B584057
theorem B979199 : Blo 385764 979199 := bstep (se 1 (by rfl) ⟨734399, by rfl⟩ : syracuseStep 979199 = 1468799) B1468799
theorem B1308095 : Blo 385764 1308095 := bstep (se 1 (by rfl) ⟨981071, by rfl⟩ : syracuseStep 1308095 = 1962143) B1962143
theorem B3340777 : Blo 385764 3340777 := bstep (se 2 (by rfl) ⟨1252791, by rfl⟩ : syracuseStep 3340777 = 2505583) B2505583
theorem B1473491 : Blo 385764 1473491 := bstep (se 1 (by rfl) ⟨1105118, by rfl⟩ : syracuseStep 1473491 = 2210237) B2210237
theorem B1048223 : Blo 385764 1048223 := bstep (se 1 (by rfl) ⟨786167, by rfl⟩ : syracuseStep 1048223 = 1572335) B1572335
theorem B21299159 : Blo 385764 21299159 := bstep (se 1 (by rfl) ⟨15974369, by rfl⟩ : syracuseStep 21299159 = 31948739) B31948739
theorem B261391697 : Blo 385764 261391697 := bstep (se 2 (by rfl) ⟨98021886, by rfl⟩ : syracuseStep 261391697 = 196043773) B196043773
theorem B1967975 : Blo 385764 1967975 := bstep (se 1 (by rfl) ⟨1475981, by rfl⟩ : syracuseStep 1967975 = 2951963) B2951963
theorem B5049215 : Blo 385764 5049215 := bstep (se 1 (by rfl) ⟨3786911, by rfl⟩ : syracuseStep 5049215 = 7573823) B7573823
theorem B1479323 : Blo 385764 1479323 := bstep (se 1 (by rfl) ⟨1109492, by rfl⟩ : syracuseStep 1479323 = 2218985) B2218985
theorem B1971539 : Blo 385764 1971539 := bstep (se 1 (by rfl) ⟨1478654, by rfl⟩ : syracuseStep 1971539 = 2957309) B2957309
theorem B2958281 : Blo 385764 2958281 := bstep (se 2 (by rfl) ⟨1109355, by rfl⟩ : syracuseStep 2958281 = 2218711) B2218711
theorem B698815 : Blo 385764 698815 := bstep (se 1 (by rfl) ⟨524111, by rfl⟩ : syracuseStep 698815 = 1048223) B1048223
theorem B56797757 : Blo 385764 56797757 := bstep (se 3 (by rfl) ⟨10649579, by rfl⟩ : syracuseStep 56797757 = 21299159) B21299159
theorem B2043389 : Blo 385764 2043389 := bstep (se 3 (by rfl) ⟨383135, by rfl⟩ : syracuseStep 2043389 = 766271) B766271
theorem B6630983 : Blo 385764 6630983 := bstep (se 1 (by rfl) ⟨4973237, by rfl⟩ : syracuseStep 6630983 = 9946475) B9946475
theorem B60243695 : Blo 385764 60243695 := bstep (se 1 (by rfl) ⟨45182771, by rfl⟩ : syracuseStep 60243695 = 90365543) B90365543
theorem B4243225 : Blo 385764 4243225 := bstep (se 2 (by rfl) ⟨1591209, by rfl⟩ : syracuseStep 4243225 = 3182419) B3182419
theorem B1098535 : Blo 385764 1098535 := bstep (se 1 (by rfl) ⟨823901, by rfl⟩ : syracuseStep 1098535 = 1647803) B1647803
theorem B869759 : Blo 385764 869759 := bstep (se 1 (by rfl) ⟨652319, by rfl⟩ : syracuseStep 869759 = 1304639) B1304639
theorem B869867 : Blo 385764 869867 := bstep (se 1 (by rfl) ⟨652400, by rfl⟩ : syracuseStep 869867 = 1304801) B1304801
theorem B870911 : Blo 385764 870911 := bstep (se 1 (by rfl) ⟨653183, by rfl⟩ : syracuseStep 870911 = 1306367) B1306367
theorem B3591049 : Blo 385764 3591049 := bstep (se 2 (by rfl) ⟨1346643, by rfl⟩ : syracuseStep 3591049 = 2693287) B2693287
theorem B872063 : Blo 385764 872063 := bstep (se 1 (by rfl) ⟨654047, by rfl⟩ : syracuseStep 872063 = 1308095) B1308095
theorem B1988587 : Blo 385764 1988587 := bstep (se 1 (by rfl) ⟨1491440, by rfl⟩ : syracuseStep 1988587 = 2982881) B2982881
theorem B6740455 : Blo 385764 6740455 := bstep (se 1 (by rfl) ⟨5055341, by rfl⟩ : syracuseStep 6740455 = 10110683) B10110683
theorem B580151 : Blo 385764 580151 := bstep (se 1 (by rfl) ⟨435113, by rfl⟩ : syracuseStep 580151 = 870227) B870227
theorem B14277181 : Blo 385764 14277181 := bstep (se 3 (by rfl) ⟨2676971, by rfl⟩ : syracuseStep 14277181 = 5353943) B5353943
theorem B386299 : Blo 385764 386299 := bstep (se 1 (by rfl) ⟨289724, by rfl⟩ : syracuseStep 386299 = 579449) B579449
theorem B6350683 : Blo 385764 6350683 := bstep (se 1 (by rfl) ⟨4763012, by rfl⟩ : syracuseStep 6350683 = 9526025) B9526025
theorem B977255 : Blo 385764 977255 := bstep (se 1 (by rfl) ⟨732941, by rfl⟩ : syracuseStep 977255 = 1465883) B1465883
theorem B387711 : Blo 385764 387711 := bstep (se 1 (by rfl) ⟨290783, by rfl⟩ : syracuseStep 387711 = 581567) B581567
theorem B977791 : Blo 385764 977791 := bstep (se 1 (by rfl) ⟨733343, by rfl⟩ : syracuseStep 977791 = 1466687) B1466687
theorem B1109675 : Blo 385764 1109675 := bstep (se 1 (by rfl) ⟨832256, by rfl⟩ : syracuseStep 1109675 = 1664513) B1664513
theorem B388863 : Blo 385764 388863 := bstep (se 1 (by rfl) ⟨291647, by rfl⟩ : syracuseStep 388863 = 583295) B583295
theorem B651935 : Blo 385764 651935 := bstep (se 1 (by rfl) ⟨488951, by rfl⟩ : syracuseStep 651935 = 977903) B977903
theorem B32404643 : Blo 385764 32404643 := bstep (se 1 (by rfl) ⟨24303482, by rfl⟩ : syracuseStep 32404643 = 48606965) B48606965
theorem B1865119 : Blo 385764 1865119 := bstep (se 1 (by rfl) ⟨1398839, by rfl⟩ : syracuseStep 1865119 = 2797679) B2797679
theorem B652799 : Blo 385764 652799 := bstep (se 1 (by rfl) ⟨489599, by rfl⟩ : syracuseStep 652799 = 979199) B979199
theorem B4454369 : Blo 385764 4454369 := bstep (se 2 (by rfl) ⟨1670388, by rfl⟩ : syracuseStep 4454369 = 3340777) B3340777
theorem B982327 : Blo 385764 982327 := bstep (se 1 (by rfl) ⟨736745, by rfl⟩ : syracuseStep 982327 = 1473491) B1473491
theorem B174261131 : Blo 385764 174261131 := bstep (se 1 (by rfl) ⟨130695848, by rfl⟩ : syracuseStep 174261131 = 261391697) B261391697
theorem B1311983 : Blo 385764 1311983 := bstep (se 1 (by rfl) ⟨983987, by rfl⟩ : syracuseStep 1311983 = 1967975) B1967975
theorem B986215 : Blo 385764 986215 := bstep (se 1 (by rfl) ⟨739661, by rfl⟩ : syracuseStep 986215 = 1479323) B1479323
theorem B1314359 : Blo 385764 1314359 := bstep (se 1 (by rfl) ⟨985769, by rfl⟩ : syracuseStep 1314359 = 1971539) B1971539
theorem B4788065 : Blo 385764 4788065 := bstep (se 2 (by rfl) ⟨1795524, by rfl⟩ : syracuseStep 4788065 = 3591049) B3591049
theorem B1972187 : Blo 385764 1972187 := bstep (se 1 (by rfl) ⟨1479140, by rfl⟩ : syracuseStep 1972187 = 2958281) B2958281
theorem B434623 : Blo 385764 434623 := bstep (se 1 (by rfl) ⟨325967, by rfl⟩ : syracuseStep 434623 = 651935) B651935
theorem B8987273 : Blo 385764 8987273 := bstep (se 2 (by rfl) ⟨3370227, by rfl⟩ : syracuseStep 8987273 = 6740455) B6740455
theorem B21603095 : Blo 385764 21603095 := bstep (se 1 (by rfl) ⟨16202321, by rfl⟩ : syracuseStep 21603095 = 32404643) B32404643
theorem B435199 : Blo 385764 435199 := bstep (se 1 (by rfl) ⟨326399, by rfl⟩ : syracuseStep 435199 = 652799) B652799
theorem B5449037 : Blo 385764 5449037 := bstep (se 3 (by rfl) ⟨1021694, by rfl⟩ : syracuseStep 5449037 = 2043389) B2043389
theorem B8467577 : Blo 385764 8467577 := bstep (se 2 (by rfl) ⟨3175341, by rfl⟩ : syracuseStep 8467577 = 6350683) B6350683
theorem B931753 : Blo 385764 931753 := bstep (se 2 (by rfl) ⟨349407, by rfl⟩ : syracuseStep 931753 = 698815) B698815
theorem B37865171 : Blo 385764 37865171 := bstep (se 1 (by rfl) ⟨28398878, by rfl⟩ : syracuseStep 37865171 = 56797757) B56797757
theorem B739783 : Blo 385764 739783 := bstep (se 1 (by rfl) ⟨554837, by rfl⟩ : syracuseStep 739783 = 1109675) B1109675
theorem B2969579 : Blo 385764 2969579 := bstep (se 1 (by rfl) ⟨2227184, by rfl⟩ : syracuseStep 2969579 = 4454369) B4454369
theorem B5657633 : Blo 385764 5657633 := bstep (se 2 (by rfl) ⟨2121612, by rfl⟩ : syracuseStep 5657633 = 4243225) B4243225
theorem B40162463 : Blo 385764 40162463 := bstep (se 1 (by rfl) ⟨30121847, by rfl⟩ : syracuseStep 40162463 = 60243695) B60243695
theorem B579839 : Blo 385764 579839 := bstep (se 1 (by rfl) ⟨434879, by rfl⟩ : syracuseStep 579839 = 869759) B869759
theorem B579911 : Blo 385764 579911 := bstep (se 1 (by rfl) ⟨434933, by rfl⟩ : syracuseStep 579911 = 869867) B869867
theorem B1464713 : Blo 385764 1464713 := bstep (se 2 (by rfl) ⟨549267, by rfl⟩ : syracuseStep 1464713 = 1098535) B1098535
theorem B580607 : Blo 385764 580607 := bstep (se 1 (by rfl) ⟨435455, by rfl⟩ : syracuseStep 580607 = 870911) B870911
theorem B3366143 : Blo 385764 3366143 := bstep (se 1 (by rfl) ⟨2524607, by rfl⟩ : syracuseStep 3366143 = 5049215) B5049215
theorem B581375 : Blo 385764 581375 := bstep (se 1 (by rfl) ⟨436031, by rfl⟩ : syracuseStep 581375 = 872063) B872063
theorem B1303721 : Blo 385764 1303721 := bstep (se 2 (by rfl) ⟨488895, by rfl⟩ : syracuseStep 1303721 = 977791) B977791
theorem B386767 : Blo 385764 386767 := bstep (se 1 (by rfl) ⟨290075, by rfl⟩ : syracuseStep 386767 = 580151) B580151
theorem B651503 : Blo 385764 651503 := bstep (se 1 (by rfl) ⟨488627, by rfl⟩ : syracuseStep 651503 = 977255) B977255
theorem B2486825 : Blo 385764 2486825 := bstep (se 2 (by rfl) ⟨932559, by rfl⟩ : syracuseStep 2486825 = 1865119) B1865119
theorem B4420655 : Blo 385764 4420655 := bstep (se 1 (by rfl) ⟨3315491, by rfl⟩ : syracuseStep 4420655 = 6630983) B6630983
theorem B2651449 : Blo 385764 2651449 := bstep (se 2 (by rfl) ⟨994293, by rfl⟩ : syracuseStep 2651449 = 1988587) B1988587
theorem B19036241 : Blo 385764 19036241 := bstep (se 2 (by rfl) ⟨7138590, by rfl⟩ : syracuseStep 19036241 = 14277181) B14277181
theorem B1309769 : Blo 385764 1309769 := bstep (se 2 (by rfl) ⟨491163, by rfl⟩ : syracuseStep 1309769 = 982327) B982327
theorem B986377 : Blo 385764 986377 := bstep (se 2 (by rfl) ⟨369891, by rfl⟩ : syracuseStep 986377 = 739783) B739783
theorem B3771755 : Blo 385764 3771755 := bstep (se 1 (by rfl) ⟨2828816, by rfl⟩ : syracuseStep 3771755 = 5657633) B5657633
theorem B26774975 : Blo 385764 26774975 := bstep (se 1 (by rfl) ⟨20081231, by rfl⟩ : syracuseStep 26774975 = 40162463) B40162463
theorem B1314791 : Blo 385764 1314791 := bstep (se 1 (by rfl) ⟨986093, by rfl⟩ : syracuseStep 1314791 = 1972187) B1972187
theorem B1314953 : Blo 385764 1314953 := bstep (se 2 (by rfl) ⟨493107, by rfl⟩ : syracuseStep 1314953 = 986215) B986215
theorem B434335 : Blo 385764 434335 := bstep (se 1 (by rfl) ⟨325751, by rfl⟩ : syracuseStep 434335 = 651503) B651503
theorem B5645051 : Blo 385764 5645051 := bstep (se 1 (by rfl) ⟨4233788, by rfl⟩ : syracuseStep 5645051 = 8467577) B8467577
theorem B12690827 : Blo 385764 12690827 := bstep (se 1 (by rfl) ⟨9518120, by rfl⟩ : syracuseStep 12690827 = 19036241) B19036241
theorem B116174087 : Blo 385764 116174087 := bstep (se 1 (by rfl) ⟨87130565, by rfl⟩ : syracuseStep 116174087 = 174261131) B174261131
theorem B25243447 : Blo 385764 25243447 := bstep (se 1 (by rfl) ⟨18932585, by rfl⟩ : syracuseStep 25243447 = 37865171) B37865171
theorem B3192043 : Blo 385764 3192043 := bstep (se 1 (by rfl) ⟨2394032, by rfl⟩ : syracuseStep 3192043 = 4788065) B4788065
theorem B14530765 : Blo 385764 14530765 := bstep (se 3 (by rfl) ⟨2724518, by rfl⟩ : syracuseStep 14530765 = 5449037) B5449037
theorem B2244095 : Blo 385764 2244095 := bstep (se 1 (by rfl) ⟨1683071, by rfl⟩ : syracuseStep 2244095 = 3366143) B3366143
theorem B14402063 : Blo 385764 14402063 := bstep (se 1 (by rfl) ⟨10801547, by rfl⟩ : syracuseStep 14402063 = 21603095) B21603095
theorem B869147 : Blo 385764 869147 := bstep (se 1 (by rfl) ⟨651860, by rfl⟩ : syracuseStep 869147 = 1303721) B1303721
theorem B1657883 : Blo 385764 1657883 := bstep (se 1 (by rfl) ⟨1243412, by rfl⟩ : syracuseStep 1657883 = 2486825) B2486825
theorem B873179 : Blo 385764 873179 := bstep (se 1 (by rfl) ⟨654884, by rfl⟩ : syracuseStep 873179 = 1309769) B1309769
theorem B7918877 : Blo 385764 7918877 := bstep (se 3 (by rfl) ⟨1484789, by rfl⟩ : syracuseStep 7918877 = 2969579) B2969579
theorem B579497 : Blo 385764 579497 := bstep (se 2 (by rfl) ⟨217311, by rfl⟩ : syracuseStep 579497 = 434623) B434623
theorem B874655 : Blo 385764 874655 := bstep (se 1 (by rfl) ⟨655991, by rfl⟩ : syracuseStep 874655 = 1311983) B1311983
theorem B580265 : Blo 385764 580265 := bstep (se 2 (by rfl) ⟨217599, by rfl⟩ : syracuseStep 580265 = 435199) B435199
theorem B876239 : Blo 385764 876239 := bstep (se 1 (by rfl) ⟨657179, by rfl⟩ : syracuseStep 876239 = 1314359) B1314359
theorem B386559 : Blo 385764 386559 := bstep (se 1 (by rfl) ⟨289919, by rfl⟩ : syracuseStep 386559 = 579839) B579839
theorem B386607 : Blo 385764 386607 := bstep (se 1 (by rfl) ⟨289955, by rfl⟩ : syracuseStep 386607 = 579911) B579911
theorem B976475 : Blo 385764 976475 := bstep (se 1 (by rfl) ⟨732356, by rfl⟩ : syracuseStep 976475 = 1464713) B1464713
theorem B387071 : Blo 385764 387071 := bstep (se 1 (by rfl) ⟨290303, by rfl⟩ : syracuseStep 387071 = 580607) B580607
theorem B387583 : Blo 385764 387583 := bstep (se 1 (by rfl) ⟨290687, by rfl⟩ : syracuseStep 387583 = 581375) B581375
theorem B5991515 : Blo 385764 5991515 := bstep (se 1 (by rfl) ⟨4493636, by rfl⟩ : syracuseStep 5991515 = 8987273) B8987273
theorem B3535265 : Blo 385764 3535265 := bstep (se 2 (by rfl) ⟨1325724, by rfl⟩ : syracuseStep 3535265 = 2651449) B2651449
theorem B1242337 : Blo 385764 1242337 := bstep (se 2 (by rfl) ⟨465876, by rfl⟩ : syracuseStep 1242337 = 931753) B931753
theorem B2947103 : Blo 385764 2947103 := bstep (se 1 (by rfl) ⟨2210327, by rfl⟩ : syracuseStep 2947103 = 4420655) B4420655
theorem B9601375 : Blo 385764 9601375 := bstep (se 1 (by rfl) ⟨7201031, by rfl⟩ : syracuseStep 9601375 = 14402063) B14402063
theorem B5279251 : Blo 385764 5279251 := bstep (se 1 (by rfl) ⟨3959438, by rfl⟩ : syracuseStep 5279251 = 7918877) B7918877
theorem B1315169 : Blo 385764 1315169 := bstep (se 2 (by rfl) ⟨493188, by rfl⟩ : syracuseStep 1315169 = 986377) B986377
theorem B33657929 : Blo 385764 33657929 := bstep (se 2 (by rfl) ⟨12621723, by rfl⟩ : syracuseStep 33657929 = 25243447) B25243447
theorem B8460551 : Blo 385764 8460551 := bstep (se 1 (by rfl) ⟨6345413, by rfl⟩ : syracuseStep 8460551 = 12690827) B12690827
theorem B19374353 : Blo 385764 19374353 := bstep (se 2 (by rfl) ⟨7265382, by rfl⟩ : syracuseStep 19374353 = 14530765) B14530765
theorem B1656449 : Blo 385764 1656449 := bstep (se 2 (by rfl) ⟨621168, by rfl⟩ : syracuseStep 1656449 = 1242337) B1242337
theorem B77449391 : Blo 385764 77449391 := bstep (se 1 (by rfl) ⟨58087043, by rfl⟩ : syracuseStep 77449391 = 116174087) B116174087
theorem B1496063 : Blo 385764 1496063 := bstep (se 1 (by rfl) ⟨1122047, by rfl⟩ : syracuseStep 1496063 = 2244095) B2244095
theorem B579113 : Blo 385764 579113 := bstep (se 2 (by rfl) ⟨217167, by rfl⟩ : syracuseStep 579113 = 434335) B434335
theorem B579431 : Blo 385764 579431 := bstep (se 1 (by rfl) ⟨434573, by rfl⟩ : syracuseStep 579431 = 869147) B869147
theorem B9427373 : Blo 385764 9427373 := bstep (se 3 (by rfl) ⟨1767632, by rfl⟩ : syracuseStep 9427373 = 3535265) B3535265
theorem B1105255 : Blo 385764 1105255 := bstep (se 1 (by rfl) ⟨828941, by rfl⟩ : syracuseStep 1105255 = 1657883) B1657883
theorem B2514503 : Blo 385764 2514503 := bstep (se 1 (by rfl) ⟨1885877, by rfl⟩ : syracuseStep 2514503 = 3771755) B3771755
theorem B17849983 : Blo 385764 17849983 := bstep (se 1 (by rfl) ⟨13387487, by rfl⟩ : syracuseStep 17849983 = 26774975) B26774975
theorem B876527 : Blo 385764 876527 := bstep (se 1 (by rfl) ⟨657395, by rfl⟩ : syracuseStep 876527 = 1314791) B1314791
theorem B876635 : Blo 385764 876635 := bstep (se 1 (by rfl) ⟨657476, by rfl⟩ : syracuseStep 876635 = 1314953) B1314953
theorem B582119 : Blo 385764 582119 := bstep (se 1 (by rfl) ⟨436589, by rfl⟩ : syracuseStep 582119 = 873179) B873179
theorem B386331 : Blo 385764 386331 := bstep (se 1 (by rfl) ⟨289748, by rfl⟩ : syracuseStep 386331 = 579497) B579497
theorem B583103 : Blo 385764 583103 := bstep (se 1 (by rfl) ⟨437327, by rfl⟩ : syracuseStep 583103 = 874655) B874655
theorem B386843 : Blo 385764 386843 := bstep (se 1 (by rfl) ⟨290132, by rfl⟩ : syracuseStep 386843 = 580265) B580265
theorem B584159 : Blo 385764 584159 := bstep (se 1 (by rfl) ⟨438119, by rfl⟩ : syracuseStep 584159 = 876239) B876239
theorem B3763367 : Blo 385764 3763367 := bstep (se 1 (by rfl) ⟨2822525, by rfl⟩ : syracuseStep 3763367 = 5645051) B5645051
theorem B650983 : Blo 385764 650983 := bstep (se 1 (by rfl) ⟨488237, by rfl⟩ : syracuseStep 650983 = 976475) B976475
theorem B4256057 : Blo 385764 4256057 := bstep (se 2 (by rfl) ⟨1596021, by rfl⟩ : syracuseStep 4256057 = 3192043) B3192043
theorem B3994343 : Blo 385764 3994343 := bstep (se 1 (by rfl) ⟨2995757, by rfl⟩ : syracuseStep 3994343 = 5991515) B5991515
theorem B1964735 : Blo 385764 1964735 := bstep (se 1 (by rfl) ⟨1473551, by rfl⟩ : syracuseStep 1964735 = 2947103) B2947103
theorem B5640367 : Blo 385764 5640367 := bstep (se 1 (by rfl) ⟨4230275, by rfl⟩ : syracuseStep 5640367 = 8460551) B8460551
theorem B12916235 : Blo 385764 12916235 := bstep (se 1 (by rfl) ⟨9687176, by rfl⟩ : syracuseStep 12916235 = 19374353) B19374353
theorem B2662895 : Blo 385764 2662895 := bstep (se 1 (by rfl) ⟨1997171, by rfl⟩ : syracuseStep 2662895 = 3994343) B3994343
theorem B23799977 : Blo 385764 23799977 := bstep (se 2 (by rfl) ⟨8924991, by rfl⟩ : syracuseStep 23799977 = 17849983) B17849983
theorem B997375 : Blo 385764 997375 := bstep (se 1 (by rfl) ⟨748031, by rfl⟩ : syracuseStep 997375 = 1496063) B1496063
theorem B867977 : Blo 385764 867977 := bstep (se 2 (by rfl) ⟨325491, by rfl⟩ : syracuseStep 867977 = 650983) B650983
theorem B2508911 : Blo 385764 2508911 := bstep (se 1 (by rfl) ⟨1881683, by rfl⟩ : syracuseStep 2508911 = 3763367) B3763367
theorem B2837371 : Blo 385764 2837371 := bstep (se 1 (by rfl) ⟨2128028, by rfl⟩ : syracuseStep 2837371 = 4256057) B4256057
theorem B6705341 : Blo 385764 6705341 := bstep (se 3 (by rfl) ⟨1257251, by rfl⟩ : syracuseStep 6705341 = 2514503) B2514503
theorem B12801833 : Blo 385764 12801833 := bstep (se 2 (by rfl) ⟨4800687, by rfl⟩ : syracuseStep 12801833 = 9601375) B9601375
theorem B1104299 : Blo 385764 1104299 := bstep (se 1 (by rfl) ⟨828224, by rfl⟩ : syracuseStep 1104299 = 1656449) B1656449
theorem B51632927 : Blo 385764 51632927 := bstep (se 1 (by rfl) ⟨38724695, by rfl⟩ : syracuseStep 51632927 = 77449391) B77449391
theorem B876779 : Blo 385764 876779 := bstep (se 1 (by rfl) ⟨657584, by rfl⟩ : syracuseStep 876779 = 1315169) B1315169
theorem B22438619 : Blo 385764 22438619 := bstep (se 1 (by rfl) ⟨16828964, by rfl⟩ : syracuseStep 22438619 = 33657929) B33657929
theorem B386075 : Blo 385764 386075 := bstep (se 1 (by rfl) ⟨289556, by rfl⟩ : syracuseStep 386075 = 579113) B579113
theorem B386287 : Blo 385764 386287 := bstep (se 1 (by rfl) ⟨289715, by rfl⟩ : syracuseStep 386287 = 579431) B579431
theorem B6284915 : Blo 385764 6284915 := bstep (se 1 (by rfl) ⟨4713686, by rfl⟩ : syracuseStep 6284915 = 9427373) B9427373
theorem B7039001 : Blo 385764 7039001 := bstep (se 2 (by rfl) ⟨2639625, by rfl⟩ : syracuseStep 7039001 = 5279251) B5279251
theorem B584351 : Blo 385764 584351 := bstep (se 1 (by rfl) ⟨438263, by rfl⟩ : syracuseStep 584351 = 876527) B876527
theorem B584423 : Blo 385764 584423 := bstep (se 1 (by rfl) ⟨438317, by rfl⟩ : syracuseStep 584423 = 876635) B876635
theorem B388079 : Blo 385764 388079 := bstep (se 1 (by rfl) ⟨291059, by rfl⟩ : syracuseStep 388079 = 582119) B582119
theorem B388735 : Blo 385764 388735 := bstep (se 1 (by rfl) ⟨291551, by rfl⟩ : syracuseStep 388735 = 583103) B583103
theorem B389439 : Blo 385764 389439 := bstep (se 1 (by rfl) ⟨292079, by rfl⟩ : syracuseStep 389439 = 584159) B584159
theorem B1309823 : Blo 385764 1309823 := bstep (se 1 (by rfl) ⟨982367, by rfl⟩ : syracuseStep 1309823 = 1964735) B1964735
theorem B1473673 : Blo 385764 1473673 := bstep (se 2 (by rfl) ⟨552627, by rfl⟩ : syracuseStep 1473673 = 1105255) B1105255
theorem B1672607 : Blo 385764 1672607 := bstep (se 1 (by rfl) ⟨1254455, by rfl⟩ : syracuseStep 1672607 = 2508911) B2508911
theorem B4692667 : Blo 385764 4692667 := bstep (se 1 (by rfl) ⟨3519500, by rfl⟩ : syracuseStep 4692667 = 7039001) B7039001
theorem B15866651 : Blo 385764 15866651 := bstep (se 1 (by rfl) ⟨11899988, by rfl⟩ : syracuseStep 15866651 = 23799977) B23799977
theorem B4470227 : Blo 385764 4470227 := bstep (se 1 (by rfl) ⟨3352670, by rfl⟩ : syracuseStep 4470227 = 6705341) B6705341
theorem B3783161 : Blo 385764 3783161 := bstep (se 2 (by rfl) ⟨1418685, by rfl⟩ : syracuseStep 3783161 = 2837371) B2837371
theorem B8534555 : Blo 385764 8534555 := bstep (se 1 (by rfl) ⟨6400916, by rfl⟩ : syracuseStep 8534555 = 12801833) B12801833
theorem B736199 : Blo 385764 736199 := bstep (se 1 (by rfl) ⟨552149, by rfl⟩ : syracuseStep 736199 = 1104299) B1104299
theorem B34421951 : Blo 385764 34421951 := bstep (se 1 (by rfl) ⟨25816463, by rfl⟩ : syracuseStep 34421951 = 51632927) B51632927
theorem B7520489 : Blo 385764 7520489 := bstep (se 2 (by rfl) ⟨2820183, by rfl⟩ : syracuseStep 7520489 = 5640367) B5640367
theorem B14959079 : Blo 385764 14959079 := bstep (se 1 (by rfl) ⟨11219309, by rfl⟩ : syracuseStep 14959079 = 22438619) B22438619
theorem B1329833 : Blo 385764 1329833 := bstep (se 2 (by rfl) ⟨498687, by rfl⟩ : syracuseStep 1329833 = 997375) B997375
theorem B873215 : Blo 385764 873215 := bstep (se 1 (by rfl) ⟨654911, by rfl⟩ : syracuseStep 873215 = 1309823) B1309823
theorem B578651 : Blo 385764 578651 := bstep (se 1 (by rfl) ⟨433988, by rfl⟩ : syracuseStep 578651 = 867977) B867977
theorem B7101053 : Blo 385764 7101053 := bstep (se 3 (by rfl) ⟨1331447, by rfl⟩ : syracuseStep 7101053 = 2662895) B2662895
theorem B8610823 : Blo 385764 8610823 := bstep (se 1 (by rfl) ⟨6458117, by rfl⟩ : syracuseStep 8610823 = 12916235) B12916235
theorem B584519 : Blo 385764 584519 := bstep (se 1 (by rfl) ⟨438389, by rfl⟩ : syracuseStep 584519 = 876779) B876779
theorem B4189943 : Blo 385764 4189943 := bstep (se 1 (by rfl) ⟨3142457, by rfl⟩ : syracuseStep 4189943 = 6284915) B6284915
theorem B389567 : Blo 385764 389567 := bstep (se 1 (by rfl) ⟨292175, by rfl⟩ : syracuseStep 389567 = 584351) B584351
theorem B389615 : Blo 385764 389615 := bstep (se 1 (by rfl) ⟨292211, by rfl⟩ : syracuseStep 389615 = 584423) B584423
theorem B1964897 : Blo 385764 1964897 := bstep (se 2 (by rfl) ⟨736836, by rfl⟩ : syracuseStep 1964897 = 1473673) B1473673
theorem B5013659 : Blo 385764 5013659 := bstep (se 1 (by rfl) ⟨3760244, by rfl⟩ : syracuseStep 5013659 = 7520489) B7520489
theorem B886555 : Blo 385764 886555 := bstep (se 1 (by rfl) ⟨664916, by rfl⟩ : syracuseStep 886555 = 1329833) B1329833
theorem B4460285 : Blo 385764 4460285 := bstep (se 3 (by rfl) ⟨836303, by rfl⟩ : syracuseStep 4460285 = 1672607) B1672607
theorem B42311069 : Blo 385764 42311069 := bstep (se 3 (by rfl) ⟨7933325, by rfl⟩ : syracuseStep 42311069 = 15866651) B15866651
theorem B2793295 : Blo 385764 2793295 := bstep (se 1 (by rfl) ⟨2094971, by rfl⟩ : syracuseStep 2793295 = 4189943) B4189943
theorem B22947967 : Blo 385764 22947967 := bstep (se 1 (by rfl) ⟨17210975, by rfl⟩ : syracuseStep 22947967 = 34421951) B34421951
theorem B9972719 : Blo 385764 9972719 := bstep (se 1 (by rfl) ⟨7479539, by rfl⟩ : syracuseStep 9972719 = 14959079) B14959079
theorem B11481097 : Blo 385764 11481097 := bstep (se 2 (by rfl) ⟨4305411, by rfl⟩ : syracuseStep 11481097 = 8610823) B8610823
theorem B4734035 : Blo 385764 4734035 := bstep (se 1 (by rfl) ⟨3550526, by rfl⟩ : syracuseStep 4734035 = 7101053) B7101053
theorem B5689703 : Blo 385764 5689703 := bstep (se 1 (by rfl) ⟨4267277, by rfl⟩ : syracuseStep 5689703 = 8534555) B8534555
theorem B582143 : Blo 385764 582143 := bstep (se 1 (by rfl) ⟨436607, by rfl⟩ : syracuseStep 582143 = 873215) B873215
theorem B385767 : Blo 385764 385767 := bstep (se 1 (by rfl) ⟨289325, by rfl⟩ : syracuseStep 385767 = 578651) B578651
theorem B389679 : Blo 385764 389679 := bstep (se 1 (by rfl) ⟨292259, by rfl⟩ : syracuseStep 389679 = 584519) B584519
theorem B6256889 : Blo 385764 6256889 := bstep (se 2 (by rfl) ⟨2346333, by rfl⟩ : syracuseStep 6256889 = 4692667) B4692667
theorem B2980151 : Blo 385764 2980151 := bstep (se 1 (by rfl) ⟨2235113, by rfl⟩ : syracuseStep 2980151 = 4470227) B4470227
theorem B2522107 : Blo 385764 2522107 := bstep (se 1 (by rfl) ⟨1891580, by rfl⟩ : syracuseStep 2522107 = 3783161) B3783161
theorem B1309931 : Blo 385764 1309931 := bstep (se 1 (by rfl) ⟨982448, by rfl⟩ : syracuseStep 1309931 = 1964897) B1964897
theorem B490799 : Blo 385764 490799 := bstep (se 1 (by rfl) ⟨368099, by rfl⟩ : syracuseStep 490799 = 736199) B736199
theorem B3342439 : Blo 385764 3342439 := bstep (se 1 (by rfl) ⟨2506829, by rfl⟩ : syracuseStep 3342439 = 5013659) B5013659
theorem B122389157 : Blo 385764 122389157 := bstep (se 4 (by rfl) ⟨11473983, by rfl⟩ : syracuseStep 122389157 = 22947967) B22947967
theorem B15172541 : Blo 385764 15172541 := bstep (se 3 (by rfl) ⟨2844851, by rfl⟩ : syracuseStep 15172541 = 5689703) B5689703
theorem B15308129 : Blo 385764 15308129 := bstep (se 2 (by rfl) ⟨5740548, by rfl⟩ : syracuseStep 15308129 = 11481097) B11481097
theorem B4728293 : Blo 385764 4728293 := bstep (se 4 (by rfl) ⟨443277, by rfl⟩ : syracuseStep 4728293 = 886555) B886555
theorem B4171259 : Blo 385764 4171259 := bstep (se 1 (by rfl) ⟨3128444, by rfl⟩ : syracuseStep 4171259 = 6256889) B6256889
theorem B3156023 : Blo 385764 3156023 := bstep (se 1 (by rfl) ⟨2367017, by rfl⟩ : syracuseStep 3156023 = 4734035) B4734035
theorem B3362809 : Blo 385764 3362809 := bstep (se 2 (by rfl) ⟨1261053, by rfl⟩ : syracuseStep 3362809 = 2522107) B2522107
theorem B1986767 : Blo 385764 1986767 := bstep (se 1 (by rfl) ⟨1490075, by rfl⟩ : syracuseStep 1986767 = 2980151) B2980151
theorem B873287 : Blo 385764 873287 := bstep (se 1 (by rfl) ⟨654965, by rfl⟩ : syracuseStep 873287 = 1309931) B1309931
theorem B3724393 : Blo 385764 3724393 := bstep (se 2 (by rfl) ⟨1396647, by rfl⟩ : syracuseStep 3724393 = 2793295) B2793295
theorem B2973523 : Blo 385764 2973523 := bstep (se 1 (by rfl) ⟨2230142, by rfl⟩ : syracuseStep 2973523 = 4460285) B4460285
theorem B28207379 : Blo 385764 28207379 := bstep (se 1 (by rfl) ⟨21155534, by rfl⟩ : syracuseStep 28207379 = 42311069) B42311069
theorem B388095 : Blo 385764 388095 := bstep (se 1 (by rfl) ⟨291071, by rfl⟩ : syracuseStep 388095 = 582143) B582143
theorem B6648479 : Blo 385764 6648479 := bstep (se 1 (by rfl) ⟨4986359, by rfl⟩ : syracuseStep 6648479 = 9972719) B9972719
theorem B1308797 : Blo 385764 1308797 := bstep (se 3 (by rfl) ⟨245399, by rfl⟩ : syracuseStep 1308797 = 490799) B490799
theorem B4456585 : Blo 385764 4456585 := bstep (se 2 (by rfl) ⟨1671219, by rfl⟩ : syracuseStep 4456585 = 3342439) B3342439
theorem B81592771 : Blo 385764 81592771 := bstep (se 1 (by rfl) ⟨61194578, by rfl⟩ : syracuseStep 81592771 = 122389157) B122389157
theorem B3152195 : Blo 385764 3152195 := bstep (se 1 (by rfl) ⟨2364146, by rfl⟩ : syracuseStep 3152195 = 4728293) B4728293
theorem B2104015 : Blo 385764 2104015 := bstep (se 1 (by rfl) ⟨1578011, by rfl⟩ : syracuseStep 2104015 = 3156023) B3156023
theorem B4432319 : Blo 385764 4432319 := bstep (se 1 (by rfl) ⟨3324239, by rfl⟩ : syracuseStep 4432319 = 6648479) B6648479
theorem B1324511 : Blo 385764 1324511 := bstep (se 1 (by rfl) ⟨993383, by rfl⟩ : syracuseStep 1324511 = 1986767) B1986767
theorem B4965857 : Blo 385764 4965857 := bstep (se 2 (by rfl) ⟨1862196, by rfl⟩ : syracuseStep 4965857 = 3724393) B3724393
theorem B872531 : Blo 385764 872531 := bstep (se 1 (by rfl) ⟨654398, by rfl⟩ : syracuseStep 872531 = 1308797) B1308797
theorem B10115027 : Blo 385764 10115027 := bstep (se 1 (by rfl) ⟨7586270, by rfl⟩ : syracuseStep 10115027 = 15172541) B15172541
theorem B582191 : Blo 385764 582191 := bstep (se 1 (by rfl) ⟨436643, by rfl⟩ : syracuseStep 582191 = 873287) B873287
theorem B40821677 : Blo 385764 40821677 := bstep (se 3 (by rfl) ⟨7654064, by rfl⟩ : syracuseStep 40821677 = 15308129) B15308129
theorem B4483745 : Blo 385764 4483745 := bstep (se 2 (by rfl) ⟨1681404, by rfl⟩ : syracuseStep 4483745 = 3362809) B3362809
theorem B2780839 : Blo 385764 2780839 := bstep (se 1 (by rfl) ⟨2085629, by rfl⟩ : syracuseStep 2780839 = 4171259) B4171259
theorem B18804919 : Blo 385764 18804919 := bstep (se 1 (by rfl) ⟨14103689, by rfl⟩ : syracuseStep 18804919 = 28207379) B28207379
theorem B3964697 : Blo 385764 3964697 := bstep (se 2 (by rfl) ⟨1486761, by rfl⟩ : syracuseStep 3964697 = 2973523) B2973523
theorem B108790361 : Blo 385764 108790361 := bstep (se 2 (by rfl) ⟨40796385, by rfl⟩ : syracuseStep 108790361 = 81592771) B81592771
theorem B3310571 : Blo 385764 3310571 := bstep (se 1 (by rfl) ⟨2482928, by rfl⟩ : syracuseStep 3310571 = 4965857) B4965857
theorem B2101463 : Blo 385764 2101463 := bstep (se 1 (by rfl) ⟨1576097, by rfl⟩ : syracuseStep 2101463 = 3152195) B3152195
theorem B3707785 : Blo 385764 3707785 := bstep (se 2 (by rfl) ⟨1390419, by rfl⟩ : syracuseStep 3707785 = 2780839) B2780839
theorem B25073225 : Blo 385764 25073225 := bstep (se 2 (by rfl) ⟨9402459, by rfl⟩ : syracuseStep 25073225 = 18804919) B18804919
theorem B2954879 : Blo 385764 2954879 := bstep (se 1 (by rfl) ⟨2216159, by rfl⟩ : syracuseStep 2954879 = 4432319) B4432319
theorem B2989163 : Blo 385764 2989163 := bstep (se 1 (by rfl) ⟨2241872, by rfl⟩ : syracuseStep 2989163 = 4483745) B4483745
theorem B23768453 : Blo 385764 23768453 := bstep (se 4 (by rfl) ⟨2228292, by rfl⟩ : syracuseStep 23768453 = 4456585) B4456585
theorem B27214451 : Blo 385764 27214451 := bstep (se 1 (by rfl) ⟨20410838, by rfl⟩ : syracuseStep 27214451 = 40821677) B40821677
theorem B2805353 : Blo 385764 2805353 := bstep (se 2 (by rfl) ⟨1052007, by rfl⟩ : syracuseStep 2805353 = 2104015) B2104015
theorem B2643131 : Blo 385764 2643131 := bstep (se 1 (by rfl) ⟨1982348, by rfl⟩ : syracuseStep 2643131 = 3964697) B3964697
theorem B581687 : Blo 385764 581687 := bstep (se 1 (by rfl) ⟨436265, by rfl⟩ : syracuseStep 581687 = 872531) B872531
theorem B6743351 : Blo 385764 6743351 := bstep (se 1 (by rfl) ⟨5057513, by rfl⟩ : syracuseStep 6743351 = 10115027) B10115027
theorem B388127 : Blo 385764 388127 := bstep (se 1 (by rfl) ⟨291095, by rfl⟩ : syracuseStep 388127 = 582191) B582191
theorem B883007 : Blo 385764 883007 := bstep (se 1 (by rfl) ⟨662255, by rfl⟩ : syracuseStep 883007 = 1324511) B1324511
theorem B1870235 : Blo 385764 1870235 := bstep (se 1 (by rfl) ⟨1402676, by rfl⟩ : syracuseStep 1870235 = 2805353) B2805353
theorem B16715483 : Blo 385764 16715483 := bstep (se 1 (by rfl) ⟨12536612, by rfl⟩ : syracuseStep 16715483 = 25073225) B25073225
theorem B1969919 : Blo 385764 1969919 := bstep (se 1 (by rfl) ⟨1477439, by rfl⟩ : syracuseStep 1969919 = 2954879) B2954879
theorem B4495567 : Blo 385764 4495567 := bstep (se 1 (by rfl) ⟨3371675, by rfl⟩ : syracuseStep 4495567 = 6743351) B6743351
theorem B72526907 : Blo 385764 72526907 := bstep (se 1 (by rfl) ⟨54395180, by rfl⟩ : syracuseStep 72526907 = 108790361) B108790361
theorem B2207047 : Blo 385764 2207047 := bstep (se 1 (by rfl) ⟨1655285, by rfl⟩ : syracuseStep 2207047 = 3310571) B3310571
theorem B15845635 : Blo 385764 15845635 := bstep (se 1 (by rfl) ⟨11884226, by rfl⟩ : syracuseStep 15845635 = 23768453) B23768453
theorem B18142967 : Blo 385764 18142967 := bstep (se 1 (by rfl) ⟨13607225, by rfl⟩ : syracuseStep 18142967 = 27214451) B27214451
theorem B1400975 : Blo 385764 1400975 := bstep (se 1 (by rfl) ⟨1050731, by rfl⟩ : syracuseStep 1400975 = 2101463) B2101463
theorem B1762087 : Blo 385764 1762087 := bstep (se 1 (by rfl) ⟨1321565, by rfl⟩ : syracuseStep 1762087 = 2643131) B2643131
theorem B1992775 : Blo 385764 1992775 := bstep (se 1 (by rfl) ⟨1494581, by rfl⟩ : syracuseStep 1992775 = 2989163) B2989163
theorem B387791 : Blo 385764 387791 := bstep (se 1 (by rfl) ⟨290843, by rfl⟩ : syracuseStep 387791 = 581687) B581687
theorem B4943713 : Blo 385764 4943713 := bstep (se 2 (by rfl) ⟨1853892, by rfl⟩ : syracuseStep 4943713 = 3707785) B3707785
theorem B588671 : Blo 385764 588671 := bstep (se 1 (by rfl) ⟨441503, by rfl⟩ : syracuseStep 588671 = 883007) B883007
theorem B1246823 : Blo 385764 1246823 := bstep (se 1 (by rfl) ⟨935117, by rfl⟩ : syracuseStep 1246823 = 1870235) B1870235
theorem B11143655 : Blo 385764 11143655 := bstep (se 1 (by rfl) ⟨8357741, by rfl⟩ : syracuseStep 11143655 = 16715483) B16715483
theorem B1313279 : Blo 385764 1313279 := bstep (se 1 (by rfl) ⟨984959, by rfl⟩ : syracuseStep 1313279 = 1969919) B1969919
theorem B2657033 : Blo 385764 2657033 := bstep (se 2 (by rfl) ⟨996387, by rfl⟩ : syracuseStep 2657033 = 1992775) B1992775
theorem B6591617 : Blo 385764 6591617 := bstep (se 2 (by rfl) ⟨2471856, by rfl⟩ : syracuseStep 6591617 = 4943713) B4943713
theorem B48381245 : Blo 385764 48381245 := bstep (se 3 (by rfl) ⟨9071483, by rfl⟩ : syracuseStep 48381245 = 18142967) B18142967
theorem B933983 : Blo 385764 933983 := bstep (se 1 (by rfl) ⟨700487, by rfl⟩ : syracuseStep 933983 = 1400975) B1400975
theorem B48351271 : Blo 385764 48351271 := bstep (se 1 (by rfl) ⟨36263453, by rfl⟩ : syracuseStep 48351271 = 72526907) B72526907
theorem B2349449 : Blo 385764 2349449 := bstep (se 2 (by rfl) ⟨881043, by rfl⟩ : syracuseStep 2349449 = 1762087) B1762087
theorem B21127513 : Blo 385764 21127513 := bstep (se 2 (by rfl) ⟨7922817, by rfl⟩ : syracuseStep 21127513 = 15845635) B15845635
theorem B2942729 : Blo 385764 2942729 := bstep (se 2 (by rfl) ⟨1103523, by rfl⟩ : syracuseStep 2942729 = 2207047) B2207047
theorem B5994089 : Blo 385764 5994089 := bstep (se 2 (by rfl) ⟨2247783, by rfl⟩ : syracuseStep 5994089 = 4495567) B4495567
theorem B392447 : Blo 385764 392447 := bstep (se 1 (by rfl) ⟨294335, by rfl⟩ : syracuseStep 392447 = 588671) B588671
theorem B622655 : Blo 385764 622655 := bstep (se 1 (by rfl) ⟨466991, by rfl⟩ : syracuseStep 622655 = 933983) B933983
theorem B1771355 : Blo 385764 1771355 := bstep (se 1 (by rfl) ⟨1328516, by rfl⟩ : syracuseStep 1771355 = 2657033) B2657033
theorem B4394411 : Blo 385764 4394411 := bstep (se 1 (by rfl) ⟨3295808, by rfl⟩ : syracuseStep 4394411 = 6591617) B6591617
theorem B32254163 : Blo 385764 32254163 := bstep (se 1 (by rfl) ⟨24190622, by rfl⟩ : syracuseStep 32254163 = 48381245) B48381245
theorem B831215 : Blo 385764 831215 := bstep (se 1 (by rfl) ⟨623411, by rfl⟩ : syracuseStep 831215 = 1246823) B1246823
theorem B64468361 : Blo 385764 64468361 := bstep (se 2 (by rfl) ⟨24175635, by rfl⟩ : syracuseStep 64468361 = 48351271) B48351271
theorem B28170017 : Blo 385764 28170017 := bstep (se 2 (by rfl) ⟨10563756, by rfl⟩ : syracuseStep 28170017 = 21127513) B21127513
theorem B7429103 : Blo 385764 7429103 := bstep (se 1 (by rfl) ⟨5571827, by rfl⟩ : syracuseStep 7429103 = 11143655) B11143655
theorem B875519 : Blo 385764 875519 := bstep (se 1 (by rfl) ⟨656639, by rfl⟩ : syracuseStep 875519 = 1313279) B1313279
theorem B1566299 : Blo 385764 1566299 := bstep (se 1 (by rfl) ⟨1174724, by rfl⟩ : syracuseStep 1566299 = 2349449) B2349449
theorem B1961819 : Blo 385764 1961819 := bstep (se 1 (by rfl) ⟨1471364, by rfl⟩ : syracuseStep 1961819 = 2942729) B2942729
theorem B1046525 : Blo 385764 1046525 := bstep (se 3 (by rfl) ⟨196223, by rfl⟩ : syracuseStep 1046525 = 392447) B392447
theorem B3996059 : Blo 385764 3996059 := bstep (se 1 (by rfl) ⟨2997044, by rfl⟩ : syracuseStep 3996059 = 5994089) B5994089
theorem B18780011 : Blo 385764 18780011 := bstep (se 1 (by rfl) ⟨14085008, by rfl⟩ : syracuseStep 18780011 = 28170017) B28170017
theorem B4952735 : Blo 385764 4952735 := bstep (se 1 (by rfl) ⟨3714551, by rfl⟩ : syracuseStep 4952735 = 7429103) B7429103
theorem B4723613 : Blo 385764 4723613 := bstep (se 3 (by rfl) ⟨885677, by rfl⟩ : syracuseStep 4723613 = 1771355) B1771355
theorem B2790733 : Blo 385764 2790733 := bstep (se 3 (by rfl) ⟨523262, by rfl⟩ : syracuseStep 2790733 = 1046525) B1046525
theorem B10656157 : Blo 385764 10656157 := bstep (se 3 (by rfl) ⟨1998029, by rfl⟩ : syracuseStep 10656157 = 3996059) B3996059
theorem B21502775 : Blo 385764 21502775 := bstep (se 1 (by rfl) ⟨16127081, by rfl⟩ : syracuseStep 21502775 = 32254163) B32254163
theorem B2929607 : Blo 385764 2929607 := bstep (se 1 (by rfl) ⟨2197205, by rfl⟩ : syracuseStep 2929607 = 4394411) B4394411
theorem B42978907 : Blo 385764 42978907 := bstep (se 1 (by rfl) ⟨32234180, by rfl⟩ : syracuseStep 42978907 = 64468361) B64468361
theorem B415103 : Blo 385764 415103 := bstep (se 1 (by rfl) ⟨311327, by rfl⟩ : syracuseStep 415103 = 622655) B622655
theorem B583679 : Blo 385764 583679 := bstep (se 1 (by rfl) ⟨437759, by rfl⟩ : syracuseStep 583679 = 875519) B875519
theorem B1044199 : Blo 385764 1044199 := bstep (se 1 (by rfl) ⟨783149, by rfl⟩ : syracuseStep 1044199 = 1566299) B1566299
theorem B554143 : Blo 385764 554143 := bstep (se 1 (by rfl) ⟨415607, by rfl⟩ : syracuseStep 554143 = 831215) B831215
theorem B1307879 : Blo 385764 1307879 := bstep (se 1 (by rfl) ⟨980909, by rfl⟩ : syracuseStep 1307879 = 1961819) B1961819
theorem B12520007 : Blo 385764 12520007 := bstep (se 1 (by rfl) ⟨9390005, by rfl⟩ : syracuseStep 12520007 = 18780011) B18780011
theorem B3149075 : Blo 385764 3149075 := bstep (se 1 (by rfl) ⟨2361806, by rfl⟩ : syracuseStep 3149075 = 4723613) B4723613
theorem B229220837 : Blo 385764 229220837 := bstep (se 4 (by rfl) ⟨21489453, by rfl⟩ : syracuseStep 229220837 = 42978907) B42978907
theorem B14335183 : Blo 385764 14335183 := bstep (se 1 (by rfl) ⟨10751387, by rfl⟩ : syracuseStep 14335183 = 21502775) B21502775
theorem B1392265 : Blo 385764 1392265 := bstep (se 2 (by rfl) ⟨522099, by rfl⟩ : syracuseStep 1392265 = 1044199) B1044199
theorem B738857 : Blo 385764 738857 := bstep (se 2 (by rfl) ⟨277071, by rfl⟩ : syracuseStep 738857 = 554143) B554143
theorem B3720977 : Blo 385764 3720977 := bstep (se 2 (by rfl) ⟨1395366, by rfl⟩ : syracuseStep 3720977 = 2790733) B2790733
theorem B14208209 : Blo 385764 14208209 := bstep (se 2 (by rfl) ⟨5328078, by rfl⟩ : syracuseStep 14208209 = 10656157) B10656157
theorem B1953071 : Blo 385764 1953071 := bstep (se 1 (by rfl) ⟨1464803, by rfl⟩ : syracuseStep 1953071 = 2929607) B2929607
theorem B871919 : Blo 385764 871919 := bstep (se 1 (by rfl) ⟨653939, by rfl⟩ : syracuseStep 871919 = 1307879) B1307879
theorem B3301823 : Blo 385764 3301823 := bstep (se 1 (by rfl) ⟨2476367, by rfl⟩ : syracuseStep 3301823 = 4952735) B4952735
theorem B1106941 : Blo 385764 1106941 := bstep (se 3 (by rfl) ⟨207551, by rfl⟩ : syracuseStep 1106941 = 415103) B415103
theorem B389119 : Blo 385764 389119 := bstep (se 1 (by rfl) ⟨291839, by rfl⟩ : syracuseStep 389119 = 583679) B583679
theorem B492571 : Blo 385764 492571 := bstep (se 1 (by rfl) ⟨369428, by rfl⟩ : syracuseStep 492571 = 738857) B738857
theorem B1475921 : Blo 385764 1475921 := bstep (se 2 (by rfl) ⟨553470, by rfl⟩ : syracuseStep 1475921 = 1106941) B1106941
theorem B9472139 : Blo 385764 9472139 := bstep (se 1 (by rfl) ⟨7104104, by rfl⟩ : syracuseStep 9472139 = 14208209) B14208209
theorem B2201215 : Blo 385764 2201215 := bstep (se 1 (by rfl) ⟨1650911, by rfl⟩ : syracuseStep 2201215 = 3301823) B3301823
theorem B8397533 : Blo 385764 8397533 := bstep (se 3 (by rfl) ⟨1574537, by rfl⟩ : syracuseStep 8397533 = 3149075) B3149075
theorem B19113577 : Blo 385764 19113577 := bstep (se 2 (by rfl) ⟨7167591, by rfl⟩ : syracuseStep 19113577 = 14335183) B14335183
theorem B152813891 : Blo 385764 152813891 := bstep (se 1 (by rfl) ⟨114610418, by rfl⟩ : syracuseStep 152813891 = 229220837) B229220837
theorem B1856353 : Blo 385764 1856353 := bstep (se 2 (by rfl) ⟨696132, by rfl⟩ : syracuseStep 1856353 = 1392265) B1392265
theorem B2480651 : Blo 385764 2480651 := bstep (se 1 (by rfl) ⟨1860488, by rfl⟩ : syracuseStep 2480651 = 3720977) B3720977
theorem B8346671 : Blo 385764 8346671 := bstep (se 1 (by rfl) ⟨6260003, by rfl⟩ : syracuseStep 8346671 = 12520007) B12520007
theorem B1302047 : Blo 385764 1302047 := bstep (se 1 (by rfl) ⟨976535, by rfl⟩ : syracuseStep 1302047 = 1953071) B1953071
theorem B581279 : Blo 385764 581279 := bstep (se 1 (by rfl) ⟨435959, by rfl⟩ : syracuseStep 581279 = 871919) B871919
theorem B101875927 : Blo 385764 101875927 := bstep (se 1 (by rfl) ⟨76406945, by rfl⟩ : syracuseStep 101875927 = 152813891) B152813891
theorem B983947 : Blo 385764 983947 := bstep (se 1 (by rfl) ⟨737960, by rfl⟩ : syracuseStep 983947 = 1475921) B1475921
theorem B656761 : Blo 385764 656761 := bstep (se 2 (by rfl) ⟨246285, by rfl⟩ : syracuseStep 656761 = 492571) B492571
theorem B1653767 : Blo 385764 1653767 := bstep (se 1 (by rfl) ⟨1240325, by rfl⟩ : syracuseStep 1653767 = 2480651) B2480651
theorem B868031 : Blo 385764 868031 := bstep (se 1 (by rfl) ⟨651023, by rfl⟩ : syracuseStep 868031 = 1302047) B1302047
theorem B2475137 : Blo 385764 2475137 := bstep (se 2 (by rfl) ⟨928176, by rfl⟩ : syracuseStep 2475137 = 1856353) B1856353
theorem B2934953 : Blo 385764 2934953 := bstep (se 2 (by rfl) ⟨1100607, by rfl⟩ : syracuseStep 2934953 = 2201215) B2201215
theorem B6314759 : Blo 385764 6314759 := bstep (se 1 (by rfl) ⟨4736069, by rfl⟩ : syracuseStep 6314759 = 9472139) B9472139
theorem B5564447 : Blo 385764 5564447 := bstep (se 1 (by rfl) ⟨4173335, by rfl⟩ : syracuseStep 5564447 = 8346671) B8346671
theorem B387519 : Blo 385764 387519 := bstep (se 1 (by rfl) ⟨290639, by rfl⟩ : syracuseStep 387519 = 581279) B581279
theorem B5598355 : Blo 385764 5598355 := bstep (se 1 (by rfl) ⟨4198766, by rfl⟩ : syracuseStep 5598355 = 8397533) B8397533
theorem B101939077 : Blo 385764 101939077 := bstep (se 4 (by rfl) ⟨9556788, by rfl⟩ : syracuseStep 101939077 = 19113577) B19113577
theorem B1311929 : Blo 385764 1311929 := bstep (se 2 (by rfl) ⟨491973, by rfl⟩ : syracuseStep 1311929 = 983947) B983947
theorem B3709631 : Blo 385764 3709631 := bstep (se 1 (by rfl) ⟨2782223, by rfl⟩ : syracuseStep 3709631 = 5564447) B5564447
theorem B135834569 : Blo 385764 135834569 := bstep (se 2 (by rfl) ⟨50937963, by rfl⟩ : syracuseStep 135834569 = 101875927) B101875927
theorem B6600365 : Blo 385764 6600365 := bstep (se 3 (by rfl) ⟨1237568, by rfl⟩ : syracuseStep 6600365 = 2475137) B2475137
theorem B4209839 : Blo 385764 4209839 := bstep (se 1 (by rfl) ⟨3157379, by rfl⟩ : syracuseStep 4209839 = 6314759) B6314759
theorem B1102511 : Blo 385764 1102511 := bstep (se 1 (by rfl) ⟨826883, by rfl⟩ : syracuseStep 1102511 = 1653767) B1653767
theorem B578687 : Blo 385764 578687 := bstep (se 1 (by rfl) ⟨434015, by rfl⟩ : syracuseStep 578687 = 868031) B868031
theorem B1956635 : Blo 385764 1956635 := bstep (se 1 (by rfl) ⟨1467476, by rfl⟩ : syracuseStep 1956635 = 2934953) B2934953
theorem B875681 : Blo 385764 875681 := bstep (se 2 (by rfl) ⟨328380, by rfl⟩ : syracuseStep 875681 = 656761) B656761
theorem B7464473 : Blo 385764 7464473 := bstep (se 2 (by rfl) ⟨2799177, by rfl⟩ : syracuseStep 7464473 = 5598355) B5598355
theorem B135918769 : Blo 385764 135918769 := bstep (se 2 (by rfl) ⟨50969538, by rfl⟩ : syracuseStep 135918769 = 101939077) B101939077
theorem B4400243 : Blo 385764 4400243 := bstep (se 1 (by rfl) ⟨3300182, by rfl⟩ : syracuseStep 4400243 = 6600365) B6600365
theorem B735007 : Blo 385764 735007 := bstep (se 1 (by rfl) ⟨551255, by rfl⟩ : syracuseStep 735007 = 1102511) B1102511
theorem B2473087 : Blo 385764 2473087 := bstep (se 1 (by rfl) ⟨1854815, by rfl⟩ : syracuseStep 2473087 = 3709631) B3709631
theorem B181225025 : Blo 385764 181225025 := bstep (se 2 (by rfl) ⟨67959384, by rfl⟩ : syracuseStep 181225025 = 135918769) B135918769
theorem B90556379 : Blo 385764 90556379 := bstep (se 1 (by rfl) ⟨67917284, by rfl⟩ : syracuseStep 90556379 = 135834569) B135834569
theorem B2806559 : Blo 385764 2806559 := bstep (se 1 (by rfl) ⟨2104919, by rfl⟩ : syracuseStep 2806559 = 4209839) B4209839
theorem B874619 : Blo 385764 874619 := bstep (se 1 (by rfl) ⟨655964, by rfl⟩ : syracuseStep 874619 = 1311929) B1311929
theorem B385791 : Blo 385764 385791 := bstep (se 1 (by rfl) ⟨289343, by rfl⟩ : syracuseStep 385791 = 578687) B578687
theorem B1304423 : Blo 385764 1304423 := bstep (se 1 (by rfl) ⟨978317, by rfl⟩ : syracuseStep 1304423 = 1956635) B1956635
theorem B583787 : Blo 385764 583787 := bstep (se 1 (by rfl) ⟨437840, by rfl⟩ : syracuseStep 583787 = 875681) B875681
theorem B4976315 : Blo 385764 4976315 := bstep (se 1 (by rfl) ⟨3732236, by rfl⟩ : syracuseStep 4976315 = 7464473) B7464473
theorem B120816683 : Blo 385764 120816683 := bstep (se 1 (by rfl) ⟨90612512, by rfl⟩ : syracuseStep 120816683 = 181225025) B181225025
theorem B1871039 : Blo 385764 1871039 := bstep (se 1 (by rfl) ⟨1403279, by rfl⟩ : syracuseStep 1871039 = 2806559) B2806559
theorem B3317543 : Blo 385764 3317543 := bstep (se 1 (by rfl) ⟨2488157, by rfl⟩ : syracuseStep 3317543 = 4976315) B4976315
theorem B60370919 : Blo 385764 60370919 := bstep (se 1 (by rfl) ⟨45278189, by rfl⟩ : syracuseStep 60370919 = 90556379) B90556379
theorem B2933495 : Blo 385764 2933495 := bstep (se 1 (by rfl) ⟨2200121, by rfl⟩ : syracuseStep 2933495 = 4400243) B4400243
theorem B869615 : Blo 385764 869615 := bstep (se 1 (by rfl) ⟨652211, by rfl⟩ : syracuseStep 869615 = 1304423) B1304423
theorem B3297449 : Blo 385764 3297449 := bstep (se 2 (by rfl) ⟨1236543, by rfl⟩ : syracuseStep 3297449 = 2473087) B2473087
theorem B583079 : Blo 385764 583079 := bstep (se 1 (by rfl) ⟨437309, by rfl⟩ : syracuseStep 583079 = 874619) B874619
theorem B389191 : Blo 385764 389191 := bstep (se 1 (by rfl) ⟨291893, by rfl⟩ : syracuseStep 389191 = 583787) B583787
theorem B980009 : Blo 385764 980009 := bstep (se 2 (by rfl) ⟨367503, by rfl⟩ : syracuseStep 980009 = 735007) B735007
theorem B80544455 : Blo 385764 80544455 := bstep (se 1 (by rfl) ⟨60408341, by rfl⟩ : syracuseStep 80544455 = 120816683) B120816683
theorem B2198299 : Blo 385764 2198299 := bstep (se 1 (by rfl) ⟨1648724, by rfl⟩ : syracuseStep 2198299 = 3297449) B3297449
theorem B40247279 : Blo 385764 40247279 := bstep (se 1 (by rfl) ⟨30185459, by rfl⟩ : syracuseStep 40247279 = 60370919) B60370919
theorem B4989437 : Blo 385764 4989437 := bstep (se 3 (by rfl) ⟨935519, by rfl⟩ : syracuseStep 4989437 = 1871039) B1871039
theorem B2211695 : Blo 385764 2211695 := bstep (se 1 (by rfl) ⟨1658771, by rfl⟩ : syracuseStep 2211695 = 3317543) B3317543
theorem B1955663 : Blo 385764 1955663 := bstep (se 1 (by rfl) ⟨1466747, by rfl⟩ : syracuseStep 1955663 = 2933495) B2933495
theorem B579743 : Blo 385764 579743 := bstep (se 1 (by rfl) ⟨434807, by rfl⟩ : syracuseStep 579743 = 869615) B869615
theorem B388719 : Blo 385764 388719 := bstep (se 1 (by rfl) ⟨291539, by rfl⟩ : syracuseStep 388719 = 583079) B583079
theorem B653339 : Blo 385764 653339 := bstep (se 1 (by rfl) ⟨490004, by rfl⟩ : syracuseStep 653339 = 980009) B980009
theorem B435559 : Blo 385764 435559 := bstep (se 1 (by rfl) ⟨326669, by rfl⟩ : syracuseStep 435559 = 653339) B653339
theorem B2931065 : Blo 385764 2931065 := bstep (se 2 (by rfl) ⟨1099149, by rfl⟩ : syracuseStep 2931065 = 2198299) B2198299
theorem B3326291 : Blo 385764 3326291 := bstep (se 1 (by rfl) ⟨2494718, by rfl⟩ : syracuseStep 3326291 = 4989437) B4989437
theorem B53696303 : Blo 385764 53696303 := bstep (se 1 (by rfl) ⟨40272227, by rfl⟩ : syracuseStep 53696303 = 80544455) B80544455
theorem B1303775 : Blo 385764 1303775 := bstep (se 1 (by rfl) ⟨977831, by rfl⟩ : syracuseStep 1303775 = 1955663) B1955663
theorem B386495 : Blo 385764 386495 := bstep (se 1 (by rfl) ⟨289871, by rfl⟩ : syracuseStep 386495 = 579743) B579743
theorem B26831519 : Blo 385764 26831519 := bstep (se 1 (by rfl) ⟨20123639, by rfl⟩ : syracuseStep 26831519 = 40247279) B40247279
theorem B1474463 : Blo 385764 1474463 := bstep (se 1 (by rfl) ⟨1105847, by rfl⟩ : syracuseStep 1474463 = 2211695) B2211695
theorem B35797535 : Blo 385764 35797535 := bstep (se 1 (by rfl) ⟨26848151, by rfl⟩ : syracuseStep 35797535 = 53696303) B53696303
theorem B869183 : Blo 385764 869183 := bstep (se 1 (by rfl) ⟨651887, by rfl⟩ : syracuseStep 869183 = 1303775) B1303775
theorem B1954043 : Blo 385764 1954043 := bstep (se 1 (by rfl) ⟨1465532, by rfl⟩ : syracuseStep 1954043 = 2931065) B2931065
theorem B2217527 : Blo 385764 2217527 := bstep (se 1 (by rfl) ⟨1663145, by rfl⟩ : syracuseStep 2217527 = 3326291) B3326291
theorem B580745 : Blo 385764 580745 := bstep (se 2 (by rfl) ⟨217779, by rfl⟩ : syracuseStep 580745 = 435559) B435559
theorem B17887679 : Blo 385764 17887679 := bstep (se 1 (by rfl) ⟨13415759, by rfl⟩ : syracuseStep 17887679 = 26831519) B26831519
theorem B982975 : Blo 385764 982975 := bstep (se 1 (by rfl) ⟨737231, by rfl⟩ : syracuseStep 982975 = 1474463) B1474463
theorem B1478351 : Blo 385764 1478351 := bstep (se 1 (by rfl) ⟨1108763, by rfl⟩ : syracuseStep 1478351 = 2217527) B2217527
theorem B23865023 : Blo 385764 23865023 := bstep (se 1 (by rfl) ⟨17898767, by rfl⟩ : syracuseStep 23865023 = 35797535) B35797535
theorem B579455 : Blo 385764 579455 := bstep (se 1 (by rfl) ⟨434591, by rfl⟩ : syracuseStep 579455 = 869183) B869183
theorem B1302695 : Blo 385764 1302695 := bstep (se 1 (by rfl) ⟨977021, by rfl⟩ : syracuseStep 1302695 = 1954043) B1954043
theorem B387163 : Blo 385764 387163 := bstep (se 1 (by rfl) ⟨290372, by rfl⟩ : syracuseStep 387163 = 580745) B580745
theorem B11925119 : Blo 385764 11925119 := bstep (se 1 (by rfl) ⟨8943839, by rfl⟩ : syracuseStep 11925119 = 17887679) B17887679
theorem B1310633 : Blo 385764 1310633 := bstep (se 2 (by rfl) ⟨491487, by rfl⟩ : syracuseStep 1310633 = 982975) B982975
theorem B985567 : Blo 385764 985567 := bstep (se 1 (by rfl) ⟨739175, by rfl⟩ : syracuseStep 985567 = 1478351) B1478351
theorem B868463 : Blo 385764 868463 := bstep (se 1 (by rfl) ⟨651347, by rfl⟩ : syracuseStep 868463 = 1302695) B1302695
theorem B15910015 : Blo 385764 15910015 := bstep (se 1 (by rfl) ⟨11932511, by rfl⟩ : syracuseStep 15910015 = 23865023) B23865023
theorem B7950079 : Blo 385764 7950079 := bstep (se 1 (by rfl) ⟨5962559, by rfl⟩ : syracuseStep 7950079 = 11925119) B11925119
theorem B873755 : Blo 385764 873755 := bstep (se 1 (by rfl) ⟨655316, by rfl⟩ : syracuseStep 873755 = 1310633) B1310633
theorem B386303 : Blo 385764 386303 := bstep (se 1 (by rfl) ⟨289727, by rfl⟩ : syracuseStep 386303 = 579455) B579455
theorem B1314089 : Blo 385764 1314089 := bstep (se 2 (by rfl) ⟨492783, by rfl⟩ : syracuseStep 1314089 = 985567) B985567
theorem B21213353 : Blo 385764 21213353 := bstep (se 2 (by rfl) ⟨7955007, by rfl⟩ : syracuseStep 21213353 = 15910015) B15910015
theorem B10600105 : Blo 385764 10600105 := bstep (se 2 (by rfl) ⟨3975039, by rfl⟩ : syracuseStep 10600105 = 7950079) B7950079
theorem B578975 : Blo 385764 578975 := bstep (se 1 (by rfl) ⟨434231, by rfl⟩ : syracuseStep 578975 = 868463) B868463
theorem B582503 : Blo 385764 582503 := bstep (se 1 (by rfl) ⟨436877, by rfl⟩ : syracuseStep 582503 = 873755) B873755
theorem B14133473 : Blo 385764 14133473 := bstep (se 2 (by rfl) ⟨5300052, by rfl⟩ : syracuseStep 14133473 = 10600105) B10600105
theorem B14142235 : Blo 385764 14142235 := bstep (se 1 (by rfl) ⟨10606676, by rfl⟩ : syracuseStep 14142235 = 21213353) B21213353
theorem B876059 : Blo 385764 876059 := bstep (se 1 (by rfl) ⟨657044, by rfl⟩ : syracuseStep 876059 = 1314089) B1314089
theorem B385983 : Blo 385764 385983 := bstep (se 1 (by rfl) ⟨289487, by rfl⟩ : syracuseStep 385983 = 578975) B578975
theorem B388335 : Blo 385764 388335 := bstep (se 1 (by rfl) ⟨291251, by rfl⟩ : syracuseStep 388335 = 582503) B582503
theorem B18856313 : Blo 385764 18856313 := bstep (se 2 (by rfl) ⟨7071117, by rfl⟩ : syracuseStep 18856313 = 14142235) B14142235
theorem B9422315 : Blo 385764 9422315 := bstep (se 1 (by rfl) ⟨7066736, by rfl⟩ : syracuseStep 9422315 = 14133473) B14133473
theorem B584039 : Blo 385764 584039 := bstep (se 1 (by rfl) ⟨438029, by rfl⟩ : syracuseStep 584039 = 876059) B876059
theorem B12570875 : Blo 385764 12570875 := bstep (se 1 (by rfl) ⟨9428156, by rfl⟩ : syracuseStep 12570875 = 18856313) B18856313
theorem B6281543 : Blo 385764 6281543 := bstep (se 1 (by rfl) ⟨4711157, by rfl⟩ : syracuseStep 6281543 = 9422315) B9422315
theorem B389359 : Blo 385764 389359 := bstep (se 1 (by rfl) ⟨292019, by rfl⟩ : syracuseStep 389359 = 584039) B584039
theorem B8380583 : Blo 385764 8380583 := bstep (se 1 (by rfl) ⟨6285437, by rfl⟩ : syracuseStep 8380583 = 12570875) B12570875
theorem B4187695 : Blo 385764 4187695 := bstep (se 1 (by rfl) ⟨3140771, by rfl⟩ : syracuseStep 4187695 = 6281543) B6281543
theorem B5583593 : Blo 385764 5583593 := bstep (se 2 (by rfl) ⟨2093847, by rfl⟩ : syracuseStep 5583593 = 4187695) B4187695
theorem B5587055 : Blo 385764 5587055 := bstep (se 1 (by rfl) ⟨4190291, by rfl⟩ : syracuseStep 5587055 = 8380583) B8380583
theorem B3722395 : Blo 385764 3722395 := bstep (se 1 (by rfl) ⟨2791796, by rfl⟩ : syracuseStep 3722395 = 5583593) B5583593
theorem B3724703 : Blo 385764 3724703 := bstep (se 1 (by rfl) ⟨2793527, by rfl⟩ : syracuseStep 3724703 = 5587055) B5587055
theorem B4963193 : Blo 385764 4963193 := bstep (se 2 (by rfl) ⟨1861197, by rfl⟩ : syracuseStep 4963193 = 3722395) B3722395
theorem B2483135 : Blo 385764 2483135 := bstep (se 1 (by rfl) ⟨1862351, by rfl⟩ : syracuseStep 2483135 = 3724703) B3724703
theorem B1655423 : Blo 385764 1655423 := bstep (se 1 (by rfl) ⟨1241567, by rfl⟩ : syracuseStep 1655423 = 2483135) B2483135
theorem B3308795 : Blo 385764 3308795 := bstep (se 1 (by rfl) ⟨2481596, by rfl⟩ : syracuseStep 3308795 = 4963193) B4963193
theorem B2205863 : Blo 385764 2205863 := bstep (se 1 (by rfl) ⟨1654397, by rfl⟩ : syracuseStep 2205863 = 3308795) B3308795
theorem B1103615 : Blo 385764 1103615 := bstep (se 1 (by rfl) ⟨827711, by rfl⟩ : syracuseStep 1103615 = 1655423) B1655423
theorem B735743 : Blo 385764 735743 := bstep (se 1 (by rfl) ⟨551807, by rfl⟩ : syracuseStep 735743 = 1103615) B1103615
theorem B1470575 : Blo 385764 1470575 := bstep (se 1 (by rfl) ⟨1102931, by rfl⟩ : syracuseStep 1470575 = 2205863) B2205863
theorem B1961981 : Blo 385764 1961981 := bstep (se 3 (by rfl) ⟨367871, by rfl⟩ : syracuseStep 1961981 = 735743) B735743
theorem B980383 : Blo 385764 980383 := bstep (se 1 (by rfl) ⟨735287, by rfl⟩ : syracuseStep 980383 = 1470575) B1470575
theorem B1307177 : Blo 385764 1307177 := bstep (se 2 (by rfl) ⟨490191, by rfl⟩ : syracuseStep 1307177 = 980383) B980383
theorem B1307987 : Blo 385764 1307987 := bstep (se 1 (by rfl) ⟨980990, by rfl⟩ : syracuseStep 1307987 = 1961981) B1961981
theorem B871451 : Blo 385764 871451 := bstep (se 1 (by rfl) ⟨653588, by rfl⟩ : syracuseStep 871451 = 1307177) B1307177
theorem B871991 : Blo 385764 871991 := bstep (se 1 (by rfl) ⟨653993, by rfl⟩ : syracuseStep 871991 = 1307987) B1307987
theorem B580967 : Blo 385764 580967 := bstep (se 1 (by rfl) ⟨435725, by rfl⟩ : syracuseStep 580967 = 871451) B871451
theorem B581327 : Blo 385764 581327 := bstep (se 1 (by rfl) ⟨435995, by rfl⟩ : syracuseStep 581327 = 871991) B871991
theorem B387311 : Blo 385764 387311 := bstep (se 1 (by rfl) ⟨290483, by rfl⟩ : syracuseStep 387311 = 580967) B580967
theorem B387551 : Blo 385764 387551 := bstep (se 1 (by rfl) ⟨290663, by rfl⟩ : syracuseStep 387551 = 581327) B581327

theorem C0 (j : ℕ) (h1 : 96441 ≤ j) (h2 : j ≤ 97140) : Blo 385764 (4 * j + 3) := by
  interval_cases j
  · exact B385767
  · exact B385771
  · exact B385775
  · exact B385779
  · exact B385783
  · exact B385787
  · exact B385791
  · exact B385795
  · exact B385799
  · exact B385803
  · exact B385807
  · exact B385811
  · exact B385815
  · exact B385819
  · exact B385823
  · exact B385827
  · exact B385831
  · exact B385835
  · exact B385839
  · exact B385843
  · exact B385847
  · exact B385851
  · exact B385855
  · exact B385859
  · exact B385863
  · exact B385867
  · exact B385871
  · exact B385875
  · exact B385879
  · exact B385883
  · exact B385887
  · exact B385891
  · exact B385895
  · exact B385899
  · exact B385903
  · exact B385907
  · exact B385911
  · exact B385915
  · exact B385919
  · exact B385923
  · exact B385927
  · exact B385931
  · exact B385935
  · exact B385939
  · exact B385943
  · exact B385947
  · exact B385951
  · exact B385955
  · exact B385959
  · exact B385963
  · exact B385967
  · exact B385971
  · exact B385975
  · exact B385979
  · exact B385983
  · exact B385987
  · exact B385991
  · exact B385995
  · exact B385999
  · exact B386003
  · exact B386007
  · exact B386011
  · exact B386015
  · exact B386019
  · exact B386023
  · exact B386027
  · exact B386031
  · exact B386035
  · exact B386039
  · exact B386043
  · exact B386047
  · exact B386051
  · exact B386055
  · exact B386059
  · exact B386063
  · exact B386067
  · exact B386071
  · exact B386075
  · exact B386079
  · exact B386083
  · exact B386087
  · exact B386091
  · exact B386095
  · exact B386099
  · exact B386103
  · exact B386107
  · exact B386111
  · exact B386115
  · exact B386119
  · exact B386123
  · exact B386127
  · exact B386131
  · exact B386135
  · exact B386139
  · exact B386143
  · exact B386147
  · exact B386151
  · exact B386155
  · exact B386159
  · exact B386163
  · exact B386167
  · exact B386171
  · exact B386175
  · exact B386179
  · exact B386183
  · exact B386187
  · exact B386191
  · exact B386195
  · exact B386199
  · exact B386203
  · exact B386207
  · exact B386211
  · exact B386215
  · exact B386219
  · exact B386223
  · exact B386227
  · exact B386231
  · exact B386235
  · exact B386239
  · exact B386243
  · exact B386247
  · exact B386251
  · exact B386255
  · exact B386259
  · exact B386263
  · exact B386267
  · exact B386271
  · exact B386275
  · exact B386279
  · exact B386283
  · exact B386287
  · exact B386291
  · exact B386295
  · exact B386299
  · exact B386303
  · exact B386307
  · exact B386311
  · exact B386315
  · exact B386319
  · exact B386323
  · exact B386327
  · exact B386331
  · exact B386335
  · exact B386339
  · exact B386343
  · exact B386347
  · exact B386351
  · exact B386355
  · exact B386359
  · exact B386363
  · exact B386367
  · exact B386371
  · exact B386375
  · exact B386379
  · exact B386383
  · exact B386387
  · exact B386391
  · exact B386395
  · exact B386399
  · exact B386403
  · exact B386407
  · exact B386411
  · exact B386415
  · exact B386419
  · exact B386423
  · exact B386427
  · exact B386431
  · exact B386435
  · exact B386439
  · exact B386443
  · exact B386447
  · exact B386451
  · exact B386455
  · exact B386459
  · exact B386463
  · exact B386467
  · exact B386471
  · exact B386475
  · exact B386479
  · exact B386483
  · exact B386487
  · exact B386491
  · exact B386495
  · exact B386499
  · exact B386503
  · exact B386507
  · exact B386511
  · exact B386515
  · exact B386519
  · exact B386523
  · exact B386527
  · exact B386531
  · exact B386535
  · exact B386539
  · exact B386543
  · exact B386547
  · exact B386551
  · exact B386555
  · exact B386559
  · exact B386563
  · exact B386567
  · exact B386571
  · exact B386575
  · exact B386579
  · exact B386583
  · exact B386587
  · exact B386591
  · exact B386595
  · exact B386599
  · exact B386603
  · exact B386607
  · exact B386611
  · exact B386615
  · exact B386619
  · exact B386623
  · exact B386627
  · exact B386631
  · exact B386635
  · exact B386639
  · exact B386643
  · exact B386647
  · exact B386651
  · exact B386655
  · exact B386659
  · exact B386663
  · exact B386667
  · exact B386671
  · exact B386675
  · exact B386679
  · exact B386683
  · exact B386687
  · exact B386691
  · exact B386695
  · exact B386699
  · exact B386703
  · exact B386707
  · exact B386711
  · exact B386715
  · exact B386719
  · exact B386723
  · exact B386727
  · exact B386731
  · exact B386735
  · exact B386739
  · exact B386743
  · exact B386747
  · exact B386751
  · exact B386755
  · exact B386759
  · exact B386763
  · exact B386767
  · exact B386771
  · exact B386775
  · exact B386779
  · exact B386783
  · exact B386787
  · exact B386791
  · exact B386795
  · exact B386799
  · exact B386803
  · exact B386807
  · exact B386811
  · exact B386815
  · exact B386819
  · exact B386823
  · exact B386827
  · exact B386831
  · exact B386835
  · exact B386839
  · exact B386843
  · exact B386847
  · exact B386851
  · exact B386855
  · exact B386859
  · exact B386863
  · exact B386867
  · exact B386871
  · exact B386875
  · exact B386879
  · exact B386883
  · exact B386887
  · exact B386891
  · exact B386895
  · exact B386899
  · exact B386903
  · exact B386907
  · exact B386911
  · exact B386915
  · exact B386919
  · exact B386923
  · exact B386927
  · exact B386931
  · exact B386935
  · exact B386939
  · exact B386943
  · exact B386947
  · exact B386951
  · exact B386955
  · exact B386959
  · exact B386963
  · exact B386967
  · exact B386971
  · exact B386975
  · exact B386979
  · exact B386983
  · exact B386987
  · exact B386991
  · exact B386995
  · exact B386999
  · exact B387003
  · exact B387007
  · exact B387011
  · exact B387015
  · exact B387019
  · exact B387023
  · exact B387027
  · exact B387031
  · exact B387035
  · exact B387039
  · exact B387043
  · exact B387047
  · exact B387051
  · exact B387055
  · exact B387059
  · exact B387063
  · exact B387067
  · exact B387071
  · exact B387075
  · exact B387079
  · exact B387083
  · exact B387087
  · exact B387091
  · exact B387095
  · exact B387099
  · exact B387103
  · exact B387107
  · exact B387111
  · exact B387115
  · exact B387119
  · exact B387123
  · exact B387127
  · exact B387131
  · exact B387135
  · exact B387139
  · exact B387143
  · exact B387147
  · exact B387151
  · exact B387155
  · exact B387159
  · exact B387163
  · exact B387167
  · exact B387171
  · exact B387175
  · exact B387179
  · exact B387183
  · exact B387187
  · exact B387191
  · exact B387195
  · exact B387199
  · exact B387203
  · exact B387207
  · exact B387211
  · exact B387215
  · exact B387219
  · exact B387223
  · exact B387227
  · exact B387231
  · exact B387235
  · exact B387239
  · exact B387243
  · exact B387247
  · exact B387251
  · exact B387255
  · exact B387259
  · exact B387263
  · exact B387267
  · exact B387271
  · exact B387275
  · exact B387279
  · exact B387283
  · exact B387287
  · exact B387291
  · exact B387295
  · exact B387299
  · exact B387303
  · exact B387307
  · exact B387311
  · exact B387315
  · exact B387319
  · exact B387323
  · exact B387327
  · exact B387331
  · exact B387335
  · exact B387339
  · exact B387343
  · exact B387347
  · exact B387351
  · exact B387355
  · exact B387359
  · exact B387363
  · exact B387367
  · exact B387371
  · exact B387375
  · exact B387379
  · exact B387383
  · exact B387387
  · exact B387391
  · exact B387395
  · exact B387399
  · exact B387403
  · exact B387407
  · exact B387411
  · exact B387415
  · exact B387419
  · exact B387423
  · exact B387427
  · exact B387431
  · exact B387435
  · exact B387439
  · exact B387443
  · exact B387447
  · exact B387451
  · exact B387455
  · exact B387459
  · exact B387463
  · exact B387467
  · exact B387471
  · exact B387475
  · exact B387479
  · exact B387483
  · exact B387487
  · exact B387491
  · exact B387495
  · exact B387499
  · exact B387503
  · exact B387507
  · exact B387511
  · exact B387515
  · exact B387519
  · exact B387523
  · exact B387527
  · exact B387531
  · exact B387535
  · exact B387539
  · exact B387543
  · exact B387547
  · exact B387551
  · exact B387555
  · exact B387559
  · exact B387563
  · exact B387567
  · exact B387571
  · exact B387575
  · exact B387579
  · exact B387583
  · exact B387587
  · exact B387591
  · exact B387595
  · exact B387599
  · exact B387603
  · exact B387607
  · exact B387611
  · exact B387615
  · exact B387619
  · exact B387623
  · exact B387627
  · exact B387631
  · exact B387635
  · exact B387639
  · exact B387643
  · exact B387647
  · exact B387651
  · exact B387655
  · exact B387659
  · exact B387663
  · exact B387667
  · exact B387671
  · exact B387675
  · exact B387679
  · exact B387683
  · exact B387687
  · exact B387691
  · exact B387695
  · exact B387699
  · exact B387703
  · exact B387707
  · exact B387711
  · exact B387715
  · exact B387719
  · exact B387723
  · exact B387727
  · exact B387731
  · exact B387735
  · exact B387739
  · exact B387743
  · exact B387747
  · exact B387751
  · exact B387755
  · exact B387759
  · exact B387763
  · exact B387767
  · exact B387771
  · exact B387775
  · exact B387779
  · exact B387783
  · exact B387787
  · exact B387791
  · exact B387795
  · exact B387799
  · exact B387803
  · exact B387807
  · exact B387811
  · exact B387815
  · exact B387819
  · exact B387823
  · exact B387827
  · exact B387831
  · exact B387835
  · exact B387839
  · exact B387843
  · exact B387847
  · exact B387851
  · exact B387855
  · exact B387859
  · exact B387863
  · exact B387867
  · exact B387871
  · exact B387875
  · exact B387879
  · exact B387883
  · exact B387887
  · exact B387891
  · exact B387895
  · exact B387899
  · exact B387903
  · exact B387907
  · exact B387911
  · exact B387915
  · exact B387919
  · exact B387923
  · exact B387927
  · exact B387931
  · exact B387935
  · exact B387939
  · exact B387943
  · exact B387947
  · exact B387951
  · exact B387955
  · exact B387959
  · exact B387963
  · exact B387967
  · exact B387971
  · exact B387975
  · exact B387979
  · exact B387983
  · exact B387987
  · exact B387991
  · exact B387995
  · exact B387999
  · exact B388003
  · exact B388007
  · exact B388011
  · exact B388015
  · exact B388019
  · exact B388023
  · exact B388027
  · exact B388031
  · exact B388035
  · exact B388039
  · exact B388043
  · exact B388047
  · exact B388051
  · exact B388055
  · exact B388059
  · exact B388063
  · exact B388067
  · exact B388071
  · exact B388075
  · exact B388079
  · exact B388083
  · exact B388087
  · exact B388091
  · exact B388095
  · exact B388099
  · exact B388103
  · exact B388107
  · exact B388111
  · exact B388115
  · exact B388119
  · exact B388123
  · exact B388127
  · exact B388131
  · exact B388135
  · exact B388139
  · exact B388143
  · exact B388147
  · exact B388151
  · exact B388155
  · exact B388159
  · exact B388163
  · exact B388167
  · exact B388171
  · exact B388175
  · exact B388179
  · exact B388183
  · exact B388187
  · exact B388191
  · exact B388195
  · exact B388199
  · exact B388203
  · exact B388207
  · exact B388211
  · exact B388215
  · exact B388219
  · exact B388223
  · exact B388227
  · exact B388231
  · exact B388235
  · exact B388239
  · exact B388243
  · exact B388247
  · exact B388251
  · exact B388255
  · exact B388259
  · exact B388263
  · exact B388267
  · exact B388271
  · exact B388275
  · exact B388279
  · exact B388283
  · exact B388287
  · exact B388291
  · exact B388295
  · exact B388299
  · exact B388303
  · exact B388307
  · exact B388311
  · exact B388315
  · exact B388319
  · exact B388323
  · exact B388327
  · exact B388331
  · exact B388335
  · exact B388339
  · exact B388343
  · exact B388347
  · exact B388351
  · exact B388355
  · exact B388359
  · exact B388363
  · exact B388367
  · exact B388371
  · exact B388375
  · exact B388379
  · exact B388383
  · exact B388387
  · exact B388391
  · exact B388395
  · exact B388399
  · exact B388403
  · exact B388407
  · exact B388411
  · exact B388415
  · exact B388419
  · exact B388423
  · exact B388427
  · exact B388431
  · exact B388435
  · exact B388439
  · exact B388443
  · exact B388447
  · exact B388451
  · exact B388455
  · exact B388459
  · exact B388463
  · exact B388467
  · exact B388471
  · exact B388475
  · exact B388479
  · exact B388483
  · exact B388487
  · exact B388491
  · exact B388495
  · exact B388499
  · exact B388503
  · exact B388507
  · exact B388511
  · exact B388515
  · exact B388519
  · exact B388523
  · exact B388527
  · exact B388531
  · exact B388535
  · exact B388539
  · exact B388543
  · exact B388547
  · exact B388551
  · exact B388555
  · exact B388559
  · exact B388563

theorem C1 (j : ℕ) (h1 : 97141 ≤ j) (h2 : j ≤ 97440) : Blo 385764 (4 * j + 3) := by
  interval_cases j
  · exact B388567
  · exact B388571
  · exact B388575
  · exact B388579
  · exact B388583
  · exact B388587
  · exact B388591
  · exact B388595
  · exact B388599
  · exact B388603
  · exact B388607
  · exact B388611
  · exact B388615
  · exact B388619
  · exact B388623
  · exact B388627
  · exact B388631
  · exact B388635
  · exact B388639
  · exact B388643
  · exact B388647
  · exact B388651
  · exact B388655
  · exact B388659
  · exact B388663
  · exact B388667
  · exact B388671
  · exact B388675
  · exact B388679
  · exact B388683
  · exact B388687
  · exact B388691
  · exact B388695
  · exact B388699
  · exact B388703
  · exact B388707
  · exact B388711
  · exact B388715
  · exact B388719
  · exact B388723
  · exact B388727
  · exact B388731
  · exact B388735
  · exact B388739
  · exact B388743
  · exact B388747
  · exact B388751
  · exact B388755
  · exact B388759
  · exact B388763
  · exact B388767
  · exact B388771
  · exact B388775
  · exact B388779
  · exact B388783
  · exact B388787
  · exact B388791
  · exact B388795
  · exact B388799
  · exact B388803
  · exact B388807
  · exact B388811
  · exact B388815
  · exact B388819
  · exact B388823
  · exact B388827
  · exact B388831
  · exact B388835
  · exact B388839
  · exact B388843
  · exact B388847
  · exact B388851
  · exact B388855
  · exact B388859
  · exact B388863
  · exact B388867
  · exact B388871
  · exact B388875
  · exact B388879
  · exact B388883
  · exact B388887
  · exact B388891
  · exact B388895
  · exact B388899
  · exact B388903
  · exact B388907
  · exact B388911
  · exact B388915
  · exact B388919
  · exact B388923
  · exact B388927
  · exact B388931
  · exact B388935
  · exact B388939
  · exact B388943
  · exact B388947
  · exact B388951
  · exact B388955
  · exact B388959
  · exact B388963
  · exact B388967
  · exact B388971
  · exact B388975
  · exact B388979
  · exact B388983
  · exact B388987
  · exact B388991
  · exact B388995
  · exact B388999
  · exact B389003
  · exact B389007
  · exact B389011
  · exact B389015
  · exact B389019
  · exact B389023
  · exact B389027
  · exact B389031
  · exact B389035
  · exact B389039
  · exact B389043
  · exact B389047
  · exact B389051
  · exact B389055
  · exact B389059
  · exact B389063
  · exact B389067
  · exact B389071
  · exact B389075
  · exact B389079
  · exact B389083
  · exact B389087
  · exact B389091
  · exact B389095
  · exact B389099
  · exact B389103
  · exact B389107
  · exact B389111
  · exact B389115
  · exact B389119
  · exact B389123
  · exact B389127
  · exact B389131
  · exact B389135
  · exact B389139
  · exact B389143
  · exact B389147
  · exact B389151
  · exact B389155
  · exact B389159
  · exact B389163
  · exact B389167
  · exact B389171
  · exact B389175
  · exact B389179
  · exact B389183
  · exact B389187
  · exact B389191
  · exact B389195
  · exact B389199
  · exact B389203
  · exact B389207
  · exact B389211
  · exact B389215
  · exact B389219
  · exact B389223
  · exact B389227
  · exact B389231
  · exact B389235
  · exact B389239
  · exact B389243
  · exact B389247
  · exact B389251
  · exact B389255
  · exact B389259
  · exact B389263
  · exact B389267
  · exact B389271
  · exact B389275
  · exact B389279
  · exact B389283
  · exact B389287
  · exact B389291
  · exact B389295
  · exact B389299
  · exact B389303
  · exact B389307
  · exact B389311
  · exact B389315
  · exact B389319
  · exact B389323
  · exact B389327
  · exact B389331
  · exact B389335
  · exact B389339
  · exact B389343
  · exact B389347
  · exact B389351
  · exact B389355
  · exact B389359
  · exact B389363
  · exact B389367
  · exact B389371
  · exact B389375
  · exact B389379
  · exact B389383
  · exact B389387
  · exact B389391
  · exact B389395
  · exact B389399
  · exact B389403
  · exact B389407
  · exact B389411
  · exact B389415
  · exact B389419
  · exact B389423
  · exact B389427
  · exact B389431
  · exact B389435
  · exact B389439
  · exact B389443
  · exact B389447
  · exact B389451
  · exact B389455
  · exact B389459
  · exact B389463
  · exact B389467
  · exact B389471
  · exact B389475
  · exact B389479
  · exact B389483
  · exact B389487
  · exact B389491
  · exact B389495
  · exact B389499
  · exact B389503
  · exact B389507
  · exact B389511
  · exact B389515
  · exact B389519
  · exact B389523
  · exact B389527
  · exact B389531
  · exact B389535
  · exact B389539
  · exact B389543
  · exact B389547
  · exact B389551
  · exact B389555
  · exact B389559
  · exact B389563
  · exact B389567
  · exact B389571
  · exact B389575
  · exact B389579
  · exact B389583
  · exact B389587
  · exact B389591
  · exact B389595
  · exact B389599
  · exact B389603
  · exact B389607
  · exact B389611
  · exact B389615
  · exact B389619
  · exact B389623
  · exact B389627
  · exact B389631
  · exact B389635
  · exact B389639
  · exact B389643
  · exact B389647
  · exact B389651
  · exact B389655
  · exact B389659
  · exact B389663
  · exact B389667
  · exact B389671
  · exact B389675
  · exact B389679
  · exact B389683
  · exact B389687
  · exact B389691
  · exact B389695
  · exact B389699
  · exact B389703
  · exact B389707
  · exact B389711
  · exact B389715
  · exact B389719
  · exact B389723
  · exact B389727
  · exact B389731
  · exact B389735
  · exact B389739
  · exact B389743
  · exact B389747
  · exact B389751
  · exact B389755
  · exact B389759
  · exact B389763

theorem solution (m : ℕ) (hlo : 385764 ≤ m) (hhi : m ≤ 389764) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 96441 ≤ j := by omega
    have hj2 : j ≤ 97440 := by omega
    have hb : Blo 385764 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 97141 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
