-- Prove2me | solution 1 for syracuse_descends_range_1366502_1368502
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:12:58.547241+00:00
-- url     : https://prove2.me/submissions/0df29acf-99b9-4a8b-985d-7dc1cc0628a9

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


theorem B7110773 : Blo 1366502 7110773 := bbase (se 5 (by rfl) ⟨333317, by rfl⟩ : syracuseStep 7110773 = 666635) (by norm_num)
theorem B2629757 : Blo 1366502 2629757 := bbase (se 3 (by rfl) ⟨493079, by rfl⟩ : syracuseStep 2629757 = 986159) (by norm_num)
theorem B6922421 : Blo 1366502 6922421 := bbase (se 5 (by rfl) ⟨324488, by rfl⟩ : syracuseStep 6922421 = 648977) (by norm_num)
theorem B6004949 : Blo 1366502 6004949 := bbase (se 7 (by rfl) ⟨70370, by rfl⟩ : syracuseStep 6004949 = 140741) (by norm_num)
theorem B2597093 : Blo 1366502 2597093 := bbase (se 4 (by rfl) ⟨243477, by rfl⟩ : syracuseStep 2597093 = 486955) (by norm_num)
theorem B5193989 : Blo 1366502 5193989 := bbase (se 4 (by rfl) ⟨486936, by rfl⟩ : syracuseStep 5193989 = 973873) (by norm_num)
theorem B4382981 : Blo 1366502 4382981 := bbase (se 4 (by rfl) ⟨410904, by rfl⟩ : syracuseStep 4382981 = 821809) (by norm_num)
theorem B3891493 : Blo 1366502 3891493 := bbase (se 4 (by rfl) ⟨364827, by rfl⟩ : syracuseStep 3891493 = 729655) (by norm_num)
theorem B1753417 : Blo 1366502 1753417 := bbase (se 2 (by rfl) ⟨657531, by rfl⟩ : syracuseStep 1753417 = 1315063) (by norm_num)
theorem B18702677 : Blo 1366502 18702677 := bbase (se 10 (by rfl) ⟨27396, by rfl⟩ : syracuseStep 18702677 = 54793) (by norm_num)
theorem B94724437 : Blo 1366502 94724437 := bbase (se 10 (by rfl) ⟨138756, by rfl⟩ : syracuseStep 94724437 = 277513) (by norm_num)
theorem B4612517 : Blo 1366502 4612517 := bbase (se 4 (by rfl) ⟨432423, by rfl⟩ : syracuseStep 4612517 = 864847) (by norm_num)
theorem B3555805 : Blo 1366502 3555805 := bbase (se 3 (by rfl) ⟨666713, by rfl⟩ : syracuseStep 3555805 = 1333427) (by norm_num)
theorem B5194277 : Blo 1366502 5194277 := bbase (se 4 (by rfl) ⟨486963, by rfl⟩ : syracuseStep 5194277 = 973927) (by norm_num)
theorem B7782965 : Blo 1366502 7782965 := bbase (se 5 (by rfl) ⟨364826, by rfl⟩ : syracuseStep 7782965 = 729653) (by norm_num)
theorem B3949253 : Blo 1366502 3949253 := bbase (se 4 (by rfl) ⟨370242, by rfl⟩ : syracuseStep 3949253 = 740485) (by norm_num)
theorem B4997861 : Blo 1366502 4997861 := bbase (se 4 (by rfl) ⟨468549, by rfl⟩ : syracuseStep 4997861 = 937099) (by norm_num)
theorem B3506957 : Blo 1366502 3506957 := bbase (se 3 (by rfl) ⟨657554, by rfl⟩ : syracuseStep 3506957 = 1315109) (by norm_num)
theorem B2220853 : Blo 1366502 2220853 := bbase (se 5 (by rfl) ⟨104102, by rfl⟩ : syracuseStep 2220853 = 208205) (by norm_num)
theorem B4612949 : Blo 1366502 4612949 := bbase (se 9 (by rfl) ⟨13514, by rfl⟩ : syracuseStep 4612949 = 27029) (by norm_num)
theorem B2499517 : Blo 1366502 2499517 := bbase (se 3 (by rfl) ⟨468659, by rfl⟩ : syracuseStep 2499517 = 937319) (by norm_num)
theorem B2597845 : Blo 1366502 2597845 := bbase (se 7 (by rfl) ⟨30443, by rfl⟩ : syracuseStep 2597845 = 60887) (by norm_num)
theorem B1729613 : Blo 1366502 1729613 := bbase (se 3 (by rfl) ⟨324302, by rfl⟩ : syracuseStep 1729613 = 648605) (by norm_num)
theorem B2597989 : Blo 1366502 2597989 := bbase (se 4 (by rfl) ⟨243561, by rfl⟩ : syracuseStep 2597989 = 487123) (by norm_num)
theorem B1729669 : Blo 1366502 1729669 := bbase (se 4 (by rfl) ⟨162156, by rfl⟩ : syracuseStep 1729669 = 324313) (by norm_num)
theorem B1729765 : Blo 1366502 1729765 := bbase (se 4 (by rfl) ⟨162165, by rfl⟩ : syracuseStep 1729765 = 324331) (by norm_num)
theorem B4613381 : Blo 1366502 4613381 := bbase (se 4 (by rfl) ⟨432504, by rfl⟩ : syracuseStep 4613381 = 865009) (by norm_num)
theorem B1385797 : Blo 1366502 1385797 := bbase (se 4 (by rfl) ⟨129918, by rfl⟩ : syracuseStep 1385797 = 259837) (by norm_num)
theorem B1385821 : Blo 1366502 1385821 := bbase (se 3 (by rfl) ⟨259841, by rfl⟩ : syracuseStep 1385821 = 519683) (by norm_num)
theorem B1729937 : Blo 1366502 1729937 := bbase (se 2 (by rfl) ⟨648726, by rfl⟩ : syracuseStep 1729937 = 1297453) (by norm_num)
theorem B17515925 : Blo 1366502 17515925 := bbase (se 6 (by rfl) ⟨410529, by rfl⟩ : syracuseStep 17515925 = 821059) (by norm_num)
theorem B6235541 : Blo 1366502 6235541 := bbase (se 6 (by rfl) ⟨146145, by rfl⟩ : syracuseStep 6235541 = 292291) (by norm_num)
theorem B6923717 : Blo 1366502 6923717 := bbase (se 4 (by rfl) ⟨649098, by rfl⟩ : syracuseStep 6923717 = 1298197) (by norm_num)
theorem B1729993 : Blo 1366502 1729993 := bbase (se 2 (by rfl) ⟨648747, by rfl⟩ : syracuseStep 1729993 = 1297495) (by norm_num)
theorem B1459669 : Blo 1366502 1459669 := bbase (se 7 (by rfl) ⟨17105, by rfl⟩ : syracuseStep 1459669 = 34211) (by norm_num)
theorem B1459729 : Blo 1366502 1459729 := bbase (se 2 (by rfl) ⟨547398, by rfl⟩ : syracuseStep 1459729 = 1094797) (by norm_num)
theorem B11240981 : Blo 1366502 11240981 := bbase (se 6 (by rfl) ⟨263460, by rfl⟩ : syracuseStep 11240981 = 526921) (by norm_num)
theorem B5842469 : Blo 1366502 5842469 := bbase (se 4 (by rfl) ⟨547731, by rfl⟩ : syracuseStep 5842469 = 1095463) (by norm_num)
theorem B1730089 : Blo 1366502 1730089 := bbase (se 2 (by rfl) ⟨648783, by rfl⟩ : syracuseStep 1730089 = 1297567) (by norm_num)
theorem B1386113 : Blo 1366502 1386113 := bbase (se 2 (by rfl) ⟨519792, by rfl⟩ : syracuseStep 1386113 = 1039585) (by norm_num)
theorem B3286669 : Blo 1366502 3286669 := bbase (se 3 (by rfl) ⟨616250, by rfl⟩ : syracuseStep 3286669 = 1232501) (by norm_num)
theorem B3696293 : Blo 1366502 3696293 := bbase (se 4 (by rfl) ⟨346527, by rfl⟩ : syracuseStep 3696293 = 693055) (by norm_num)
theorem B4613813 : Blo 1366502 4613813 := bbase (se 5 (by rfl) ⟨216272, by rfl⟩ : syracuseStep 4613813 = 432545) (by norm_num)
theorem B5195461 : Blo 1366502 5195461 := bbase (se 4 (by rfl) ⟨487074, by rfl⟩ : syracuseStep 5195461 = 974149) (by norm_num)
theorem B1730261 : Blo 1366502 1730261 := bbase (se 7 (by rfl) ⟨20276, by rfl⟩ : syracuseStep 1730261 = 40553) (by norm_num)
theorem B2049773 : Blo 1366502 2049773 := bbase (se 3 (by rfl) ⟨384332, by rfl⟩ : syracuseStep 2049773 = 768665) (by norm_num)
theorem B2049797 : Blo 1366502 2049797 := bbase (se 4 (by rfl) ⟨192168, by rfl⟩ : syracuseStep 2049797 = 384337) (by norm_num)
theorem B3892997 : Blo 1366502 3892997 := bbase (se 4 (by rfl) ⟨364968, by rfl⟩ : syracuseStep 3892997 = 729937) (by norm_num)
theorem B1730317 : Blo 1366502 1730317 := bbase (se 3 (by rfl) ⟨324434, by rfl⟩ : syracuseStep 1730317 = 648869) (by norm_num)
theorem B19703573 : Blo 1366502 19703573 := bbase (se 6 (by rfl) ⟨461802, by rfl⟩ : syracuseStep 19703573 = 923605) (by norm_num)
theorem B2049821 : Blo 1366502 2049821 := bbase (se 3 (by rfl) ⟨384341, by rfl⟩ : syracuseStep 2049821 = 768683) (by norm_num)
theorem B2049845 : Blo 1366502 2049845 := bbase (se 5 (by rfl) ⟨96086, by rfl⟩ : syracuseStep 2049845 = 192173) (by norm_num)
theorem B5130037 : Blo 1366502 5130037 := bbase (se 5 (by rfl) ⟨240470, by rfl⟩ : syracuseStep 5130037 = 480941) (by norm_num)
theorem B2049869 : Blo 1366502 2049869 := bbase (se 3 (by rfl) ⟨384350, by rfl⟩ : syracuseStep 2049869 = 768701) (by norm_num)
theorem B1460045 : Blo 1366502 1460045 := bbase (se 3 (by rfl) ⟨273758, by rfl⟩ : syracuseStep 1460045 = 547517) (by norm_num)
theorem B2049893 : Blo 1366502 2049893 := bbase (se 4 (by rfl) ⟨192177, by rfl⟩ : syracuseStep 2049893 = 384355) (by norm_num)
theorem B1730413 : Blo 1366502 1730413 := bbase (se 3 (by rfl) ⟨324452, by rfl⟩ : syracuseStep 1730413 = 648905) (by norm_num)
theorem B2049917 : Blo 1366502 2049917 := bbase (se 3 (by rfl) ⟨384359, by rfl⟩ : syracuseStep 2049917 = 768719) (by norm_num)
theorem B2049941 : Blo 1366502 2049941 := bbase (se 6 (by rfl) ⟨48045, by rfl⟩ : syracuseStep 2049941 = 96091) (by norm_num)
theorem B5547941 : Blo 1366502 5547941 := bbase (se 4 (by rfl) ⟨520119, by rfl⟩ : syracuseStep 5547941 = 1040239) (by norm_num)
theorem B2049965 : Blo 1366502 2049965 := bbase (se 3 (by rfl) ⟨384368, by rfl⟩ : syracuseStep 2049965 = 768737) (by norm_num)
theorem B11675573 : Blo 1366502 11675573 := bbase (se 5 (by rfl) ⟨547292, by rfl⟩ : syracuseStep 11675573 = 1094585) (by norm_num)
theorem B2049989 : Blo 1366502 2049989 := bbase (se 4 (by rfl) ⟨192186, by rfl⟩ : syracuseStep 2049989 = 384373) (by norm_num)
theorem B2050013 : Blo 1366502 2050013 := bbase (se 3 (by rfl) ⟨384377, by rfl⟩ : syracuseStep 2050013 = 768755) (by norm_num)
theorem B2050037 : Blo 1366502 2050037 := bbase (se 5 (by rfl) ⟨96095, by rfl⟩ : syracuseStep 2050037 = 192191) (by norm_num)
theorem B5195765 : Blo 1366502 5195765 := bbase (se 5 (by rfl) ⟨243551, by rfl⟩ : syracuseStep 5195765 = 487103) (by norm_num)
theorem B2050061 : Blo 1366502 2050061 := bbase (se 3 (by rfl) ⟨384386, by rfl⟩ : syracuseStep 2050061 = 768773) (by norm_num)
theorem B4925461 : Blo 1366502 4925461 := bbase (se 6 (by rfl) ⟨115440, by rfl⟩ : syracuseStep 4925461 = 230881) (by norm_num)
theorem B1730585 : Blo 1366502 1730585 := bbase (se 2 (by rfl) ⟨648969, by rfl⟩ : syracuseStep 1730585 = 1297939) (by norm_num)
theorem B2050085 : Blo 1366502 2050085 := bbase (se 4 (by rfl) ⟨192195, by rfl⟩ : syracuseStep 2050085 = 384391) (by norm_num)
theorem B3459125 : Blo 1366502 3459125 := bbase (se 5 (by rfl) ⟨162146, by rfl⟩ : syracuseStep 3459125 = 324293) (by norm_num)
theorem B2050109 : Blo 1366502 2050109 := bbase (se 3 (by rfl) ⟨384395, by rfl⟩ : syracuseStep 2050109 = 768791) (by norm_num)
theorem B1730641 : Blo 1366502 1730641 := bbase (se 2 (by rfl) ⟨648990, by rfl⟩ : syracuseStep 1730641 = 1297981) (by norm_num)
theorem B2050133 : Blo 1366502 2050133 := bbase (se 8 (by rfl) ⟨12012, by rfl⟩ : syracuseStep 2050133 = 24025) (by norm_num)
theorem B2918501 : Blo 1366502 2918501 := bbase (se 4 (by rfl) ⟨273609, by rfl⟩ : syracuseStep 2918501 = 547219) (by norm_num)
theorem B4614245 : Blo 1366502 4614245 := bbase (se 4 (by rfl) ⟨432585, by rfl⟩ : syracuseStep 4614245 = 865171) (by norm_num)
theorem B2050157 : Blo 1366502 2050157 := bbase (se 3 (by rfl) ⟨384404, by rfl⟩ : syracuseStep 2050157 = 768809) (by norm_num)
theorem B2050181 : Blo 1366502 2050181 := bbase (se 4 (by rfl) ⟨192204, by rfl⟩ : syracuseStep 2050181 = 384409) (by norm_num)
theorem B2050205 : Blo 1366502 2050205 := bbase (se 3 (by rfl) ⟨384413, by rfl⟩ : syracuseStep 2050205 = 768827) (by norm_num)
theorem B1730737 : Blo 1366502 1730737 := bbase (se 2 (by rfl) ⟨649026, by rfl⟩ : syracuseStep 1730737 = 1298053) (by norm_num)
theorem B2050229 : Blo 1366502 2050229 := bbase (se 5 (by rfl) ⟨96104, by rfl⟩ : syracuseStep 2050229 = 192209) (by norm_num)
theorem B2050253 : Blo 1366502 2050253 := bbase (se 3 (by rfl) ⟨384422, by rfl⟩ : syracuseStep 2050253 = 768845) (by norm_num)
theorem B2050277 : Blo 1366502 2050277 := bbase (se 4 (by rfl) ⟨192213, by rfl⟩ : syracuseStep 2050277 = 384427) (by norm_num)
theorem B2050301 : Blo 1366502 2050301 := bbase (se 3 (by rfl) ⟨384431, by rfl⟩ : syracuseStep 2050301 = 768863) (by norm_num)
theorem B1460489 : Blo 1366502 1460489 := bbase (se 2 (by rfl) ⟨547683, by rfl⟩ : syracuseStep 1460489 = 1095367) (by norm_num)
theorem B1665293 : Blo 1366502 1665293 := bbase (se 3 (by rfl) ⟨312242, by rfl⟩ : syracuseStep 1665293 = 624485) (by norm_num)
theorem B2050325 : Blo 1366502 2050325 := bbase (se 6 (by rfl) ⟨48054, by rfl⟩ : syracuseStep 2050325 = 96109) (by norm_num)
theorem B2050349 : Blo 1366502 2050349 := bbase (se 3 (by rfl) ⟨384440, by rfl⟩ : syracuseStep 2050349 = 768881) (by norm_num)
theorem B1755445 : Blo 1366502 1755445 := bbase (se 5 (by rfl) ⟨82286, by rfl⟩ : syracuseStep 1755445 = 164573) (by norm_num)
theorem B2050373 : Blo 1366502 2050373 := bbase (se 4 (by rfl) ⟨192222, by rfl⟩ : syracuseStep 2050373 = 384445) (by norm_num)
theorem B1460549 : Blo 1366502 1460549 := bbase (se 4 (by rfl) ⟨136926, by rfl⟩ : syracuseStep 1460549 = 273853) (by norm_num)
theorem B2918749 : Blo 1366502 2918749 := bbase (se 3 (by rfl) ⟨547265, by rfl⟩ : syracuseStep 2918749 = 1094531) (by norm_num)
theorem B2050397 : Blo 1366502 2050397 := bbase (se 3 (by rfl) ⟨384449, by rfl⟩ : syracuseStep 2050397 = 768899) (by norm_num)
theorem B1730909 : Blo 1366502 1730909 := bbase (se 3 (by rfl) ⟨324545, by rfl⟩ : syracuseStep 1730909 = 649091) (by norm_num)
theorem B2050421 : Blo 1366502 2050421 := bbase (se 5 (by rfl) ⟨96113, by rfl⟩ : syracuseStep 2050421 = 192227) (by norm_num)
theorem B3459469 : Blo 1366502 3459469 := bbase (se 3 (by rfl) ⟨648650, by rfl⟩ : syracuseStep 3459469 = 1297301) (by norm_num)
theorem B2050445 : Blo 1366502 2050445 := bbase (se 3 (by rfl) ⟨384458, by rfl⟩ : syracuseStep 2050445 = 768917) (by norm_num)
theorem B1730965 : Blo 1366502 1730965 := bbase (se 6 (by rfl) ⟨40569, by rfl⟩ : syracuseStep 1730965 = 81139) (by norm_num)
theorem B2050469 : Blo 1366502 2050469 := bbase (se 4 (by rfl) ⟨192231, by rfl⟩ : syracuseStep 2050469 = 384463) (by norm_num)
theorem B2050493 : Blo 1366502 2050493 := bbase (se 3 (by rfl) ⟨384467, by rfl⟩ : syracuseStep 2050493 = 768935) (by norm_num)
theorem B1460677 : Blo 1366502 1460677 := bbase (se 4 (by rfl) ⟨136938, by rfl⟩ : syracuseStep 1460677 = 273877) (by norm_num)
theorem B2050517 : Blo 1366502 2050517 := bbase (se 7 (by rfl) ⟨24029, by rfl⟩ : syracuseStep 2050517 = 48059) (by norm_num)
theorem B1386973 : Blo 1366502 1386973 := bbase (se 3 (by rfl) ⟨260057, by rfl⟩ : syracuseStep 1386973 = 520115) (by norm_num)
theorem B2050541 : Blo 1366502 2050541 := bbase (se 3 (by rfl) ⟨384476, by rfl⟩ : syracuseStep 2050541 = 768953) (by norm_num)
theorem B1731061 : Blo 1366502 1731061 := bbase (se 5 (by rfl) ⟨81143, by rfl⟩ : syracuseStep 1731061 = 162287) (by norm_num)
theorem B2632181 : Blo 1366502 2632181 := bbase (se 5 (by rfl) ⟨123383, by rfl⟩ : syracuseStep 2632181 = 246767) (by norm_num)
theorem B3459581 : Blo 1366502 3459581 := bbase (se 3 (by rfl) ⟨648671, by rfl⟩ : syracuseStep 3459581 = 1297343) (by norm_num)
theorem B2050565 : Blo 1366502 2050565 := bbase (se 4 (by rfl) ⟨192240, by rfl⟩ : syracuseStep 2050565 = 384481) (by norm_num)
theorem B2189837 : Blo 1366502 2189837 := bbase (se 3 (by rfl) ⟨410594, by rfl⟩ : syracuseStep 2189837 = 821189) (by norm_num)
theorem B4614677 : Blo 1366502 4614677 := bbase (se 6 (by rfl) ⟨108156, by rfl⟩ : syracuseStep 4614677 = 216313) (by norm_num)
theorem B2050589 : Blo 1366502 2050589 := bbase (se 3 (by rfl) ⟨384485, by rfl⟩ : syracuseStep 2050589 = 768971) (by norm_num)
theorem B2050613 : Blo 1366502 2050613 := bbase (se 5 (by rfl) ⟨96122, by rfl⟩ : syracuseStep 2050613 = 192245) (by norm_num)
theorem B2050637 : Blo 1366502 2050637 := bbase (se 3 (by rfl) ⟨384494, by rfl⟩ : syracuseStep 2050637 = 768989) (by norm_num)
theorem B2050661 : Blo 1366502 2050661 := bbase (se 4 (by rfl) ⟨192249, by rfl⟩ : syracuseStep 2050661 = 384499) (by norm_num)
theorem B2108005 : Blo 1366502 2108005 := bbase (se 4 (by rfl) ⟨197625, by rfl⟩ : syracuseStep 2108005 = 395251) (by norm_num)
theorem B3074669 : Blo 1366502 3074669 := bbase (se 3 (by rfl) ⟨576500, by rfl⟩ : syracuseStep 3074669 = 1153001) (by norm_num)
theorem B2050685 : Blo 1366502 2050685 := bbase (se 3 (by rfl) ⟨384503, by rfl⟩ : syracuseStep 2050685 = 769007) (by norm_num)
theorem B2050709 : Blo 1366502 2050709 := bbase (se 6 (by rfl) ⟨48063, by rfl⟩ : syracuseStep 2050709 = 96127) (by norm_num)
theorem B1731233 : Blo 1366502 1731233 := bbase (se 2 (by rfl) ⟨649212, by rfl⟩ : syracuseStep 1731233 = 1298425) (by norm_num)
theorem B2050733 : Blo 1366502 2050733 := bbase (se 3 (by rfl) ⟨384512, by rfl⟩ : syracuseStep 2050733 = 769025) (by norm_num)
theorem B3074741 : Blo 1366502 3074741 := bbase (se 5 (by rfl) ⟨144128, by rfl⟩ : syracuseStep 3074741 = 288257) (by norm_num)
theorem B3459773 : Blo 1366502 3459773 := bbase (se 3 (by rfl) ⟨648707, by rfl⟩ : syracuseStep 3459773 = 1297415) (by norm_num)
theorem B2050757 : Blo 1366502 2050757 := bbase (se 4 (by rfl) ⟨192258, by rfl⟩ : syracuseStep 2050757 = 384517) (by norm_num)
theorem B7785173 : Blo 1366502 7785173 := bbase (se 7 (by rfl) ⟨91232, by rfl⟩ : syracuseStep 7785173 = 182465) (by norm_num)
theorem B6925013 : Blo 1366502 6925013 := bbase (se 7 (by rfl) ⟨81152, by rfl⟩ : syracuseStep 6925013 = 162305) (by norm_num)
theorem B1731289 : Blo 1366502 1731289 := bbase (se 2 (by rfl) ⟨649233, by rfl⟩ : syracuseStep 1731289 = 1298467) (by norm_num)
theorem B2050781 : Blo 1366502 2050781 := bbase (se 3 (by rfl) ⟨384521, by rfl⟩ : syracuseStep 2050781 = 769043) (by norm_num)
theorem B2050805 : Blo 1366502 2050805 := bbase (se 5 (by rfl) ⟨96131, by rfl⟩ : syracuseStep 2050805 = 192263) (by norm_num)
theorem B3074813 : Blo 1366502 3074813 := bbase (se 3 (by rfl) ⟨576527, by rfl⟩ : syracuseStep 3074813 = 1153055) (by norm_num)
theorem B2050829 : Blo 1366502 2050829 := bbase (se 3 (by rfl) ⟨384530, by rfl⟩ : syracuseStep 2050829 = 769061) (by norm_num)
theorem B2050853 : Blo 1366502 2050853 := bbase (se 4 (by rfl) ⟨192267, by rfl⟩ : syracuseStep 2050853 = 384535) (by norm_num)
theorem B1731385 : Blo 1366502 1731385 := bbase (se 2 (by rfl) ⟨649269, by rfl⟩ : syracuseStep 1731385 = 1298539) (by norm_num)
theorem B2050877 : Blo 1366502 2050877 := bbase (se 3 (by rfl) ⟨384539, by rfl⟩ : syracuseStep 2050877 = 769079) (by norm_num)
theorem B3074885 : Blo 1366502 3074885 := bbase (se 4 (by rfl) ⟨288270, by rfl⟩ : syracuseStep 3074885 = 576541) (by norm_num)
theorem B2919253 : Blo 1366502 2919253 := bbase (se 9 (by rfl) ⟨8552, by rfl⟩ : syracuseStep 2919253 = 17105) (by norm_num)
theorem B2050901 : Blo 1366502 2050901 := bbase (se 9 (by rfl) ⟨6008, by rfl⟩ : syracuseStep 2050901 = 12017) (by norm_num)
theorem B2050925 : Blo 1366502 2050925 := bbase (se 3 (by rfl) ⟨384548, by rfl⟩ : syracuseStep 2050925 = 769097) (by norm_num)
theorem B1461121 : Blo 1366502 1461121 := bbase (se 2 (by rfl) ⟨547920, by rfl⟩ : syracuseStep 1461121 = 1095841) (by norm_num)
theorem B2050949 : Blo 1366502 2050949 := bbase (se 4 (by rfl) ⟨192276, by rfl⟩ : syracuseStep 2050949 = 384553) (by norm_num)
theorem B3074957 : Blo 1366502 3074957 := bbase (se 3 (by rfl) ⟨576554, by rfl⟩ : syracuseStep 3074957 = 1153109) (by norm_num)
theorem B2771869 : Blo 1366502 2771869 := bbase (se 3 (by rfl) ⟨519725, by rfl⟩ : syracuseStep 2771869 = 1039451) (by norm_num)
theorem B2050973 : Blo 1366502 2050973 := bbase (se 3 (by rfl) ⟨384557, by rfl⟩ : syracuseStep 2050973 = 769115) (by norm_num)
theorem B2050997 : Blo 1366502 2050997 := bbase (se 5 (by rfl) ⟨96140, by rfl⟩ : syracuseStep 2050997 = 192281) (by norm_num)
theorem B4615109 : Blo 1366502 4615109 := bbase (se 4 (by rfl) ⟨432666, by rfl⟩ : syracuseStep 4615109 = 865333) (by norm_num)
theorem B2051021 : Blo 1366502 2051021 := bbase (se 3 (by rfl) ⟨384566, by rfl⟩ : syracuseStep 2051021 = 769133) (by norm_num)
theorem B3075029 : Blo 1366502 3075029 := bbase (se 7 (by rfl) ⟨36035, by rfl⟩ : syracuseStep 3075029 = 72071) (by norm_num)
theorem B2051045 : Blo 1366502 2051045 := bbase (se 4 (by rfl) ⟨192285, by rfl⟩ : syracuseStep 2051045 = 384571) (by norm_num)
theorem B1731557 : Blo 1366502 1731557 := bbase (se 4 (by rfl) ⟨162333, by rfl⟩ : syracuseStep 1731557 = 324667) (by norm_num)
theorem B3288053 : Blo 1366502 3288053 := bbase (se 5 (by rfl) ⟨154127, by rfl⟩ : syracuseStep 3288053 = 308255) (by norm_num)
theorem B1461241 : Blo 1366502 1461241 := bbase (se 2 (by rfl) ⟨547965, by rfl⟩ : syracuseStep 1461241 = 1095931) (by norm_num)
theorem B2051069 : Blo 1366502 2051069 := bbase (se 3 (by rfl) ⟨384575, by rfl⟩ : syracuseStep 2051069 = 769151) (by norm_num)
theorem B3288061 : Blo 1366502 3288061 := bbase (se 3 (by rfl) ⟨616511, by rfl⟩ : syracuseStep 3288061 = 1233023) (by norm_num)
theorem B2190349 : Blo 1366502 2190349 := bbase (se 3 (by rfl) ⟨410690, by rfl⟩ : syracuseStep 2190349 = 821381) (by norm_num)
theorem B3460117 : Blo 1366502 3460117 := bbase (se 6 (by rfl) ⟨81096, by rfl⟩ : syracuseStep 3460117 = 162193) (by norm_num)
theorem B2051093 : Blo 1366502 2051093 := bbase (se 6 (by rfl) ⟨48072, by rfl⟩ : syracuseStep 2051093 = 96145) (by norm_num)
theorem B3075101 : Blo 1366502 3075101 := bbase (se 3 (by rfl) ⟨576581, by rfl⟩ : syracuseStep 3075101 = 1153163) (by norm_num)
theorem B1731613 : Blo 1366502 1731613 := bbase (se 3 (by rfl) ⟨324677, by rfl⟩ : syracuseStep 1731613 = 649355) (by norm_num)
theorem B2051117 : Blo 1366502 2051117 := bbase (se 3 (by rfl) ⟨384584, by rfl⟩ : syracuseStep 2051117 = 769169) (by norm_num)
theorem B6237253 : Blo 1366502 6237253 := bbase (se 4 (by rfl) ⟨584742, by rfl⟩ : syracuseStep 6237253 = 1169485) (by norm_num)
theorem B2051141 : Blo 1366502 2051141 := bbase (se 4 (by rfl) ⟨192294, by rfl⟩ : syracuseStep 2051141 = 384589) (by norm_num)
theorem B2051165 : Blo 1366502 2051165 := bbase (se 3 (by rfl) ⟨384593, by rfl⟩ : syracuseStep 2051165 = 769187) (by norm_num)
theorem B3075173 : Blo 1366502 3075173 := bbase (se 4 (by rfl) ⟨288297, by rfl⟩ : syracuseStep 3075173 = 576595) (by norm_num)
theorem B2051189 : Blo 1366502 2051189 := bbase (se 5 (by rfl) ⟨96149, by rfl⟩ : syracuseStep 2051189 = 192299) (by norm_num)
theorem B1559669 : Blo 1366502 1559669 := bbase (se 5 (by rfl) ⟨73109, by rfl⟩ : syracuseStep 1559669 = 146219) (by norm_num)
theorem B1731709 : Blo 1366502 1731709 := bbase (se 3 (by rfl) ⟨324695, by rfl⟩ : syracuseStep 1731709 = 649391) (by norm_num)
theorem B3460229 : Blo 1366502 3460229 := bbase (se 4 (by rfl) ⟨324396, by rfl⟩ : syracuseStep 3460229 = 648793) (by norm_num)
theorem B2051213 : Blo 1366502 2051213 := bbase (se 3 (by rfl) ⟨384602, by rfl⟩ : syracuseStep 2051213 = 769205) (by norm_num)
theorem B2051237 : Blo 1366502 2051237 := bbase (se 4 (by rfl) ⟨192303, by rfl⟩ : syracuseStep 2051237 = 384607) (by norm_num)
theorem B3075245 : Blo 1366502 3075245 := bbase (se 3 (by rfl) ⟨576608, by rfl⟩ : syracuseStep 3075245 = 1153217) (by norm_num)
theorem B2337965 : Blo 1366502 2337965 := bbase (se 3 (by rfl) ⟨438368, by rfl⟩ : syracuseStep 2337965 = 876737) (by norm_num)
theorem B2051261 : Blo 1366502 2051261 := bbase (se 3 (by rfl) ⟨384611, by rfl⟩ : syracuseStep 2051261 = 769223) (by norm_num)
theorem B2051285 : Blo 1366502 2051285 := bbase (se 7 (by rfl) ⟨24038, by rfl⟩ : syracuseStep 2051285 = 48077) (by norm_num)
theorem B2051309 : Blo 1366502 2051309 := bbase (se 3 (by rfl) ⟨384620, by rfl⟩ : syracuseStep 2051309 = 769241) (by norm_num)
theorem B3075317 : Blo 1366502 3075317 := bbase (se 5 (by rfl) ⟨144155, by rfl⟩ : syracuseStep 3075317 = 288311) (by norm_num)
theorem B2051333 : Blo 1366502 2051333 := bbase (se 4 (by rfl) ⟨192312, by rfl⟩ : syracuseStep 2051333 = 384625) (by norm_num)
theorem B2051357 : Blo 1366502 2051357 := bbase (se 3 (by rfl) ⟨384629, by rfl⟩ : syracuseStep 2051357 = 769259) (by norm_num)
theorem B1731881 : Blo 1366502 1731881 := bbase (se 2 (by rfl) ⟨649455, by rfl⟩ : syracuseStep 1731881 = 1298911) (by norm_num)
theorem B2051381 : Blo 1366502 2051381 := bbase (se 5 (by rfl) ⟨96158, by rfl⟩ : syracuseStep 2051381 = 192317) (by norm_num)
theorem B3894581 : Blo 1366502 3894581 := bbase (se 5 (by rfl) ⟨182558, by rfl⟩ : syracuseStep 3894581 = 365117) (by norm_num)
theorem B3075389 : Blo 1366502 3075389 := bbase (se 3 (by rfl) ⟨576635, by rfl⟩ : syracuseStep 3075389 = 1153271) (by norm_num)
theorem B3460421 : Blo 1366502 3460421 := bbase (se 4 (by rfl) ⟨324414, by rfl⟩ : syracuseStep 3460421 = 648829) (by norm_num)
theorem B2051405 : Blo 1366502 2051405 := bbase (se 3 (by rfl) ⟨384638, by rfl⟩ : syracuseStep 2051405 = 769277) (by norm_num)
theorem B6663509 : Blo 1366502 6663509 := bbase (se 11 (by rfl) ⟨4880, by rfl⟩ : syracuseStep 6663509 = 9761) (by norm_num)
theorem B1731937 : Blo 1366502 1731937 := bbase (se 2 (by rfl) ⟨649476, by rfl⟩ : syracuseStep 1731937 = 1298953) (by norm_num)
theorem B2051429 : Blo 1366502 2051429 := bbase (se 4 (by rfl) ⟨192321, by rfl⟩ : syracuseStep 2051429 = 384643) (by norm_num)
theorem B3698021 : Blo 1366502 3698021 := bbase (se 4 (by rfl) ⟨346689, by rfl⟩ : syracuseStep 3698021 = 693379) (by norm_num)
theorem B4615541 : Blo 1366502 4615541 := bbase (se 5 (by rfl) ⟨216353, by rfl⟩ : syracuseStep 4615541 = 432707) (by norm_num)
theorem B2051453 : Blo 1366502 2051453 := bbase (se 3 (by rfl) ⟨384647, by rfl⟩ : syracuseStep 2051453 = 769295) (by norm_num)
theorem B3075461 : Blo 1366502 3075461 := bbase (se 4 (by rfl) ⟨288324, by rfl⟩ : syracuseStep 3075461 = 576649) (by norm_num)
theorem B2051477 : Blo 1366502 2051477 := bbase (se 6 (by rfl) ⟨48081, by rfl⟩ : syracuseStep 2051477 = 96163) (by norm_num)
theorem B2772389 : Blo 1366502 2772389 := bbase (se 4 (by rfl) ⟨259911, by rfl⟩ : syracuseStep 2772389 = 519823) (by norm_num)
theorem B3509669 : Blo 1366502 3509669 := bbase (se 4 (by rfl) ⟨329031, by rfl⟩ : syracuseStep 3509669 = 658063) (by norm_num)
theorem B2051501 : Blo 1366502 2051501 := bbase (se 3 (by rfl) ⟨384656, by rfl⟩ : syracuseStep 2051501 = 769313) (by norm_num)
theorem B8760757 : Blo 1366502 8760757 := bbase (se 5 (by rfl) ⟨410660, by rfl⟩ : syracuseStep 8760757 = 821321) (by norm_num)
theorem B2051525 : Blo 1366502 2051525 := bbase (se 4 (by rfl) ⟨192330, by rfl⟩ : syracuseStep 2051525 = 384661) (by norm_num)
theorem B3075533 : Blo 1366502 3075533 := bbase (se 3 (by rfl) ⟨576662, by rfl⟩ : syracuseStep 3075533 = 1153325) (by norm_num)
theorem B6237653 : Blo 1366502 6237653 := bbase (se 7 (by rfl) ⟨73097, by rfl⟩ : syracuseStep 6237653 = 146195) (by norm_num)
theorem B2051549 : Blo 1366502 2051549 := bbase (se 3 (by rfl) ⟨384665, by rfl⟩ : syracuseStep 2051549 = 769331) (by norm_num)
theorem B2051573 : Blo 1366502 2051573 := bbase (se 5 (by rfl) ⟨96167, by rfl⟩ : syracuseStep 2051573 = 192335) (by norm_num)
theorem B1641989 : Blo 1366502 1641989 := bbase (se 4 (by rfl) ⟨153936, by rfl⟩ : syracuseStep 1641989 = 307873) (by norm_num)
theorem B2051597 : Blo 1366502 2051597 := bbase (se 3 (by rfl) ⟨384674, by rfl⟩ : syracuseStep 2051597 = 769349) (by norm_num)
theorem B3075605 : Blo 1366502 3075605 := bbase (se 6 (by rfl) ⟨72084, by rfl⟩ : syracuseStep 3075605 = 144169) (by norm_num)
theorem B2051621 : Blo 1366502 2051621 := bbase (se 4 (by rfl) ⟨192339, by rfl⟩ : syracuseStep 2051621 = 384679) (by norm_num)
theorem B2051645 : Blo 1366502 2051645 := bbase (se 3 (by rfl) ⟨384683, by rfl⟩ : syracuseStep 2051645 = 769367) (by norm_num)
theorem B2051669 : Blo 1366502 2051669 := bbase (se 8 (by rfl) ⟨12021, by rfl⟩ : syracuseStep 2051669 = 24043) (by norm_num)
theorem B3075677 : Blo 1366502 3075677 := bbase (se 3 (by rfl) ⟨576689, by rfl⟩ : syracuseStep 3075677 = 1153379) (by norm_num)
theorem B2051693 : Blo 1366502 2051693 := bbase (se 3 (by rfl) ⟨384692, by rfl⟩ : syracuseStep 2051693 = 769385) (by norm_num)
theorem B2051717 : Blo 1366502 2051717 := bbase (se 4 (by rfl) ⟨192348, by rfl⟩ : syracuseStep 2051717 = 384697) (by norm_num)
theorem B1560217 : Blo 1366502 1560217 := bbase (se 2 (by rfl) ⟨585081, by rfl⟩ : syracuseStep 1560217 = 1170163) (by norm_num)
theorem B3460765 : Blo 1366502 3460765 := bbase (se 3 (by rfl) ⟨648893, by rfl⟩ : syracuseStep 3460765 = 1297787) (by norm_num)
theorem B2051741 : Blo 1366502 2051741 := bbase (se 3 (by rfl) ⟨384701, by rfl⟩ : syracuseStep 2051741 = 769403) (by norm_num)
theorem B3075749 : Blo 1366502 3075749 := bbase (se 4 (by rfl) ⟨288351, by rfl⟩ : syracuseStep 3075749 = 576703) (by norm_num)
theorem B2051765 : Blo 1366502 2051765 := bbase (se 5 (by rfl) ⟨96176, by rfl⟩ : syracuseStep 2051765 = 192353) (by norm_num)
theorem B1560253 : Blo 1366502 1560253 := bbase (se 3 (by rfl) ⟨292547, by rfl⟩ : syracuseStep 1560253 = 585095) (by norm_num)
theorem B2920141 : Blo 1366502 2920141 := bbase (se 3 (by rfl) ⟨547526, by rfl⟩ : syracuseStep 2920141 = 1095053) (by norm_num)
theorem B2051789 : Blo 1366502 2051789 := bbase (se 3 (by rfl) ⟨384710, by rfl⟩ : syracuseStep 2051789 = 769421) (by norm_num)
theorem B2051813 : Blo 1366502 2051813 := bbase (se 4 (by rfl) ⟨192357, by rfl⟩ : syracuseStep 2051813 = 384715) (by norm_num)
theorem B3075821 : Blo 1366502 3075821 := bbase (se 3 (by rfl) ⟨576716, by rfl⟩ : syracuseStep 3075821 = 1153433) (by norm_num)
theorem B2051837 : Blo 1366502 2051837 := bbase (se 3 (by rfl) ⟨384719, by rfl⟩ : syracuseStep 2051837 = 769439) (by norm_num)
theorem B3460877 : Blo 1366502 3460877 := bbase (se 3 (by rfl) ⟨648914, by rfl⟩ : syracuseStep 3460877 = 1297829) (by norm_num)
theorem B2051861 : Blo 1366502 2051861 := bbase (se 6 (by rfl) ⟨48090, by rfl⟩ : syracuseStep 2051861 = 96181) (by norm_num)
theorem B4615973 : Blo 1366502 4615973 := bbase (se 4 (by rfl) ⟨432747, by rfl⟩ : syracuseStep 4615973 = 865495) (by norm_num)
theorem B2051885 : Blo 1366502 2051885 := bbase (se 3 (by rfl) ⟨384728, by rfl⟩ : syracuseStep 2051885 = 769457) (by norm_num)
theorem B3075893 : Blo 1366502 3075893 := bbase (se 5 (by rfl) ⟨144182, by rfl⟩ : syracuseStep 3075893 = 288365) (by norm_num)
theorem B1642297 : Blo 1366502 1642297 := bbase (se 2 (by rfl) ⟨615861, by rfl⟩ : syracuseStep 1642297 = 1231723) (by norm_num)
theorem B2051909 : Blo 1366502 2051909 := bbase (se 4 (by rfl) ⟨192366, by rfl⟩ : syracuseStep 2051909 = 384733) (by norm_num)
theorem B2051933 : Blo 1366502 2051933 := bbase (se 3 (by rfl) ⟨384737, by rfl⟩ : syracuseStep 2051933 = 769475) (by norm_num)
theorem B2051957 : Blo 1366502 2051957 := bbase (se 5 (by rfl) ⟨96185, by rfl⟩ : syracuseStep 2051957 = 192371) (by norm_num)
theorem B3075965 : Blo 1366502 3075965 := bbase (se 3 (by rfl) ⟨576743, by rfl⟩ : syracuseStep 3075965 = 1153487) (by norm_num)
theorem B2051981 : Blo 1366502 2051981 := bbase (se 3 (by rfl) ⟨384746, by rfl⟩ : syracuseStep 2051981 = 769493) (by norm_num)
theorem B2052005 : Blo 1366502 2052005 := bbase (se 4 (by rfl) ⟨192375, by rfl⟩ : syracuseStep 2052005 = 384751) (by norm_num)
theorem B2052029 : Blo 1366502 2052029 := bbase (se 3 (by rfl) ⟨384755, by rfl⟩ : syracuseStep 2052029 = 769511) (by norm_num)
theorem B3076037 : Blo 1366502 3076037 := bbase (se 4 (by rfl) ⟨288378, by rfl⟩ : syracuseStep 3076037 = 576757) (by norm_num)
theorem B3461069 : Blo 1366502 3461069 := bbase (se 3 (by rfl) ⟨648950, by rfl⟩ : syracuseStep 3461069 = 1297901) (by norm_num)
theorem B3895253 : Blo 1366502 3895253 := bbase (se 7 (by rfl) ⟨45647, by rfl⟩ : syracuseStep 3895253 = 91295) (by norm_num)
theorem B2052053 : Blo 1366502 2052053 := bbase (se 7 (by rfl) ⟨24047, by rfl⟩ : syracuseStep 2052053 = 48095) (by norm_num)
theorem B6926309 : Blo 1366502 6926309 := bbase (se 4 (by rfl) ⟨649341, by rfl⟩ : syracuseStep 6926309 = 1298683) (by norm_num)
theorem B2306029 : Blo 1366502 2306029 := bbase (se 3 (by rfl) ⟨432380, by rfl⟩ : syracuseStep 2306029 = 864761) (by norm_num)
theorem B2052077 : Blo 1366502 2052077 := bbase (se 3 (by rfl) ⟨384764, by rfl⟩ : syracuseStep 2052077 = 769529) (by norm_num)
theorem B2191349 : Blo 1366502 2191349 := bbase (se 5 (by rfl) ⟨102719, by rfl⟩ : syracuseStep 2191349 = 205439) (by norm_num)
theorem B2052101 : Blo 1366502 2052101 := bbase (se 4 (by rfl) ⟨192384, by rfl⟩ : syracuseStep 2052101 = 384769) (by norm_num)
theorem B3076109 : Blo 1366502 3076109 := bbase (se 3 (by rfl) ⟨576770, by rfl⟩ : syracuseStep 3076109 = 1153541) (by norm_num)
theorem B2052125 : Blo 1366502 2052125 := bbase (se 3 (by rfl) ⟨384773, by rfl⟩ : syracuseStep 2052125 = 769547) (by norm_num)
theorem B2052149 : Blo 1366502 2052149 := bbase (se 5 (by rfl) ⟨96194, by rfl⟩ : syracuseStep 2052149 = 192389) (by norm_num)
theorem B2306117 : Blo 1366502 2306117 := bbase (se 4 (by rfl) ⟨216198, by rfl⟩ : syracuseStep 2306117 = 432397) (by norm_num)
theorem B2052173 : Blo 1366502 2052173 := bbase (se 3 (by rfl) ⟨384782, by rfl⟩ : syracuseStep 2052173 = 769565) (by norm_num)
theorem B3076181 : Blo 1366502 3076181 := bbase (se 8 (by rfl) ⟨18024, by rfl⟩ : syracuseStep 3076181 = 36049) (by norm_num)
theorem B2052197 : Blo 1366502 2052197 := bbase (se 4 (by rfl) ⟨192393, by rfl⟩ : syracuseStep 2052197 = 384787) (by norm_num)
theorem B2191477 : Blo 1366502 2191477 := bbase (se 5 (by rfl) ⟨102725, by rfl⟩ : syracuseStep 2191477 = 205451) (by norm_num)
theorem B2052221 : Blo 1366502 2052221 := bbase (se 3 (by rfl) ⟨384791, by rfl⟩ : syracuseStep 2052221 = 769583) (by norm_num)
theorem B2052245 : Blo 1366502 2052245 := bbase (se 6 (by rfl) ⟨48099, by rfl⟩ : syracuseStep 2052245 = 96199) (by norm_num)
theorem B3076253 : Blo 1366502 3076253 := bbase (se 3 (by rfl) ⟨576797, by rfl⟩ : syracuseStep 3076253 = 1153595) (by norm_num)
theorem B2052269 : Blo 1366502 2052269 := bbase (se 3 (by rfl) ⟨384800, by rfl⟩ : syracuseStep 2052269 = 769601) (by norm_num)
theorem B2191541 : Blo 1366502 2191541 := bbase (se 5 (by rfl) ⟨102728, by rfl⟩ : syracuseStep 2191541 = 205457) (by norm_num)
theorem B1642685 : Blo 1366502 1642685 := bbase (se 3 (by rfl) ⟨308003, by rfl⟩ : syracuseStep 1642685 = 616007) (by norm_num)
theorem B2920637 : Blo 1366502 2920637 := bbase (se 3 (by rfl) ⟨547619, by rfl⟩ : syracuseStep 2920637 = 1095239) (by norm_num)
theorem B2306245 : Blo 1366502 2306245 := bbase (se 4 (by rfl) ⟨216210, by rfl⟩ : syracuseStep 2306245 = 432421) (by norm_num)
theorem B6574277 : Blo 1366502 6574277 := bbase (se 4 (by rfl) ⟨616338, by rfl⟩ : syracuseStep 6574277 = 1232677) (by norm_num)
theorem B2052293 : Blo 1366502 2052293 := bbase (se 4 (by rfl) ⟨192402, by rfl⟩ : syracuseStep 2052293 = 384805) (by norm_num)
theorem B4616405 : Blo 1366502 4616405 := bbase (se 7 (by rfl) ⟨54098, by rfl⟩ : syracuseStep 4616405 = 108197) (by norm_num)
theorem B2052317 : Blo 1366502 2052317 := bbase (se 3 (by rfl) ⟨384809, by rfl⟩ : syracuseStep 2052317 = 769619) (by norm_num)
theorem B1405153 : Blo 1366502 1405153 := bbase (se 2 (by rfl) ⟨526932, by rfl⟩ : syracuseStep 1405153 = 1053865) (by norm_num)
theorem B4378853 : Blo 1366502 4378853 := bbase (se 4 (by rfl) ⟨410517, by rfl⟩ : syracuseStep 4378853 = 821035) (by norm_num)
theorem B3076325 : Blo 1366502 3076325 := bbase (se 4 (by rfl) ⟨288405, by rfl⟩ : syracuseStep 3076325 = 576811) (by norm_num)
theorem B2052341 : Blo 1366502 2052341 := bbase (se 5 (by rfl) ⟨96203, by rfl⟩ : syracuseStep 2052341 = 192407) (by norm_num)
theorem B2052365 : Blo 1366502 2052365 := bbase (se 3 (by rfl) ⟨384818, by rfl⟩ : syracuseStep 2052365 = 769637) (by norm_num)
theorem B2306333 : Blo 1366502 2306333 := bbase (se 3 (by rfl) ⟨432437, by rfl⟩ : syracuseStep 2306333 = 864875) (by norm_num)
theorem B3461413 : Blo 1366502 3461413 := bbase (se 4 (by rfl) ⟨324507, by rfl⟩ : syracuseStep 3461413 = 649015) (by norm_num)
theorem B2052389 : Blo 1366502 2052389 := bbase (se 4 (by rfl) ⟨192411, by rfl⟩ : syracuseStep 2052389 = 384823) (by norm_num)
theorem B3076397 : Blo 1366502 3076397 := bbase (se 3 (by rfl) ⟨576824, by rfl⟩ : syracuseStep 3076397 = 1153649) (by norm_num)
theorem B2052413 : Blo 1366502 2052413 := bbase (se 3 (by rfl) ⟨384827, by rfl⟩ : syracuseStep 2052413 = 769655) (by norm_num)
theorem B2052437 : Blo 1366502 2052437 := bbase (se 10 (by rfl) ⟨3006, by rfl⟩ : syracuseStep 2052437 = 6013) (by norm_num)
theorem B2052461 : Blo 1366502 2052461 := bbase (se 3 (by rfl) ⟨384836, by rfl⟩ : syracuseStep 2052461 = 769673) (by norm_num)
theorem B3076469 : Blo 1366502 3076469 := bbase (se 5 (by rfl) ⟨144209, by rfl⟩ : syracuseStep 3076469 = 288419) (by norm_num)
theorem B6918533 : Blo 1366502 6918533 := bbase (se 4 (by rfl) ⟨648612, by rfl⟩ : syracuseStep 6918533 = 1297225) (by norm_num)
theorem B3895685 : Blo 1366502 3895685 := bbase (se 4 (by rfl) ⟨365220, by rfl⟩ : syracuseStep 3895685 = 730441) (by norm_num)
theorem B2052485 : Blo 1366502 2052485 := bbase (se 4 (by rfl) ⟨192420, by rfl⟩ : syracuseStep 2052485 = 384841) (by norm_num)
theorem B3461525 : Blo 1366502 3461525 := bbase (se 6 (by rfl) ⟨81129, by rfl⟩ : syracuseStep 3461525 = 162259) (by norm_num)
theorem B2306461 : Blo 1366502 2306461 := bbase (se 3 (by rfl) ⟨432461, by rfl⟩ : syracuseStep 2306461 = 864923) (by norm_num)
theorem B2052509 : Blo 1366502 2052509 := bbase (se 3 (by rfl) ⟨384845, by rfl⟩ : syracuseStep 2052509 = 769691) (by norm_num)
theorem B2052533 : Blo 1366502 2052533 := bbase (se 5 (by rfl) ⟨96212, by rfl⟩ : syracuseStep 2052533 = 192425) (by norm_num)
theorem B3076541 : Blo 1366502 3076541 := bbase (se 3 (by rfl) ⟨576851, by rfl⟩ : syracuseStep 3076541 = 1153703) (by norm_num)
theorem B2773453 : Blo 1366502 2773453 := bbase (se 3 (by rfl) ⟨520022, by rfl⟩ : syracuseStep 2773453 = 1040045) (by norm_num)
theorem B2052557 : Blo 1366502 2052557 := bbase (se 3 (by rfl) ⟨384854, by rfl⟩ : syracuseStep 2052557 = 769709) (by norm_num)
theorem B5190101 : Blo 1366502 5190101 := bbase (se 7 (by rfl) ⟨60821, by rfl⟩ : syracuseStep 5190101 = 121643) (by norm_num)
theorem B2339285 : Blo 1366502 2339285 := bbase (se 7 (by rfl) ⟨27413, by rfl⟩ : syracuseStep 2339285 = 54827) (by norm_num)
theorem B2052581 : Blo 1366502 2052581 := bbase (se 4 (by rfl) ⟨192429, by rfl⟩ : syracuseStep 2052581 = 384859) (by norm_num)
theorem B2306549 : Blo 1366502 2306549 := bbase (se 5 (by rfl) ⟨108119, by rfl⟩ : syracuseStep 2306549 = 216239) (by norm_num)
theorem B2052605 : Blo 1366502 2052605 := bbase (se 3 (by rfl) ⟨384863, by rfl⟩ : syracuseStep 2052605 = 769727) (by norm_num)
theorem B1479169 : Blo 1366502 1479169 := bbase (se 2 (by rfl) ⟨554688, by rfl⟩ : syracuseStep 1479169 = 1109377) (by norm_num)
theorem B3076613 : Blo 1366502 3076613 := bbase (se 4 (by rfl) ⟨288432, by rfl⟩ : syracuseStep 3076613 = 576865) (by norm_num)
theorem B2052629 : Blo 1366502 2052629 := bbase (se 6 (by rfl) ⟨48108, by rfl⟩ : syracuseStep 2052629 = 96217) (by norm_num)
theorem B1643041 : Blo 1366502 1643041 := bbase (se 2 (by rfl) ⟨616140, by rfl⟩ : syracuseStep 1643041 = 1232281) (by norm_num)
theorem B2052653 : Blo 1366502 2052653 := bbase (se 3 (by rfl) ⟨384872, by rfl⟩ : syracuseStep 2052653 = 769745) (by norm_num)
theorem B2052677 : Blo 1366502 2052677 := bbase (se 4 (by rfl) ⟨192438, by rfl⟩ : syracuseStep 2052677 = 384877) (by norm_num)
theorem B3076685 : Blo 1366502 3076685 := bbase (se 3 (by rfl) ⟨576878, by rfl⟩ : syracuseStep 3076685 = 1153757) (by norm_num)
theorem B1946197 : Blo 1366502 1946197 := bbase (se 8 (by rfl) ⟨11403, by rfl⟩ : syracuseStep 1946197 = 22807) (by norm_num)
theorem B3461717 : Blo 1366502 3461717 := bbase (se 8 (by rfl) ⟨20283, by rfl⟩ : syracuseStep 3461717 = 40567) (by norm_num)
theorem B2052701 : Blo 1366502 2052701 := bbase (se 3 (by rfl) ⟨384881, by rfl⟩ : syracuseStep 2052701 = 769763) (by norm_num)
theorem B2306677 : Blo 1366502 2306677 := bbase (se 5 (by rfl) ⟨108125, by rfl⟩ : syracuseStep 2306677 = 216251) (by norm_num)
theorem B2052725 : Blo 1366502 2052725 := bbase (se 5 (by rfl) ⟨96221, by rfl⟩ : syracuseStep 2052725 = 192443) (by norm_num)
theorem B4616837 : Blo 1366502 4616837 := bbase (se 4 (by rfl) ⟨432828, by rfl⟩ : syracuseStep 4616837 = 865657) (by norm_num)
theorem B2052749 : Blo 1366502 2052749 := bbase (se 3 (by rfl) ⟨384890, by rfl⟩ : syracuseStep 2052749 = 769781) (by norm_num)
theorem B3076757 : Blo 1366502 3076757 := bbase (se 6 (by rfl) ⟨72111, by rfl⟩ : syracuseStep 3076757 = 144223) (by norm_num)
theorem B2306765 : Blo 1366502 2306765 := bbase (se 3 (by rfl) ⟨432518, by rfl⟩ : syracuseStep 2306765 = 865037) (by norm_num)
theorem B3076829 : Blo 1366502 3076829 := bbase (se 3 (by rfl) ⟨576905, by rfl⟩ : syracuseStep 3076829 = 1153811) (by norm_num)
theorem B5190389 : Blo 1366502 5190389 := bbase (se 5 (by rfl) ⟨243299, by rfl⟩ : syracuseStep 5190389 = 486599) (by norm_num)
theorem B3076901 : Blo 1366502 3076901 := bbase (se 4 (by rfl) ⟨288459, by rfl⟩ : syracuseStep 3076901 = 576919) (by norm_num)
theorem B2306893 : Blo 1366502 2306893 := bbase (se 3 (by rfl) ⟨432542, by rfl⟩ : syracuseStep 2306893 = 865085) (by norm_num)
theorem B3076973 : Blo 1366502 3076973 := bbase (se 3 (by rfl) ⟨576932, by rfl⟩ : syracuseStep 3076973 = 1153865) (by norm_num)
theorem B1643377 : Blo 1366502 1643377 := bbase (se 2 (by rfl) ⟨616266, by rfl⟩ : syracuseStep 1643377 = 1232533) (by norm_num)
theorem B3330973 : Blo 1366502 3330973 := bbase (se 3 (by rfl) ⟨624557, by rfl⟩ : syracuseStep 3330973 = 1249115) (by norm_num)
theorem B2306981 : Blo 1366502 2306981 := bbase (se 4 (by rfl) ⟨216279, by rfl⟩ : syracuseStep 2306981 = 432559) (by norm_num)
theorem B1946533 : Blo 1366502 1946533 := bbase (se 4 (by rfl) ⟨182487, by rfl⟩ : syracuseStep 1946533 = 364975) (by norm_num)
theorem B3462061 : Blo 1366502 3462061 := bbase (se 3 (by rfl) ⟨649136, by rfl⟩ : syracuseStep 3462061 = 1298273) (by norm_num)
theorem B3077045 : Blo 1366502 3077045 := bbase (se 5 (by rfl) ⟨144236, by rfl⟩ : syracuseStep 3077045 = 288473) (by norm_num)
theorem B2462717 : Blo 1366502 2462717 := bbase (se 3 (by rfl) ⟨461759, by rfl⟩ : syracuseStep 2462717 = 923519) (by norm_num)
theorem B3077117 : Blo 1366502 3077117 := bbase (se 3 (by rfl) ⟨576959, by rfl⟩ : syracuseStep 3077117 = 1153919) (by norm_num)
theorem B3462173 : Blo 1366502 3462173 := bbase (se 3 (by rfl) ⟨649157, by rfl⟩ : syracuseStep 3462173 = 1298315) (by norm_num)
theorem B2307109 : Blo 1366502 2307109 := bbase (se 4 (by rfl) ⟨216291, by rfl⟩ : syracuseStep 2307109 = 432583) (by norm_num)
theorem B9851957 : Blo 1366502 9851957 := bbase (se 5 (by rfl) ⟨461810, by rfl⟩ : syracuseStep 9851957 = 923621) (by norm_num)
theorem B2921525 : Blo 1366502 2921525 := bbase (se 5 (by rfl) ⟨136946, by rfl⟩ : syracuseStep 2921525 = 273893) (by norm_num)
theorem B4617269 : Blo 1366502 4617269 := bbase (se 5 (by rfl) ⟨216434, by rfl⟩ : syracuseStep 4617269 = 432869) (by norm_num)
theorem B2249789 : Blo 1366502 2249789 := bbase (se 3 (by rfl) ⟨421835, by rfl⟩ : syracuseStep 2249789 = 843671) (by norm_num)
theorem B3077189 : Blo 1366502 3077189 := bbase (se 4 (by rfl) ⟨288486, by rfl⟩ : syracuseStep 3077189 = 576973) (by norm_num)
theorem B3896437 : Blo 1366502 3896437 := bbase (se 5 (by rfl) ⟨182645, by rfl⟩ : syracuseStep 3896437 = 365291) (by norm_num)
theorem B2307197 : Blo 1366502 2307197 := bbase (se 3 (by rfl) ⟨432599, by rfl⟩ : syracuseStep 2307197 = 865199) (by norm_num)
theorem B1946749 : Blo 1366502 1946749 := bbase (se 3 (by rfl) ⟨365015, by rfl⟩ : syracuseStep 1946749 = 730031) (by norm_num)
theorem B3077261 : Blo 1366502 3077261 := bbase (se 3 (by rfl) ⟨576986, by rfl⟩ : syracuseStep 3077261 = 1153973) (by norm_num)
theorem B2921645 : Blo 1366502 2921645 := bbase (se 3 (by rfl) ⟨547808, by rfl⟩ : syracuseStep 2921645 = 1095617) (by norm_num)
theorem B2774189 : Blo 1366502 2774189 := bbase (se 3 (by rfl) ⟨520160, by rfl⟩ : syracuseStep 2774189 = 1040321) (by norm_num)
theorem B3077333 : Blo 1366502 3077333 := bbase (se 7 (by rfl) ⟨36062, by rfl⟩ : syracuseStep 3077333 = 72125) (by norm_num)
theorem B3462365 : Blo 1366502 3462365 := bbase (se 3 (by rfl) ⟨649193, by rfl⟩ : syracuseStep 3462365 = 1298387) (by norm_num)
theorem B6927605 : Blo 1366502 6927605 := bbase (se 5 (by rfl) ⟨324731, by rfl⟩ : syracuseStep 6927605 = 649463) (by norm_num)
theorem B2307325 : Blo 1366502 2307325 := bbase (se 3 (by rfl) ⟨432623, by rfl⟩ : syracuseStep 2307325 = 865247) (by norm_num)
theorem B13137173 : Blo 1366502 13137173 := bbase (se 6 (by rfl) ⟨307902, by rfl⟩ : syracuseStep 13137173 = 615805) (by norm_num)
theorem B3077405 : Blo 1366502 3077405 := bbase (se 3 (by rfl) ⟨577013, by rfl⟩ : syracuseStep 3077405 = 1154027) (by norm_num)
theorem B1537321 : Blo 1366502 1537321 := bbase (se 2 (by rfl) ⟨576495, by rfl⟩ : syracuseStep 1537321 = 1152991) (by norm_num)
theorem B2667845 : Blo 1366502 2667845 := bbase (se 4 (by rfl) ⟨250110, by rfl⟩ : syracuseStep 2667845 = 500221) (by norm_num)
theorem B1537357 : Blo 1366502 1537357 := bbase (se 3 (by rfl) ⟨288254, by rfl⟩ : syracuseStep 1537357 = 576509) (by norm_num)
theorem B2307413 : Blo 1366502 2307413 := bbase (se 13 (by rfl) ⟨422, by rfl⟩ : syracuseStep 2307413 = 845) (by norm_num)
theorem B3077477 : Blo 1366502 3077477 := bbase (se 4 (by rfl) ⟨288513, by rfl⟩ : syracuseStep 3077477 = 577027) (by norm_num)
theorem B1537393 : Blo 1366502 1537393 := bbase (se 2 (by rfl) ⟨576522, by rfl⟩ : syracuseStep 1537393 = 1153045) (by norm_num)
theorem B1537429 : Blo 1366502 1537429 := bbase (se 6 (by rfl) ⟨36033, by rfl⟩ : syracuseStep 1537429 = 72067) (by norm_num)
theorem B3077549 : Blo 1366502 3077549 := bbase (se 3 (by rfl) ⟨577040, by rfl⟩ : syracuseStep 3077549 = 1154081) (by norm_num)
theorem B1537465 : Blo 1366502 1537465 := bbase (se 2 (by rfl) ⟨576549, by rfl⟩ : syracuseStep 1537465 = 1153099) (by norm_num)
theorem B2594261 : Blo 1366502 2594261 := bbase (se 7 (by rfl) ⟨30401, by rfl⟩ : syracuseStep 2594261 = 60803) (by norm_num)
theorem B2307541 : Blo 1366502 2307541 := bbase (se 7 (by rfl) ⟨27041, by rfl⟩ : syracuseStep 2307541 = 54083) (by norm_num)
theorem B1537501 : Blo 1366502 1537501 := bbase (se 3 (by rfl) ⟨288281, by rfl⟩ : syracuseStep 1537501 = 576563) (by norm_num)
theorem B4617701 : Blo 1366502 4617701 := bbase (se 4 (by rfl) ⟨432909, by rfl⟩ : syracuseStep 4617701 = 865819) (by norm_num)
theorem B1947125 : Blo 1366502 1947125 := bbase (se 5 (by rfl) ⟨91271, by rfl⟩ : syracuseStep 1947125 = 182543) (by norm_num)
theorem B3077621 : Blo 1366502 3077621 := bbase (se 5 (by rfl) ⟨144263, by rfl⟩ : syracuseStep 3077621 = 288527) (by norm_num)
theorem B1537537 : Blo 1366502 1537537 := bbase (se 2 (by rfl) ⟨576576, by rfl⟩ : syracuseStep 1537537 = 1153153) (by norm_num)
theorem B1537573 : Blo 1366502 1537573 := bbase (se 4 (by rfl) ⟨144147, by rfl⟩ : syracuseStep 1537573 = 288295) (by norm_num)
theorem B2307629 : Blo 1366502 2307629 := bbase (se 3 (by rfl) ⟨432680, by rfl⟩ : syracuseStep 2307629 = 865361) (by norm_num)
theorem B3462709 : Blo 1366502 3462709 := bbase (se 5 (by rfl) ⟨162314, by rfl⟩ : syracuseStep 3462709 = 324629) (by norm_num)
theorem B3077693 : Blo 1366502 3077693 := bbase (se 3 (by rfl) ⟨577067, by rfl⟩ : syracuseStep 3077693 = 1154135) (by norm_num)
theorem B6567493 : Blo 1366502 6567493 := bbase (se 4 (by rfl) ⟨615702, by rfl⟩ : syracuseStep 6567493 = 1231405) (by norm_num)
theorem B1537609 : Blo 1366502 1537609 := bbase (se 2 (by rfl) ⟨576603, by rfl⟩ : syracuseStep 1537609 = 1153207) (by norm_num)
theorem B2250317 : Blo 1366502 2250317 := bbase (se 3 (by rfl) ⟨421934, by rfl⟩ : syracuseStep 2250317 = 843869) (by norm_num)
theorem B6575701 : Blo 1366502 6575701 := bbase (se 8 (by rfl) ⟨38529, by rfl⟩ : syracuseStep 6575701 = 77059) (by norm_num)
theorem B2594405 : Blo 1366502 2594405 := bbase (se 4 (by rfl) ⟨243225, by rfl⟩ : syracuseStep 2594405 = 486451) (by norm_num)
theorem B6239845 : Blo 1366502 6239845 := bbase (se 4 (by rfl) ⟨584985, by rfl⟩ : syracuseStep 6239845 = 1169971) (by norm_num)
theorem B1537645 : Blo 1366502 1537645 := bbase (se 3 (by rfl) ⟨288308, by rfl⟩ : syracuseStep 1537645 = 576617) (by norm_num)
theorem B4380277 : Blo 1366502 4380277 := bbase (se 5 (by rfl) ⟨205325, by rfl⟩ : syracuseStep 4380277 = 410651) (by norm_num)
theorem B3077765 : Blo 1366502 3077765 := bbase (se 4 (by rfl) ⟨288540, by rfl⟩ : syracuseStep 3077765 = 577081) (by norm_num)
theorem B1537681 : Blo 1366502 1537681 := bbase (se 2 (by rfl) ⟨576630, by rfl⟩ : syracuseStep 1537681 = 1153261) (by norm_num)
theorem B6919829 : Blo 1366502 6919829 := bbase (se 6 (by rfl) ⟨162183, by rfl⟩ : syracuseStep 6919829 = 324367) (by norm_num)
theorem B3462821 : Blo 1366502 3462821 := bbase (se 4 (by rfl) ⟨324639, by rfl⟩ : syracuseStep 3462821 = 649279) (by norm_num)
theorem B2307757 : Blo 1366502 2307757 := bbase (se 3 (by rfl) ⟨432704, by rfl⟩ : syracuseStep 2307757 = 865409) (by norm_num)
theorem B1537717 : Blo 1366502 1537717 := bbase (se 5 (by rfl) ⟨72080, by rfl⟩ : syracuseStep 1537717 = 144161) (by norm_num)
theorem B3077837 : Blo 1366502 3077837 := bbase (se 3 (by rfl) ⟨577094, by rfl⟩ : syracuseStep 3077837 = 1154189) (by norm_num)
theorem B1537753 : Blo 1366502 1537753 := bbase (se 2 (by rfl) ⟨576657, by rfl⟩ : syracuseStep 1537753 = 1153315) (by norm_num)
theorem B1537789 : Blo 1366502 1537789 := bbase (se 3 (by rfl) ⟨288335, by rfl⟩ : syracuseStep 1537789 = 576671) (by norm_num)
theorem B2307845 : Blo 1366502 2307845 := bbase (se 4 (by rfl) ⟨216360, by rfl⟩ : syracuseStep 2307845 = 432721) (by norm_num)
theorem B2463509 : Blo 1366502 2463509 := bbase (se 6 (by rfl) ⟨57738, by rfl⟩ : syracuseStep 2463509 = 115477) (by norm_num)
theorem B3077909 : Blo 1366502 3077909 := bbase (se 6 (by rfl) ⟨72138, by rfl⟩ : syracuseStep 3077909 = 144277) (by norm_num)
theorem B1537825 : Blo 1366502 1537825 := bbase (se 2 (by rfl) ⟨576684, by rfl⟩ : syracuseStep 1537825 = 1153369) (by norm_num)
theorem B2922277 : Blo 1366502 2922277 := bbase (se 4 (by rfl) ⟨273963, by rfl⟩ : syracuseStep 2922277 = 547927) (by norm_num)
theorem B1537861 : Blo 1366502 1537861 := bbase (se 4 (by rfl) ⟨144174, by rfl⟩ : syracuseStep 1537861 = 288349) (by norm_num)
theorem B3077981 : Blo 1366502 3077981 := bbase (se 3 (by rfl) ⟨577121, by rfl⟩ : syracuseStep 3077981 = 1154243) (by norm_num)
theorem B3463013 : Blo 1366502 3463013 := bbase (se 4 (by rfl) ⟨324657, by rfl⟩ : syracuseStep 3463013 = 649315) (by norm_num)
theorem B1537897 : Blo 1366502 1537897 := bbase (se 2 (by rfl) ⟨576711, by rfl⟩ : syracuseStep 1537897 = 1153423) (by norm_num)
theorem B2594693 : Blo 1366502 2594693 := bbase (se 4 (by rfl) ⟨243252, by rfl⟩ : syracuseStep 2594693 = 486505) (by norm_num)
theorem B2307973 : Blo 1366502 2307973 := bbase (se 4 (by rfl) ⟨216372, by rfl⟩ : syracuseStep 2307973 = 432745) (by norm_num)
theorem B1537933 : Blo 1366502 1537933 := bbase (se 3 (by rfl) ⟨288362, by rfl⟩ : syracuseStep 1537933 = 576725) (by norm_num)
theorem B5191573 : Blo 1366502 5191573 := bbase (se 6 (by rfl) ⟨121677, by rfl⟩ : syracuseStep 5191573 = 243355) (by norm_num)
theorem B4618133 : Blo 1366502 4618133 := bbase (se 6 (by rfl) ⟨108237, by rfl⟩ : syracuseStep 4618133 = 216475) (by norm_num)
theorem B2463653 : Blo 1366502 2463653 := bbase (se 4 (by rfl) ⟨230967, by rfl⟩ : syracuseStep 2463653 = 461935) (by norm_num)
theorem B3078053 : Blo 1366502 3078053 := bbase (se 4 (by rfl) ⟨288567, by rfl⟩ : syracuseStep 3078053 = 577135) (by norm_num)
theorem B1537969 : Blo 1366502 1537969 := bbase (se 2 (by rfl) ⟨576738, by rfl⟩ : syracuseStep 1537969 = 1153477) (by norm_num)
theorem B10385333 : Blo 1366502 10385333 := bbase (se 5 (by rfl) ⟨486812, by rfl⟩ : syracuseStep 10385333 = 973625) (by norm_num)
theorem B1538005 : Blo 1366502 1538005 := bbase (se 7 (by rfl) ⟨18023, by rfl⟩ : syracuseStep 1538005 = 36047) (by norm_num)
theorem B2308061 : Blo 1366502 2308061 := bbase (se 3 (by rfl) ⟨432761, by rfl⟩ : syracuseStep 2308061 = 865523) (by norm_num)
theorem B3078125 : Blo 1366502 3078125 := bbase (se 3 (by rfl) ⟨577148, by rfl⟩ : syracuseStep 3078125 = 1154297) (by norm_num)
theorem B2463733 : Blo 1366502 2463733 := bbase (se 5 (by rfl) ⟨115487, by rfl⟩ : syracuseStep 2463733 = 230975) (by norm_num)
theorem B1538041 : Blo 1366502 1538041 := bbase (se 2 (by rfl) ⟨576765, by rfl⟩ : syracuseStep 1538041 = 1153531) (by norm_num)
theorem B2594845 : Blo 1366502 2594845 := bbase (se 3 (by rfl) ⟨486533, by rfl⟩ : syracuseStep 2594845 = 973067) (by norm_num)
theorem B1538077 : Blo 1366502 1538077 := bbase (se 3 (by rfl) ⟨288389, by rfl⟩ : syracuseStep 1538077 = 576779) (by norm_num)
theorem B2463797 : Blo 1366502 2463797 := bbase (se 5 (by rfl) ⟨115490, by rfl⟩ : syracuseStep 2463797 = 230981) (by norm_num)
theorem B3078197 : Blo 1366502 3078197 := bbase (se 5 (by rfl) ⟨144290, by rfl⟩ : syracuseStep 3078197 = 288581) (by norm_num)
theorem B1538113 : Blo 1366502 1538113 := bbase (se 2 (by rfl) ⟨576792, by rfl⟩ : syracuseStep 1538113 = 1153585) (by norm_num)
theorem B96073813 : Blo 1366502 96073813 := bbase (se 8 (by rfl) ⟨562932, by rfl⟩ : syracuseStep 96073813 = 1125865) (by norm_num)
theorem B2308189 : Blo 1366502 2308189 := bbase (se 3 (by rfl) ⟨432785, by rfl⟩ : syracuseStep 2308189 = 865571) (by norm_num)
theorem B1538149 : Blo 1366502 1538149 := bbase (se 4 (by rfl) ⟨144201, by rfl⟩ : syracuseStep 1538149 = 288403) (by norm_num)
theorem B3078269 : Blo 1366502 3078269 := bbase (se 3 (by rfl) ⟨577175, by rfl⟩ : syracuseStep 3078269 = 1154351) (by norm_num)
theorem B1538185 : Blo 1366502 1538185 := bbase (se 2 (by rfl) ⟨576819, by rfl⟩ : syracuseStep 1538185 = 1153639) (by norm_num)
theorem B15587477 : Blo 1366502 15587477 := bbase (se 6 (by rfl) ⟨365331, by rfl⟩ : syracuseStep 15587477 = 730663) (by norm_num)
theorem B1538221 : Blo 1366502 1538221 := bbase (se 3 (by rfl) ⟨288416, by rfl⟩ : syracuseStep 1538221 = 576833) (by norm_num)
theorem B2308277 : Blo 1366502 2308277 := bbase (se 5 (by rfl) ⟨108200, by rfl⟩ : syracuseStep 2308277 = 216401) (by norm_num)
theorem B3463357 : Blo 1366502 3463357 := bbase (se 3 (by rfl) ⟨649379, by rfl⟩ : syracuseStep 3463357 = 1298759) (by norm_num)
theorem B5191877 : Blo 1366502 5191877 := bbase (se 4 (by rfl) ⟨486738, by rfl⟩ : syracuseStep 5191877 = 973477) (by norm_num)
theorem B1480901 : Blo 1366502 1480901 := bbase (se 4 (by rfl) ⟨138834, by rfl⟩ : syracuseStep 1480901 = 277669) (by norm_num)
theorem B3078341 : Blo 1366502 3078341 := bbase (se 4 (by rfl) ⟨288594, by rfl⟩ : syracuseStep 3078341 = 577189) (by norm_num)
theorem B1538257 : Blo 1366502 1538257 := bbase (se 2 (by rfl) ⟨576846, by rfl⟩ : syracuseStep 1538257 = 1153693) (by norm_num)
theorem B1538293 : Blo 1366502 1538293 := bbase (se 5 (by rfl) ⟨72107, by rfl⟩ : syracuseStep 1538293 = 144215) (by norm_num)
theorem B3078413 : Blo 1366502 3078413 := bbase (se 3 (by rfl) ⟨577202, by rfl⟩ : syracuseStep 3078413 = 1154405) (by norm_num)
theorem B1538329 : Blo 1366502 1538329 := bbase (se 2 (by rfl) ⟨576873, by rfl⟩ : syracuseStep 1538329 = 1153747) (by norm_num)
theorem B3463469 : Blo 1366502 3463469 := bbase (se 3 (by rfl) ⟨649400, by rfl⟩ : syracuseStep 3463469 = 1298801) (by norm_num)
theorem B2308405 : Blo 1366502 2308405 := bbase (se 5 (by rfl) ⟨108206, by rfl⟩ : syracuseStep 2308405 = 216413) (by norm_num)
theorem B1538365 : Blo 1366502 1538365 := bbase (se 3 (by rfl) ⟨288443, by rfl⟩ : syracuseStep 1538365 = 576887) (by norm_num)
theorem B4618565 : Blo 1366502 4618565 := bbase (se 4 (by rfl) ⟨432990, by rfl⟩ : syracuseStep 4618565 = 865981) (by norm_num)
theorem B2595149 : Blo 1366502 2595149 := bbase (se 3 (by rfl) ⟨486590, by rfl⟩ : syracuseStep 2595149 = 973181) (by norm_num)
theorem B10377557 : Blo 1366502 10377557 := bbase (se 10 (by rfl) ⟨15201, by rfl⟩ : syracuseStep 10377557 = 30403) (by norm_num)
theorem B3078485 : Blo 1366502 3078485 := bbase (se 10 (by rfl) ⟨4509, by rfl⟩ : syracuseStep 3078485 = 9019) (by norm_num)
theorem B1538401 : Blo 1366502 1538401 := bbase (se 2 (by rfl) ⟨576900, by rfl⟩ : syracuseStep 1538401 = 1153801) (by norm_num)
theorem B1538437 : Blo 1366502 1538437 := bbase (se 4 (by rfl) ⟨144228, by rfl⟩ : syracuseStep 1538437 = 288457) (by norm_num)
theorem B2308493 : Blo 1366502 2308493 := bbase (se 3 (by rfl) ⟨432842, by rfl⟩ : syracuseStep 2308493 = 865685) (by norm_num)
theorem B2251157 : Blo 1366502 2251157 := bbase (se 6 (by rfl) ⟨52761, by rfl⟩ : syracuseStep 2251157 = 105523) (by norm_num)
theorem B3078557 : Blo 1366502 3078557 := bbase (se 3 (by rfl) ⟨577229, by rfl⟩ : syracuseStep 3078557 = 1154459) (by norm_num)
theorem B1538473 : Blo 1366502 1538473 := bbase (se 2 (by rfl) ⟨576927, by rfl⟩ : syracuseStep 1538473 = 1153855) (by norm_num)
theorem B1538509 : Blo 1366502 1538509 := bbase (se 3 (by rfl) ⟨288470, by rfl⟩ : syracuseStep 1538509 = 576941) (by norm_num)
theorem B3078629 : Blo 1366502 3078629 := bbase (se 4 (by rfl) ⟨288621, by rfl⟩ : syracuseStep 3078629 = 577243) (by norm_num)
theorem B3463661 : Blo 1366502 3463661 := bbase (se 3 (by rfl) ⟨649436, by rfl⟩ : syracuseStep 3463661 = 1298873) (by norm_num)
theorem B1538545 : Blo 1366502 1538545 := bbase (se 2 (by rfl) ⟨576954, by rfl⟩ : syracuseStep 1538545 = 1153909) (by norm_num)
theorem B2308621 : Blo 1366502 2308621 := bbase (se 3 (by rfl) ⟨432866, by rfl⟩ : syracuseStep 2308621 = 865733) (by norm_num)
theorem B1538581 : Blo 1366502 1538581 := bbase (se 6 (by rfl) ⟨36060, by rfl⟩ : syracuseStep 1538581 = 72121) (by norm_num)
theorem B3078701 : Blo 1366502 3078701 := bbase (se 3 (by rfl) ⟨577256, by rfl⟩ : syracuseStep 3078701 = 1154513) (by norm_num)
theorem B1538617 : Blo 1366502 1538617 := bbase (se 2 (by rfl) ⟨576981, by rfl⟩ : syracuseStep 1538617 = 1153963) (by norm_num)
theorem B1538653 : Blo 1366502 1538653 := bbase (se 3 (by rfl) ⟨288497, by rfl⟩ : syracuseStep 1538653 = 576995) (by norm_num)
theorem B2308709 : Blo 1366502 2308709 := bbase (se 4 (by rfl) ⟨216441, by rfl⟩ : syracuseStep 2308709 = 432883) (by norm_num)
theorem B3078773 : Blo 1366502 3078773 := bbase (se 5 (by rfl) ⟨144317, by rfl⟩ : syracuseStep 3078773 = 288635) (by norm_num)
theorem B1538689 : Blo 1366502 1538689 := bbase (se 2 (by rfl) ⟨577008, by rfl⟩ : syracuseStep 1538689 = 1154017) (by norm_num)
theorem B2079389 : Blo 1366502 2079389 := bbase (se 3 (by rfl) ⟨389885, by rfl⟩ : syracuseStep 2079389 = 779771) (by norm_num)
theorem B1538725 : Blo 1366502 1538725 := bbase (se 4 (by rfl) ⟨144255, by rfl⟩ : syracuseStep 1538725 = 288511) (by norm_num)
theorem B3078845 : Blo 1366502 3078845 := bbase (se 3 (by rfl) ⟨577283, by rfl⟩ : syracuseStep 3078845 = 1154567) (by norm_num)
theorem B1538761 : Blo 1366502 1538761 := bbase (se 2 (by rfl) ⟨577035, by rfl⟩ : syracuseStep 1538761 = 1154071) (by norm_num)
theorem B2308837 : Blo 1366502 2308837 := bbase (se 4 (by rfl) ⟨216453, by rfl⟩ : syracuseStep 2308837 = 432907) (by norm_num)
theorem B1538797 : Blo 1366502 1538797 := bbase (se 3 (by rfl) ⟨288524, by rfl⟩ : syracuseStep 1538797 = 577049) (by norm_num)
theorem B3554053 : Blo 1366502 3554053 := bbase (se 4 (by rfl) ⟨333192, by rfl⟩ : syracuseStep 3554053 = 666385) (by norm_num)
theorem B3078917 : Blo 1366502 3078917 := bbase (se 4 (by rfl) ⟨288648, by rfl⟩ : syracuseStep 3078917 = 577297) (by norm_num)
theorem B1538833 : Blo 1366502 1538833 := bbase (se 2 (by rfl) ⟨577062, by rfl⟩ : syracuseStep 1538833 = 1154125) (by norm_num)
theorem B1538869 : Blo 1366502 1538869 := bbase (se 5 (by rfl) ⟨72134, by rfl⟩ : syracuseStep 1538869 = 144269) (by norm_num)
theorem B2308925 : Blo 1366502 2308925 := bbase (se 3 (by rfl) ⟨432923, by rfl⟩ : syracuseStep 2308925 = 865847) (by norm_num)
theorem B5839685 : Blo 1366502 5839685 := bbase (se 4 (by rfl) ⟨547470, by rfl⟩ : syracuseStep 5839685 = 1094941) (by norm_num)
theorem B3464005 : Blo 1366502 3464005 := bbase (se 4 (by rfl) ⟨324750, by rfl⟩ : syracuseStep 3464005 = 649501) (by norm_num)
theorem B3078989 : Blo 1366502 3078989 := bbase (se 3 (by rfl) ⟨577310, by rfl⟩ : syracuseStep 3078989 = 1154621) (by norm_num)
theorem B1538905 : Blo 1366502 1538905 := bbase (se 2 (by rfl) ⟨577089, by rfl⟩ : syracuseStep 1538905 = 1154179) (by norm_num)
theorem B1538941 : Blo 1366502 1538941 := bbase (se 3 (by rfl) ⟨288551, by rfl⟩ : syracuseStep 1538941 = 577103) (by norm_num)
theorem B3079061 : Blo 1366502 3079061 := bbase (se 6 (by rfl) ⟨72165, by rfl⟩ : syracuseStep 3079061 = 144331) (by norm_num)
theorem B1538977 : Blo 1366502 1538977 := bbase (se 2 (by rfl) ⟨577116, by rfl⟩ : syracuseStep 1538977 = 1154233) (by norm_num)
theorem B6921125 : Blo 1366502 6921125 := bbase (se 4 (by rfl) ⟨648855, by rfl⟩ : syracuseStep 6921125 = 1297711) (by norm_num)
theorem B2309053 : Blo 1366502 2309053 := bbase (se 3 (by rfl) ⟨432947, by rfl⟩ : syracuseStep 2309053 = 865895) (by norm_num)
theorem B1539013 : Blo 1366502 1539013 := bbase (se 4 (by rfl) ⟨144282, by rfl⟩ : syracuseStep 1539013 = 288565) (by norm_num)
theorem B1539049 : Blo 1366502 1539049 := bbase (se 2 (by rfl) ⟨577143, by rfl⟩ : syracuseStep 1539049 = 1154287) (by norm_num)
theorem B1539085 : Blo 1366502 1539085 := bbase (se 3 (by rfl) ⟨288578, by rfl⟩ : syracuseStep 1539085 = 577157) (by norm_num)
theorem B2309141 : Blo 1366502 2309141 := bbase (se 6 (by rfl) ⟨54120, by rfl⟩ : syracuseStep 2309141 = 108241) (by norm_num)
theorem B1539121 : Blo 1366502 1539121 := bbase (se 2 (by rfl) ⟨577170, by rfl⟩ : syracuseStep 1539121 = 1154341) (by norm_num)
theorem B2595901 : Blo 1366502 2595901 := bbase (se 3 (by rfl) ⟨486731, by rfl⟩ : syracuseStep 2595901 = 973463) (by norm_num)
theorem B1539157 : Blo 1366502 1539157 := bbase (se 8 (by rfl) ⟨9018, by rfl⟩ : syracuseStep 1539157 = 18037) (by norm_num)
theorem B23379029 : Blo 1366502 23379029 := bbase (se 8 (by rfl) ⟨136986, by rfl⟩ : syracuseStep 23379029 = 273973) (by norm_num)
theorem B1539193 : Blo 1366502 1539193 := bbase (se 2 (by rfl) ⟨577197, by rfl⟩ : syracuseStep 1539193 = 1154395) (by norm_num)
theorem B2309269 : Blo 1366502 2309269 := bbase (se 6 (by rfl) ⟨54123, by rfl⟩ : syracuseStep 2309269 = 108247) (by norm_num)
theorem B1539229 : Blo 1366502 1539229 := bbase (se 3 (by rfl) ⟨288605, by rfl⟩ : syracuseStep 1539229 = 577211) (by norm_num)
theorem B4381877 : Blo 1366502 4381877 := bbase (se 5 (by rfl) ⟨205400, by rfl⟩ : syracuseStep 4381877 = 410801) (by norm_num)
theorem B1539265 : Blo 1366502 1539265 := bbase (se 2 (by rfl) ⟨577224, by rfl⟩ : syracuseStep 1539265 = 1154449) (by norm_num)
theorem B2596045 : Blo 1366502 2596045 := bbase (se 3 (by rfl) ⟨486758, by rfl⟩ : syracuseStep 2596045 = 973517) (by norm_num)
theorem B1539301 : Blo 1366502 1539301 := bbase (se 4 (by rfl) ⟨144309, by rfl⟩ : syracuseStep 1539301 = 288619) (by norm_num)
theorem B1539337 : Blo 1366502 1539337 := bbase (se 2 (by rfl) ⟨577251, by rfl⟩ : syracuseStep 1539337 = 1154503) (by norm_num)
theorem B1539373 : Blo 1366502 1539373 := bbase (se 3 (by rfl) ⟨288632, by rfl⟩ : syracuseStep 1539373 = 577265) (by norm_num)
theorem B1539409 : Blo 1366502 1539409 := bbase (se 2 (by rfl) ⟨577278, by rfl⟩ : syracuseStep 1539409 = 1154557) (by norm_num)
theorem B2596205 : Blo 1366502 2596205 := bbase (se 3 (by rfl) ⟨486788, by rfl⟩ : syracuseStep 2596205 = 973577) (by norm_num)
theorem B1539445 : Blo 1366502 1539445 := bbase (se 5 (by rfl) ⟨72161, by rfl⟩ : syracuseStep 1539445 = 144323) (by norm_num)
theorem B1539481 : Blo 1366502 1539481 := bbase (se 2 (by rfl) ⟨577305, by rfl⟩ : syracuseStep 1539481 = 1154611) (by norm_num)
theorem B1539517 : Blo 1366502 1539517 := bbase (se 3 (by rfl) ⟨288659, by rfl⟩ : syracuseStep 1539517 = 577319) (by norm_num)
theorem B1539553 : Blo 1366502 1539553 := bbase (se 2 (by rfl) ⟨577332, by rfl⟩ : syracuseStep 1539553 = 1154665) (by norm_num)
theorem B3948005 : Blo 1366502 3948005 := bbase (se 4 (by rfl) ⟨370125, by rfl⟩ : syracuseStep 3948005 = 740251) (by norm_num)
theorem B2596349 : Blo 1366502 2596349 := bbase (se 3 (by rfl) ⟨486815, by rfl⟩ : syracuseStep 2596349 = 973631) (by norm_num)
theorem B3120653 : Blo 1366502 3120653 := bbase (se 3 (by rfl) ⟨585122, by rfl⟩ : syracuseStep 3120653 = 1170245) (by norm_num)
theorem B3284525 : Blo 1366502 3284525 := bbase (se 3 (by rfl) ⟨615848, by rfl⟩ : syracuseStep 3284525 = 1231697) (by norm_num)
theorem B2080333 : Blo 1366502 2080333 := bbase (se 3 (by rfl) ⟨390062, by rfl⟩ : syracuseStep 2080333 = 780125) (by norm_num)
theorem B8756885 : Blo 1366502 8756885 := bbase (se 6 (by rfl) ⟨205239, by rfl⟩ : syracuseStep 8756885 = 410479) (by norm_num)
theorem B3284669 : Blo 1366502 3284669 := bbase (se 3 (by rfl) ⟨615875, by rfl⟩ : syracuseStep 3284669 = 1231751) (by norm_num)
theorem B31571669 : Blo 1366502 31571669 := bbase (se 7 (by rfl) ⟨369980, by rfl⟩ : syracuseStep 31571669 = 739961) (by norm_num)
theorem B6233861 : Blo 1366502 6233861 := bbase (se 4 (by rfl) ⟨584424, by rfl⟩ : syracuseStep 6233861 = 1168849) (by norm_num)
theorem B2596637 : Blo 1366502 2596637 := bbase (se 3 (by rfl) ⟨486869, by rfl⟩ : syracuseStep 2596637 = 973739) (by norm_num)
theorem B5840693 : Blo 1366502 5840693 := bbase (se 5 (by rfl) ⟨273782, by rfl⟩ : syracuseStep 5840693 = 547565) (by norm_num)
theorem B2596789 : Blo 1366502 2596789 := bbase (se 5 (by rfl) ⟨121724, by rfl⟩ : syracuseStep 2596789 = 243449) (by norm_num)
theorem B1974245 : Blo 1366502 1974245 := bbase (se 4 (by rfl) ⟨185085, by rfl⟩ : syracuseStep 1974245 = 370171) (by norm_num)
theorem B4612085 : Blo 1366502 4612085 := bbase (se 5 (by rfl) ⟨216191, by rfl⟩ : syracuseStep 4612085 = 432383) (by norm_num)
theorem B1368067 : Blo 1366502 1368067 := bstep (se 1 (by rfl) ⟨1026050, by rfl⟩ : syracuseStep 1368067 = 2052101) B2052101
theorem B1368083 : Blo 1366502 1368083 := bstep (se 1 (by rfl) ⟨1026062, by rfl⟩ : syracuseStep 1368083 = 2052125) B2052125
theorem B1368099 : Blo 1366502 1368099 := bstep (se 1 (by rfl) ⟨1026074, by rfl⟩ : syracuseStep 1368099 = 2052149) B2052149
theorem B1368115 : Blo 1366502 1368115 := bstep (se 1 (by rfl) ⟨1026086, by rfl⟩ : syracuseStep 1368115 = 2052173) B2052173
theorem B1368131 : Blo 1366502 1368131 := bstep (se 1 (by rfl) ⟨1026098, by rfl⟩ : syracuseStep 1368131 = 2052197) B2052197
theorem B1753171 : Blo 1366502 1753171 := bstep (se 1 (by rfl) ⟨1314878, by rfl⟩ : syracuseStep 1753171 = 2629757) B2629757
theorem B1368147 : Blo 1366502 1368147 := bstep (se 1 (by rfl) ⟨1026110, by rfl⟩ : syracuseStep 1368147 = 2052221) B2052221
theorem B1368163 : Blo 1366502 1368163 := bstep (se 1 (by rfl) ⟨1026122, by rfl⟩ : syracuseStep 1368163 = 2052245) B2052245
theorem B128098417 : Blo 1366502 128098417 := bstep (se 2 (by rfl) ⟨48036906, by rfl⟩ : syracuseStep 128098417 = 96073813) B96073813
theorem B1368179 : Blo 1366502 1368179 := bstep (se 1 (by rfl) ⟨1026134, by rfl⟩ : syracuseStep 1368179 = 2052269) B2052269
theorem B4382851 : Blo 1366502 4382851 := bstep (se 1 (by rfl) ⟨3287138, by rfl⟩ : syracuseStep 4382851 = 6574277) B6574277
theorem B1368195 : Blo 1366502 1368195 := bstep (se 1 (by rfl) ⟨1026146, by rfl⟩ : syracuseStep 1368195 = 2052293) B2052293
theorem B6570125 : Blo 1366502 6570125 := bstep (se 3 (by rfl) ⟨1231898, by rfl⟩ : syracuseStep 6570125 = 2463797) B2463797
theorem B1368211 : Blo 1366502 1368211 := bstep (se 1 (by rfl) ⟨1026158, by rfl⟩ : syracuseStep 1368211 = 2052317) B2052317
theorem B1368227 : Blo 1366502 1368227 := bstep (se 1 (by rfl) ⟨1026170, by rfl⟩ : syracuseStep 1368227 = 2052341) B2052341
theorem B1368243 : Blo 1366502 1368243 := bstep (se 1 (by rfl) ⟨1026182, by rfl⟩ : syracuseStep 1368243 = 2052365) B2052365
theorem B1368259 : Blo 1366502 1368259 := bstep (se 1 (by rfl) ⟨1026194, by rfl⟩ : syracuseStep 1368259 = 2052389) B2052389
theorem B4612301 : Blo 1366502 4612301 := bstep (se 3 (by rfl) ⟨864806, by rfl⟩ : syracuseStep 4612301 = 1729613) B1729613
theorem B1368275 : Blo 1366502 1368275 := bstep (se 1 (by rfl) ⟨1026206, by rfl⟩ : syracuseStep 1368275 = 2052413) B2052413
theorem B1368291 : Blo 1366502 1368291 := bstep (se 1 (by rfl) ⟨1026218, by rfl⟩ : syracuseStep 1368291 = 2052437) B2052437
theorem B1368307 : Blo 1366502 1368307 := bstep (se 1 (by rfl) ⟨1026230, by rfl⟩ : syracuseStep 1368307 = 2052461) B2052461
theorem B4612355 : Blo 1366502 4612355 := bstep (se 1 (by rfl) ⟨3459266, by rfl⟩ : syracuseStep 4612355 = 6918533) B6918533
theorem B2597123 : Blo 1366502 2597123 := bstep (se 1 (by rfl) ⟨1947842, by rfl⟩ : syracuseStep 2597123 = 3895685) B3895685
theorem B1368323 : Blo 1366502 1368323 := bstep (se 1 (by rfl) ⟨1026242, by rfl⟩ : syracuseStep 1368323 = 2052485) B2052485
theorem B1368339 : Blo 1366502 1368339 := bstep (se 1 (by rfl) ⟨1026254, by rfl⟩ : syracuseStep 1368339 = 2052509) B2052509
theorem B1368355 : Blo 1366502 1368355 := bstep (se 1 (by rfl) ⟨1026266, by rfl⟩ : syracuseStep 1368355 = 2052533) B2052533
theorem B1368371 : Blo 1366502 1368371 := bstep (se 1 (by rfl) ⟨1026278, by rfl⟩ : syracuseStep 1368371 = 2052557) B2052557
theorem B1368387 : Blo 1366502 1368387 := bstep (se 1 (by rfl) ⟨1026290, by rfl⟩ : syracuseStep 1368387 = 2052581) B2052581
theorem B1368403 : Blo 1366502 1368403 := bstep (se 1 (by rfl) ⟨1026302, by rfl⟩ : syracuseStep 1368403 = 2052605) B2052605
theorem B1368419 : Blo 1366502 1368419 := bstep (se 1 (by rfl) ⟨1026314, by rfl⟩ : syracuseStep 1368419 = 2052629) B2052629
theorem B1368435 : Blo 1366502 1368435 := bstep (se 1 (by rfl) ⟨1026326, by rfl⟩ : syracuseStep 1368435 = 2052653) B2052653
theorem B1368451 : Blo 1366502 1368451 := bstep (se 1 (by rfl) ⟨1026338, by rfl⟩ : syracuseStep 1368451 = 2052677) B2052677
theorem B1368467 : Blo 1366502 1368467 := bstep (se 1 (by rfl) ⟨1026350, by rfl⟩ : syracuseStep 1368467 = 2052701) B2052701
theorem B1368483 : Blo 1366502 1368483 := bstep (se 1 (by rfl) ⟨1026362, by rfl⟩ : syracuseStep 1368483 = 2052725) B2052725
theorem B1368499 : Blo 1366502 1368499 := bstep (se 1 (by rfl) ⟨1026374, by rfl⟩ : syracuseStep 1368499 = 2052749) B2052749
theorem B7397837 : Blo 1366502 7397837 := bstep (se 3 (by rfl) ⟨1387094, by rfl⟩ : syracuseStep 7397837 = 2774189) B2774189
theorem B3891665 : Blo 1366502 3891665 := bstep (se 2 (by rfl) ⟨1459374, by rfl⟩ : syracuseStep 3891665 = 2918749) B2918749
theorem B3949069 : Blo 1366502 3949069 := bstep (se 3 (by rfl) ⟨740450, by rfl⟩ : syracuseStep 3949069 = 1480901) B1480901
theorem B4612625 : Blo 1366502 4612625 := bstep (se 2 (by rfl) ⟨1729734, by rfl⟩ : syracuseStep 4612625 = 3459469) B3459469
theorem B4440781 : Blo 1366502 4440781 := bstep (se 3 (by rfl) ⟨832646, by rfl⟩ : syracuseStep 4440781 = 1665293) B1665293
theorem B8758115 : Blo 1366502 8758115 := bstep (se 1 (by rfl) ⟨6568586, by rfl⟩ : syracuseStep 8758115 = 13137173) B13137173
theorem B1778563 : Blo 1366502 1778563 := bstep (se 1 (by rfl) ⟨1333922, by rfl⟩ : syracuseStep 1778563 = 2667845) B2667845
theorem B49873805 : Blo 1366502 49873805 := bstep (se 3 (by rfl) ⟨9351338, by rfl⟩ : syracuseStep 49873805 = 18702677) B18702677
theorem B1729507 : Blo 1366502 1729507 := bstep (se 1 (by rfl) ⟨1297130, by rfl⟩ : syracuseStep 1729507 = 2594261) B2594261
theorem B4613165 : Blo 1366502 4613165 := bstep (se 3 (by rfl) ⟨864968, by rfl⟩ : syracuseStep 4613165 = 1729937) B1729937
theorem B1500211 : Blo 1366502 1500211 := bstep (se 1 (by rfl) ⟨1125158, by rfl⟩ : syracuseStep 1500211 = 2250317) B2250317
theorem B1729603 : Blo 1366502 1729603 := bstep (se 1 (by rfl) ⟨1297202, by rfl⟩ : syracuseStep 1729603 = 2594405) B2594405
theorem B4613219 : Blo 1366502 4613219 := bstep (se 1 (by rfl) ⟨3459914, by rfl⟩ : syracuseStep 4613219 = 6919829) B6919829
theorem B3892337 : Blo 1366502 3892337 := bstep (se 2 (by rfl) ⟨1459626, by rfl⟩ : syracuseStep 3892337 = 2919253) B2919253
theorem B3695825 : Blo 1366502 3695825 := bstep (se 2 (by rfl) ⟨1385934, by rfl⟩ : syracuseStep 3695825 = 2771869) B2771869
theorem B10528013 : Blo 1366502 10528013 := bstep (se 3 (by rfl) ⟨1974002, by rfl⟩ : syracuseStep 10528013 = 3948005) B3948005
theorem B7783715 : Blo 1366502 7783715 := bstep (se 1 (by rfl) ⟨5837786, by rfl⟩ : syracuseStep 7783715 = 11675573) B11675573
theorem B6923555 : Blo 1366502 6923555 := bstep (se 1 (by rfl) ⟨5192666, by rfl⟩ : syracuseStep 6923555 = 10385333) B10385333
theorem B4384081 : Blo 1366502 4384081 := bstep (se 2 (by rfl) ⟨1644030, by rfl⟩ : syracuseStep 4384081 = 3288061) B3288061
theorem B4613489 : Blo 1366502 4613489 := bstep (se 2 (by rfl) ⟨1730058, by rfl⟩ : syracuseStep 4613489 = 3460117) B3460117
theorem B5195249 : Blo 1366502 5195249 := bstep (se 2 (by rfl) ⟨1948218, by rfl⟩ : syracuseStep 5195249 = 3896437) B3896437
theorem B1730099 : Blo 1366502 1730099 := bstep (se 1 (by rfl) ⟨1297574, by rfl⟩ : syracuseStep 1730099 = 2595149) B2595149
theorem B3696301 : Blo 1366502 3696301 := bstep (se 3 (by rfl) ⟨693056, by rfl⟩ : syracuseStep 3696301 = 1386113) B1386113
theorem B1459891 : Blo 1366502 1459891 := bstep (se 1 (by rfl) ⟨1094918, by rfl⟩ : syracuseStep 1459891 = 2189837) B2189837
theorem B2049761 : Blo 1366502 2049761 := bstep (se 2 (by rfl) ⟨768660, by rfl⟩ : syracuseStep 2049761 = 1537321) B1537321
theorem B2049779 : Blo 1366502 2049779 := bstep (se 1 (by rfl) ⟨1537334, by rfl⟩ : syracuseStep 2049779 = 3074669) B3074669
theorem B2049809 : Blo 1366502 2049809 := bstep (se 2 (by rfl) ⟨768678, by rfl⟩ : syracuseStep 2049809 = 1537357) B1537357
theorem B2049827 : Blo 1366502 2049827 := bstep (se 1 (by rfl) ⟨1537370, by rfl⟩ : syracuseStep 2049827 = 3074741) B3074741
theorem B2049857 : Blo 1366502 2049857 := bstep (se 2 (by rfl) ⟨768696, by rfl⟩ : syracuseStep 2049857 = 1537393) B1537393
theorem B8759117 : Blo 1366502 8759117 := bstep (se 3 (by rfl) ⟨1642334, by rfl⟩ : syracuseStep 8759117 = 3284669) B3284669
theorem B2049875 : Blo 1366502 2049875 := bstep (se 1 (by rfl) ⟨1537406, by rfl⟩ : syracuseStep 2049875 = 3074813) B3074813
theorem B2049905 : Blo 1366502 2049905 := bstep (se 2 (by rfl) ⟨768714, by rfl⟩ : syracuseStep 2049905 = 1537429) B1537429
theorem B2049923 : Blo 1366502 2049923 := bstep (se 1 (by rfl) ⟨1537442, by rfl⟩ : syracuseStep 2049923 = 3074885) B3074885
theorem B3893123 : Blo 1366502 3893123 := bstep (se 1 (by rfl) ⟨2919842, by rfl⟩ : syracuseStep 3893123 = 5839685) B5839685
theorem B4614029 : Blo 1366502 4614029 := bstep (se 3 (by rfl) ⟨865130, by rfl⟩ : syracuseStep 4614029 = 1730261) B1730261
theorem B2049953 : Blo 1366502 2049953 := bstep (se 2 (by rfl) ⟨768732, by rfl⟩ : syracuseStep 2049953 = 1537465) B1537465
theorem B2049971 : Blo 1366502 2049971 := bstep (se 1 (by rfl) ⟨1537478, by rfl⟩ : syracuseStep 2049971 = 3074957) B3074957
theorem B4614083 : Blo 1366502 4614083 := bstep (se 1 (by rfl) ⟨3460562, by rfl⟩ : syracuseStep 4614083 = 6921125) B6921125
theorem B2050001 : Blo 1366502 2050001 := bstep (se 2 (by rfl) ⟨768750, by rfl⟩ : syracuseStep 2050001 = 1537501) B1537501
theorem B2050019 : Blo 1366502 2050019 := bstep (se 1 (by rfl) ⟨1537514, by rfl⟩ : syracuseStep 2050019 = 3075029) B3075029
theorem B2050049 : Blo 1366502 2050049 := bstep (se 2 (by rfl) ⟨768768, by rfl⟩ : syracuseStep 2050049 = 1537537) B1537537
theorem B7792645 : Blo 1366502 7792645 := bstep (se 4 (by rfl) ⟨730560, by rfl⟩ : syracuseStep 7792645 = 1461121) B1461121
theorem B2050067 : Blo 1366502 2050067 := bstep (se 1 (by rfl) ⟨1537550, by rfl⟩ : syracuseStep 2050067 = 3075101) B3075101
theorem B2050097 : Blo 1366502 2050097 := bstep (se 2 (by rfl) ⟨768786, by rfl⟩ : syracuseStep 2050097 = 1537573) B1537573
theorem B2050115 : Blo 1366502 2050115 := bstep (se 1 (by rfl) ⟨1537586, by rfl⟩ : syracuseStep 2050115 = 3075173) B3075173
theorem B6924365 : Blo 1366502 6924365 := bstep (se 3 (by rfl) ⟨1298318, by rfl⟩ : syracuseStep 6924365 = 2596637) B2596637
theorem B2050145 : Blo 1366502 2050145 := bstep (se 2 (by rfl) ⟨768804, by rfl⟩ : syracuseStep 2050145 = 1537609) B1537609
theorem B8767601 : Blo 1366502 8767601 := bstep (se 2 (by rfl) ⟨3287850, by rfl⟩ : syracuseStep 8767601 = 6575701) B6575701
theorem B2050163 : Blo 1366502 2050163 := bstep (se 1 (by rfl) ⟨1537622, by rfl⟩ : syracuseStep 2050163 = 3075245) B3075245
theorem B1558643 : Blo 1366502 1558643 := bstep (se 1 (by rfl) ⟨1168982, by rfl⟩ : syracuseStep 1558643 = 2337965) B2337965
theorem B2050193 : Blo 1366502 2050193 := bstep (se 2 (by rfl) ⟨768822, by rfl⟩ : syracuseStep 2050193 = 1537645) B1537645
theorem B2050211 : Blo 1366502 2050211 := bstep (se 1 (by rfl) ⟨1537658, by rfl⟩ : syracuseStep 2050211 = 3075317) B3075317
theorem B2050241 : Blo 1366502 2050241 := bstep (se 2 (by rfl) ⟨768840, by rfl⟩ : syracuseStep 2050241 = 1537681) B1537681
theorem B3893453 : Blo 1366502 3893453 := bstep (se 3 (by rfl) ⟨730022, by rfl⟩ : syracuseStep 3893453 = 1460045) B1460045
theorem B4614353 : Blo 1366502 4614353 := bstep (se 2 (by rfl) ⟨1730382, by rfl⟩ : syracuseStep 4614353 = 3460765) B3460765
theorem B2050259 : Blo 1366502 2050259 := bstep (se 1 (by rfl) ⟨1537694, by rfl⟩ : syracuseStep 2050259 = 3075389) B3075389
theorem B4442339 : Blo 1366502 4442339 := bstep (se 1 (by rfl) ⟨3331754, by rfl⟩ : syracuseStep 4442339 = 6663509) B6663509
theorem B2050289 : Blo 1366502 2050289 := bstep (se 2 (by rfl) ⟨768858, by rfl⟩ : syracuseStep 2050289 = 1537717) B1537717
theorem B1730803 : Blo 1366502 1730803 := bstep (se 1 (by rfl) ⟨1298102, by rfl⟩ : syracuseStep 1730803 = 2596205) B2596205
theorem B2050307 : Blo 1366502 2050307 := bstep (se 1 (by rfl) ⟨1537730, by rfl⟩ : syracuseStep 2050307 = 3075461) B3075461
theorem B3893521 : Blo 1366502 3893521 := bstep (se 2 (by rfl) ⟨1460070, by rfl⟩ : syracuseStep 3893521 = 2920141) B2920141
theorem B2050337 : Blo 1366502 2050337 := bstep (se 2 (by rfl) ⟨768876, by rfl⟩ : syracuseStep 2050337 = 1537753) B1537753
theorem B2050355 : Blo 1366502 2050355 := bstep (se 1 (by rfl) ⟨1537766, by rfl⟩ : syracuseStep 2050355 = 3075533) B3075533
theorem B13330757 : Blo 1366502 13330757 := bstep (se 4 (by rfl) ⟨1249758, by rfl⟩ : syracuseStep 13330757 = 2499517) B2499517
theorem B2050385 : Blo 1366502 2050385 := bstep (se 2 (by rfl) ⟨768894, by rfl⟩ : syracuseStep 2050385 = 1537789) B1537789
theorem B1730899 : Blo 1366502 1730899 := bstep (se 1 (by rfl) ⟨1298174, by rfl⟩ : syracuseStep 1730899 = 2596349) B2596349
theorem B2050403 : Blo 1366502 2050403 := bstep (se 1 (by rfl) ⟨1537802, by rfl⟩ : syracuseStep 2050403 = 3075605) B3075605
theorem B2189683 : Blo 1366502 2189683 := bstep (se 1 (by rfl) ⟨1642262, by rfl⟩ : syracuseStep 2189683 = 3284525) B3284525
theorem B2050433 : Blo 1366502 2050433 := bstep (se 2 (by rfl) ⟨768912, by rfl⟩ : syracuseStep 2050433 = 1537825) B1537825
theorem B2050451 : Blo 1366502 2050451 := bstep (se 1 (by rfl) ⟨1537838, by rfl⟩ : syracuseStep 2050451 = 3075677) B3075677
theorem B2189729 : Blo 1366502 2189729 := bstep (se 2 (by rfl) ⟨821148, by rfl⟩ : syracuseStep 2189729 = 1642297) B1642297
theorem B2050481 : Blo 1366502 2050481 := bstep (se 2 (by rfl) ⟨768930, by rfl⟩ : syracuseStep 2050481 = 1537861) B1537861
theorem B2050499 : Blo 1366502 2050499 := bstep (se 1 (by rfl) ⟨1537874, by rfl⟩ : syracuseStep 2050499 = 3075749) B3075749
theorem B2050529 : Blo 1366502 2050529 := bstep (se 2 (by rfl) ⟨768948, by rfl⟩ : syracuseStep 2050529 = 1537897) B1537897
theorem B21047779 : Blo 1366502 21047779 := bstep (se 1 (by rfl) ⟨15785834, by rfl⟩ : syracuseStep 21047779 = 31571669) B31571669
theorem B2050547 : Blo 1366502 2050547 := bstep (se 1 (by rfl) ⟨1537910, by rfl⟩ : syracuseStep 2050547 = 3075821) B3075821
theorem B4155907 : Blo 1366502 4155907 := bstep (se 1 (by rfl) ⟨3116930, by rfl⟩ : syracuseStep 4155907 = 6233861) B6233861
theorem B2050577 : Blo 1366502 2050577 := bstep (se 2 (by rfl) ⟨768966, by rfl⟩ : syracuseStep 2050577 = 1537933) B1537933
theorem B2050595 : Blo 1366502 2050595 := bstep (se 1 (by rfl) ⟨1537946, by rfl⟩ : syracuseStep 2050595 = 3075893) B3075893
theorem B3893795 : Blo 1366502 3893795 := bstep (se 1 (by rfl) ⟨2920346, by rfl⟩ : syracuseStep 3893795 = 5840693) B5840693
theorem B2050625 : Blo 1366502 2050625 := bstep (se 2 (by rfl) ⟨768984, by rfl⟩ : syracuseStep 2050625 = 1537969) B1537969
theorem B2050643 : Blo 1366502 2050643 := bstep (se 1 (by rfl) ⟨1537982, by rfl⟩ : syracuseStep 2050643 = 3075965) B3075965
theorem B2050673 : Blo 1366502 2050673 := bstep (se 2 (by rfl) ⟨769002, by rfl⟩ : syracuseStep 2050673 = 1538005) B1538005
theorem B2050691 : Blo 1366502 2050691 := bstep (se 1 (by rfl) ⟨1538018, by rfl⟩ : syracuseStep 2050691 = 3076037) B3076037
theorem B3074705 : Blo 1366502 3074705 := bstep (se 2 (by rfl) ⟨1153014, by rfl⟩ : syracuseStep 3074705 = 2306029) B2306029
theorem B2050721 : Blo 1366502 2050721 := bstep (se 2 (by rfl) ⟨769020, by rfl⟩ : syracuseStep 2050721 = 1538041) B1538041
theorem B3074723 : Blo 1366502 3074723 := bstep (se 1 (by rfl) ⟨2306042, by rfl⟩ : syracuseStep 3074723 = 4612085) B4612085
theorem B1460899 : Blo 1366502 1460899 := bstep (se 1 (by rfl) ⟨1095674, by rfl⟩ : syracuseStep 1460899 = 2191349) B2191349
theorem B2050739 : Blo 1366502 2050739 := bstep (se 1 (by rfl) ⟨1538054, by rfl⟩ : syracuseStep 2050739 = 3076109) B3076109
theorem B3459793 : Blo 1366502 3459793 := bstep (se 2 (by rfl) ⟨1297422, by rfl⟩ : syracuseStep 3459793 = 2594845) B2594845
theorem B2050769 : Blo 1366502 2050769 := bstep (se 2 (by rfl) ⟨769038, by rfl⟩ : syracuseStep 2050769 = 1538077) B1538077
theorem B2050787 : Blo 1366502 2050787 := bstep (se 1 (by rfl) ⟨1538090, by rfl⟩ : syracuseStep 2050787 = 3076181) B3076181
theorem B4614893 : Blo 1366502 4614893 := bstep (se 3 (by rfl) ⟨865292, by rfl⟩ : syracuseStep 4614893 = 1730585) B1730585
theorem B2050817 : Blo 1366502 2050817 := bstep (se 2 (by rfl) ⟨769056, by rfl⟩ : syracuseStep 2050817 = 1538113) B1538113
theorem B2050835 : Blo 1366502 2050835 := bstep (se 1 (by rfl) ⟨1538126, by rfl⟩ : syracuseStep 2050835 = 3076253) B3076253
theorem B75819797 : Blo 1366502 75819797 := bstep (se 6 (by rfl) ⟨1777026, by rfl⟩ : syracuseStep 75819797 = 3554053) B3554053
theorem B4614947 : Blo 1366502 4614947 := bstep (se 1 (by rfl) ⟨3461210, by rfl⟩ : syracuseStep 4614947 = 6922421) B6922421
theorem B2050865 : Blo 1366502 2050865 := bstep (se 2 (by rfl) ⟨769074, by rfl⟩ : syracuseStep 2050865 = 1538149) B1538149
theorem B37407541 : Blo 1366502 37407541 := bstep (se 5 (by rfl) ⟨1753478, by rfl⟩ : syracuseStep 37407541 = 3506957) B3506957
theorem B2919235 : Blo 1366502 2919235 := bstep (se 1 (by rfl) ⟨2189426, by rfl⟩ : syracuseStep 2919235 = 4378853) B4378853
theorem B2050883 : Blo 1366502 2050883 := bstep (se 1 (by rfl) ⟨1538162, by rfl⟩ : syracuseStep 2050883 = 3076325) B3076325
theorem B1731395 : Blo 1366502 1731395 := bstep (se 1 (by rfl) ⟨1298546, by rfl⟩ : syracuseStep 1731395 = 2597093) B2597093
theorem B5999437 : Blo 1366502 5999437 := bstep (se 3 (by rfl) ⟨1124894, by rfl⟩ : syracuseStep 5999437 = 2249789) B2249789
theorem B2050913 : Blo 1366502 2050913 := bstep (se 2 (by rfl) ⟨769092, by rfl⟩ : syracuseStep 2050913 = 1538185) B1538185
theorem B2050931 : Blo 1366502 2050931 := bstep (se 1 (by rfl) ⟨1538198, by rfl⟩ : syracuseStep 2050931 = 3076397) B3076397
theorem B2050961 : Blo 1366502 2050961 := bstep (se 2 (by rfl) ⟨769110, by rfl⟩ : syracuseStep 2050961 = 1538221) B1538221
theorem B2050979 : Blo 1366502 2050979 := bstep (se 1 (by rfl) ⟨1538234, by rfl⟩ : syracuseStep 2050979 = 3076469) B3076469
theorem B3074993 : Blo 1366502 3074993 := bstep (se 2 (by rfl) ⟨1153122, by rfl⟩ : syracuseStep 3074993 = 2306245) B2306245
theorem B2051009 : Blo 1366502 2051009 := bstep (se 2 (by rfl) ⟨769128, by rfl⟩ : syracuseStep 2051009 = 1538257) B1538257
theorem B3075011 : Blo 1366502 3075011 := bstep (se 1 (by rfl) ⟨2306258, by rfl⟩ : syracuseStep 3075011 = 4612517) B4612517
theorem B2051027 : Blo 1366502 2051027 := bstep (se 1 (by rfl) ⟨1538270, by rfl⟩ : syracuseStep 2051027 = 3076541) B3076541
theorem B3460067 : Blo 1366502 3460067 := bstep (se 1 (by rfl) ⟨2595050, by rfl⟩ : syracuseStep 3460067 = 5190101) B5190101
theorem B2051057 : Blo 1366502 2051057 := bstep (se 2 (by rfl) ⟨769146, by rfl⟩ : syracuseStep 2051057 = 1538293) B1538293
theorem B2051075 : Blo 1366502 2051075 := bstep (se 1 (by rfl) ⟨1538306, by rfl⟩ : syracuseStep 2051075 = 3076613) B3076613
theorem B2051105 : Blo 1366502 2051105 := bstep (se 2 (by rfl) ⟨769164, by rfl⟩ : syracuseStep 2051105 = 1538329) B1538329
theorem B5188643 : Blo 1366502 5188643 := bstep (se 1 (by rfl) ⟨3891482, by rfl⟩ : syracuseStep 5188643 = 7782965) B7782965
theorem B5188657 : Blo 1366502 5188657 := bstep (se 2 (by rfl) ⟨1945746, by rfl⟩ : syracuseStep 5188657 = 3891493) B3891493
theorem B4615217 : Blo 1366502 4615217 := bstep (se 2 (by rfl) ⟨1730706, by rfl⟩ : syracuseStep 4615217 = 3461413) B3461413
theorem B2051123 : Blo 1366502 2051123 := bstep (se 1 (by rfl) ⟨1538342, by rfl⟩ : syracuseStep 2051123 = 3076685) B3076685
theorem B2051153 : Blo 1366502 2051153 := bstep (se 2 (by rfl) ⟨769182, by rfl⟩ : syracuseStep 2051153 = 1538365) B1538365
theorem B2051171 : Blo 1366502 2051171 := bstep (se 1 (by rfl) ⟨1538378, by rfl⟩ : syracuseStep 2051171 = 3076757) B3076757
theorem B126299249 : Blo 1366502 126299249 := bstep (se 2 (by rfl) ⟨47362218, by rfl⟩ : syracuseStep 126299249 = 94724437) B94724437
theorem B2051201 : Blo 1366502 2051201 := bstep (se 2 (by rfl) ⟨769200, by rfl⟩ : syracuseStep 2051201 = 1538401) B1538401
theorem B2632835 : Blo 1366502 2632835 := bstep (se 1 (by rfl) ⟨1974626, by rfl⟩ : syracuseStep 2632835 = 3949253) B3949253
theorem B11685005 : Blo 1366502 11685005 := bstep (se 3 (by rfl) ⟨2190938, by rfl⟩ : syracuseStep 11685005 = 4381877) B4381877
theorem B5844109 : Blo 1366502 5844109 := bstep (se 3 (by rfl) ⟨1095770, by rfl⟩ : syracuseStep 5844109 = 2191541) B2191541
theorem B2051219 : Blo 1366502 2051219 := bstep (se 1 (by rfl) ⟨1538414, by rfl⟩ : syracuseStep 2051219 = 3076829) B3076829
theorem B3460259 : Blo 1366502 3460259 := bstep (se 1 (by rfl) ⟨2595194, by rfl⟩ : syracuseStep 3460259 = 5190389) B5190389
theorem B2051249 : Blo 1366502 2051249 := bstep (se 2 (by rfl) ⟨769218, by rfl⟩ : syracuseStep 2051249 = 1538437) B1538437
theorem B2051267 : Blo 1366502 2051267 := bstep (se 1 (by rfl) ⟨1538450, by rfl⟩ : syracuseStep 2051267 = 3076901) B3076901
theorem B3075281 : Blo 1366502 3075281 := bstep (se 2 (by rfl) ⟨1153230, by rfl⟩ : syracuseStep 3075281 = 2306461) B2306461
theorem B2051297 : Blo 1366502 2051297 := bstep (se 2 (by rfl) ⟨769236, by rfl⟩ : syracuseStep 2051297 = 1538473) B1538473
theorem B3075299 : Blo 1366502 3075299 := bstep (se 1 (by rfl) ⟨2306474, by rfl⟩ : syracuseStep 3075299 = 4612949) B4612949
theorem B2051315 : Blo 1366502 2051315 := bstep (se 1 (by rfl) ⟨1538486, by rfl⟩ : syracuseStep 2051315 = 3076973) B3076973
theorem B2051345 : Blo 1366502 2051345 := bstep (se 2 (by rfl) ⟨769254, by rfl⟩ : syracuseStep 2051345 = 1538509) B1538509
theorem B3697937 : Blo 1366502 3697937 := bstep (se 2 (by rfl) ⟨1386726, by rfl⟩ : syracuseStep 3697937 = 2773453) B2773453
theorem B2051363 : Blo 1366502 2051363 := bstep (se 1 (by rfl) ⟨1538522, by rfl⟩ : syracuseStep 2051363 = 3077045) B3077045
theorem B2051393 : Blo 1366502 2051393 := bstep (se 2 (by rfl) ⟨769272, by rfl⟩ : syracuseStep 2051393 = 1538545) B1538545
theorem B1641811 : Blo 1366502 1641811 := bstep (se 1 (by rfl) ⟨1231358, by rfl⟩ : syracuseStep 1641811 = 2462717) B2462717
theorem B2051411 : Blo 1366502 2051411 := bstep (se 1 (by rfl) ⟨1538558, by rfl⟩ : syracuseStep 2051411 = 3077117) B3077117
theorem B3894637 : Blo 1366502 3894637 := bstep (se 3 (by rfl) ⟨730244, by rfl⟩ : syracuseStep 3894637 = 1460489) B1460489
theorem B2051441 : Blo 1366502 2051441 := bstep (se 2 (by rfl) ⟨769290, by rfl⟩ : syracuseStep 2051441 = 1538581) B1538581
theorem B2190721 : Blo 1366502 2190721 := bstep (se 2 (by rfl) ⟨821520, by rfl⟩ : syracuseStep 2190721 = 1643041) B1643041
theorem B2051459 : Blo 1366502 2051459 := bstep (se 1 (by rfl) ⟨1538594, by rfl⟩ : syracuseStep 2051459 = 3077189) B3077189
theorem B2051489 : Blo 1366502 2051489 := bstep (se 2 (by rfl) ⟨769308, by rfl⟩ : syracuseStep 2051489 = 1538617) B1538617
theorem B2051507 : Blo 1366502 2051507 := bstep (se 1 (by rfl) ⟨1538630, by rfl⟩ : syracuseStep 2051507 = 3077261) B3077261
theorem B2051537 : Blo 1366502 2051537 := bstep (se 2 (by rfl) ⟨769326, by rfl⟩ : syracuseStep 2051537 = 1538653) B1538653
theorem B2051555 : Blo 1366502 2051555 := bstep (se 1 (by rfl) ⟨1538666, by rfl⟩ : syracuseStep 2051555 = 3077333) B3077333
theorem B3075569 : Blo 1366502 3075569 := bstep (se 2 (by rfl) ⟨1153338, by rfl⟩ : syracuseStep 3075569 = 2306677) B2306677
theorem B2051585 : Blo 1366502 2051585 := bstep (se 2 (by rfl) ⟨769344, by rfl⟩ : syracuseStep 2051585 = 1538689) B1538689
theorem B3075587 : Blo 1366502 3075587 := bstep (se 1 (by rfl) ⟨2306690, by rfl⟩ : syracuseStep 3075587 = 4613381) B4613381
theorem B3894797 : Blo 1366502 3894797 := bstep (se 3 (by rfl) ⟨730274, by rfl⟩ : syracuseStep 3894797 = 1460549) B1460549
theorem B2051603 : Blo 1366502 2051603 := bstep (se 1 (by rfl) ⟨1538702, by rfl⟩ : syracuseStep 2051603 = 3077405) B3077405
theorem B2051633 : Blo 1366502 2051633 := bstep (se 2 (by rfl) ⟨769362, by rfl⟩ : syracuseStep 2051633 = 1538725) B1538725
theorem B2051651 : Blo 1366502 2051651 := bstep (se 1 (by rfl) ⟨1538738, by rfl⟩ : syracuseStep 2051651 = 3077477) B3077477
theorem B4615757 : Blo 1366502 4615757 := bstep (se 3 (by rfl) ⟨865454, by rfl⟩ : syracuseStep 4615757 = 1730909) B1730909
theorem B2051681 : Blo 1366502 2051681 := bstep (se 2 (by rfl) ⟨769380, by rfl⟩ : syracuseStep 2051681 = 1538761) B1538761
theorem B11677283 : Blo 1366502 11677283 := bstep (se 1 (by rfl) ⟨8757962, by rfl⟩ : syracuseStep 11677283 = 17515925) B17515925
theorem B4157027 : Blo 1366502 4157027 := bstep (se 1 (by rfl) ⟨3117770, by rfl⟩ : syracuseStep 4157027 = 6235541) B6235541
theorem B2051699 : Blo 1366502 2051699 := bstep (se 1 (by rfl) ⟨1538774, by rfl⟩ : syracuseStep 2051699 = 3077549) B3077549
theorem B4615811 : Blo 1366502 4615811 := bstep (se 1 (by rfl) ⟨3461858, by rfl⟩ : syracuseStep 4615811 = 6923717) B6923717
theorem B2051729 : Blo 1366502 2051729 := bstep (se 2 (by rfl) ⟨769398, by rfl⟩ : syracuseStep 2051729 = 1538797) B1538797
theorem B2051747 : Blo 1366502 2051747 := bstep (se 1 (by rfl) ⟨1538810, by rfl⟩ : syracuseStep 2051747 = 3077621) B3077621
theorem B2051777 : Blo 1366502 2051777 := bstep (se 2 (by rfl) ⟨769416, by rfl⟩ : syracuseStep 2051777 = 1538833) B1538833
theorem B3894979 : Blo 1366502 3894979 := bstep (se 1 (by rfl) ⟨2921234, by rfl⟩ : syracuseStep 3894979 = 5842469) B5842469
theorem B2051795 : Blo 1366502 2051795 := bstep (se 1 (by rfl) ⟨1538846, by rfl⟩ : syracuseStep 2051795 = 3077693) B3077693
theorem B2961137 : Blo 1366502 2961137 := bstep (se 2 (by rfl) ⟨1110426, by rfl⟩ : syracuseStep 2961137 = 2220853) B2220853
theorem B2051825 : Blo 1366502 2051825 := bstep (se 2 (by rfl) ⟨769434, by rfl⟩ : syracuseStep 2051825 = 1538869) B1538869
theorem B2051843 : Blo 1366502 2051843 := bstep (se 1 (by rfl) ⟨1538882, by rfl⟩ : syracuseStep 2051843 = 3077765) B3077765
theorem B3075857 : Blo 1366502 3075857 := bstep (se 2 (by rfl) ⟨1153446, by rfl⟩ : syracuseStep 3075857 = 2306893) B2306893
theorem B2051873 : Blo 1366502 2051873 := bstep (se 2 (by rfl) ⟨769452, by rfl⟩ : syracuseStep 2051873 = 1538905) B1538905
theorem B3075875 : Blo 1366502 3075875 := bstep (se 1 (by rfl) ⟨2306906, by rfl⟩ : syracuseStep 3075875 = 4613813) B4613813
theorem B2051891 : Blo 1366502 2051891 := bstep (se 1 (by rfl) ⟨1538918, by rfl⟩ : syracuseStep 2051891 = 3077837) B3077837
theorem B2191169 : Blo 1366502 2191169 := bstep (se 2 (by rfl) ⟨821688, by rfl⟩ : syracuseStep 2191169 = 1643377) B1643377
theorem B2051921 : Blo 1366502 2051921 := bstep (se 2 (by rfl) ⟨769470, by rfl⟩ : syracuseStep 2051921 = 1538941) B1538941
theorem B13135715 : Blo 1366502 13135715 := bstep (se 1 (by rfl) ⟨9851786, by rfl⟩ : syracuseStep 13135715 = 19703573) B19703573
theorem B1642339 : Blo 1366502 1642339 := bstep (se 1 (by rfl) ⟨1231754, by rfl⟩ : syracuseStep 1642339 = 2463509) B2463509
theorem B2051939 : Blo 1366502 2051939 := bstep (se 1 (by rfl) ⟨1538954, by rfl⟩ : syracuseStep 2051939 = 3077909) B3077909
theorem B2051969 : Blo 1366502 2051969 := bstep (se 2 (by rfl) ⟨769488, by rfl⟩ : syracuseStep 2051969 = 1538977) B1538977
theorem B4616081 : Blo 1366502 4616081 := bstep (se 2 (by rfl) ⟨1731030, by rfl⟩ : syracuseStep 4616081 = 3462061) B3462061
theorem B2051987 : Blo 1366502 2051987 := bstep (se 1 (by rfl) ⟨1538990, by rfl⟩ : syracuseStep 2051987 = 3077981) B3077981
theorem B2052017 : Blo 1366502 2052017 := bstep (se 2 (by rfl) ⟨769506, by rfl⟩ : syracuseStep 2052017 = 1539013) B1539013
theorem B2052035 : Blo 1366502 2052035 := bstep (se 1 (by rfl) ⟨1539026, by rfl⟩ : syracuseStep 2052035 = 3078053) B3078053
theorem B3698627 : Blo 1366502 3698627 := bstep (se 1 (by rfl) ⟨2773970, by rfl⟩ : syracuseStep 3698627 = 5547941) B5547941
theorem B2052065 : Blo 1366502 2052065 := bstep (se 2 (by rfl) ⟨769524, by rfl⟩ : syracuseStep 2052065 = 1539049) B1539049
theorem B2052083 : Blo 1366502 2052083 := bstep (se 1 (by rfl) ⟨1539062, by rfl⟩ : syracuseStep 2052083 = 3078125) B3078125
theorem B4378637 : Blo 1366502 4378637 := bstep (se 3 (by rfl) ⟨820994, by rfl⟩ : syracuseStep 4378637 = 1641989) B1641989
theorem B2920465 : Blo 1366502 2920465 := bstep (se 2 (by rfl) ⟨1095174, by rfl⟩ : syracuseStep 2920465 = 2190349) B2190349
theorem B2052113 : Blo 1366502 2052113 := bstep (se 2 (by rfl) ⟨769542, by rfl⟩ : syracuseStep 2052113 = 1539085) B1539085
theorem B2306083 : Blo 1366502 2306083 := bstep (se 1 (by rfl) ⟨1729562, by rfl⟩ : syracuseStep 2306083 = 3459125) B3459125
theorem B2052131 : Blo 1366502 2052131 := bstep (se 1 (by rfl) ⟨1539098, by rfl⟩ : syracuseStep 2052131 = 3078197) B3078197
theorem B3076145 : Blo 1366502 3076145 := bstep (se 2 (by rfl) ⟨1153554, by rfl⟩ : syracuseStep 3076145 = 2307109) B2307109
theorem B2052161 : Blo 1366502 2052161 := bstep (se 2 (by rfl) ⟨769560, by rfl⟩ : syracuseStep 2052161 = 1539121) B1539121
theorem B1945667 : Blo 1366502 1945667 := bstep (se 1 (by rfl) ⟨1459250, by rfl⟩ : syracuseStep 1945667 = 2918501) B2918501
theorem B3076163 : Blo 1366502 3076163 := bstep (se 1 (by rfl) ⟨2307122, by rfl⟩ : syracuseStep 3076163 = 4614245) B4614245
theorem B3461201 : Blo 1366502 3461201 := bstep (se 2 (by rfl) ⟨1297950, by rfl⟩ : syracuseStep 3461201 = 2595901) B2595901
theorem B2052179 : Blo 1366502 2052179 := bstep (se 1 (by rfl) ⟨1539134, by rfl⟩ : syracuseStep 2052179 = 3078269) B3078269
theorem B10391651 : Blo 1366502 10391651 := bstep (se 1 (by rfl) ⟨7793738, by rfl⟩ : syracuseStep 10391651 = 15587477) B15587477
theorem B2052209 : Blo 1366502 2052209 := bstep (se 2 (by rfl) ⟨769578, by rfl⟩ : syracuseStep 2052209 = 1539157) B1539157
theorem B3461251 : Blo 1366502 3461251 := bstep (se 1 (by rfl) ⟨2595938, by rfl⟩ : syracuseStep 3461251 = 5191877) B5191877
theorem B2052227 : Blo 1366502 2052227 := bstep (se 1 (by rfl) ⟨1539170, by rfl⟩ : syracuseStep 2052227 = 3078341) B3078341
theorem B2052257 : Blo 1366502 2052257 := bstep (se 2 (by rfl) ⟨769596, by rfl⟩ : syracuseStep 2052257 = 1539193) B1539193
theorem B2306225 : Blo 1366502 2306225 := bstep (se 2 (by rfl) ⟨864834, by rfl⟩ : syracuseStep 2306225 = 1729669) B1729669
theorem B2052275 : Blo 1366502 2052275 := bstep (se 1 (by rfl) ⟨1539206, by rfl⟩ : syracuseStep 2052275 = 3078413) B3078413
theorem B2052305 : Blo 1366502 2052305 := bstep (se 2 (by rfl) ⟨769614, by rfl⟩ : syracuseStep 2052305 = 1539229) B1539229
theorem B6918371 : Blo 1366502 6918371 := bstep (se 1 (by rfl) ⟨5188778, by rfl⟩ : syracuseStep 6918371 = 10377557) B10377557
theorem B2052323 : Blo 1366502 2052323 := bstep (se 1 (by rfl) ⟨1539242, by rfl⟩ : syracuseStep 2052323 = 3078485) B3078485
theorem B2052353 : Blo 1366502 2052353 := bstep (se 2 (by rfl) ⟨769632, by rfl⟩ : syracuseStep 2052353 = 1539265) B1539265
theorem B3461393 : Blo 1366502 3461393 := bstep (se 2 (by rfl) ⟨1298022, by rfl⟩ : syracuseStep 3461393 = 2596045) B2596045
theorem B2052371 : Blo 1366502 2052371 := bstep (se 1 (by rfl) ⟨1539278, by rfl⟩ : syracuseStep 2052371 = 3078557) B3078557
theorem B2306353 : Blo 1366502 2306353 := bstep (se 2 (by rfl) ⟨864882, by rfl⟩ : syracuseStep 2306353 = 1729765) B1729765
theorem B2052401 : Blo 1366502 2052401 := bstep (se 2 (by rfl) ⟨769650, by rfl⟩ : syracuseStep 2052401 = 1539301) B1539301
theorem B2052419 : Blo 1366502 2052419 := bstep (se 1 (by rfl) ⟨1539314, by rfl⟩ : syracuseStep 2052419 = 3078629) B3078629
theorem B3076433 : Blo 1366502 3076433 := bstep (se 2 (by rfl) ⟨1153662, by rfl⟩ : syracuseStep 3076433 = 2307325) B2307325
theorem B2306387 : Blo 1366502 2306387 := bstep (se 1 (by rfl) ⟨1729790, by rfl⟩ : syracuseStep 2306387 = 3459581) B3459581
theorem B2052449 : Blo 1366502 2052449 := bstep (se 2 (by rfl) ⟨769668, by rfl⟩ : syracuseStep 2052449 = 1539337) B1539337
theorem B3076451 : Blo 1366502 3076451 := bstep (se 1 (by rfl) ⟨2307338, by rfl⟩ : syracuseStep 3076451 = 4614677) B4614677
theorem B2052467 : Blo 1366502 2052467 := bstep (se 1 (by rfl) ⟨1539350, by rfl⟩ : syracuseStep 2052467 = 3078701) B3078701
theorem B9351557 : Blo 1366502 9351557 := bstep (se 4 (by rfl) ⟨876708, by rfl⟩ : syracuseStep 9351557 = 1753417) B1753417
theorem B2052497 : Blo 1366502 2052497 := bstep (se 2 (by rfl) ⟨769686, by rfl⟩ : syracuseStep 2052497 = 1539373) B1539373
theorem B2052515 : Blo 1366502 2052515 := bstep (se 1 (by rfl) ⟨1539386, by rfl⟩ : syracuseStep 2052515 = 3078773) B3078773
theorem B4616621 : Blo 1366502 4616621 := bstep (se 3 (by rfl) ⟨865616, by rfl⟩ : syracuseStep 4616621 = 1731233) B1731233
theorem B1847729 : Blo 1366502 1847729 := bstep (se 2 (by rfl) ⟨692898, by rfl⟩ : syracuseStep 1847729 = 1385797) B1385797
theorem B2052545 : Blo 1366502 2052545 := bstep (se 2 (by rfl) ⟨769704, by rfl⟩ : syracuseStep 2052545 = 1539409) B1539409
theorem B1847761 : Blo 1366502 1847761 := bstep (se 2 (by rfl) ⟨692910, by rfl⟩ : syracuseStep 1847761 = 1385821) B1385821
theorem B2306515 : Blo 1366502 2306515 := bstep (se 1 (by rfl) ⟨1729886, by rfl⟩ : syracuseStep 2306515 = 3459773) B3459773
theorem B2052563 : Blo 1366502 2052563 := bstep (se 1 (by rfl) ⟨1539422, by rfl⟩ : syracuseStep 2052563 = 3078845) B3078845
theorem B5190115 : Blo 1366502 5190115 := bstep (se 1 (by rfl) ⟨3892586, by rfl⟩ : syracuseStep 5190115 = 7785173) B7785173
theorem B4616675 : Blo 1366502 4616675 := bstep (se 1 (by rfl) ⟨3462506, by rfl⟩ : syracuseStep 4616675 = 6925013) B6925013
theorem B2052593 : Blo 1366502 2052593 := bstep (se 2 (by rfl) ⟨769722, by rfl⟩ : syracuseStep 2052593 = 1539445) B1539445
theorem B2052611 : Blo 1366502 2052611 := bstep (se 1 (by rfl) ⟨1539458, by rfl⟩ : syracuseStep 2052611 = 3078917) B3078917
theorem B2052641 : Blo 1366502 2052641 := bstep (se 2 (by rfl) ⟨769740, by rfl⟩ : syracuseStep 2052641 = 1539481) B1539481
theorem B2052659 : Blo 1366502 2052659 := bstep (se 1 (by rfl) ⟨1539494, by rfl⟩ : syracuseStep 2052659 = 3078989) B3078989
theorem B2052689 : Blo 1366502 2052689 := bstep (se 2 (by rfl) ⟨769758, by rfl⟩ : syracuseStep 2052689 = 1539517) B1539517
theorem B2306657 : Blo 1366502 2306657 := bstep (se 2 (by rfl) ⟨864996, by rfl⟩ : syracuseStep 2306657 = 1729993) B1729993
theorem B2052707 : Blo 1366502 2052707 := bstep (se 1 (by rfl) ⟨1539530, by rfl⟩ : syracuseStep 2052707 = 3079061) B3079061
theorem B1946225 : Blo 1366502 1946225 := bstep (se 2 (by rfl) ⟨729834, by rfl⟩ : syracuseStep 1946225 = 1459669) B1459669
theorem B3076721 : Blo 1366502 3076721 := bstep (se 2 (by rfl) ⟨1153770, by rfl⟩ : syracuseStep 3076721 = 2307541) B2307541
theorem B2052737 : Blo 1366502 2052737 := bstep (se 2 (by rfl) ⟨769776, by rfl⟩ : syracuseStep 2052737 = 1539553) B1539553
theorem B3076739 : Blo 1366502 3076739 := bstep (se 1 (by rfl) ⟨2307554, by rfl⟩ : syracuseStep 3076739 = 4615109) B4615109
theorem B2192035 : Blo 1366502 2192035 := bstep (se 1 (by rfl) ⟨1644026, by rfl⟩ : syracuseStep 2192035 = 3288053) B3288053
theorem B1946305 : Blo 1366502 1946305 := bstep (se 2 (by rfl) ⟨729864, by rfl⟩ : syracuseStep 1946305 = 1459729) B1459729
theorem B2306785 : Blo 1366502 2306785 := bstep (se 2 (by rfl) ⟨865044, by rfl⟩ : syracuseStep 2306785 = 1730089) B1730089
theorem B15586019 : Blo 1366502 15586019 := bstep (se 1 (by rfl) ⟨11689514, by rfl⟩ : syracuseStep 15586019 = 23379029) B23379029
theorem B4616945 : Blo 1366502 4616945 := bstep (se 2 (by rfl) ⟨1731354, by rfl⟩ : syracuseStep 4616945 = 3462709) B3462709
theorem B2306819 : Blo 1366502 2306819 := bstep (se 1 (by rfl) ⟨1730114, by rfl⟩ : syracuseStep 2306819 = 3460229) B3460229
theorem B2773777 : Blo 1366502 2773777 := bstep (se 2 (by rfl) ⟨1040166, by rfl⟩ : syracuseStep 2773777 = 2080333) B2080333
theorem B44970773 : Blo 1366502 44970773 := bstep (se 6 (by rfl) ⟨1054002, by rfl⟩ : syracuseStep 44970773 = 2108005) B2108005
theorem B8319793 : Blo 1366502 8319793 := bstep (se 2 (by rfl) ⟨3119922, by rfl⟩ : syracuseStep 8319793 = 6239845) B6239845
theorem B17765189 : Blo 1366502 17765189 := bstep (se 4 (by rfl) ⟨1665486, by rfl⟩ : syracuseStep 17765189 = 3330973) B3330973
theorem B2306947 : Blo 1366502 2306947 := bstep (se 1 (by rfl) ⟨1730210, by rfl⟩ : syracuseStep 2306947 = 3460421) B3460421
theorem B3077009 : Blo 1366502 3077009 := bstep (se 2 (by rfl) ⟨1153878, by rfl⟩ : syracuseStep 3077009 = 2307757) B2307757
theorem B3077027 : Blo 1366502 3077027 := bstep (se 1 (by rfl) ⟨2307770, by rfl⟩ : syracuseStep 3077027 = 4615541) B4615541
theorem B6927281 : Blo 1366502 6927281 := bstep (se 2 (by rfl) ⟨2597730, by rfl⟩ : syracuseStep 6927281 = 5195461) B5195461
theorem B1848259 : Blo 1366502 1848259 := bstep (se 1 (by rfl) ⟨1386194, by rfl⟩ : syracuseStep 1848259 = 2772389) B2772389
theorem B2339779 : Blo 1366502 2339779 := bstep (se 1 (by rfl) ⟨1754834, by rfl⟩ : syracuseStep 2339779 = 3509669) B3509669
theorem B6919181 : Blo 1366502 6919181 := bstep (se 3 (by rfl) ⟨1297346, by rfl⟩ : syracuseStep 6919181 = 2594693) B2594693
theorem B2307089 : Blo 1366502 2307089 := bstep (se 2 (by rfl) ⟨865158, by rfl⟩ : syracuseStep 2307089 = 1730317) B1730317
theorem B3896369 : Blo 1366502 3896369 := bstep (se 2 (by rfl) ⟨1461138, by rfl⟩ : syracuseStep 3896369 = 2922277) B2922277
theorem B21058613 : Blo 1366502 21058613 := bstep (se 5 (by rfl) ⟨987122, by rfl⟩ : syracuseStep 21058613 = 1974245) B1974245
theorem B53310517 : Blo 1366502 53310517 := bstep (se 5 (by rfl) ⟨2498930, by rfl⟩ : syracuseStep 53310517 = 4997861) B4997861
theorem B5837923 : Blo 1366502 5837923 := bstep (se 1 (by rfl) ⟨4378442, by rfl⟩ : syracuseStep 5837923 = 8756885) B8756885
theorem B2307217 : Blo 1366502 2307217 := bstep (se 2 (by rfl) ⟨865206, by rfl⟩ : syracuseStep 2307217 = 1730413) B1730413
theorem B3077297 : Blo 1366502 3077297 := bstep (se 2 (by rfl) ⟨1153986, by rfl⟩ : syracuseStep 3077297 = 2307973) B2307973
theorem B2307251 : Blo 1366502 2307251 := bstep (se 1 (by rfl) ⟨1730438, by rfl⟩ : syracuseStep 2307251 = 3460877) B3460877
theorem B3077315 : Blo 1366502 3077315 := bstep (se 1 (by rfl) ⟨2307986, by rfl⟩ : syracuseStep 3077315 = 4615973) B4615973
theorem B3462385 : Blo 1366502 3462385 := bstep (se 2 (by rfl) ⟨1298394, by rfl⟩ : syracuseStep 3462385 = 2596789) B2596789
theorem B4617485 : Blo 1366502 4617485 := bstep (se 3 (by rfl) ⟨865778, by rfl⟩ : syracuseStep 4617485 = 1731557) B1731557
theorem B2307379 : Blo 1366502 2307379 := bstep (se 1 (by rfl) ⟨1730534, by rfl⟩ : syracuseStep 2307379 = 3461069) B3461069
theorem B4617539 : Blo 1366502 4617539 := bstep (se 1 (by rfl) ⟨3463154, by rfl⟩ : syracuseStep 4617539 = 6926309) B6926309
theorem B6567281 : Blo 1366502 6567281 := bstep (se 2 (by rfl) ⟨2462730, by rfl⟩ : syracuseStep 6567281 = 4925461) B4925461
theorem B1537411 : Blo 1366502 1537411 := bstep (se 1 (by rfl) ⟨1153058, by rfl⟩ : syracuseStep 1537411 = 2306117) B2306117
theorem B4740515 : Blo 1366502 4740515 := bstep (se 1 (by rfl) ⟨3555386, by rfl⟩ : syracuseStep 4740515 = 7110773) B7110773
theorem B2307521 : Blo 1366502 2307521 := bstep (se 2 (by rfl) ⟨865320, by rfl⟩ : syracuseStep 2307521 = 1730641) B1730641
theorem B3077585 : Blo 1366502 3077585 := bstep (se 2 (by rfl) ⟨1154094, by rfl⟩ : syracuseStep 3077585 = 2308189) B2308189
theorem B1947091 : Blo 1366502 1947091 := bstep (se 1 (by rfl) ⟨1460318, by rfl⟩ : syracuseStep 1947091 = 2920637) B2920637
theorem B3077603 : Blo 1366502 3077603 := bstep (se 1 (by rfl) ⟨2308202, by rfl⟩ : syracuseStep 3077603 = 4616405) B4616405
theorem B2921969 : Blo 1366502 2921969 := bstep (se 2 (by rfl) ⟨1095738, by rfl⟩ : syracuseStep 2921969 = 2191477) B2191477
theorem B3462659 : Blo 1366502 3462659 := bstep (se 1 (by rfl) ⟨2596994, by rfl⟩ : syracuseStep 3462659 = 5193989) B5193989
theorem B2921987 : Blo 1366502 2921987 := bstep (se 1 (by rfl) ⟨2191490, by rfl⟩ : syracuseStep 2921987 = 4382981) B4382981
theorem B1537555 : Blo 1366502 1537555 := bstep (se 1 (by rfl) ⟨1153166, by rfl⟩ : syracuseStep 1537555 = 2306333) B2306333
theorem B2307649 : Blo 1366502 2307649 := bstep (se 2 (by rfl) ⟨865368, by rfl⟩ : syracuseStep 2307649 = 1730737) B1730737
theorem B4617809 : Blo 1366502 4617809 := bstep (se 2 (by rfl) ⟨1731678, by rfl⟩ : syracuseStep 4617809 = 3463357) B3463357
theorem B2307683 : Blo 1366502 2307683 := bstep (se 1 (by rfl) ⟨1730762, by rfl⟩ : syracuseStep 2307683 = 3461525) B3461525
theorem B4159117 : Blo 1366502 4159117 := bstep (se 3 (by rfl) ⟨779834, by rfl⟩ : syracuseStep 4159117 = 1559669) B1559669
theorem B1537699 : Blo 1366502 1537699 := bstep (se 1 (by rfl) ⟨1153274, by rfl⟩ : syracuseStep 1537699 = 2306549) B2306549
theorem B3462851 : Blo 1366502 3462851 := bstep (se 1 (by rfl) ⟨2597138, by rfl⟩ : syracuseStep 3462851 = 5194277) B5194277
theorem B33265349 : Blo 1366502 33265349 := bstep (se 4 (by rfl) ⟨3118626, by rfl⟩ : syracuseStep 33265349 = 6237253) B6237253
theorem B2307811 : Blo 1366502 2307811 := bstep (se 1 (by rfl) ⟨1730858, by rfl⟩ : syracuseStep 2307811 = 3461717) B3461717
theorem B3077873 : Blo 1366502 3077873 := bstep (se 2 (by rfl) ⟨1154202, by rfl⟩ : syracuseStep 3077873 = 2308405) B2308405
theorem B2340593 : Blo 1366502 2340593 := bstep (se 2 (by rfl) ⟨877722, by rfl⟩ : syracuseStep 2340593 = 1755445) B1755445
theorem B3077891 : Blo 1366502 3077891 := bstep (se 1 (by rfl) ⟨2308418, by rfl⟩ : syracuseStep 3077891 = 4616837) B4616837
theorem B1537843 : Blo 1366502 1537843 := bstep (se 1 (by rfl) ⟨1153382, by rfl⟩ : syracuseStep 1537843 = 2306765) B2306765
theorem B4380493 : Blo 1366502 4380493 := bstep (se 3 (by rfl) ⟨821342, by rfl⟩ : syracuseStep 4380493 = 1642685) B1642685
theorem B2307953 : Blo 1366502 2307953 := bstep (se 2 (by rfl) ⟨865482, by rfl⟩ : syracuseStep 2307953 = 1730965) B1730965
theorem B16013197 : Blo 1366502 16013197 := bstep (se 3 (by rfl) ⟨3002474, by rfl⟩ : syracuseStep 16013197 = 6004949) B6004949
theorem B1947569 : Blo 1366502 1947569 := bstep (se 2 (by rfl) ⟨730338, by rfl⟩ : syracuseStep 1947569 = 1460677) B1460677
theorem B1537987 : Blo 1366502 1537987 := bstep (se 1 (by rfl) ⟨1153490, by rfl⟩ : syracuseStep 1537987 = 2306981) B2306981
theorem B4741073 : Blo 1366502 4741073 := bstep (se 2 (by rfl) ⟨1777902, by rfl⟩ : syracuseStep 4741073 = 3555805) B3555805
theorem B1849297 : Blo 1366502 1849297 := bstep (se 2 (by rfl) ⟨693486, by rfl⟩ : syracuseStep 1849297 = 1386973) B1386973
theorem B2308081 : Blo 1366502 2308081 := bstep (se 2 (by rfl) ⟨865530, by rfl⟩ : syracuseStep 2308081 = 1731061) B1731061
theorem B1972225 : Blo 1366502 1972225 := bstep (se 2 (by rfl) ⟨739584, by rfl⟩ : syracuseStep 1972225 = 1479169) B1479169
theorem B3078161 : Blo 1366502 3078161 := bstep (se 2 (by rfl) ⟨1154310, by rfl⟩ : syracuseStep 3078161 = 2308621) B2308621
theorem B2308115 : Blo 1366502 2308115 := bstep (se 1 (by rfl) ⟨1731086, by rfl⟩ : syracuseStep 2308115 = 3462173) B3462173
theorem B6567971 : Blo 1366502 6567971 := bstep (se 1 (by rfl) ⟨4925978, by rfl⟩ : syracuseStep 6567971 = 9851957) B9851957
theorem B1947683 : Blo 1366502 1947683 := bstep (se 1 (by rfl) ⟨1460762, by rfl⟩ : syracuseStep 1947683 = 2921525) B2921525
theorem B3078179 : Blo 1366502 3078179 := bstep (se 1 (by rfl) ⟨2308634, by rfl⟩ : syracuseStep 3078179 = 4617269) B4617269
theorem B1538131 : Blo 1366502 1538131 := bstep (se 1 (by rfl) ⟨1153598, by rfl⟩ : syracuseStep 1538131 = 2307197) B2307197
theorem B4618349 : Blo 1366502 4618349 := bstep (se 3 (by rfl) ⟨865940, by rfl⟩ : syracuseStep 4618349 = 1731881) B1731881
theorem B2594929 : Blo 1366502 2594929 := bstep (se 2 (by rfl) ⟨973098, by rfl⟩ : syracuseStep 2594929 = 1946197) B1946197
theorem B1947763 : Blo 1366502 1947763 := bstep (se 1 (by rfl) ⟨1460822, by rfl⟩ : syracuseStep 1947763 = 2921645) B2921645
theorem B2308243 : Blo 1366502 2308243 := bstep (se 1 (by rfl) ⟨1731182, by rfl⟩ : syracuseStep 2308243 = 3462365) B3462365
theorem B4618403 : Blo 1366502 4618403 := bstep (se 1 (by rfl) ⟨3463802, by rfl⟩ : syracuseStep 4618403 = 6927605) B6927605
theorem B1538275 : Blo 1366502 1538275 := bstep (se 1 (by rfl) ⟨1153706, by rfl⟩ : syracuseStep 1538275 = 2307413) B2307413
theorem B9861389 : Blo 1366502 9861389 := bstep (se 3 (by rfl) ⟨1849010, by rfl⟩ : syracuseStep 9861389 = 3698021) B3698021
theorem B2308385 : Blo 1366502 2308385 := bstep (se 2 (by rfl) ⟨865644, by rfl⟩ : syracuseStep 2308385 = 1731289) B1731289
theorem B3078449 : Blo 1366502 3078449 := bstep (se 2 (by rfl) ⟨1154418, by rfl⟩ : syracuseStep 3078449 = 2308837) B2308837
theorem B3078467 : Blo 1366502 3078467 := bstep (se 1 (by rfl) ⟨2308850, by rfl⟩ : syracuseStep 3078467 = 4617701) B4617701
theorem B7493987 : Blo 1366502 7493987 := bstep (se 1 (by rfl) ⟨5620490, by rfl⟩ : syracuseStep 7493987 = 11240981) B11240981
theorem B1538419 : Blo 1366502 1538419 := bstep (se 1 (by rfl) ⟨1153814, by rfl⟩ : syracuseStep 1538419 = 2307629) B2307629
theorem B6003085 : Blo 1366502 6003085 := bstep (se 3 (by rfl) ⟨1125578, by rfl⟩ : syracuseStep 6003085 = 2251157) B2251157
theorem B2308513 : Blo 1366502 2308513 := bstep (se 2 (by rfl) ⟨865692, by rfl⟩ : syracuseStep 2308513 = 1731385) B1731385
theorem B4618673 : Blo 1366502 4618673 := bstep (se 2 (by rfl) ⟨1732002, by rfl⟩ : syracuseStep 4618673 = 3464005) B3464005
theorem B2464195 : Blo 1366502 2464195 := bstep (se 1 (by rfl) ⟨1848146, by rfl⟩ : syracuseStep 2464195 = 3696293) B3696293
theorem B2308547 : Blo 1366502 2308547 := bstep (se 1 (by rfl) ⟨1731410, by rfl⟩ : syracuseStep 2308547 = 3462821) B3462821
theorem B1366515 : Blo 1366502 1366515 := bstep (se 1 (by rfl) ⟨1024886, by rfl⟩ : syracuseStep 1366515 = 2049773) B2049773
theorem B1366531 : Blo 1366502 1366531 := bstep (se 1 (by rfl) ⟨1024898, by rfl⟩ : syracuseStep 1366531 = 2049797) B2049797
theorem B2595331 : Blo 1366502 2595331 := bstep (se 1 (by rfl) ⟨1946498, by rfl⟩ : syracuseStep 2595331 = 3892997) B3892997
theorem B7494149 : Blo 1366502 7494149 := bstep (se 4 (by rfl) ⟨702576, by rfl⟩ : syracuseStep 7494149 = 1405153) B1405153
theorem B1538563 : Blo 1366502 1538563 := bstep (se 1 (by rfl) ⟨1153922, by rfl⟩ : syracuseStep 1538563 = 2307845) B2307845
theorem B1366547 : Blo 1366502 1366547 := bstep (se 1 (by rfl) ⟨1024910, by rfl⟩ : syracuseStep 1366547 = 2049821) B2049821
theorem B1366563 : Blo 1366502 1366563 := bstep (se 1 (by rfl) ⟨1024922, by rfl⟩ : syracuseStep 1366563 = 2049845) B2049845
theorem B2595377 : Blo 1366502 2595377 := bstep (se 2 (by rfl) ⟨973266, by rfl⟩ : syracuseStep 2595377 = 1946533) B1946533
theorem B1366579 : Blo 1366502 1366579 := bstep (se 1 (by rfl) ⟨1024934, by rfl⟩ : syracuseStep 1366579 = 2049869) B2049869
theorem B1366595 : Blo 1366502 1366595 := bstep (se 1 (by rfl) ⟨1024946, by rfl⟩ : syracuseStep 1366595 = 2049893) B2049893
theorem B2308675 : Blo 1366502 2308675 := bstep (se 1 (by rfl) ⟨1731506, by rfl⟩ : syracuseStep 2308675 = 3463013) B3463013
theorem B3078737 : Blo 1366502 3078737 := bstep (se 2 (by rfl) ⟨1154526, by rfl⟩ : syracuseStep 3078737 = 2309053) B2309053
theorem B1366611 : Blo 1366502 1366611 := bstep (se 1 (by rfl) ⟨1024958, by rfl⟩ : syracuseStep 1366611 = 2049917) B2049917
theorem B1366627 : Blo 1366502 1366627 := bstep (se 1 (by rfl) ⟨1024970, by rfl⟩ : syracuseStep 1366627 = 2049941) B2049941
theorem B3078755 : Blo 1366502 3078755 := bstep (se 1 (by rfl) ⟨2309066, by rfl⟩ : syracuseStep 3078755 = 4618133) B4618133
theorem B3463793 : Blo 1366502 3463793 := bstep (se 2 (by rfl) ⟨1298922, by rfl⟩ : syracuseStep 3463793 = 2597845) B2597845
theorem B1366643 : Blo 1366502 1366643 := bstep (se 1 (by rfl) ⟨1024982, by rfl⟩ : syracuseStep 1366643 = 2049965) B2049965
theorem B1366659 : Blo 1366502 1366659 := bstep (se 1 (by rfl) ⟨1024994, by rfl⟩ : syracuseStep 1366659 = 2049989) B2049989
theorem B5192333 : Blo 1366502 5192333 := bstep (se 3 (by rfl) ⟨973562, by rfl⟩ : syracuseStep 5192333 = 1947125) B1947125
theorem B7019149 : Blo 1366502 7019149 := bstep (se 3 (by rfl) ⟨1316090, by rfl⟩ : syracuseStep 7019149 = 2632181) B2632181
theorem B1366675 : Blo 1366502 1366675 := bstep (se 1 (by rfl) ⟨1025006, by rfl⟩ : syracuseStep 1366675 = 2050013) B2050013
theorem B1538707 : Blo 1366502 1538707 := bstep (se 1 (by rfl) ⟨1154030, by rfl⟩ : syracuseStep 1538707 = 2308061) B2308061
theorem B1948321 : Blo 1366502 1948321 := bstep (se 2 (by rfl) ⟨730620, by rfl⟩ : syracuseStep 1948321 = 1461241) B1461241
theorem B1366691 : Blo 1366502 1366691 := bstep (se 1 (by rfl) ⟨1025018, by rfl⟩ : syracuseStep 1366691 = 2050037) B2050037
theorem B3463843 : Blo 1366502 3463843 := bstep (se 1 (by rfl) ⟨2597882, by rfl⟩ : syracuseStep 3463843 = 5195765) B5195765
theorem B1366707 : Blo 1366502 1366707 := bstep (se 1 (by rfl) ⟨1025030, by rfl⟩ : syracuseStep 1366707 = 2050061) B2050061
theorem B1366723 : Blo 1366502 1366723 := bstep (se 1 (by rfl) ⟨1025042, by rfl⟩ : syracuseStep 1366723 = 2050085) B2050085
theorem B8321741 : Blo 1366502 8321741 := bstep (se 3 (by rfl) ⟨1560326, by rfl⟩ : syracuseStep 8321741 = 3120653) B3120653
theorem B2308817 : Blo 1366502 2308817 := bstep (se 2 (by rfl) ⟨865806, by rfl⟩ : syracuseStep 2308817 = 1731613) B1731613
theorem B1366739 : Blo 1366502 1366739 := bstep (se 1 (by rfl) ⟨1025054, by rfl⟩ : syracuseStep 1366739 = 2050109) B2050109
theorem B1366755 : Blo 1366502 1366755 := bstep (se 1 (by rfl) ⟨1025066, by rfl⟩ : syracuseStep 1366755 = 2050133) B2050133
theorem B1366771 : Blo 1366502 1366771 := bstep (se 1 (by rfl) ⟨1025078, by rfl⟩ : syracuseStep 1366771 = 2050157) B2050157
theorem B1366787 : Blo 1366502 1366787 := bstep (se 1 (by rfl) ⟨1025090, by rfl⟩ : syracuseStep 1366787 = 2050181) B2050181
theorem B1366803 : Blo 1366502 1366803 := bstep (se 1 (by rfl) ⟨1025102, by rfl⟩ : syracuseStep 1366803 = 2050205) B2050205
theorem B1366819 : Blo 1366502 1366819 := bstep (se 1 (by rfl) ⟨1025114, by rfl⟩ : syracuseStep 1366819 = 2050229) B2050229
theorem B1538851 : Blo 1366502 1538851 := bstep (se 1 (by rfl) ⟨1154138, by rfl⟩ : syracuseStep 1538851 = 2308277) B2308277
theorem B3463985 : Blo 1366502 3463985 := bstep (se 2 (by rfl) ⟨1298994, by rfl⟩ : syracuseStep 3463985 = 2597989) B2597989
theorem B1366835 : Blo 1366502 1366835 := bstep (se 1 (by rfl) ⟨1025126, by rfl⟩ : syracuseStep 1366835 = 2050253) B2050253
theorem B1366851 : Blo 1366502 1366851 := bstep (se 1 (by rfl) ⟨1025138, by rfl⟩ : syracuseStep 1366851 = 2050277) B2050277
theorem B2595665 : Blo 1366502 2595665 := bstep (se 2 (by rfl) ⟨973374, by rfl⟩ : syracuseStep 2595665 = 1946749) B1946749
theorem B2308945 : Blo 1366502 2308945 := bstep (se 2 (by rfl) ⟨865854, by rfl⟩ : syracuseStep 2308945 = 1731709) B1731709
theorem B1366867 : Blo 1366502 1366867 := bstep (se 1 (by rfl) ⟨1025150, by rfl⟩ : syracuseStep 1366867 = 2050301) B2050301
theorem B1366883 : Blo 1366502 1366883 := bstep (se 1 (by rfl) ⟨1025162, by rfl⟩ : syracuseStep 1366883 = 2050325) B2050325
theorem B3079025 : Blo 1366502 3079025 := bstep (se 2 (by rfl) ⟨1154634, by rfl⟩ : syracuseStep 3079025 = 2309269) B2309269
theorem B1366899 : Blo 1366502 1366899 := bstep (se 1 (by rfl) ⟨1025174, by rfl⟩ : syracuseStep 1366899 = 2050349) B2050349
theorem B2308979 : Blo 1366502 2308979 := bstep (se 1 (by rfl) ⟨1731734, by rfl⟩ : syracuseStep 2308979 = 3463469) B3463469
theorem B1366915 : Blo 1366502 1366915 := bstep (se 1 (by rfl) ⟨1025186, by rfl⟩ : syracuseStep 1366915 = 2050373) B2050373
theorem B3079043 : Blo 1366502 3079043 := bstep (se 1 (by rfl) ⟨2309282, by rfl⟩ : syracuseStep 3079043 = 4618565) B4618565
theorem B1366931 : Blo 1366502 1366931 := bstep (se 1 (by rfl) ⟨1025198, by rfl⟩ : syracuseStep 1366931 = 2050397) B2050397
theorem B1366947 : Blo 1366502 1366947 := bstep (se 1 (by rfl) ⟨1025210, by rfl⟩ : syracuseStep 1366947 = 2050421) B2050421
theorem B1366963 : Blo 1366502 1366963 := bstep (se 1 (by rfl) ⟨1025222, by rfl⟩ : syracuseStep 1366963 = 2050445) B2050445
theorem B1538995 : Blo 1366502 1538995 := bstep (se 1 (by rfl) ⟨1154246, by rfl⟩ : syracuseStep 1538995 = 2308493) B2308493
theorem B1366979 : Blo 1366502 1366979 := bstep (se 1 (by rfl) ⟨1025234, by rfl⟩ : syracuseStep 1366979 = 2050469) B2050469
theorem B1366995 : Blo 1366502 1366995 := bstep (se 1 (by rfl) ⟨1025246, by rfl⟩ : syracuseStep 1366995 = 2050493) B2050493
theorem B1367011 : Blo 1366502 1367011 := bstep (se 1 (by rfl) ⟨1025258, by rfl⟩ : syracuseStep 1367011 = 2050517) B2050517
theorem B1367027 : Blo 1366502 1367027 := bstep (se 1 (by rfl) ⟨1025270, by rfl⟩ : syracuseStep 1367027 = 2050541) B2050541
theorem B2309107 : Blo 1366502 2309107 := bstep (se 1 (by rfl) ⟨1731830, by rfl⟩ : syracuseStep 2309107 = 3463661) B3463661
theorem B1367043 : Blo 1366502 1367043 := bstep (se 1 (by rfl) ⟨1025282, by rfl⟩ : syracuseStep 1367043 = 2050565) B2050565
theorem B1367059 : Blo 1366502 1367059 := bstep (se 1 (by rfl) ⟨1025294, by rfl⟩ : syracuseStep 1367059 = 2050589) B2050589
theorem B1367075 : Blo 1366502 1367075 := bstep (se 1 (by rfl) ⟨1025306, by rfl⟩ : syracuseStep 1367075 = 2050613) B2050613
theorem B1367091 : Blo 1366502 1367091 := bstep (se 1 (by rfl) ⟨1025318, by rfl⟩ : syracuseStep 1367091 = 2050637) B2050637
theorem B1367107 : Blo 1366502 1367107 := bstep (se 1 (by rfl) ⟨1025330, by rfl⟩ : syracuseStep 1367107 = 2050661) B2050661
theorem B1539139 : Blo 1366502 1539139 := bstep (se 1 (by rfl) ⟨1154354, by rfl⟩ : syracuseStep 1539139 = 2308709) B2308709
theorem B5545037 : Blo 1366502 5545037 := bstep (se 3 (by rfl) ⟨1039694, by rfl⟩ : syracuseStep 5545037 = 2079389) B2079389
theorem B1367123 : Blo 1366502 1367123 := bstep (se 1 (by rfl) ⟨1025342, by rfl⟩ : syracuseStep 1367123 = 2050685) B2050685
theorem B1367139 : Blo 1366502 1367139 := bstep (se 1 (by rfl) ⟨1025354, by rfl⟩ : syracuseStep 1367139 = 2050709) B2050709
theorem B1367155 : Blo 1366502 1367155 := bstep (se 1 (by rfl) ⟨1025366, by rfl⟩ : syracuseStep 1367155 = 2050733) B2050733
theorem B2309249 : Blo 1366502 2309249 := bstep (se 2 (by rfl) ⟨865968, by rfl⟩ : syracuseStep 2309249 = 1731937) B1731937
theorem B1367171 : Blo 1366502 1367171 := bstep (se 1 (by rfl) ⟨1025378, by rfl⟩ : syracuseStep 1367171 = 2050757) B2050757
theorem B1367187 : Blo 1366502 1367187 := bstep (se 1 (by rfl) ⟨1025390, by rfl⟩ : syracuseStep 1367187 = 2050781) B2050781
theorem B1367203 : Blo 1366502 1367203 := bstep (se 1 (by rfl) ⟨1025402, by rfl⟩ : syracuseStep 1367203 = 2050805) B2050805
theorem B1367219 : Blo 1366502 1367219 := bstep (se 1 (by rfl) ⟨1025414, by rfl⟩ : syracuseStep 1367219 = 2050829) B2050829
theorem B1367235 : Blo 1366502 1367235 := bstep (se 1 (by rfl) ⟨1025426, by rfl⟩ : syracuseStep 1367235 = 2050853) B2050853
theorem B1367251 : Blo 1366502 1367251 := bstep (se 1 (by rfl) ⟨1025438, by rfl⟩ : syracuseStep 1367251 = 2050877) B2050877
theorem B1539283 : Blo 1366502 1539283 := bstep (se 1 (by rfl) ⟨1154462, by rfl⟩ : syracuseStep 1539283 = 2308925) B2308925
theorem B1367267 : Blo 1366502 1367267 := bstep (se 1 (by rfl) ⟨1025450, by rfl⟩ : syracuseStep 1367267 = 2050901) B2050901
theorem B11681009 : Blo 1366502 11681009 := bstep (se 2 (by rfl) ⟨4380378, by rfl⟩ : syracuseStep 11681009 = 8760757) B8760757
theorem B1367283 : Blo 1366502 1367283 := bstep (se 1 (by rfl) ⟨1025462, by rfl⟩ : syracuseStep 1367283 = 2050925) B2050925
theorem B1367299 : Blo 1366502 1367299 := bstep (se 1 (by rfl) ⟨1025474, by rfl⟩ : syracuseStep 1367299 = 2050949) B2050949
theorem B1367315 : Blo 1366502 1367315 := bstep (se 1 (by rfl) ⟨1025486, by rfl⟩ : syracuseStep 1367315 = 2050973) B2050973
theorem B1367331 : Blo 1366502 1367331 := bstep (se 1 (by rfl) ⟨1025498, by rfl⟩ : syracuseStep 1367331 = 2050997) B2050997
theorem B1367347 : Blo 1366502 1367347 := bstep (se 1 (by rfl) ⟨1025510, by rfl⟩ : syracuseStep 1367347 = 2051021) B2051021
theorem B1367363 : Blo 1366502 1367363 := bstep (se 1 (by rfl) ⟨1025522, by rfl⟩ : syracuseStep 1367363 = 2051045) B2051045
theorem B1367379 : Blo 1366502 1367379 := bstep (se 1 (by rfl) ⟨1025534, by rfl⟩ : syracuseStep 1367379 = 2051069) B2051069
theorem B1367395 : Blo 1366502 1367395 := bstep (se 1 (by rfl) ⟨1025546, by rfl⟩ : syracuseStep 1367395 = 2051093) B2051093
theorem B1539427 : Blo 1366502 1539427 := bstep (se 1 (by rfl) ⟨1154570, by rfl⟩ : syracuseStep 1539427 = 2309141) B2309141
theorem B1367411 : Blo 1366502 1367411 := bstep (se 1 (by rfl) ⟨1025558, by rfl⟩ : syracuseStep 1367411 = 2051117) B2051117
theorem B1367427 : Blo 1366502 1367427 := bstep (se 1 (by rfl) ⟨1025570, by rfl⟩ : syracuseStep 1367427 = 2051141) B2051141
theorem B1367443 : Blo 1366502 1367443 := bstep (se 1 (by rfl) ⟨1025582, by rfl⟩ : syracuseStep 1367443 = 2051165) B2051165
theorem B1367459 : Blo 1366502 1367459 := bstep (se 1 (by rfl) ⟨1025594, by rfl⟩ : syracuseStep 1367459 = 2051189) B2051189
theorem B8756657 : Blo 1366502 8756657 := bstep (se 2 (by rfl) ⟨3283746, by rfl⟩ : syracuseStep 8756657 = 6567493) B6567493
theorem B1367475 : Blo 1366502 1367475 := bstep (se 1 (by rfl) ⟨1025606, by rfl⟩ : syracuseStep 1367475 = 2051213) B2051213
theorem B1367491 : Blo 1366502 1367491 := bstep (se 1 (by rfl) ⟨1025618, by rfl⟩ : syracuseStep 1367491 = 2051237) B2051237
theorem B1367507 : Blo 1366502 1367507 := bstep (se 1 (by rfl) ⟨1025630, by rfl⟩ : syracuseStep 1367507 = 2051261) B2051261
theorem B1367523 : Blo 1366502 1367523 := bstep (se 1 (by rfl) ⟨1025642, by rfl⟩ : syracuseStep 1367523 = 2051285) B2051285
theorem B5840369 : Blo 1366502 5840369 := bstep (se 2 (by rfl) ⟨2190138, by rfl⟩ : syracuseStep 5840369 = 4380277) B4380277
theorem B1367539 : Blo 1366502 1367539 := bstep (se 1 (by rfl) ⟨1025654, by rfl⟩ : syracuseStep 1367539 = 2051309) B2051309
theorem B1367555 : Blo 1366502 1367555 := bstep (se 1 (by rfl) ⟨1025666, by rfl⟩ : syracuseStep 1367555 = 2051333) B2051333
theorem B4382225 : Blo 1366502 4382225 := bstep (se 2 (by rfl) ⟨1643334, by rfl⟩ : syracuseStep 4382225 = 3286669) B3286669
theorem B1367571 : Blo 1366502 1367571 := bstep (se 1 (by rfl) ⟨1025678, by rfl⟩ : syracuseStep 1367571 = 2051357) B2051357
theorem B2080289 : Blo 1366502 2080289 := bstep (se 2 (by rfl) ⟨780108, by rfl⟩ : syracuseStep 2080289 = 1560217) B1560217
theorem B1367587 : Blo 1366502 1367587 := bstep (se 1 (by rfl) ⟨1025690, by rfl⟩ : syracuseStep 1367587 = 2051381) B2051381
theorem B2596387 : Blo 1366502 2596387 := bstep (se 1 (by rfl) ⟨1947290, by rfl⟩ : syracuseStep 2596387 = 3894581) B3894581
theorem B1367603 : Blo 1366502 1367603 := bstep (se 1 (by rfl) ⟨1025702, by rfl⟩ : syracuseStep 1367603 = 2051405) B2051405
theorem B66534965 : Blo 1366502 66534965 := bstep (se 5 (by rfl) ⟨3118826, by rfl⟩ : syracuseStep 66534965 = 6237653) B6237653
theorem B24952373 : Blo 1366502 24952373 := bstep (se 5 (by rfl) ⟨1169642, by rfl⟩ : syracuseStep 24952373 = 2339285) B2339285
theorem B1367619 : Blo 1366502 1367619 := bstep (se 1 (by rfl) ⟨1025714, by rfl⟩ : syracuseStep 1367619 = 2051429) B2051429
theorem B2080337 : Blo 1366502 2080337 := bstep (se 2 (by rfl) ⟨780126, by rfl⟩ : syracuseStep 2080337 = 1560253) B1560253
theorem B1367635 : Blo 1366502 1367635 := bstep (se 1 (by rfl) ⟨1025726, by rfl⟩ : syracuseStep 1367635 = 2051453) B2051453
theorem B1367651 : Blo 1366502 1367651 := bstep (se 1 (by rfl) ⟨1025738, by rfl⟩ : syracuseStep 1367651 = 2051477) B2051477
theorem B1367667 : Blo 1366502 1367667 := bstep (se 1 (by rfl) ⟨1025750, by rfl⟩ : syracuseStep 1367667 = 2051501) B2051501
theorem B1367683 : Blo 1366502 1367683 := bstep (se 1 (by rfl) ⟨1025762, by rfl⟩ : syracuseStep 1367683 = 2051525) B2051525
theorem B1367699 : Blo 1366502 1367699 := bstep (se 1 (by rfl) ⟨1025774, by rfl⟩ : syracuseStep 1367699 = 2051549) B2051549
theorem B1367715 : Blo 1366502 1367715 := bstep (se 1 (by rfl) ⟨1025786, by rfl⟩ : syracuseStep 1367715 = 2051573) B2051573
theorem B1367731 : Blo 1366502 1367731 := bstep (se 1 (by rfl) ⟨1025798, by rfl⟩ : syracuseStep 1367731 = 2051597) B2051597
theorem B1367747 : Blo 1366502 1367747 := bstep (se 1 (by rfl) ⟨1025810, by rfl⟩ : syracuseStep 1367747 = 2051621) B2051621
theorem B1367763 : Blo 1366502 1367763 := bstep (se 1 (by rfl) ⟨1025822, by rfl⟩ : syracuseStep 1367763 = 2051645) B2051645
theorem B1367779 : Blo 1366502 1367779 := bstep (se 1 (by rfl) ⟨1025834, by rfl⟩ : syracuseStep 1367779 = 2051669) B2051669
theorem B6840049 : Blo 1366502 6840049 := bstep (se 2 (by rfl) ⟨2565018, by rfl⟩ : syracuseStep 6840049 = 5130037) B5130037
theorem B1367795 : Blo 1366502 1367795 := bstep (se 1 (by rfl) ⟨1025846, by rfl⟩ : syracuseStep 1367795 = 2051693) B2051693
theorem B1367811 : Blo 1366502 1367811 := bstep (se 1 (by rfl) ⟨1025858, by rfl⟩ : syracuseStep 1367811 = 2051717) B2051717
theorem B6569741 : Blo 1366502 6569741 := bstep (se 3 (by rfl) ⟨1231826, by rfl⟩ : syracuseStep 6569741 = 2463653) B2463653
theorem B1367827 : Blo 1366502 1367827 := bstep (se 1 (by rfl) ⟨1025870, by rfl⟩ : syracuseStep 1367827 = 2051741) B2051741
theorem B1367843 : Blo 1366502 1367843 := bstep (se 1 (by rfl) ⟨1025882, by rfl⟩ : syracuseStep 1367843 = 2051765) B2051765
theorem B1367859 : Blo 1366502 1367859 := bstep (se 1 (by rfl) ⟨1025894, by rfl⟩ : syracuseStep 1367859 = 2051789) B2051789
theorem B1367875 : Blo 1366502 1367875 := bstep (se 1 (by rfl) ⟨1025906, by rfl⟩ : syracuseStep 1367875 = 2051813) B2051813
theorem B1367891 : Blo 1366502 1367891 := bstep (se 1 (by rfl) ⟨1025918, by rfl⟩ : syracuseStep 1367891 = 2051837) B2051837
theorem B1367907 : Blo 1366502 1367907 := bstep (se 1 (by rfl) ⟨1025930, by rfl⟩ : syracuseStep 1367907 = 2051861) B2051861
theorem B6922097 : Blo 1366502 6922097 := bstep (se 2 (by rfl) ⟨2595786, by rfl⟩ : syracuseStep 6922097 = 5191573) B5191573
theorem B1367923 : Blo 1366502 1367923 := bstep (se 1 (by rfl) ⟨1025942, by rfl⟩ : syracuseStep 1367923 = 2051885) B2051885
theorem B1367939 : Blo 1366502 1367939 := bstep (se 1 (by rfl) ⟨1025954, by rfl⟩ : syracuseStep 1367939 = 2051909) B2051909
theorem B1367955 : Blo 1366502 1367955 := bstep (se 1 (by rfl) ⟨1025966, by rfl⟩ : syracuseStep 1367955 = 2051933) B2051933
theorem B1367971 : Blo 1366502 1367971 := bstep (se 1 (by rfl) ⟨1025978, by rfl⟩ : syracuseStep 1367971 = 2051957) B2051957
theorem B1367987 : Blo 1366502 1367987 := bstep (se 1 (by rfl) ⟨1025990, by rfl⟩ : syracuseStep 1367987 = 2051981) B2051981
theorem B1368003 : Blo 1366502 1368003 := bstep (se 1 (by rfl) ⟨1026002, by rfl⟩ : syracuseStep 1368003 = 2052005) B2052005
theorem B1368019 : Blo 1366502 1368019 := bstep (se 1 (by rfl) ⟨1026014, by rfl⟩ : syracuseStep 1368019 = 2052029) B2052029
theorem B2596835 : Blo 1366502 2596835 := bstep (se 1 (by rfl) ⟨1947626, by rfl⟩ : syracuseStep 2596835 = 3895253) B3895253
theorem B1368035 : Blo 1366502 1368035 := bstep (se 1 (by rfl) ⟨1026026, by rfl⟩ : syracuseStep 1368035 = 2052053) B2052053
theorem B3284977 : Blo 1366502 3284977 := bstep (se 2 (by rfl) ⟨1231866, by rfl⟩ : syracuseStep 3284977 = 2463733) B2463733
theorem B1368051 : Blo 1366502 1368051 := bstep (se 1 (by rfl) ⟨1026038, by rfl⟩ : syracuseStep 1368051 = 2052077) B2052077
theorem B2629633 : Blo 1366502 2629633 := bstep (se 2 (by rfl) ⟨986112, by rfl⟩ : syracuseStep 2629633 = 1972225) B1972225
theorem B1368075 : Blo 1366502 1368075 := bstep (se 1 (by rfl) ⟨1026056, by rfl⟩ : syracuseStep 1368075 = 2052113) B2052113
theorem B1368087 : Blo 1366502 1368087 := bstep (se 1 (by rfl) ⟨1026065, by rfl⟩ : syracuseStep 1368087 = 2052131) B2052131
theorem B1368107 : Blo 1366502 1368107 := bstep (se 1 (by rfl) ⟨1026080, by rfl⟩ : syracuseStep 1368107 = 2052161) B2052161
theorem B1368119 : Blo 1366502 1368119 := bstep (se 1 (by rfl) ⟨1026089, by rfl⟩ : syracuseStep 1368119 = 2052179) B2052179
theorem B1368139 : Blo 1366502 1368139 := bstep (se 1 (by rfl) ⟨1026104, by rfl⟩ : syracuseStep 1368139 = 2052209) B2052209
theorem B1368151 : Blo 1366502 1368151 := bstep (se 1 (by rfl) ⟨1026113, by rfl⟩ : syracuseStep 1368151 = 2052227) B2052227
theorem B17514589 : Blo 1366502 17514589 := bstep (se 3 (by rfl) ⟨3283985, by rfl⟩ : syracuseStep 17514589 = 6567971) B6567971
theorem B5193821 : Blo 1366502 5193821 := bstep (se 3 (by rfl) ⟨973841, by rfl⟩ : syracuseStep 5193821 = 1947683) B1947683
theorem B1368171 : Blo 1366502 1368171 := bstep (se 1 (by rfl) ⟨1026128, by rfl⟩ : syracuseStep 1368171 = 2052257) B2052257
theorem B1368183 : Blo 1366502 1368183 := bstep (se 1 (by rfl) ⟨1026137, by rfl⟩ : syracuseStep 1368183 = 2052275) B2052275
theorem B1368203 : Blo 1366502 1368203 := bstep (se 1 (by rfl) ⟨1026152, by rfl⟩ : syracuseStep 1368203 = 2052305) B2052305
theorem B4612247 : Blo 1366502 4612247 := bstep (se 1 (by rfl) ⟨3459185, by rfl⟩ : syracuseStep 4612247 = 6918371) B6918371
theorem B1368215 : Blo 1366502 1368215 := bstep (se 1 (by rfl) ⟨1026161, by rfl⟩ : syracuseStep 1368215 = 2052323) B2052323
theorem B2597017 : Blo 1366502 2597017 := bstep (se 2 (by rfl) ⟨973881, by rfl⟩ : syracuseStep 2597017 = 1947763) B1947763
theorem B1368235 : Blo 1366502 1368235 := bstep (se 1 (by rfl) ⟨1026176, by rfl⟩ : syracuseStep 1368235 = 2052353) B2052353
theorem B1368247 : Blo 1366502 1368247 := bstep (se 1 (by rfl) ⟨1026185, by rfl⟩ : syracuseStep 1368247 = 2052371) B2052371
theorem B1368267 : Blo 1366502 1368267 := bstep (se 1 (by rfl) ⟨1026200, by rfl⟩ : syracuseStep 1368267 = 2052401) B2052401
theorem B1368279 : Blo 1366502 1368279 := bstep (se 1 (by rfl) ⟨1026209, by rfl⟩ : syracuseStep 1368279 = 2052419) B2052419
theorem B1368299 : Blo 1366502 1368299 := bstep (se 1 (by rfl) ⟨1026224, by rfl⟩ : syracuseStep 1368299 = 2052449) B2052449
theorem B1368311 : Blo 1366502 1368311 := bstep (se 1 (by rfl) ⟨1026233, by rfl⟩ : syracuseStep 1368311 = 2052467) B2052467
theorem B6234371 : Blo 1366502 6234371 := bstep (se 1 (by rfl) ⟨4675778, by rfl⟩ : syracuseStep 6234371 = 9351557) B9351557
theorem B1368331 : Blo 1366502 1368331 := bstep (se 1 (by rfl) ⟨1026248, by rfl⟩ : syracuseStep 1368331 = 2052497) B2052497
theorem B1368343 : Blo 1366502 1368343 := bstep (se 1 (by rfl) ⟨1026257, by rfl⟩ : syracuseStep 1368343 = 2052515) B2052515
theorem B1368363 : Blo 1366502 1368363 := bstep (se 1 (by rfl) ⟨1026272, by rfl⟩ : syracuseStep 1368363 = 2052545) B2052545
theorem B4931891 : Blo 1366502 4931891 := bstep (se 1 (by rfl) ⟨3698918, by rfl⟩ : syracuseStep 4931891 = 7397837) B7397837
theorem B1368375 : Blo 1366502 1368375 := bstep (se 1 (by rfl) ⟨1026281, by rfl⟩ : syracuseStep 1368375 = 2052563) B2052563
theorem B1368395 : Blo 1366502 1368395 := bstep (se 1 (by rfl) ⟨1026296, by rfl⟩ : syracuseStep 1368395 = 2052593) B2052593
theorem B1368407 : Blo 1366502 1368407 := bstep (se 1 (by rfl) ⟨1026305, by rfl⟩ : syracuseStep 1368407 = 2052611) B2052611
theorem B7020893 : Blo 1366502 7020893 := bstep (se 3 (by rfl) ⟨1316417, by rfl⟩ : syracuseStep 7020893 = 2632835) B2632835
theorem B1368427 : Blo 1366502 1368427 := bstep (se 1 (by rfl) ⟨1026320, by rfl⟩ : syracuseStep 1368427 = 2052641) B2052641
theorem B1368439 : Blo 1366502 1368439 := bstep (se 1 (by rfl) ⟨1026329, by rfl⟩ : syracuseStep 1368439 = 2052659) B2052659
theorem B1368459 : Blo 1366502 1368459 := bstep (se 1 (by rfl) ⟨1026344, by rfl⟩ : syracuseStep 1368459 = 2052689) B2052689
theorem B1368471 : Blo 1366502 1368471 := bstep (se 1 (by rfl) ⟨1026353, by rfl⟩ : syracuseStep 1368471 = 2052707) B2052707
theorem B1368491 : Blo 1366502 1368491 := bstep (se 1 (by rfl) ⟨1026368, by rfl⟩ : syracuseStep 1368491 = 2052737) B2052737
theorem B8004113 : Blo 1366502 8004113 := bstep (se 2 (by rfl) ⟨3001542, by rfl⟩ : syracuseStep 8004113 = 6003085) B6003085
theorem B9855533 : Blo 1366502 9855533 := bstep (se 3 (by rfl) ⟨1847912, by rfl⟩ : syracuseStep 9855533 = 3695825) B3695825
theorem B3285593 : Blo 1366502 3285593 := bstep (se 2 (by rfl) ⟨1232097, by rfl⟩ : syracuseStep 3285593 = 2464195) B2464195
theorem B4612787 : Blo 1366502 4612787 := bstep (se 1 (by rfl) ⟨3459590, by rfl⟩ : syracuseStep 4612787 = 6919181) B6919181
theorem B2597579 : Blo 1366502 2597579 := bstep (se 1 (by rfl) ⟨1948184, by rfl⟩ : syracuseStep 2597579 = 3896369) B3896369
theorem B28074701 : Blo 1366502 28074701 := bstep (se 3 (by rfl) ⟨5264006, by rfl⟩ : syracuseStep 28074701 = 10528013) B10528013
theorem B7791461 : Blo 1366502 7791461 := bstep (se 4 (by rfl) ⟨730449, by rfl⟩ : syracuseStep 7791461 = 1460899) B1460899
theorem B2597761 : Blo 1366502 2597761 := bstep (se 2 (by rfl) ⟨974160, by rfl⟩ : syracuseStep 2597761 = 1948321) B1948321
theorem B4613057 : Blo 1366502 4613057 := bstep (se 2 (by rfl) ⟨1729896, by rfl⟩ : syracuseStep 4613057 = 3459793) B3459793
theorem B11093057 : Blo 1366502 11093057 := bstep (se 2 (by rfl) ⟨4159896, by rfl⟩ : syracuseStep 11093057 = 8319793) B8319793
theorem B3892313 : Blo 1366502 3892313 := bstep (se 2 (by rfl) ⟨1459617, by rfl⟩ : syracuseStep 3892313 = 2919235) B2919235
theorem B22176899 : Blo 1366502 22176899 := bstep (se 1 (by rfl) ⟨16632674, by rfl⟩ : syracuseStep 22176899 = 33265349) B33265349
theorem B5547437 : Blo 1366502 5547437 := bstep (se 3 (by rfl) ⟨1040144, by rfl⟩ : syracuseStep 5547437 = 2080289) B2080289
theorem B7783897 : Blo 1366502 7783897 := bstep (se 2 (by rfl) ⟨2918961, by rfl⟩ : syracuseStep 7783897 = 5837923) B5837923
theorem B4613597 : Blo 1366502 4613597 := bstep (se 3 (by rfl) ⟨865049, by rfl⟩ : syracuseStep 4613597 = 1730099) B1730099
theorem B7792145 : Blo 1366502 7792145 := bstep (se 2 (by rfl) ⟨2922054, by rfl⟩ : syracuseStep 7792145 = 5844109) B5844109
theorem B5547565 : Blo 1366502 5547565 := bstep (se 3 (by rfl) ⟨1040168, by rfl⟩ : syracuseStep 5547565 = 2080337) B2080337
theorem B1459819 : Blo 1366502 1459819 := bstep (se 1 (by rfl) ⟨1094864, by rfl⟩ : syracuseStep 1459819 = 2189729) B2189729
theorem B1730251 : Blo 1366502 1730251 := bstep (se 1 (by rfl) ⟨1297688, by rfl⟩ : syracuseStep 1730251 = 2595377) B2595377
theorem B2049803 : Blo 1366502 2049803 := bstep (se 1 (by rfl) ⟨1537352, by rfl⟩ : syracuseStep 2049803 = 3074705) B3074705
theorem B2049815 : Blo 1366502 2049815 := bstep (se 1 (by rfl) ⟨1537361, by rfl⟩ : syracuseStep 2049815 = 3074723) B3074723
theorem B2189081 : Blo 1366502 2189081 := bstep (se 2 (by rfl) ⟨820905, by rfl⟩ : syracuseStep 2189081 = 1641811) B1641811
theorem B5547827 : Blo 1366502 5547827 := bstep (se 1 (by rfl) ⟨4160870, by rfl⟩ : syracuseStep 5547827 = 8321741) B8321741
theorem B2049881 : Blo 1366502 2049881 := bstep (se 2 (by rfl) ⟨768705, by rfl⟩ : syracuseStep 2049881 = 1537411) B1537411
theorem B50546531 : Blo 1366502 50546531 := bstep (se 1 (by rfl) ⟨37909898, by rfl⟩ : syracuseStep 50546531 = 75819797) B75819797
theorem B8759141 : Blo 1366502 8759141 := bstep (se 4 (by rfl) ⟨821169, by rfl⟩ : syracuseStep 8759141 = 1642339) B1642339
theorem B2049995 : Blo 1366502 2049995 := bstep (se 1 (by rfl) ⟨1537496, by rfl⟩ : syracuseStep 2049995 = 3074993) B3074993
theorem B2050007 : Blo 1366502 2050007 := bstep (se 1 (by rfl) ⟨1537505, by rfl⟩ : syracuseStep 2050007 = 3075011) B3075011
theorem B3459095 : Blo 1366502 3459095 := bstep (se 1 (by rfl) ⟨2594321, by rfl⟩ : syracuseStep 3459095 = 5188643) B5188643
theorem B2050073 : Blo 1366502 2050073 := bstep (se 2 (by rfl) ⟨768777, by rfl⟩ : syracuseStep 2050073 = 1537555) B1537555
theorem B3696691 : Blo 1366502 3696691 := bstep (se 1 (by rfl) ⟨2772518, by rfl⟩ : syracuseStep 3696691 = 5545037) B5545037
theorem B85403717 : Blo 1366502 85403717 := bstep (se 4 (by rfl) ⟨8006598, by rfl⟩ : syracuseStep 85403717 = 16013197) B16013197
theorem B84199499 : Blo 1366502 84199499 := bstep (se 1 (by rfl) ⟨63149624, by rfl⟩ : syracuseStep 84199499 = 126299249) B126299249
theorem B2050187 : Blo 1366502 2050187 := bstep (se 1 (by rfl) ⟨1537640, by rfl⟩ : syracuseStep 2050187 = 3075281) B3075281
theorem B2050199 : Blo 1366502 2050199 := bstep (se 1 (by rfl) ⟨1537649, by rfl⟩ : syracuseStep 2050199 = 3075299) B3075299
theorem B5843117 : Blo 1366502 5843117 := bstep (se 3 (by rfl) ⟨1095584, by rfl⟩ : syracuseStep 5843117 = 2191169) B2191169
theorem B2050265 : Blo 1366502 2050265 := bstep (se 2 (by rfl) ⟨768849, by rfl⟩ : syracuseStep 2050265 = 1537699) B1537699
theorem B9120065 : Blo 1366502 9120065 := bstep (se 2 (by rfl) ⟨3420024, by rfl⟩ : syracuseStep 9120065 = 6840049) B6840049
theorem B2050379 : Blo 1366502 2050379 := bstep (se 1 (by rfl) ⟨1537784, by rfl⟩ : syracuseStep 2050379 = 3075569) B3075569
theorem B3893579 : Blo 1366502 3893579 := bstep (se 1 (by rfl) ⟨2920184, by rfl⟩ : syracuseStep 3893579 = 5840369) B5840369
theorem B2050391 : Blo 1366502 2050391 := bstep (se 1 (by rfl) ⟨1537793, by rfl⟩ : syracuseStep 2050391 = 3075587) B3075587
theorem B7784855 : Blo 1366502 7784855 := bstep (se 1 (by rfl) ⟨5838641, by rfl⟩ : syracuseStep 7784855 = 11677283) B11677283
theorem B2771351 : Blo 1366502 2771351 := bstep (se 1 (by rfl) ⟨2078513, by rfl⟩ : syracuseStep 2771351 = 4157027) B4157027
theorem B2050457 : Blo 1366502 2050457 := bstep (se 2 (by rfl) ⟨768921, by rfl⟩ : syracuseStep 2050457 = 1537843) B1537843
theorem B2050571 : Blo 1366502 2050571 := bstep (se 1 (by rfl) ⟨1537928, by rfl⟩ : syracuseStep 2050571 = 3075857) B3075857
theorem B2050583 : Blo 1366502 2050583 := bstep (se 1 (by rfl) ⟨1537937, by rfl⟩ : syracuseStep 2050583 = 3075875) B3075875
theorem B4614731 : Blo 1366502 4614731 := bstep (se 1 (by rfl) ⟨3461048, by rfl⟩ : syracuseStep 4614731 = 6922097) B6922097
theorem B2050649 : Blo 1366502 2050649 := bstep (se 2 (by rfl) ⟨768993, by rfl⟩ : syracuseStep 2050649 = 1537987) B1537987
theorem B1731223 : Blo 1366502 1731223 := bstep (se 1 (by rfl) ⟨1298417, by rfl⟩ : syracuseStep 1731223 = 2596835) B2596835
theorem B10390193 : Blo 1366502 10390193 := bstep (se 2 (by rfl) ⟨3896322, by rfl⟩ : syracuseStep 10390193 = 7792645) B7792645
theorem B2919091 : Blo 1366502 2919091 := bstep (se 1 (by rfl) ⟨2189318, by rfl⟩ : syracuseStep 2919091 = 4378637) B4378637
theorem B2050763 : Blo 1366502 2050763 := bstep (se 1 (by rfl) ⟨1538072, by rfl⟩ : syracuseStep 2050763 = 3076145) B3076145
theorem B2050775 : Blo 1366502 2050775 := bstep (se 1 (by rfl) ⟨1538081, by rfl⟩ : syracuseStep 2050775 = 3076163) B3076163
theorem B3074777 : Blo 1366502 3074777 := bstep (se 2 (by rfl) ⟨1153041, by rfl⟩ : syracuseStep 3074777 = 2306083) B2306083
theorem B15575813 : Blo 1366502 15575813 := bstep (se 4 (by rfl) ⟨1460232, by rfl⟩ : syracuseStep 15575813 = 2920465) B2920465
theorem B2050841 : Blo 1366502 2050841 := bstep (se 2 (by rfl) ⟨769065, by rfl⟩ : syracuseStep 2050841 = 1538131) B1538131
theorem B3074867 : Blo 1366502 3074867 := bstep (se 1 (by rfl) ⟨2306150, by rfl⟩ : syracuseStep 3074867 = 4612301) B4612301
theorem B3459905 : Blo 1366502 3459905 := bstep (se 2 (by rfl) ⟨1297464, by rfl⟩ : syracuseStep 3459905 = 2594929) B2594929
theorem B170797889 : Blo 1366502 170797889 := bstep (se 2 (by rfl) ⟨64049208, by rfl⟩ : syracuseStep 170797889 = 128098417) B128098417
theorem B3074903 : Blo 1366502 3074903 := bstep (se 1 (by rfl) ⟨2306177, by rfl⟩ : syracuseStep 3074903 = 4612355) B4612355
theorem B4615001 : Blo 1366502 4615001 := bstep (se 2 (by rfl) ⟨1730625, by rfl⟩ : syracuseStep 4615001 = 3461251) B3461251
theorem B5843801 : Blo 1366502 5843801 := bstep (se 2 (by rfl) ⟨2191425, by rfl⟩ : syracuseStep 5843801 = 4382851) B4382851
theorem B5188445 : Blo 1366502 5188445 := bstep (se 3 (by rfl) ⟨972833, by rfl⟩ : syracuseStep 5188445 = 1945667) B1945667
theorem B2050955 : Blo 1366502 2050955 := bstep (se 1 (by rfl) ⟨1538216, by rfl⟩ : syracuseStep 2050955 = 3076433) B3076433
theorem B2050967 : Blo 1366502 2050967 := bstep (se 1 (by rfl) ⟨1538225, by rfl⟩ : syracuseStep 2050967 = 3076451) B3076451
theorem B284322757 : Blo 1366502 284322757 := bstep (se 4 (by rfl) ⟨26655258, by rfl⟩ : syracuseStep 284322757 = 53310517) B53310517
theorem B2051033 : Blo 1366502 2051033 := bstep (se 2 (by rfl) ⟨769137, by rfl⟩ : syracuseStep 2051033 = 1538275) B1538275
theorem B4156381 : Blo 1366502 4156381 := bstep (se 3 (by rfl) ⟨779321, by rfl⟩ : syracuseStep 4156381 = 1558643) B1558643
theorem B3075083 : Blo 1366502 3075083 := bstep (se 1 (by rfl) ⟨2306312, by rfl⟩ : syracuseStep 3075083 = 4612625) B4612625
theorem B3075137 : Blo 1366502 3075137 := bstep (se 2 (by rfl) ⟨1153176, by rfl⟩ : syracuseStep 3075137 = 2306353) B2306353
theorem B2051147 : Blo 1366502 2051147 := bstep (se 1 (by rfl) ⟨1538360, by rfl⟩ : syracuseStep 2051147 = 3076721) B3076721
theorem B2051159 : Blo 1366502 2051159 := bstep (se 1 (by rfl) ⟨1538369, by rfl⟩ : syracuseStep 2051159 = 3076739) B3076739
theorem B9350245 : Blo 1366502 9350245 := bstep (se 4 (by rfl) ⟨876585, by rfl⟩ : syracuseStep 9350245 = 1753171) B1753171
theorem B10390679 : Blo 1366502 10390679 := bstep (se 1 (by rfl) ⟨7793009, by rfl⟩ : syracuseStep 10390679 = 15586019) B15586019
theorem B2919577 : Blo 1366502 2919577 := bstep (se 2 (by rfl) ⟨1094841, by rfl⟩ : syracuseStep 2919577 = 2189683) B2189683
theorem B2051225 : Blo 1366502 2051225 := bstep (se 2 (by rfl) ⟨769209, by rfl⟩ : syracuseStep 2051225 = 1538419) B1538419
theorem B2051339 : Blo 1366502 2051339 := bstep (se 1 (by rfl) ⟨1538504, by rfl⟩ : syracuseStep 2051339 = 3077009) B3077009
theorem B2051351 : Blo 1366502 2051351 := bstep (se 1 (by rfl) ⟨1538513, by rfl⟩ : syracuseStep 2051351 = 3077027) B3077027
theorem B3075353 : Blo 1366502 3075353 := bstep (se 2 (by rfl) ⟨1153257, by rfl⟩ : syracuseStep 3075353 = 2306515) B2306515
theorem B5541209 : Blo 1366502 5541209 := bstep (se 2 (by rfl) ⟨2077953, by rfl⟩ : syracuseStep 5541209 = 4155907) B4155907
theorem B3460441 : Blo 1366502 3460441 := bstep (se 2 (by rfl) ⟨1297665, by rfl⟩ : syracuseStep 3460441 = 2595331) B2595331
theorem B2051417 : Blo 1366502 2051417 := bstep (se 2 (by rfl) ⟨769281, by rfl⟩ : syracuseStep 2051417 = 1538563) B1538563
theorem B6925661 : Blo 1366502 6925661 := bstep (se 3 (by rfl) ⟨1298561, by rfl⟩ : syracuseStep 6925661 = 2597123) B2597123
theorem B3075443 : Blo 1366502 3075443 := bstep (se 1 (by rfl) ⟨2306582, by rfl⟩ : syracuseStep 3075443 = 4613165) B4613165
theorem B3075479 : Blo 1366502 3075479 := bstep (se 1 (by rfl) ⟨2306609, by rfl⟩ : syracuseStep 3075479 = 4613219) B4613219
theorem B2051531 : Blo 1366502 2051531 := bstep (se 1 (by rfl) ⟨1538648, by rfl⟩ : syracuseStep 2051531 = 3077297) B3077297
theorem B2051543 : Blo 1366502 2051543 := bstep (se 1 (by rfl) ⟨1538657, by rfl⟩ : syracuseStep 2051543 = 3077315) B3077315
theorem B9358865 : Blo 1366502 9358865 := bstep (se 2 (by rfl) ⟨3509574, by rfl⟩ : syracuseStep 9358865 = 7019149) B7019149
theorem B5189143 : Blo 1366502 5189143 := bstep (se 1 (by rfl) ⟨3891857, by rfl⟩ : syracuseStep 5189143 = 7783715) B7783715
theorem B4615703 : Blo 1366502 4615703 := bstep (se 1 (by rfl) ⟨3461777, by rfl⟩ : syracuseStep 4615703 = 6923555) B6923555
theorem B2051609 : Blo 1366502 2051609 := bstep (se 2 (by rfl) ⟨769353, by rfl⟩ : syracuseStep 2051609 = 1538707) B1538707
theorem B4378187 : Blo 1366502 4378187 := bstep (se 1 (by rfl) ⟨3283640, by rfl⟩ : syracuseStep 4378187 = 6567281) B6567281
theorem B3075659 : Blo 1366502 3075659 := bstep (se 1 (by rfl) ⟨2306744, by rfl⟩ : syracuseStep 3075659 = 4613489) B4613489
theorem B3075713 : Blo 1366502 3075713 := bstep (se 2 (by rfl) ⟨1153392, by rfl⟩ : syracuseStep 3075713 = 2306785) B2306785
theorem B2051723 : Blo 1366502 2051723 := bstep (se 1 (by rfl) ⟨1538792, by rfl⟩ : syracuseStep 2051723 = 3077585) B3077585
theorem B2051735 : Blo 1366502 2051735 := bstep (se 1 (by rfl) ⟨1538801, by rfl⟩ : syracuseStep 2051735 = 3077603) B3077603
theorem B3698369 : Blo 1366502 3698369 := bstep (se 2 (by rfl) ⟨1386888, by rfl⟩ : syracuseStep 3698369 = 2773777) B2773777
theorem B2051801 : Blo 1366502 2051801 := bstep (se 2 (by rfl) ⟨769425, by rfl⟩ : syracuseStep 2051801 = 1538851) B1538851
theorem B49876721 : Blo 1366502 49876721 := bstep (se 2 (by rfl) ⟨18703770, by rfl⟩ : syracuseStep 49876721 = 37407541) B37407541
theorem B7999249 : Blo 1366502 7999249 := bstep (se 2 (by rfl) ⟨2999718, by rfl⟩ : syracuseStep 7999249 = 5999437) B5999437
theorem B4927277 : Blo 1366502 4927277 := bstep (se 3 (by rfl) ⟨923864, by rfl⟩ : syracuseStep 4927277 = 1847729) B1847729
theorem B2051915 : Blo 1366502 2051915 := bstep (se 1 (by rfl) ⟨1538936, by rfl⟩ : syracuseStep 2051915 = 3077873) B3077873
theorem B1560395 : Blo 1366502 1560395 := bstep (se 1 (by rfl) ⟨1170296, by rfl⟩ : syracuseStep 1560395 = 2340593) B2340593
theorem B2051927 : Blo 1366502 2051927 := bstep (se 1 (by rfl) ⟨1538945, by rfl⟩ : syracuseStep 2051927 = 3077891) B3077891
theorem B3075929 : Blo 1366502 3075929 := bstep (se 2 (by rfl) ⟨1153473, by rfl⟩ : syracuseStep 3075929 = 2306947) B2306947
theorem B2051993 : Blo 1366502 2051993 := bstep (se 2 (by rfl) ⟨769497, by rfl⟩ : syracuseStep 2051993 = 1538995) B1538995
theorem B3076019 : Blo 1366502 3076019 := bstep (se 1 (by rfl) ⟨2307014, by rfl⟩ : syracuseStep 3076019 = 4614029) B4614029
theorem B3076055 : Blo 1366502 3076055 := bstep (se 1 (by rfl) ⟨2307041, by rfl⟩ : syracuseStep 3076055 = 4614083) B4614083
theorem B2306009 : Blo 1366502 2306009 := bstep (se 2 (by rfl) ⟨864753, by rfl⟩ : syracuseStep 2306009 = 1729507) B1729507
theorem B2052107 : Blo 1366502 2052107 := bstep (se 1 (by rfl) ⟨1539080, by rfl⟩ : syracuseStep 2052107 = 3078161) B3078161
theorem B2052119 : Blo 1366502 2052119 := bstep (se 1 (by rfl) ⟨1539089, by rfl⟩ : syracuseStep 2052119 = 3078179) B3078179
theorem B4616243 : Blo 1366502 4616243 := bstep (se 1 (by rfl) ⟨3462182, by rfl⟩ : syracuseStep 4616243 = 6924365) B6924365
theorem B6918209 : Blo 1366502 6918209 := bstep (se 2 (by rfl) ⟨2594328, by rfl⟩ : syracuseStep 6918209 = 5188657) B5188657
theorem B5845067 : Blo 1366502 5845067 := bstep (se 1 (by rfl) ⟨4383800, by rfl⟩ : syracuseStep 5845067 = 8767601) B8767601
theorem B2306137 : Blo 1366502 2306137 := bstep (se 2 (by rfl) ⟨864801, by rfl⟩ : syracuseStep 2306137 = 1729603) B1729603
theorem B2052185 : Blo 1366502 2052185 := bstep (se 2 (by rfl) ⟨769569, by rfl⟩ : syracuseStep 2052185 = 1539139) B1539139
theorem B3076235 : Blo 1366502 3076235 := bstep (se 1 (by rfl) ⟨2307176, by rfl⟩ : syracuseStep 3076235 = 4614353) B4614353
theorem B2961559 : Blo 1366502 2961559 := bstep (se 1 (by rfl) ⟨2221169, by rfl⟩ : syracuseStep 2961559 = 4442339) B4442339
theorem B6574259 : Blo 1366502 6574259 := bstep (se 1 (by rfl) ⟨4930694, by rfl⟩ : syracuseStep 6574259 = 9861389) B9861389
theorem B3076289 : Blo 1366502 3076289 := bstep (se 2 (by rfl) ⟨1153608, by rfl⟩ : syracuseStep 3076289 = 2307217) B2307217
theorem B2052299 : Blo 1366502 2052299 := bstep (se 1 (by rfl) ⟨1539224, by rfl⟩ : syracuseStep 2052299 = 3078449) B3078449
theorem B2052311 : Blo 1366502 2052311 := bstep (se 1 (by rfl) ⟨1539233, by rfl⟩ : syracuseStep 2052311 = 3078467) B3078467
theorem B2052377 : Blo 1366502 2052377 := bstep (se 2 (by rfl) ⟨769641, by rfl⟩ : syracuseStep 2052377 = 1539283) B1539283
theorem B5189933 : Blo 1366502 5189933 := bstep (se 3 (by rfl) ⟨973112, by rfl⟩ : syracuseStep 5189933 = 1946225) B1946225
theorem B4616513 : Blo 1366502 4616513 := bstep (se 2 (by rfl) ⟨1731192, by rfl⟩ : syracuseStep 4616513 = 3462385) B3462385
theorem B2052491 : Blo 1366502 2052491 := bstep (se 1 (by rfl) ⟨1539368, by rfl⟩ : syracuseStep 2052491 = 3078737) B3078737
theorem B2052503 : Blo 1366502 2052503 := bstep (se 1 (by rfl) ⟨1539377, by rfl⟩ : syracuseStep 2052503 = 3078755) B3078755
theorem B3076505 : Blo 1366502 3076505 := bstep (se 2 (by rfl) ⟨1153689, by rfl⟩ : syracuseStep 3076505 = 2307379) B2307379
theorem B3461555 : Blo 1366502 3461555 := bstep (se 1 (by rfl) ⟨2596166, by rfl⟩ : syracuseStep 3461555 = 5192333) B5192333
theorem B5845441 : Blo 1366502 5845441 := bstep (se 2 (by rfl) ⟨2192040, by rfl⟩ : syracuseStep 5845441 = 4384081) B4384081
theorem B2052569 : Blo 1366502 2052569 := bstep (se 2 (by rfl) ⟨769713, by rfl⟩ : syracuseStep 2052569 = 1539427) B1539427
theorem B3076595 : Blo 1366502 3076595 := bstep (se 1 (by rfl) ⟨2307446, by rfl⟩ : syracuseStep 3076595 = 4614893) B4614893
theorem B2920961 : Blo 1366502 2920961 := bstep (se 2 (by rfl) ⟨1095360, by rfl⟩ : syracuseStep 2920961 = 2190721) B2190721
theorem B3076631 : Blo 1366502 3076631 := bstep (se 1 (by rfl) ⟨2307473, by rfl⟩ : syracuseStep 3076631 = 4614947) B4614947
theorem B2052683 : Blo 1366502 2052683 := bstep (se 1 (by rfl) ⟨1539512, by rfl⟩ : syracuseStep 2052683 = 3079025) B3079025
theorem B2052695 : Blo 1366502 2052695 := bstep (se 1 (by rfl) ⟨1539521, by rfl⟩ : syracuseStep 2052695 = 3079043) B3079043
theorem B2306711 : Blo 1366502 2306711 := bstep (se 1 (by rfl) ⟨1730033, by rfl⟩ : syracuseStep 2306711 = 3460067) B3460067
theorem B3076811 : Blo 1366502 3076811 := bstep (se 1 (by rfl) ⟨2307608, by rfl⟩ : syracuseStep 3076811 = 4615217) B4615217
theorem B3461849 : Blo 1366502 3461849 := bstep (se 2 (by rfl) ⟨1298193, by rfl⟩ : syracuseStep 3461849 = 2596387) B2596387
theorem B3076865 : Blo 1366502 3076865 := bstep (se 2 (by rfl) ⟨1153824, by rfl⟩ : syracuseStep 3076865 = 2307649) B2307649
theorem B2306839 : Blo 1366502 2306839 := bstep (se 1 (by rfl) ⟨1730129, by rfl⟩ : syracuseStep 2306839 = 3460259) B3460259
theorem B7787339 : Blo 1366502 7787339 := bstep (se 1 (by rfl) ⟨5840504, by rfl⟩ : syracuseStep 7787339 = 11681009) B11681009
theorem B4617053 : Blo 1366502 4617053 := bstep (se 3 (by rfl) ⟨865697, by rfl⟩ : syracuseStep 4617053 = 1731395) B1731395
theorem B4928401 : Blo 1366502 4928401 := bstep (se 2 (by rfl) ⟨1848150, by rfl⟩ : syracuseStep 4928401 = 3696301) B3696301
theorem B1946521 : Blo 1366502 1946521 := bstep (se 2 (by rfl) ⟨729945, by rfl⟩ : syracuseStep 1946521 = 1459891) B1459891
theorem B5837771 : Blo 1366502 5837771 := bstep (se 1 (by rfl) ⟨4378328, by rfl⟩ : syracuseStep 5837771 = 8756657) B8756657
theorem B3077081 : Blo 1366502 3077081 := bstep (se 2 (by rfl) ⟨1153905, by rfl⟩ : syracuseStep 3077081 = 2307811) B2307811
theorem B2921483 : Blo 1366502 2921483 := bstep (se 1 (by rfl) ⟨2191112, by rfl⟩ : syracuseStep 2921483 = 4382225) B4382225
theorem B44356643 : Blo 1366502 44356643 := bstep (se 1 (by rfl) ⟨33267482, by rfl⟩ : syracuseStep 44356643 = 66534965) B66534965
theorem B16634915 : Blo 1366502 16634915 := bstep (se 1 (by rfl) ⟨12476186, by rfl⟩ : syracuseStep 16634915 = 24952373) B24952373
theorem B3077171 : Blo 1366502 3077171 := bstep (se 1 (by rfl) ⟨2307878, by rfl⟩ : syracuseStep 3077171 = 4615757) B4615757
theorem B3077207 : Blo 1366502 3077207 := bstep (se 1 (by rfl) ⟨2307905, by rfl⟩ : syracuseStep 3077207 = 4615811) B4615811
theorem B4379827 : Blo 1366502 4379827 := bstep (se 1 (by rfl) ⟨3284870, by rfl⟩ : syracuseStep 4379827 = 6569741) B6569741
theorem B3077387 : Blo 1366502 3077387 := bstep (se 1 (by rfl) ⟨2308040, by rfl⟩ : syracuseStep 3077387 = 4616081) B4616081
theorem B4379969 : Blo 1366502 4379969 := bstep (se 2 (by rfl) ⟨1642488, by rfl⟩ : syracuseStep 4379969 = 3284977) B3284977
theorem B3077441 : Blo 1366502 3077441 := bstep (se 2 (by rfl) ⟨1154040, by rfl⟩ : syracuseStep 3077441 = 2308081) B2308081
theorem B2307467 : Blo 1366502 2307467 := bstep (se 1 (by rfl) ⟨1730600, by rfl⟩ : syracuseStep 2307467 = 3461201) B3461201
theorem B6927767 : Blo 1366502 6927767 := bstep (se 1 (by rfl) ⟨5195825, by rfl⟩ : syracuseStep 6927767 = 10391651) B10391651
theorem B4380083 : Blo 1366502 4380083 := bstep (se 1 (by rfl) ⟨3285062, by rfl⟩ : syracuseStep 4380083 = 6570125) B6570125
theorem B1537483 : Blo 1366502 1537483 := bstep (se 1 (by rfl) ⟨1153112, by rfl⟩ : syracuseStep 1537483 = 2306225) B2306225
theorem B2307595 : Blo 1366502 2307595 := bstep (se 1 (by rfl) ⟨1730696, by rfl⟩ : syracuseStep 2307595 = 3461393) B3461393
theorem B3077657 : Blo 1366502 3077657 := bstep (se 2 (by rfl) ⟨1154121, by rfl⟩ : syracuseStep 3077657 = 2308243) B2308243
theorem B1537591 : Blo 1366502 1537591 := bstep (se 1 (by rfl) ⟨1153193, by rfl⟩ : syracuseStep 1537591 = 2306387) B2306387
theorem B8001125 : Blo 1366502 8001125 := bstep (se 4 (by rfl) ⟨750105, by rfl⟩ : syracuseStep 8001125 = 1500211) B1500211
theorem B3077747 : Blo 1366502 3077747 := bstep (se 1 (by rfl) ⟨2308310, by rfl⟩ : syracuseStep 3077747 = 4616621) B4616621
theorem B2594443 : Blo 1366502 2594443 := bstep (se 1 (by rfl) ⟨1945832, by rfl⟩ : syracuseStep 2594443 = 3891665) B3891665
theorem B3077783 : Blo 1366502 3077783 := bstep (se 1 (by rfl) ⟨2308337, by rfl⟩ : syracuseStep 3077783 = 4616675) B4616675
theorem B2307737 : Blo 1366502 2307737 := bstep (se 2 (by rfl) ⟨865401, by rfl⟩ : syracuseStep 2307737 = 1730803) B1730803
theorem B5191361 : Blo 1366502 5191361 := bstep (se 2 (by rfl) ⟨1946760, by rfl⟩ : syracuseStep 5191361 = 3893521) B3893521
theorem B1537771 : Blo 1366502 1537771 := bstep (se 1 (by rfl) ⟨1153328, by rfl⟩ : syracuseStep 1537771 = 2306657) B2306657
theorem B2307865 : Blo 1366502 2307865 := bstep (se 2 (by rfl) ⟨865449, by rfl⟩ : syracuseStep 2307865 = 1730899) B1730899
theorem B3077963 : Blo 1366502 3077963 := bstep (se 1 (by rfl) ⟨2308472, by rfl⟩ : syracuseStep 3077963 = 4616945) B4616945
theorem B1537879 : Blo 1366502 1537879 := bstep (se 1 (by rfl) ⟨1153409, by rfl⟩ : syracuseStep 1537879 = 2306819) B2306819
theorem B3078017 : Blo 1366502 3078017 := bstep (se 2 (by rfl) ⟨1154256, by rfl⟩ : syracuseStep 3078017 = 2308513) B2308513
theorem B11843459 : Blo 1366502 11843459 := bstep (se 1 (by rfl) ⟨8882594, by rfl⟩ : syracuseStep 11843459 = 17765189) B17765189
theorem B5838743 : Blo 1366502 5838743 := bstep (se 1 (by rfl) ⟨4379057, by rfl⟩ : syracuseStep 5838743 = 8758115) B8758115
theorem B33249203 : Blo 1366502 33249203 := bstep (se 1 (by rfl) ⟨24936902, by rfl⟩ : syracuseStep 33249203 = 49873805) B49873805
theorem B4618187 : Blo 1366502 4618187 := bstep (se 1 (by rfl) ⟨3463640, by rfl⟩ : syracuseStep 4618187 = 6927281) B6927281
theorem B6920153 : Blo 1366502 6920153 := bstep (se 2 (by rfl) ⟨2595057, by rfl⟩ : syracuseStep 6920153 = 5190115) B5190115
theorem B28063705 : Blo 1366502 28063705 := bstep (se 2 (by rfl) ⟨10523889, by rfl⟩ : syracuseStep 28063705 = 21047779) B21047779
theorem B1538059 : Blo 1366502 1538059 := bstep (se 1 (by rfl) ⟨1153544, by rfl⟩ : syracuseStep 1538059 = 2307089) B2307089
theorem B5265425 : Blo 1366502 5265425 := bstep (se 2 (by rfl) ⟨1974534, by rfl⟩ : syracuseStep 5265425 = 3949069) B3949069
theorem B14039075 : Blo 1366502 14039075 := bstep (se 1 (by rfl) ⟨10529306, by rfl⟩ : syracuseStep 14039075 = 21058613) B21058613
theorem B22181957 : Blo 1366502 22181957 := bstep (se 4 (by rfl) ⟨2079558, by rfl⟩ : syracuseStep 22181957 = 4159117) B4159117
theorem B2594891 : Blo 1366502 2594891 := bstep (se 1 (by rfl) ⟨1946168, by rfl⟩ : syracuseStep 2594891 = 3892337) B3892337
theorem B3078233 : Blo 1366502 3078233 := bstep (se 2 (by rfl) ⟨1154337, by rfl⟩ : syracuseStep 3078233 = 2308675) B2308675
theorem B1538167 : Blo 1366502 1538167 := bstep (se 1 (by rfl) ⟨1153625, by rfl⟩ : syracuseStep 1538167 = 2307251) B2307251
theorem B3078323 : Blo 1366502 3078323 := bstep (se 1 (by rfl) ⟨2308742, by rfl⟩ : syracuseStep 3078323 = 4617485) B4617485
theorem B3078359 : Blo 1366502 3078359 := bstep (se 1 (by rfl) ⟨2308769, by rfl⟩ : syracuseStep 3078359 = 4617539) B4617539
theorem B4618457 : Blo 1366502 4618457 := bstep (se 2 (by rfl) ⟨1731921, by rfl⟩ : syracuseStep 4618457 = 3463843) B3463843
theorem B2922713 : Blo 1366502 2922713 := bstep (se 2 (by rfl) ⟨1096017, by rfl⟩ : syracuseStep 2922713 = 2192035) B2192035
theorem B2595073 : Blo 1366502 2595073 := bstep (se 2 (by rfl) ⟨973152, by rfl⟩ : syracuseStep 2595073 = 1946305) B1946305
theorem B5921041 : Blo 1366502 5921041 := bstep (se 2 (by rfl) ⟨2220390, by rfl⟩ : syracuseStep 5921041 = 4440781) B4440781
theorem B3160343 : Blo 1366502 3160343 := bstep (se 1 (by rfl) ⟨2370257, by rfl⟩ : syracuseStep 3160343 = 4740515) B4740515
theorem B1538347 : Blo 1366502 1538347 := bstep (se 1 (by rfl) ⟨1153760, by rfl⟩ : syracuseStep 1538347 = 2307521) B2307521
theorem B1947979 : Blo 1366502 1947979 := bstep (se 1 (by rfl) ⟨1460984, by rfl⟩ : syracuseStep 1947979 = 2921969) B2921969
theorem B3463499 : Blo 1366502 3463499 := bstep (se 1 (by rfl) ⟨2597624, by rfl⟩ : syracuseStep 3463499 = 5195249) B5195249
theorem B2308439 : Blo 1366502 2308439 := bstep (se 1 (by rfl) ⟨1731329, by rfl⟩ : syracuseStep 2308439 = 3462659) B3462659
theorem B1947991 : Blo 1366502 1947991 := bstep (se 1 (by rfl) ⟨1460993, by rfl⟩ : syracuseStep 1947991 = 2921987) B2921987
theorem B3078539 : Blo 1366502 3078539 := bstep (se 1 (by rfl) ⟨2308904, by rfl⟩ : syracuseStep 3078539 = 4617809) B4617809
theorem B1538455 : Blo 1366502 1538455 := bstep (se 1 (by rfl) ⟨1153841, by rfl⟩ : syracuseStep 1538455 = 2307683) B2307683
theorem B3078593 : Blo 1366502 3078593 := bstep (se 2 (by rfl) ⟨1154472, by rfl⟩ : syracuseStep 3078593 = 2308945) B2308945
theorem B2308567 : Blo 1366502 2308567 := bstep (se 1 (by rfl) ⟨1731425, by rfl⟩ : syracuseStep 2308567 = 3462851) B3462851
theorem B1366507 : Blo 1366502 1366507 := bstep (se 1 (by rfl) ⟨1024880, by rfl⟩ : syracuseStep 1366507 = 2049761) B2049761
theorem B1366519 : Blo 1366502 1366519 := bstep (se 1 (by rfl) ⟨1024889, by rfl⟩ : syracuseStep 1366519 = 2049779) B2049779
theorem B1366539 : Blo 1366502 1366539 := bstep (se 1 (by rfl) ⟨1024904, by rfl⟩ : syracuseStep 1366539 = 2049809) B2049809
theorem B1366551 : Blo 1366502 1366551 := bstep (se 1 (by rfl) ⟨1024913, by rfl⟩ : syracuseStep 1366551 = 2049827) B2049827
theorem B1366571 : Blo 1366502 1366571 := bstep (se 1 (by rfl) ⟨1024928, by rfl⟩ : syracuseStep 1366571 = 2049857) B2049857
theorem B5839411 : Blo 1366502 5839411 := bstep (se 1 (by rfl) ⟨4379558, by rfl⟩ : syracuseStep 5839411 = 8759117) B8759117
theorem B1366583 : Blo 1366502 1366583 := bstep (se 1 (by rfl) ⟨1024937, by rfl⟩ : syracuseStep 1366583 = 2049875) B2049875
theorem B1366603 : Blo 1366502 1366603 := bstep (se 1 (by rfl) ⟨1024952, by rfl⟩ : syracuseStep 1366603 = 2049905) B2049905
theorem B1538635 : Blo 1366502 1538635 := bstep (se 1 (by rfl) ⟨1153976, by rfl⟩ : syracuseStep 1538635 = 2307953) B2307953
theorem B1366615 : Blo 1366502 1366615 := bstep (se 1 (by rfl) ⟨1024961, by rfl⟩ : syracuseStep 1366615 = 2049923) B2049923
theorem B2595415 : Blo 1366502 2595415 := bstep (se 1 (by rfl) ⟨1946561, by rfl⟩ : syracuseStep 2595415 = 3893123) B3893123
theorem B2464345 : Blo 1366502 2464345 := bstep (se 2 (by rfl) ⟨924129, by rfl⟩ : syracuseStep 2464345 = 1848259) B1848259
theorem B3119705 : Blo 1366502 3119705 := bstep (se 2 (by rfl) ⟨1169889, by rfl⟩ : syracuseStep 3119705 = 2339779) B2339779
theorem B1366635 : Blo 1366502 1366635 := bstep (se 1 (by rfl) ⟨1024976, by rfl⟩ : syracuseStep 1366635 = 2049953) B2049953
theorem B1366647 : Blo 1366502 1366647 := bstep (se 1 (by rfl) ⟨1024985, by rfl⟩ : syracuseStep 1366647 = 2049971) B2049971
theorem B1366667 : Blo 1366502 1366667 := bstep (se 1 (by rfl) ⟨1025000, by rfl⟩ : syracuseStep 1366667 = 2050001) B2050001
theorem B3160715 : Blo 1366502 3160715 := bstep (se 1 (by rfl) ⟨2370536, by rfl⟩ : syracuseStep 3160715 = 4741073) B4741073
theorem B1366679 : Blo 1366502 1366679 := bstep (se 1 (by rfl) ⟨1025009, by rfl⟩ : syracuseStep 1366679 = 2050019) B2050019
theorem B3078809 : Blo 1366502 3078809 := bstep (se 2 (by rfl) ⟨1154553, by rfl⟩ : syracuseStep 3078809 = 2309107) B2309107
theorem B1366699 : Blo 1366502 1366699 := bstep (se 1 (by rfl) ⟨1025024, by rfl⟩ : syracuseStep 1366699 = 2050049) B2050049
theorem B1366711 : Blo 1366502 1366711 := bstep (se 1 (by rfl) ⟨1025033, by rfl⟩ : syracuseStep 1366711 = 2050067) B2050067
theorem B1538743 : Blo 1366502 1538743 := bstep (se 1 (by rfl) ⟨1154057, by rfl⟩ : syracuseStep 1538743 = 2308115) B2308115
theorem B1366731 : Blo 1366502 1366731 := bstep (se 1 (by rfl) ⟨1025048, by rfl⟩ : syracuseStep 1366731 = 2050097) B2050097
theorem B1366743 : Blo 1366502 1366743 := bstep (se 1 (by rfl) ⟨1025057, by rfl⟩ : syracuseStep 1366743 = 2050115) B2050115
theorem B1366763 : Blo 1366502 1366763 := bstep (se 1 (by rfl) ⟨1025072, by rfl⟩ : syracuseStep 1366763 = 2050145) B2050145
theorem B3078899 : Blo 1366502 3078899 := bstep (se 1 (by rfl) ⟨2309174, by rfl⟩ : syracuseStep 3078899 = 4618349) B4618349
theorem B1366775 : Blo 1366502 1366775 := bstep (se 1 (by rfl) ⟨1025081, by rfl⟩ : syracuseStep 1366775 = 2050163) B2050163
theorem B1366795 : Blo 1366502 1366795 := bstep (se 1 (by rfl) ⟨1025096, by rfl⟩ : syracuseStep 1366795 = 2050193) B2050193
theorem B1366807 : Blo 1366502 1366807 := bstep (se 1 (by rfl) ⟨1025105, by rfl⟩ : syracuseStep 1366807 = 2050211) B2050211
theorem B3078935 : Blo 1366502 3078935 := bstep (se 1 (by rfl) ⟨2309201, by rfl⟩ : syracuseStep 3078935 = 4618403) B4618403
theorem B1366827 : Blo 1366502 1366827 := bstep (se 1 (by rfl) ⟨1025120, by rfl⟩ : syracuseStep 1366827 = 2050241) B2050241
theorem B2595635 : Blo 1366502 2595635 := bstep (se 1 (by rfl) ⟨1946726, by rfl⟩ : syracuseStep 2595635 = 3893453) B3893453
theorem B1366839 : Blo 1366502 1366839 := bstep (se 1 (by rfl) ⟨1025129, by rfl⟩ : syracuseStep 1366839 = 2050259) B2050259
theorem B1366859 : Blo 1366502 1366859 := bstep (se 1 (by rfl) ⟨1025144, by rfl⟩ : syracuseStep 1366859 = 2050289) B2050289
theorem B1366871 : Blo 1366502 1366871 := bstep (se 1 (by rfl) ⟨1025153, by rfl⟩ : syracuseStep 1366871 = 2050307) B2050307
theorem B1366891 : Blo 1366502 1366891 := bstep (se 1 (by rfl) ⟨1025168, by rfl⟩ : syracuseStep 1366891 = 2050337) B2050337
theorem B1538923 : Blo 1366502 1538923 := bstep (se 1 (by rfl) ⟨1154192, by rfl⟩ : syracuseStep 1538923 = 2308385) B2308385
theorem B1366903 : Blo 1366502 1366903 := bstep (se 1 (by rfl) ⟨1025177, by rfl⟩ : syracuseStep 1366903 = 2050355) B2050355
theorem B8887171 : Blo 1366502 8887171 := bstep (se 1 (by rfl) ⟨6665378, by rfl⟩ : syracuseStep 8887171 = 13330757) B13330757
theorem B1366923 : Blo 1366502 1366923 := bstep (se 1 (by rfl) ⟨1025192, by rfl⟩ : syracuseStep 1366923 = 2050385) B2050385
theorem B1366935 : Blo 1366502 1366935 := bstep (se 1 (by rfl) ⟨1025201, by rfl⟩ : syracuseStep 1366935 = 2050403) B2050403
theorem B4995991 : Blo 1366502 4995991 := bstep (se 1 (by rfl) ⟨3746993, by rfl⟩ : syracuseStep 4995991 = 7493987) B7493987
theorem B1366955 : Blo 1366502 1366955 := bstep (se 1 (by rfl) ⟨1025216, by rfl⟩ : syracuseStep 1366955 = 2050433) B2050433
theorem B1366967 : Blo 1366502 1366967 := bstep (se 1 (by rfl) ⟨1025225, by rfl⟩ : syracuseStep 1366967 = 2050451) B2050451
theorem B1366987 : Blo 1366502 1366987 := bstep (se 1 (by rfl) ⟨1025240, by rfl⟩ : syracuseStep 1366987 = 2050481) B2050481
theorem B3079115 : Blo 1366502 3079115 := bstep (se 1 (by rfl) ⟨2309336, by rfl⟩ : syracuseStep 3079115 = 4618673) B4618673
theorem B1366999 : Blo 1366502 1366999 := bstep (se 1 (by rfl) ⟨1025249, by rfl⟩ : syracuseStep 1366999 = 2050499) B2050499
theorem B1539031 : Blo 1366502 1539031 := bstep (se 1 (by rfl) ⟨1154273, by rfl⟩ : syracuseStep 1539031 = 2308547) B2308547
theorem B1367019 : Blo 1366502 1367019 := bstep (se 1 (by rfl) ⟨1025264, by rfl⟩ : syracuseStep 1367019 = 2050529) B2050529
theorem B1367031 : Blo 1366502 1367031 := bstep (se 1 (by rfl) ⟨1025273, by rfl⟩ : syracuseStep 1367031 = 2050547) B2050547
theorem B4996099 : Blo 1366502 4996099 := bstep (se 1 (by rfl) ⟨3747074, by rfl⟩ : syracuseStep 4996099 = 7494149) B7494149
theorem B1367051 : Blo 1366502 1367051 := bstep (se 1 (by rfl) ⟨1025288, by rfl⟩ : syracuseStep 1367051 = 2050577) B2050577
theorem B1367063 : Blo 1366502 1367063 := bstep (se 1 (by rfl) ⟨1025297, by rfl⟩ : syracuseStep 1367063 = 2050595) B2050595
theorem B2595863 : Blo 1366502 2595863 := bstep (se 1 (by rfl) ⟨1946897, by rfl⟩ : syracuseStep 2595863 = 3893795) B3893795
theorem B1367083 : Blo 1366502 1367083 := bstep (se 1 (by rfl) ⟨1025312, by rfl⟩ : syracuseStep 1367083 = 2050625) B2050625
theorem B1367095 : Blo 1366502 1367095 := bstep (se 1 (by rfl) ⟨1025321, by rfl⟩ : syracuseStep 1367095 = 2050643) B2050643
theorem B1367115 : Blo 1366502 1367115 := bstep (se 1 (by rfl) ⟨1025336, by rfl⟩ : syracuseStep 1367115 = 2050673) B2050673
theorem B2309195 : Blo 1366502 2309195 := bstep (se 1 (by rfl) ⟨1731896, by rfl⟩ : syracuseStep 2309195 = 3463793) B3463793
theorem B1367127 : Blo 1366502 1367127 := bstep (se 1 (by rfl) ⟨1025345, by rfl⟩ : syracuseStep 1367127 = 2050691) B2050691
theorem B1367147 : Blo 1366502 1367147 := bstep (se 1 (by rfl) ⟨1025360, by rfl⟩ : syracuseStep 1367147 = 2050721) B2050721
theorem B1367159 : Blo 1366502 1367159 := bstep (se 1 (by rfl) ⟨1025369, by rfl⟩ : syracuseStep 1367159 = 2050739) B2050739
theorem B1367179 : Blo 1366502 1367179 := bstep (se 1 (by rfl) ⟨1025384, by rfl⟩ : syracuseStep 1367179 = 2050769) B2050769
theorem B1539211 : Blo 1366502 1539211 := bstep (se 1 (by rfl) ⟨1154408, by rfl⟩ : syracuseStep 1539211 = 2308817) B2308817
theorem B5192849 : Blo 1366502 5192849 := bstep (se 2 (by rfl) ⟨1947318, by rfl⟩ : syracuseStep 5192849 = 3894637) B3894637
theorem B1367191 : Blo 1366502 1367191 := bstep (se 1 (by rfl) ⟨1025393, by rfl⟩ : syracuseStep 1367191 = 2050787) B2050787
theorem B1367211 : Blo 1366502 1367211 := bstep (se 1 (by rfl) ⟨1025408, by rfl⟩ : syracuseStep 1367211 = 2050817) B2050817
theorem B1367223 : Blo 1366502 1367223 := bstep (se 1 (by rfl) ⟨1025417, by rfl⟩ : syracuseStep 1367223 = 2050835) B2050835
theorem B1367243 : Blo 1366502 1367243 := bstep (se 1 (by rfl) ⟨1025432, by rfl⟩ : syracuseStep 1367243 = 2050865) B2050865
theorem B2309323 : Blo 1366502 2309323 := bstep (se 1 (by rfl) ⟨1731992, by rfl⟩ : syracuseStep 2309323 = 3463985) B3463985
theorem B1367255 : Blo 1366502 1367255 := bstep (se 1 (by rfl) ⟨1025441, by rfl⟩ : syracuseStep 1367255 = 2050883) B2050883
theorem B1367275 : Blo 1366502 1367275 := bstep (se 1 (by rfl) ⟨1025456, by rfl⟩ : syracuseStep 1367275 = 2050913) B2050913
theorem B1367287 : Blo 1366502 1367287 := bstep (se 1 (by rfl) ⟨1025465, by rfl⟩ : syracuseStep 1367287 = 2050931) B2050931
theorem B1539319 : Blo 1366502 1539319 := bstep (se 1 (by rfl) ⟨1154489, by rfl⟩ : syracuseStep 1539319 = 2308979) B2308979
theorem B1367307 : Blo 1366502 1367307 := bstep (se 1 (by rfl) ⟨1025480, by rfl⟩ : syracuseStep 1367307 = 2050961) B2050961
theorem B1367319 : Blo 1366502 1367319 := bstep (se 1 (by rfl) ⟨1025489, by rfl⟩ : syracuseStep 1367319 = 2050979) B2050979
theorem B2596121 : Blo 1366502 2596121 := bstep (se 2 (by rfl) ⟨973545, by rfl⟩ : syracuseStep 2596121 = 1947091) B1947091
theorem B1367339 : Blo 1366502 1367339 := bstep (se 1 (by rfl) ⟨1025504, by rfl⟩ : syracuseStep 1367339 = 2051009) B2051009
theorem B7896365 : Blo 1366502 7896365 := bstep (se 3 (by rfl) ⟨1480568, by rfl⟩ : syracuseStep 7896365 = 2961137) B2961137
theorem B1367351 : Blo 1366502 1367351 := bstep (se 1 (by rfl) ⟨1025513, by rfl⟩ : syracuseStep 1367351 = 2051027) B2051027
theorem B1367371 : Blo 1366502 1367371 := bstep (se 1 (by rfl) ⟨1025528, by rfl⟩ : syracuseStep 1367371 = 2051057) B2051057
theorem B1367383 : Blo 1366502 1367383 := bstep (se 1 (by rfl) ⟨1025537, by rfl⟩ : syracuseStep 1367383 = 2051075) B2051075
theorem B9485669 : Blo 1366502 9485669 := bstep (se 4 (by rfl) ⟨889281, by rfl⟩ : syracuseStep 9485669 = 1778563) B1778563
theorem B1367403 : Blo 1366502 1367403 := bstep (se 1 (by rfl) ⟨1025552, by rfl⟩ : syracuseStep 1367403 = 2051105) B2051105
theorem B1367415 : Blo 1366502 1367415 := bstep (se 1 (by rfl) ⟨1025561, by rfl⟩ : syracuseStep 1367415 = 2051123) B2051123
theorem B1367435 : Blo 1366502 1367435 := bstep (se 1 (by rfl) ⟨1025576, by rfl⟩ : syracuseStep 1367435 = 2051153) B2051153
theorem B119922061 : Blo 1366502 119922061 := bstep (se 3 (by rfl) ⟨22485386, by rfl⟩ : syracuseStep 119922061 = 44970773) B44970773
theorem B1367447 : Blo 1366502 1367447 := bstep (se 1 (by rfl) ⟨1025585, by rfl⟩ : syracuseStep 1367447 = 2051171) B2051171
theorem B1367467 : Blo 1366502 1367467 := bstep (se 1 (by rfl) ⟨1025600, by rfl⟩ : syracuseStep 1367467 = 2051201) B2051201
theorem B1539499 : Blo 1366502 1539499 := bstep (se 1 (by rfl) ⟨1154624, by rfl⟩ : syracuseStep 1539499 = 2309249) B2309249
theorem B7790003 : Blo 1366502 7790003 := bstep (se 1 (by rfl) ⟨5842502, by rfl⟩ : syracuseStep 7790003 = 11685005) B11685005
theorem B1367479 : Blo 1366502 1367479 := bstep (se 1 (by rfl) ⟨1025609, by rfl⟩ : syracuseStep 1367479 = 2051219) B2051219
theorem B1367499 : Blo 1366502 1367499 := bstep (se 1 (by rfl) ⟨1025624, by rfl⟩ : syracuseStep 1367499 = 2051249) B2051249
theorem B1367511 : Blo 1366502 1367511 := bstep (se 1 (by rfl) ⟨1025633, by rfl⟩ : syracuseStep 1367511 = 2051267) B2051267
theorem B1367531 : Blo 1366502 1367531 := bstep (se 1 (by rfl) ⟨1025648, by rfl⟩ : syracuseStep 1367531 = 2051297) B2051297
theorem B1367543 : Blo 1366502 1367543 := bstep (se 1 (by rfl) ⟨1025657, by rfl⟩ : syracuseStep 1367543 = 2051315) B2051315
theorem B1367563 : Blo 1366502 1367563 := bstep (se 1 (by rfl) ⟨1025672, by rfl⟩ : syracuseStep 1367563 = 2051345) B2051345
theorem B2465291 : Blo 1366502 2465291 := bstep (se 1 (by rfl) ⟨1848968, by rfl⟩ : syracuseStep 2465291 = 3697937) B3697937
theorem B1367575 : Blo 1366502 1367575 := bstep (se 1 (by rfl) ⟨1025681, by rfl⟩ : syracuseStep 1367575 = 2051363) B2051363
theorem B1367595 : Blo 1366502 1367595 := bstep (se 1 (by rfl) ⟨1025696, by rfl⟩ : syracuseStep 1367595 = 2051393) B2051393
theorem B6921773 : Blo 1366502 6921773 := bstep (se 3 (by rfl) ⟨1297832, by rfl⟩ : syracuseStep 6921773 = 2595665) B2595665
theorem B1367607 : Blo 1366502 1367607 := bstep (se 1 (by rfl) ⟨1025705, by rfl⟩ : syracuseStep 1367607 = 2051411) B2051411
theorem B1367627 : Blo 1366502 1367627 := bstep (se 1 (by rfl) ⟨1025720, by rfl⟩ : syracuseStep 1367627 = 2051441) B2051441
theorem B1367639 : Blo 1366502 1367639 := bstep (se 1 (by rfl) ⟨1025729, by rfl⟩ : syracuseStep 1367639 = 2051459) B2051459
theorem B5193305 : Blo 1366502 5193305 := bstep (se 2 (by rfl) ⟨1947489, by rfl⟩ : syracuseStep 5193305 = 3894979) B3894979
theorem B1367659 : Blo 1366502 1367659 := bstep (se 1 (by rfl) ⟨1025744, by rfl⟩ : syracuseStep 1367659 = 2051489) B2051489
theorem B1367671 : Blo 1366502 1367671 := bstep (se 1 (by rfl) ⟨1025753, by rfl⟩ : syracuseStep 1367671 = 2051507) B2051507
theorem B1367691 : Blo 1366502 1367691 := bstep (se 1 (by rfl) ⟨1025768, by rfl⟩ : syracuseStep 1367691 = 2051537) B2051537
theorem B1367703 : Blo 1366502 1367703 := bstep (se 1 (by rfl) ⟨1025777, by rfl⟩ : syracuseStep 1367703 = 2051555) B2051555
theorem B1367723 : Blo 1366502 1367723 := bstep (se 1 (by rfl) ⟨1025792, by rfl⟩ : syracuseStep 1367723 = 2051585) B2051585
theorem B2596531 : Blo 1366502 2596531 := bstep (se 1 (by rfl) ⟨1947398, by rfl⟩ : syracuseStep 2596531 = 3894797) B3894797
theorem B1367735 : Blo 1366502 1367735 := bstep (se 1 (by rfl) ⟨1025801, by rfl⟩ : syracuseStep 1367735 = 2051603) B2051603
theorem B1367755 : Blo 1366502 1367755 := bstep (se 1 (by rfl) ⟨1025816, by rfl⟩ : syracuseStep 1367755 = 2051633) B2051633
theorem B1367767 : Blo 1366502 1367767 := bstep (se 1 (by rfl) ⟨1025825, by rfl⟩ : syracuseStep 1367767 = 2051651) B2051651
theorem B1367787 : Blo 1366502 1367787 := bstep (se 1 (by rfl) ⟨1025840, by rfl⟩ : syracuseStep 1367787 = 2051681) B2051681
theorem B1367799 : Blo 1366502 1367799 := bstep (se 1 (by rfl) ⟨1025849, by rfl⟩ : syracuseStep 1367799 = 2051699) B2051699
theorem B9854725 : Blo 1366502 9854725 := bstep (se 4 (by rfl) ⟨923880, by rfl⟩ : syracuseStep 9854725 = 1847761) B1847761
theorem B1367819 : Blo 1366502 1367819 := bstep (se 1 (by rfl) ⟨1025864, by rfl⟩ : syracuseStep 1367819 = 2051729) B2051729
theorem B5840657 : Blo 1366502 5840657 := bstep (se 2 (by rfl) ⟨2190246, by rfl⟩ : syracuseStep 5840657 = 4380493) B4380493
theorem B1367831 : Blo 1366502 1367831 := bstep (se 1 (by rfl) ⟨1025873, by rfl⟩ : syracuseStep 1367831 = 2051747) B2051747
theorem B1367851 : Blo 1366502 1367851 := bstep (se 1 (by rfl) ⟨1025888, by rfl⟩ : syracuseStep 1367851 = 2051777) B2051777
theorem B5193517 : Blo 1366502 5193517 := bstep (se 3 (by rfl) ⟨973784, by rfl⟩ : syracuseStep 5193517 = 1947569) B1947569
theorem B1367863 : Blo 1366502 1367863 := bstep (se 1 (by rfl) ⟨1025897, by rfl⟩ : syracuseStep 1367863 = 2051795) B2051795
theorem B1367883 : Blo 1366502 1367883 := bstep (se 1 (by rfl) ⟨1025912, by rfl⟩ : syracuseStep 1367883 = 2051825) B2051825
theorem B1367895 : Blo 1366502 1367895 := bstep (se 1 (by rfl) ⟨1025921, by rfl⟩ : syracuseStep 1367895 = 2051843) B2051843
theorem B9863005 : Blo 1366502 9863005 := bstep (se 3 (by rfl) ⟨1849313, by rfl⟩ : syracuseStep 9863005 = 3698627) B3698627
theorem B1367915 : Blo 1366502 1367915 := bstep (se 1 (by rfl) ⟨1025936, by rfl⟩ : syracuseStep 1367915 = 2051873) B2051873
theorem B1367927 : Blo 1366502 1367927 := bstep (se 1 (by rfl) ⟨1025945, by rfl⟩ : syracuseStep 1367927 = 2051891) B2051891
theorem B1367947 : Blo 1366502 1367947 := bstep (se 1 (by rfl) ⟨1025960, by rfl⟩ : syracuseStep 1367947 = 2051921) B2051921
theorem B8757143 : Blo 1366502 8757143 := bstep (se 1 (by rfl) ⟨6567857, by rfl⟩ : syracuseStep 8757143 = 13135715) B13135715
theorem B1367959 : Blo 1366502 1367959 := bstep (se 1 (by rfl) ⟨1025969, by rfl⟩ : syracuseStep 1367959 = 2051939) B2051939
theorem B1367979 : Blo 1366502 1367979 := bstep (se 1 (by rfl) ⟨1025984, by rfl⟩ : syracuseStep 1367979 = 2051969) B2051969
theorem B1367991 : Blo 1366502 1367991 := bstep (se 1 (by rfl) ⟨1025993, by rfl⟩ : syracuseStep 1367991 = 2051987) B2051987
theorem B2465729 : Blo 1366502 2465729 := bstep (se 2 (by rfl) ⟨924648, by rfl⟩ : syracuseStep 2465729 = 1849297) B1849297
theorem B1368011 : Blo 1366502 1368011 := bstep (se 1 (by rfl) ⟨1026008, by rfl⟩ : syracuseStep 1368011 = 2052017) B2052017
theorem B1368023 : Blo 1366502 1368023 := bstep (se 1 (by rfl) ⟨1026017, by rfl⟩ : syracuseStep 1368023 = 2052035) B2052035
theorem B1368043 : Blo 1366502 1368043 := bstep (se 1 (by rfl) ⟨1026032, by rfl⟩ : syracuseStep 1368043 = 2052065) B2052065
theorem B1368055 : Blo 1366502 1368055 := bstep (se 1 (by rfl) ⟨1026041, by rfl⟩ : syracuseStep 1368055 = 2052083) B2052083
theorem B3506177 : Blo 1366502 3506177 := bstep (se 2 (by rfl) ⟨1314816, by rfl⟩ : syracuseStep 3506177 = 2629633) B2629633
theorem B1368071 : Blo 1366502 1368071 := bstep (se 1 (by rfl) ⟨1026053, by rfl⟩ : syracuseStep 1368071 = 2052107) B2052107
theorem B1368079 : Blo 1366502 1368079 := bstep (se 1 (by rfl) ⟨1026059, by rfl⟩ : syracuseStep 1368079 = 2052119) B2052119
theorem B4612139 : Blo 1366502 4612139 := bstep (se 1 (by rfl) ⟨3459104, by rfl⟩ : syracuseStep 4612139 = 6918209) B6918209
theorem B14041133 : Blo 1366502 14041133 := bstep (se 3 (by rfl) ⟨2632712, by rfl⟩ : syracuseStep 14041133 = 5265425) B5265425
theorem B1368123 : Blo 1366502 1368123 := bstep (se 1 (by rfl) ⟨1026092, by rfl⟩ : syracuseStep 1368123 = 2052185) B2052185
theorem B4382839 : Blo 1366502 4382839 := bstep (se 1 (by rfl) ⟨3287129, by rfl⟩ : syracuseStep 4382839 = 6574259) B6574259
theorem B1368199 : Blo 1366502 1368199 := bstep (se 1 (by rfl) ⟨1026149, by rfl⟩ : syracuseStep 1368199 = 2052299) B2052299
theorem B1368207 : Blo 1366502 1368207 := bstep (se 1 (by rfl) ⟨1026155, by rfl⟩ : syracuseStep 1368207 = 2052311) B2052311
theorem B1368251 : Blo 1366502 1368251 := bstep (se 1 (by rfl) ⟨1026188, by rfl⟩ : syracuseStep 1368251 = 2052377) B2052377
theorem B3948745 : Blo 1366502 3948745 := bstep (se 2 (by rfl) ⟨1480779, by rfl⟩ : syracuseStep 3948745 = 2961559) B2961559
theorem B10379501 : Blo 1366502 10379501 := bstep (se 3 (by rfl) ⟨1946156, by rfl⟩ : syracuseStep 10379501 = 3892313) B3892313
theorem B1368327 : Blo 1366502 1368327 := bstep (se 1 (by rfl) ⟨1026245, by rfl⟩ : syracuseStep 1368327 = 2052491) B2052491
theorem B1368335 : Blo 1366502 1368335 := bstep (se 1 (by rfl) ⟨1026251, by rfl⟩ : syracuseStep 1368335 = 2052503) B2052503
theorem B1368379 : Blo 1366502 1368379 := bstep (se 1 (by rfl) ⟨1026284, by rfl⟩ : syracuseStep 1368379 = 2052569) B2052569
theorem B1368455 : Blo 1366502 1368455 := bstep (se 1 (by rfl) ⟨1026341, by rfl⟩ : syracuseStep 1368455 = 2052683) B2052683
theorem B1368463 : Blo 1366502 1368463 := bstep (se 1 (by rfl) ⟨1026347, by rfl⟩ : syracuseStep 1368463 = 2052695) B2052695
theorem B2597321 : Blo 1366502 2597321 := bstep (se 2 (by rfl) ⟨973995, by rfl⟩ : syracuseStep 2597321 = 1947991) B1947991
theorem B15581645 : Blo 1366502 15581645 := bstep (se 3 (by rfl) ⟨2921558, by rfl⟩ : syracuseStep 15581645 = 5843117) B5843117
theorem B5194307 : Blo 1366502 5194307 := bstep (se 1 (by rfl) ⟨3895730, by rfl⟩ : syracuseStep 5194307 = 7791461) B7791461
theorem B3891847 : Blo 1366502 3891847 := bstep (se 1 (by rfl) ⟨2918885, by rfl⟩ : syracuseStep 3891847 = 5837771) B5837771
theorem B3285793 : Blo 1366502 3285793 := bstep (se 2 (by rfl) ⟨1232172, by rfl⟩ : syracuseStep 3285793 = 2464345) B2464345
theorem B3892121 : Blo 1366502 3892121 := bstep (se 2 (by rfl) ⟨1459545, by rfl⟩ : syracuseStep 3892121 = 2919091) B2919091
theorem B5194763 : Blo 1366502 5194763 := bstep (se 1 (by rfl) ⟨3896072, by rfl⟩ : syracuseStep 5194763 = 7792145) B7792145
theorem B5334083 : Blo 1366502 5334083 := bstep (se 1 (by rfl) ⟨4000562, by rfl⟩ : syracuseStep 5334083 = 8001125) B8001125
theorem B1459387 : Blo 1366502 1459387 := bstep (se 1 (by rfl) ⟨1094540, by rfl⟩ : syracuseStep 1459387 = 2189081) B2189081
theorem B6571201 : Blo 1366502 6571201 := bstep (se 2 (by rfl) ⟨2464200, by rfl⟩ : syracuseStep 6571201 = 4928401) B4928401
theorem B4613435 : Blo 1366502 4613435 := bstep (se 1 (by rfl) ⟨3460076, by rfl⟩ : syracuseStep 4613435 = 6920153) B6920153
theorem B14787971 : Blo 1366502 14787971 := bstep (se 1 (by rfl) ⟨11090978, by rfl⟩ : syracuseStep 14787971 = 22181957) B22181957
theorem B56935811 : Blo 1366502 56935811 := bstep (se 1 (by rfl) ⟨42701858, by rfl⟩ : syracuseStep 56935811 = 85403717) B85403717
theorem B1729927 : Blo 1366502 1729927 := bstep (se 1 (by rfl) ⟨1297445, by rfl⟩ : syracuseStep 1729927 = 2594891) B2594891
theorem B56132999 : Blo 1366502 56132999 := bstep (se 1 (by rfl) ⟨42099749, by rfl⟩ : syracuseStep 56132999 = 84199499) B84199499
theorem B26281421 : Blo 1366502 26281421 := bstep (se 3 (by rfl) ⟨4927766, by rfl⟩ : syracuseStep 26281421 = 9855533) B9855533
theorem B2106895 : Blo 1366502 2106895 := bstep (se 1 (by rfl) ⟨1580171, by rfl⟩ : syracuseStep 2106895 = 3160343) B3160343
theorem B3892769 : Blo 1366502 3892769 := bstep (se 2 (by rfl) ⟨1459788, by rfl⟩ : syracuseStep 3892769 = 2919577) B2919577
theorem B10389221 : Blo 1366502 10389221 := bstep (se 4 (by rfl) ⟨973989, by rfl⟩ : syracuseStep 10389221 = 1947979) B1947979
theorem B4613921 : Blo 1366502 4613921 := bstep (se 2 (by rfl) ⟨1730220, by rfl⟩ : syracuseStep 4613921 = 3460441) B3460441
theorem B2049851 : Blo 1366502 2049851 := bstep (se 1 (by rfl) ⟨1537388, by rfl⟩ : syracuseStep 2049851 = 3074777) B3074777
theorem B2049911 : Blo 1366502 2049911 := bstep (se 1 (by rfl) ⟨1537433, by rfl⟩ : syracuseStep 2049911 = 3074867) B3074867
theorem B1730423 : Blo 1366502 1730423 := bstep (se 1 (by rfl) ⟨1297817, by rfl⟩ : syracuseStep 1730423 = 2595635) B2595635
theorem B2049935 : Blo 1366502 2049935 := bstep (se 1 (by rfl) ⟨1537451, by rfl⟩ : syracuseStep 2049935 = 3074903) B3074903
theorem B3458963 : Blo 1366502 3458963 := bstep (se 1 (by rfl) ⟨2594222, by rfl⟩ : syracuseStep 3458963 = 5188445) B5188445
theorem B2049977 : Blo 1366502 2049977 := bstep (se 2 (by rfl) ⟨768741, by rfl⟩ : syracuseStep 2049977 = 1537483) B1537483
theorem B2050055 : Blo 1366502 2050055 := bstep (se 1 (by rfl) ⟨1537541, by rfl⟩ : syracuseStep 2050055 = 3075083) B3075083
theorem B1730575 : Blo 1366502 1730575 := bstep (se 1 (by rfl) ⟨1297931, by rfl⟩ : syracuseStep 1730575 = 2595863) B2595863
theorem B2050091 : Blo 1366502 2050091 := bstep (se 1 (by rfl) ⟨1537568, by rfl⟩ : syracuseStep 2050091 = 3075137) B3075137
theorem B2050121 : Blo 1366502 2050121 := bstep (se 2 (by rfl) ⟨768795, by rfl⟩ : syracuseStep 2050121 = 1537591) B1537591
theorem B10381445 : Blo 1366502 10381445 := bstep (se 4 (by rfl) ⟨973260, by rfl⟩ : syracuseStep 10381445 = 1946521) B1946521
theorem B3459257 : Blo 1366502 3459257 := bstep (se 2 (by rfl) ⟨1297221, by rfl⟩ : syracuseStep 3459257 = 2594443) B2594443
theorem B2050235 : Blo 1366502 2050235 := bstep (se 1 (by rfl) ⟨1537676, by rfl⟩ : syracuseStep 2050235 = 3075353) B3075353
theorem B1730747 : Blo 1366502 1730747 := bstep (se 1 (by rfl) ⟨1298060, by rfl⟩ : syracuseStep 1730747 = 2596121) B2596121
theorem B2050295 : Blo 1366502 2050295 := bstep (se 1 (by rfl) ⟨1537721, by rfl⟩ : syracuseStep 2050295 = 3075443) B3075443
theorem B2050319 : Blo 1366502 2050319 := bstep (se 1 (by rfl) ⟨1537739, by rfl⟩ : syracuseStep 2050319 = 3075479) B3075479
theorem B2050361 : Blo 1366502 2050361 := bstep (se 2 (by rfl) ⟨768885, by rfl⟩ : syracuseStep 2050361 = 1537771) B1537771
theorem B4614515 : Blo 1366502 4614515 := bstep (se 1 (by rfl) ⟨3460886, by rfl⟩ : syracuseStep 4614515 = 6921773) B6921773
theorem B2918791 : Blo 1366502 2918791 := bstep (se 1 (by rfl) ⟨2189093, by rfl⟩ : syracuseStep 2918791 = 4378187) B4378187
theorem B2050439 : Blo 1366502 2050439 := bstep (se 1 (by rfl) ⟨1537829, by rfl⟩ : syracuseStep 2050439 = 3075659) B3075659
theorem B6924689 : Blo 1366502 6924689 := bstep (se 2 (by rfl) ⟨2596758, by rfl⟩ : syracuseStep 6924689 = 5193517) B5193517
theorem B2050475 : Blo 1366502 2050475 := bstep (se 1 (by rfl) ⟨1537856, by rfl⟩ : syracuseStep 2050475 = 3075713) B3075713
theorem B2050505 : Blo 1366502 2050505 := bstep (se 2 (by rfl) ⟨768939, by rfl⟩ : syracuseStep 2050505 = 1537879) B1537879
theorem B13150673 : Blo 1366502 13150673 := bstep (se 2 (by rfl) ⟨4931502, by rfl⟩ : syracuseStep 13150673 = 9863005) B9863005
theorem B3893771 : Blo 1366502 3893771 := bstep (se 1 (by rfl) ⟨2920328, by rfl⟩ : syracuseStep 3893771 = 5840657) B5840657
theorem B2050619 : Blo 1366502 2050619 := bstep (se 1 (by rfl) ⟨1537964, by rfl⟩ : syracuseStep 2050619 = 3075929) B3075929
theorem B2050679 : Blo 1366502 2050679 := bstep (se 1 (by rfl) ⟨1538009, by rfl⟩ : syracuseStep 2050679 = 3076019) B3076019
theorem B2050703 : Blo 1366502 2050703 := bstep (se 1 (by rfl) ⟨1538027, by rfl⟩ : syracuseStep 2050703 = 3076055) B3076055
theorem B2050745 : Blo 1366502 2050745 := bstep (se 2 (by rfl) ⟨769029, by rfl⟩ : syracuseStep 2050745 = 1538059) B1538059
theorem B2050823 : Blo 1366502 2050823 := bstep (se 1 (by rfl) ⟨1538117, by rfl⟩ : syracuseStep 2050823 = 3076235) B3076235
theorem B3074831 : Blo 1366502 3074831 := bstep (se 1 (by rfl) ⟨2306123, by rfl⟩ : syracuseStep 3074831 = 4612247) B4612247
theorem B3074849 : Blo 1366502 3074849 := bstep (se 2 (by rfl) ⟨1153068, by rfl⟩ : syracuseStep 3074849 = 2306137) B2306137
theorem B2050859 : Blo 1366502 2050859 := bstep (se 1 (by rfl) ⟨1538144, by rfl⟩ : syracuseStep 2050859 = 3076289) B3076289
theorem B2050889 : Blo 1366502 2050889 := bstep (se 2 (by rfl) ⟨769083, by rfl⟩ : syracuseStep 2050889 = 1538167) B1538167
theorem B4156247 : Blo 1366502 4156247 := bstep (se 1 (by rfl) ⟨3117185, by rfl⟩ : syracuseStep 4156247 = 6234371) B6234371
theorem B3459955 : Blo 1366502 3459955 := bstep (se 1 (by rfl) ⟨2594966, by rfl⟩ : syracuseStep 3459955 = 5189933) B5189933
theorem B3287927 : Blo 1366502 3287927 := bstep (se 1 (by rfl) ⟨2465945, by rfl⟩ : syracuseStep 3287927 = 4931891) B4931891
theorem B4680595 : Blo 1366502 4680595 := bstep (se 1 (by rfl) ⟨3510446, by rfl⟩ : syracuseStep 4680595 = 7020893) B7020893
theorem B2051003 : Blo 1366502 2051003 := bstep (se 1 (by rfl) ⟨1538252, by rfl⟩ : syracuseStep 2051003 = 3076505) B3076505
theorem B2051063 : Blo 1366502 2051063 := bstep (se 1 (by rfl) ⟨1538297, by rfl⟩ : syracuseStep 2051063 = 3076595) B3076595
theorem B3460097 : Blo 1366502 3460097 := bstep (se 2 (by rfl) ⟨1297536, by rfl⟩ : syracuseStep 3460097 = 2595073) B2595073
theorem B5336075 : Blo 1366502 5336075 := bstep (se 1 (by rfl) ⟨4002056, by rfl⟩ : syracuseStep 5336075 = 8004113) B8004113
theorem B2051087 : Blo 1366502 2051087 := bstep (se 1 (by rfl) ⟨1538315, by rfl⟩ : syracuseStep 2051087 = 3076631) B3076631
theorem B2051129 : Blo 1366502 2051129 := bstep (se 2 (by rfl) ⟨769173, by rfl⟩ : syracuseStep 2051129 = 1538347) B1538347
theorem B2190395 : Blo 1366502 2190395 := bstep (se 1 (by rfl) ⟨1642796, by rfl⟩ : syracuseStep 2190395 = 3285593) B3285593
theorem B3075191 : Blo 1366502 3075191 := bstep (se 1 (by rfl) ⟨2306393, by rfl⟩ : syracuseStep 3075191 = 4612787) B4612787
theorem B2051207 : Blo 1366502 2051207 := bstep (se 1 (by rfl) ⟨1538405, by rfl⟩ : syracuseStep 2051207 = 3076811) B3076811
theorem B1731719 : Blo 1366502 1731719 := bstep (se 1 (by rfl) ⟨1298789, by rfl⟩ : syracuseStep 1731719 = 2597579) B2597579
theorem B2051243 : Blo 1366502 2051243 := bstep (se 1 (by rfl) ⟨1538432, by rfl⟩ : syracuseStep 2051243 = 3076865) B3076865
theorem B2051273 : Blo 1366502 2051273 := bstep (se 2 (by rfl) ⟨769227, by rfl⟩ : syracuseStep 2051273 = 1538455) B1538455
theorem B7793921 : Blo 1366502 7793921 := bstep (se 2 (by rfl) ⟨2922720, by rfl⟩ : syracuseStep 7793921 = 5845441) B5845441
theorem B3075371 : Blo 1366502 3075371 := bstep (se 1 (by rfl) ⟨2306528, by rfl⟩ : syracuseStep 3075371 = 4613057) B4613057
theorem B2051387 : Blo 1366502 2051387 := bstep (se 1 (by rfl) ⟨1538540, by rfl⟩ : syracuseStep 2051387 = 3077081) B3077081
theorem B2051447 : Blo 1366502 2051447 := bstep (se 1 (by rfl) ⟨1538585, by rfl⟩ : syracuseStep 2051447 = 3077171) B3077171
theorem B2051471 : Blo 1366502 2051471 := bstep (se 1 (by rfl) ⟨1538603, by rfl⟩ : syracuseStep 2051471 = 3077207) B3077207
theorem B7785881 : Blo 1366502 7785881 := bstep (se 2 (by rfl) ⟨2919705, by rfl⟩ : syracuseStep 7785881 = 5839411) B5839411
theorem B2051513 : Blo 1366502 2051513 := bstep (se 2 (by rfl) ⟨769317, by rfl⟩ : syracuseStep 2051513 = 1538635) B1538635
theorem B3460553 : Blo 1366502 3460553 := bstep (se 2 (by rfl) ⟨1297707, by rfl⟩ : syracuseStep 3460553 = 2595415) B2595415
theorem B2051591 : Blo 1366502 2051591 := bstep (se 1 (by rfl) ⟨1538693, by rfl⟩ : syracuseStep 2051591 = 3077387) B3077387
theorem B2919979 : Blo 1366502 2919979 := bstep (se 1 (by rfl) ⟨2189984, by rfl⟩ : syracuseStep 2919979 = 4379969) B4379969
theorem B2051627 : Blo 1366502 2051627 := bstep (se 1 (by rfl) ⟨1538720, by rfl⟩ : syracuseStep 2051627 = 3077441) B3077441
theorem B2051657 : Blo 1366502 2051657 := bstep (se 2 (by rfl) ⟨769371, by rfl⟩ : syracuseStep 2051657 = 1538743) B1538743
theorem B3698291 : Blo 1366502 3698291 := bstep (se 1 (by rfl) ⟨2773718, by rfl⟩ : syracuseStep 3698291 = 5547437) B5547437
theorem B2920055 : Blo 1366502 2920055 := bstep (se 1 (by rfl) ⟨2190041, by rfl⟩ : syracuseStep 2920055 = 4380083) B4380083
theorem B3075731 : Blo 1366502 3075731 := bstep (se 1 (by rfl) ⟨2306798, by rfl⟩ : syracuseStep 3075731 = 4613597) B4613597
theorem B2051771 : Blo 1366502 2051771 := bstep (se 1 (by rfl) ⟨1538828, by rfl⟩ : syracuseStep 2051771 = 3077657) B3077657
theorem B3075785 : Blo 1366502 3075785 := bstep (se 2 (by rfl) ⟨1153419, by rfl⟩ : syracuseStep 3075785 = 2306839) B2306839
theorem B2051831 : Blo 1366502 2051831 := bstep (se 1 (by rfl) ⟨1538873, by rfl⟩ : syracuseStep 2051831 = 3077747) B3077747
theorem B2051855 : Blo 1366502 2051855 := bstep (se 1 (by rfl) ⟨1538891, by rfl⟩ : syracuseStep 2051855 = 3077783) B3077783
theorem B3460907 : Blo 1366502 3460907 := bstep (se 1 (by rfl) ⟨2595680, by rfl⟩ : syracuseStep 3460907 = 5191361) B5191361
theorem B2051897 : Blo 1366502 2051897 := bstep (se 2 (by rfl) ⟨769461, by rfl⟩ : syracuseStep 2051897 = 1538923) B1538923
theorem B11849561 : Blo 1366502 11849561 := bstep (se 2 (by rfl) ⟨4443585, by rfl⟩ : syracuseStep 11849561 = 8887171) B8887171
theorem B3698551 : Blo 1366502 3698551 := bstep (se 1 (by rfl) ⟨2773913, by rfl⟩ : syracuseStep 3698551 = 5547827) B5547827
theorem B2051975 : Blo 1366502 2051975 := bstep (se 1 (by rfl) ⟨1538981, by rfl⟩ : syracuseStep 2051975 = 3077963) B3077963
theorem B2052011 : Blo 1366502 2052011 := bstep (se 1 (by rfl) ⟨1539008, by rfl⟩ : syracuseStep 2052011 = 3078017) B3078017
theorem B379097009 : Blo 1366502 379097009 := bstep (se 2 (by rfl) ⟨142161378, by rfl⟩ : syracuseStep 379097009 = 284322757) B284322757
theorem B2052041 : Blo 1366502 2052041 := bstep (se 2 (by rfl) ⟨769515, by rfl⟩ : syracuseStep 2052041 = 1539031) B1539031
theorem B5541841 : Blo 1366502 5541841 := bstep (se 2 (by rfl) ⟨2078190, by rfl⟩ : syracuseStep 5541841 = 4156381) B4156381
theorem B2306063 : Blo 1366502 2306063 := bstep (se 1 (by rfl) ⟨1729547, by rfl⟩ : syracuseStep 2306063 = 3459095) B3459095
theorem B9359383 : Blo 1366502 9359383 := bstep (se 1 (by rfl) ⟨7019537, by rfl⟩ : syracuseStep 9359383 = 14039075) B14039075
theorem B2052155 : Blo 1366502 2052155 := bstep (se 1 (by rfl) ⟨1539116, by rfl⟩ : syracuseStep 2052155 = 3078233) B3078233
theorem B2052215 : Blo 1366502 2052215 := bstep (se 1 (by rfl) ⟨1539161, by rfl⟩ : syracuseStep 2052215 = 3078323) B3078323
theorem B2052239 : Blo 1366502 2052239 := bstep (se 1 (by rfl) ⟨1539179, by rfl⟩ : syracuseStep 2052239 = 3078359) B3078359
theorem B2052281 : Blo 1366502 2052281 := bstep (se 2 (by rfl) ⟨769605, by rfl⟩ : syracuseStep 2052281 = 1539211) B1539211
theorem B2052359 : Blo 1366502 2052359 := bstep (se 1 (by rfl) ⟨1539269, by rfl⟩ : syracuseStep 2052359 = 3078539) B3078539
theorem B5189903 : Blo 1366502 5189903 := bstep (se 1 (by rfl) ⟨3892427, by rfl⟩ : syracuseStep 5189903 = 7784855) B7784855
theorem B1847567 : Blo 1366502 1847567 := bstep (se 1 (by rfl) ⟨1385675, by rfl⟩ : syracuseStep 1847567 = 2771351) B2771351
theorem B2052395 : Blo 1366502 2052395 := bstep (se 1 (by rfl) ⟨1539296, by rfl⟩ : syracuseStep 2052395 = 3078593) B3078593
theorem B2052425 : Blo 1366502 2052425 := bstep (se 2 (by rfl) ⟨769659, by rfl⟩ : syracuseStep 2052425 = 1539319) B1539319
theorem B3076487 : Blo 1366502 3076487 := bstep (se 1 (by rfl) ⟨2307365, by rfl⟩ : syracuseStep 3076487 = 4614731) B4614731
theorem B2052539 : Blo 1366502 2052539 := bstep (se 1 (by rfl) ⟨1539404, by rfl⟩ : syracuseStep 2052539 = 3078809) B3078809
theorem B6926795 : Blo 1366502 6926795 := bstep (se 1 (by rfl) ⟨5195096, by rfl⟩ : syracuseStep 6926795 = 10390193) B10390193
theorem B2052599 : Blo 1366502 2052599 := bstep (se 1 (by rfl) ⟨1539449, by rfl⟩ : syracuseStep 2052599 = 3078899) B3078899
theorem B10383875 : Blo 1366502 10383875 := bstep (se 1 (by rfl) ⟨7787906, by rfl⟩ : syracuseStep 10383875 = 15575813) B15575813
theorem B2052623 : Blo 1366502 2052623 := bstep (se 1 (by rfl) ⟨1539467, by rfl⟩ : syracuseStep 2052623 = 3078935) B3078935
theorem B159896081 : Blo 1366502 159896081 := bstep (se 2 (by rfl) ⟨59961030, by rfl⟩ : syracuseStep 159896081 = 119922061) B119922061
theorem B2306603 : Blo 1366502 2306603 := bstep (se 1 (by rfl) ⟨1729952, by rfl⟩ : syracuseStep 2306603 = 3459905) B3459905
theorem B113865259 : Blo 1366502 113865259 := bstep (se 1 (by rfl) ⟨85398944, by rfl⟩ : syracuseStep 113865259 = 170797889) B170797889
theorem B2052665 : Blo 1366502 2052665 := bstep (se 2 (by rfl) ⟨769749, by rfl⟩ : syracuseStep 2052665 = 1539499) B1539499
theorem B3076667 : Blo 1366502 3076667 := bstep (se 1 (by rfl) ⟨2307500, by rfl⟩ : syracuseStep 3076667 = 4615001) B4615001
theorem B3895867 : Blo 1366502 3895867 := bstep (se 1 (by rfl) ⟨2921900, by rfl⟩ : syracuseStep 3895867 = 5843801) B5843801
theorem B2052743 : Blo 1366502 2052743 := bstep (se 1 (by rfl) ⟨1539557, by rfl⟩ : syracuseStep 2052743 = 3079115) B3079115
theorem B3076793 : Blo 1366502 3076793 := bstep (se 2 (by rfl) ⟨1153797, by rfl⟩ : syracuseStep 3076793 = 2307595) B2307595
theorem B6918857 : Blo 1366502 6918857 := bstep (se 2 (by rfl) ⟨2594571, by rfl⟩ : syracuseStep 6918857 = 5189143) B5189143
theorem B3461899 : Blo 1366502 3461899 := bstep (se 1 (by rfl) ⟨2596424, by rfl⟩ : syracuseStep 3461899 = 5192849) B5192849
theorem B6927119 : Blo 1366502 6927119 := bstep (se 1 (by rfl) ⟨5195339, by rfl⟩ : syracuseStep 6927119 = 10390679) B10390679
theorem B26645285 : Blo 1366502 26645285 := bstep (se 4 (by rfl) ⟨2497995, by rfl⟩ : syracuseStep 26645285 = 4995991) B4995991
theorem B1946425 : Blo 1366502 1946425 := bstep (se 2 (by rfl) ⟨729909, by rfl⟩ : syracuseStep 1946425 = 1459819) B1459819
theorem B5264243 : Blo 1366502 5264243 := bstep (se 1 (by rfl) ⟨3948182, by rfl⟩ : syracuseStep 5264243 = 7896365) B7896365
theorem B4617107 : Blo 1366502 4617107 := bstep (se 1 (by rfl) ⟨3462830, by rfl⟩ : syracuseStep 4617107 = 6925661) B6925661
theorem B3462041 : Blo 1366502 3462041 := bstep (se 2 (by rfl) ⟨1298265, by rfl⟩ : syracuseStep 3462041 = 2596531) B2596531
theorem B2307001 : Blo 1366502 2307001 := bstep (se 2 (by rfl) ⟨865125, by rfl⟩ : syracuseStep 2307001 = 1730251) B1730251
theorem B1643527 : Blo 1366502 1643527 := bstep (se 1 (by rfl) ⟨1232645, by rfl⟩ : syracuseStep 1643527 = 2465291) B2465291
theorem B6239243 : Blo 1366502 6239243 := bstep (se 1 (by rfl) ⟨4679432, by rfl⟩ : syracuseStep 6239243 = 9358865) B9358865
theorem B3077135 : Blo 1366502 3077135 := bstep (se 1 (by rfl) ⟨2307851, by rfl⟩ : syracuseStep 3077135 = 4615703) B4615703
theorem B3077153 : Blo 1366502 3077153 := bstep (se 2 (by rfl) ⟨1153932, by rfl⟩ : syracuseStep 3077153 = 2307865) B2307865
theorem B3462203 : Blo 1366502 3462203 := bstep (se 1 (by rfl) ⟨2596652, by rfl⟩ : syracuseStep 3462203 = 5193305) B5193305
theorem B15569981 : Blo 1366502 15569981 := bstep (se 3 (by rfl) ⟨2919371, by rfl⟩ : syracuseStep 15569981 = 5838743) B5838743
theorem B5838095 : Blo 1366502 5838095 := bstep (se 1 (by rfl) ⟨4378571, by rfl⟩ : syracuseStep 5838095 = 8757143) B8757143
theorem B37418273 : Blo 1366502 37418273 := bstep (se 2 (by rfl) ⟨14031852, by rfl⟩ : syracuseStep 37418273 = 28063705) B28063705
theorem B1643819 : Blo 1366502 1643819 := bstep (se 1 (by rfl) ⟨1232864, by rfl⟩ : syracuseStep 1643819 = 2465729) B2465729
theorem B1537339 : Blo 1366502 1537339 := bstep (se 1 (by rfl) ⟨1153004, by rfl⟩ : syracuseStep 1537339 = 2306009) B2306009
theorem B26645861 : Blo 1366502 26645861 := bstep (se 4 (by rfl) ⟨2498049, by rfl⟩ : syracuseStep 26645861 = 4996099) B4996099
theorem B3077495 : Blo 1366502 3077495 := bstep (se 1 (by rfl) ⟨2308121, by rfl⟩ : syracuseStep 3077495 = 4616243) B4616243
theorem B3896711 : Blo 1366502 3896711 := bstep (se 1 (by rfl) ⟨2922533, by rfl⟩ : syracuseStep 3896711 = 5845067) B5845067
theorem B3462547 : Blo 1366502 3462547 := bstep (se 1 (by rfl) ⟨2596910, by rfl⟩ : syracuseStep 3462547 = 5193821) B5193821
theorem B4928921 : Blo 1366502 4928921 := bstep (se 2 (by rfl) ⟨1848345, by rfl⟩ : syracuseStep 4928921 = 3696691) B3696691
theorem B23352785 : Blo 1366502 23352785 := bstep (se 2 (by rfl) ⟨8757294, by rfl⟩ : syracuseStep 23352785 = 17514589) B17514589
theorem B3462689 : Blo 1366502 3462689 := bstep (se 2 (by rfl) ⟨1298508, by rfl⟩ : syracuseStep 3462689 = 2597017) B2597017
theorem B3077675 : Blo 1366502 3077675 := bstep (se 1 (by rfl) ⟨2308256, by rfl⟩ : syracuseStep 3077675 = 4616513) B4616513
theorem B2307703 : Blo 1366502 2307703 := bstep (se 1 (by rfl) ⟨1730777, by rfl⟩ : syracuseStep 2307703 = 3461555) B3461555
theorem B7894721 : Blo 1366502 7894721 := bstep (se 2 (by rfl) ⟨2960520, by rfl⟩ : syracuseStep 7894721 = 5921041) B5921041
theorem B1537807 : Blo 1366502 1537807 := bstep (se 1 (by rfl) ⟨1153355, by rfl⟩ : syracuseStep 1537807 = 2306711) B2306711
theorem B18716467 : Blo 1366502 18716467 := bstep (se 1 (by rfl) ⟨14037350, by rfl⟩ : syracuseStep 18716467 = 28074701) B28074701
theorem B2307899 : Blo 1366502 2307899 := bstep (se 1 (by rfl) ⟨1730924, by rfl⟩ : syracuseStep 2307899 = 3461849) B3461849
theorem B5191559 : Blo 1366502 5191559 := bstep (se 1 (by rfl) ⟨3893669, by rfl⟩ : syracuseStep 5191559 = 7787339) B7787339
theorem B3078035 : Blo 1366502 3078035 := bstep (se 1 (by rfl) ⟨2308526, by rfl⟩ : syracuseStep 3078035 = 4617053) B4617053
theorem B3078089 : Blo 1366502 3078089 := bstep (se 2 (by rfl) ⟨1154283, by rfl⟩ : syracuseStep 3078089 = 2308567) B2308567
theorem B1947655 : Blo 1366502 1947655 := bstep (se 1 (by rfl) ⟨1460741, by rfl⟩ : syracuseStep 1947655 = 2921483) B2921483
theorem B29571095 : Blo 1366502 29571095 := bstep (se 1 (by rfl) ⟨22178321, by rfl⟩ : syracuseStep 29571095 = 44356643) B44356643
theorem B11089943 : Blo 1366502 11089943 := bstep (se 1 (by rfl) ⟨8317457, by rfl⟩ : syracuseStep 11089943 = 16634915) B16634915
theorem B7395371 : Blo 1366502 7395371 := bstep (se 1 (by rfl) ⟨5546528, by rfl⟩ : syracuseStep 7395371 = 11093057) B11093057
theorem B14784599 : Blo 1366502 14784599 := bstep (se 1 (by rfl) ⟨11088449, by rfl⟩ : syracuseStep 14784599 = 22176899) B22176899
theorem B24320173 : Blo 1366502 24320173 := bstep (se 3 (by rfl) ⟨4560032, by rfl⟩ : syracuseStep 24320173 = 9120065) B9120065
theorem B2308297 : Blo 1366502 2308297 := bstep (se 2 (by rfl) ⟨865611, by rfl⟩ : syracuseStep 2308297 = 1731223) B1731223
theorem B1538311 : Blo 1366502 1538311 := bstep (se 1 (by rfl) ⟨1153733, by rfl⟩ : syracuseStep 1538311 = 2307467) B2307467
theorem B4618511 : Blo 1366502 4618511 := bstep (se 1 (by rfl) ⟨3463883, by rfl⟩ : syracuseStep 4618511 = 6927767) B6927767
theorem B1538491 : Blo 1366502 1538491 := bstep (se 1 (by rfl) ⟨1153868, by rfl⟩ : syracuseStep 1538491 = 2307737) B2307737
theorem B3463681 : Blo 1366502 3463681 := bstep (se 2 (by rfl) ⟨1298880, by rfl⟩ : syracuseStep 3463681 = 2597761) B2597761
theorem B1366535 : Blo 1366502 1366535 := bstep (se 1 (by rfl) ⟨1024901, by rfl⟩ : syracuseStep 1366535 = 2049803) B2049803
theorem B1366543 : Blo 1366502 1366543 := bstep (se 1 (by rfl) ⟨1024907, by rfl⟩ : syracuseStep 1366543 = 2049815) B2049815
theorem B1366587 : Blo 1366502 1366587 := bstep (se 1 (by rfl) ⟨1024940, by rfl⟩ : syracuseStep 1366587 = 2049881) B2049881
theorem B5839427 : Blo 1366502 5839427 := bstep (se 1 (by rfl) ⟨4379570, by rfl⟩ : syracuseStep 5839427 = 8759141) B8759141
theorem B7895639 : Blo 1366502 7895639 := bstep (se 1 (by rfl) ⟨5921729, by rfl⟩ : syracuseStep 7895639 = 11843459) B11843459
theorem B22166135 : Blo 1366502 22166135 := bstep (se 1 (by rfl) ⟨16624601, by rfl⟩ : syracuseStep 22166135 = 33249203) B33249203
theorem B1366663 : Blo 1366502 1366663 := bstep (se 1 (by rfl) ⟨1024997, by rfl⟩ : syracuseStep 1366663 = 2049995) B2049995
theorem B3078791 : Blo 1366502 3078791 := bstep (se 1 (by rfl) ⟨2309093, by rfl⟩ : syracuseStep 3078791 = 4618187) B4618187
theorem B1366671 : Blo 1366502 1366671 := bstep (se 1 (by rfl) ⟨1025003, by rfl⟩ : syracuseStep 1366671 = 2050007) B2050007
theorem B7789229 : Blo 1366502 7789229 := bstep (se 3 (by rfl) ⟨1460480, by rfl⟩ : syracuseStep 7789229 = 2920961) B2920961
theorem B1366715 : Blo 1366502 1366715 := bstep (se 1 (by rfl) ⟨1025036, by rfl⟩ : syracuseStep 1366715 = 2050073) B2050073
theorem B1366791 : Blo 1366502 1366791 := bstep (se 1 (by rfl) ⟨1025093, by rfl⟩ : syracuseStep 1366791 = 2050187) B2050187
theorem B1366799 : Blo 1366502 1366799 := bstep (se 1 (by rfl) ⟨1025099, by rfl⟩ : syracuseStep 1366799 = 2050199) B2050199
theorem B12466993 : Blo 1366502 12466993 := bstep (se 2 (by rfl) ⟨4675122, by rfl⟩ : syracuseStep 12466993 = 9350245) B9350245
theorem B1366843 : Blo 1366502 1366843 := bstep (se 1 (by rfl) ⟨1025132, by rfl⟩ : syracuseStep 1366843 = 2050265) B2050265
theorem B3078971 : Blo 1366502 3078971 := bstep (se 1 (by rfl) ⟨2309228, by rfl⟩ : syracuseStep 3078971 = 4618457) B4618457
theorem B1948475 : Blo 1366502 1948475 := bstep (se 1 (by rfl) ⟨1461356, by rfl⟩ : syracuseStep 1948475 = 2922713) B2922713
theorem B1366919 : Blo 1366502 1366919 := bstep (se 1 (by rfl) ⟨1025189, by rfl⟩ : syracuseStep 1366919 = 2050379) B2050379
theorem B2595719 : Blo 1366502 2595719 := bstep (se 1 (by rfl) ⟨1946789, by rfl⟩ : syracuseStep 2595719 = 3893579) B3893579
theorem B2308999 : Blo 1366502 2308999 := bstep (se 1 (by rfl) ⟨1731749, by rfl⟩ : syracuseStep 2308999 = 3463499) B3463499
theorem B1366927 : Blo 1366502 1366927 := bstep (se 1 (by rfl) ⟨1025195, by rfl⟩ : syracuseStep 1366927 = 2050391) B2050391
theorem B1538959 : Blo 1366502 1538959 := bstep (se 1 (by rfl) ⟨1154219, by rfl⟩ : syracuseStep 1538959 = 2308439) B2308439
theorem B5839769 : Blo 1366502 5839769 := bstep (se 2 (by rfl) ⟨2189913, by rfl⟩ : syracuseStep 5839769 = 4379827) B4379827
theorem B3079097 : Blo 1366502 3079097 := bstep (se 2 (by rfl) ⟨1154661, by rfl⟩ : syracuseStep 3079097 = 2309323) B2309323
theorem B1366971 : Blo 1366502 1366971 := bstep (se 1 (by rfl) ⟨1025228, by rfl⟩ : syracuseStep 1366971 = 2050457) B2050457
theorem B1367047 : Blo 1366502 1367047 := bstep (se 1 (by rfl) ⟨1025285, by rfl⟩ : syracuseStep 1367047 = 2050571) B2050571
theorem B1367055 : Blo 1366502 1367055 := bstep (se 1 (by rfl) ⟨1025291, by rfl⟩ : syracuseStep 1367055 = 2050583) B2050583
theorem B8428573 : Blo 1366502 8428573 := bstep (se 3 (by rfl) ⟨1580357, by rfl⟩ : syracuseStep 8428573 = 3160715) B3160715
theorem B1367099 : Blo 1366502 1367099 := bstep (se 1 (by rfl) ⟨1025324, by rfl⟩ : syracuseStep 1367099 = 2050649) B2050649
theorem B2079803 : Blo 1366502 2079803 := bstep (se 1 (by rfl) ⟨1559852, by rfl⟩ : syracuseStep 2079803 = 3119705) B3119705
theorem B1367175 : Blo 1366502 1367175 := bstep (se 1 (by rfl) ⟨1025381, by rfl⟩ : syracuseStep 1367175 = 2050763) B2050763
theorem B1367183 : Blo 1366502 1367183 := bstep (se 1 (by rfl) ⟨1025387, by rfl⟩ : syracuseStep 1367183 = 2050775) B2050775
theorem B1367227 : Blo 1366502 1367227 := bstep (se 1 (by rfl) ⟨1025420, by rfl⟩ : syracuseStep 1367227 = 2050841) B2050841
theorem B1367303 : Blo 1366502 1367303 := bstep (se 1 (by rfl) ⟨1025477, by rfl⟩ : syracuseStep 1367303 = 2050955) B2050955
theorem B1367311 : Blo 1366502 1367311 := bstep (se 1 (by rfl) ⟨1025483, by rfl⟩ : syracuseStep 1367311 = 2050967) B2050967
theorem B10378529 : Blo 1366502 10378529 := bstep (se 2 (by rfl) ⟨3891948, by rfl⟩ : syracuseStep 10378529 = 7783897) B7783897
theorem B1367355 : Blo 1366502 1367355 := bstep (se 1 (by rfl) ⟨1025516, by rfl⟩ : syracuseStep 1367355 = 2051033) B2051033
theorem B1367431 : Blo 1366502 1367431 := bstep (se 1 (by rfl) ⟨1025573, by rfl⟩ : syracuseStep 1367431 = 2051147) B2051147
theorem B1539463 : Blo 1366502 1539463 := bstep (se 1 (by rfl) ⟨1154597, by rfl⟩ : syracuseStep 1539463 = 2309195) B2309195
theorem B1367439 : Blo 1366502 1367439 := bstep (se 1 (by rfl) ⟨1025579, by rfl⟩ : syracuseStep 1367439 = 2051159) B2051159
theorem B7396753 : Blo 1366502 7396753 := bstep (se 2 (by rfl) ⟨2773782, by rfl⟩ : syracuseStep 7396753 = 5547565) B5547565
theorem B1367483 : Blo 1366502 1367483 := bstep (se 1 (by rfl) ⟨1025612, by rfl⟩ : syracuseStep 1367483 = 2051225) B2051225
theorem B13139405 : Blo 1366502 13139405 := bstep (se 3 (by rfl) ⟨2463638, by rfl⟩ : syracuseStep 13139405 = 4927277) B4927277
theorem B1367559 : Blo 1366502 1367559 := bstep (se 1 (by rfl) ⟨1025669, by rfl⟩ : syracuseStep 1367559 = 2051339) B2051339
theorem B1367567 : Blo 1366502 1367567 := bstep (se 1 (by rfl) ⟨1025675, by rfl⟩ : syracuseStep 1367567 = 2051351) B2051351
theorem B4161053 : Blo 1366502 4161053 := bstep (se 3 (by rfl) ⟨780197, by rfl⟩ : syracuseStep 4161053 = 1560395) B1560395
theorem B3694139 : Blo 1366502 3694139 := bstep (se 1 (by rfl) ⟨2770604, by rfl⟩ : syracuseStep 3694139 = 5541209) B5541209
theorem B1367611 : Blo 1366502 1367611 := bstep (se 1 (by rfl) ⟨1025708, by rfl⟩ : syracuseStep 1367611 = 2051417) B2051417
theorem B6323779 : Blo 1366502 6323779 := bstep (se 1 (by rfl) ⟨4742834, by rfl⟩ : syracuseStep 6323779 = 9485669) B9485669
theorem B134790749 : Blo 1366502 134790749 := bstep (se 3 (by rfl) ⟨25273265, by rfl⟩ : syracuseStep 134790749 = 50546531) B50546531
theorem B5193335 : Blo 1366502 5193335 := bstep (se 1 (by rfl) ⟨3895001, by rfl⟩ : syracuseStep 5193335 = 7790003) B7790003
theorem B1367687 : Blo 1366502 1367687 := bstep (se 1 (by rfl) ⟨1025765, by rfl⟩ : syracuseStep 1367687 = 2051531) B2051531
theorem B1367695 : Blo 1366502 1367695 := bstep (se 1 (by rfl) ⟨1025771, by rfl⟩ : syracuseStep 1367695 = 2051543) B2051543
theorem B13139633 : Blo 1366502 13139633 := bstep (se 2 (by rfl) ⟨4927362, by rfl⟩ : syracuseStep 13139633 = 9854725) B9854725
theorem B1367739 : Blo 1366502 1367739 := bstep (se 1 (by rfl) ⟨1025804, by rfl⟩ : syracuseStep 1367739 = 2051609) B2051609
theorem B10665665 : Blo 1366502 10665665 := bstep (se 2 (by rfl) ⟨3999624, by rfl⟩ : syracuseStep 10665665 = 7999249) B7999249
theorem B1367815 : Blo 1366502 1367815 := bstep (se 1 (by rfl) ⟨1025861, by rfl⟩ : syracuseStep 1367815 = 2051723) B2051723
theorem B1367823 : Blo 1366502 1367823 := bstep (se 1 (by rfl) ⟨1025867, by rfl⟩ : syracuseStep 1367823 = 2051735) B2051735
theorem B2465579 : Blo 1366502 2465579 := bstep (se 1 (by rfl) ⟨1849184, by rfl⟩ : syracuseStep 2465579 = 3698369) B3698369
theorem B1367867 : Blo 1366502 1367867 := bstep (se 1 (by rfl) ⟨1025900, by rfl⟩ : syracuseStep 1367867 = 2051801) B2051801
theorem B33251147 : Blo 1366502 33251147 := bstep (se 1 (by rfl) ⟨24938360, by rfl⟩ : syracuseStep 33251147 = 49876721) B49876721
theorem B1367943 : Blo 1366502 1367943 := bstep (se 1 (by rfl) ⟨1025957, by rfl⟩ : syracuseStep 1367943 = 2051915) B2051915
theorem B1367951 : Blo 1366502 1367951 := bstep (se 1 (by rfl) ⟨1025963, by rfl⟩ : syracuseStep 1367951 = 2051927) B2051927
theorem B1367995 : Blo 1366502 1367995 := bstep (se 1 (by rfl) ⟨1025996, by rfl⟩ : syracuseStep 1367995 = 2051993) B2051993
theorem B2596873 : Blo 1366502 2596873 := bstep (se 2 (by rfl) ⟨973827, by rfl⟩ : syracuseStep 2596873 = 1947655) B1947655
theorem B14229533 : Blo 1366502 14229533 := bstep (se 3 (by rfl) ⟨2668037, by rfl⟩ : syracuseStep 14229533 = 5336075) B5336075
theorem B1368103 : Blo 1366502 1368103 := bstep (se 1 (by rfl) ⟨1026077, by rfl⟩ : syracuseStep 1368103 = 2052155) B2052155
theorem B1368143 : Blo 1366502 1368143 := bstep (se 1 (by rfl) ⟨1026107, by rfl⟩ : syracuseStep 1368143 = 2052215) B2052215
theorem B1368159 : Blo 1366502 1368159 := bstep (se 1 (by rfl) ⟨1026119, by rfl⟩ : syracuseStep 1368159 = 2052239) B2052239
theorem B1368187 : Blo 1366502 1368187 := bstep (se 1 (by rfl) ⟨1026140, by rfl⟩ : syracuseStep 1368187 = 2052281) B2052281
theorem B5546141 : Blo 1366502 5546141 := bstep (se 3 (by rfl) ⟨1039901, by rfl⟩ : syracuseStep 5546141 = 2079803) B2079803
theorem B1368239 : Blo 1366502 1368239 := bstep (se 1 (by rfl) ⟨1026179, by rfl⟩ : syracuseStep 1368239 = 2052359) B2052359
theorem B1368263 : Blo 1366502 1368263 := bstep (se 1 (by rfl) ⟨1026197, by rfl⟩ : syracuseStep 1368263 = 2052395) B2052395
theorem B1368283 : Blo 1366502 1368283 := bstep (se 1 (by rfl) ⟨1026212, by rfl⟩ : syracuseStep 1368283 = 2052425) B2052425
theorem B1368359 : Blo 1366502 1368359 := bstep (se 1 (by rfl) ⟨1026269, by rfl⟩ : syracuseStep 1368359 = 2052539) B2052539
theorem B10387763 : Blo 1366502 10387763 := bstep (se 1 (by rfl) ⟨7790822, by rfl⟩ : syracuseStep 10387763 = 15581645) B15581645
theorem B1368399 : Blo 1366502 1368399 := bstep (se 1 (by rfl) ⟨1026299, by rfl⟩ : syracuseStep 1368399 = 2052599) B2052599
theorem B6922583 : Blo 1366502 6922583 := bstep (se 1 (by rfl) ⟨5191937, by rfl⟩ : syracuseStep 6922583 = 10383875) B10383875
theorem B1368415 : Blo 1366502 1368415 := bstep (se 1 (by rfl) ⟨1026311, by rfl⟩ : syracuseStep 1368415 = 2052623) B2052623
theorem B1368443 : Blo 1366502 1368443 := bstep (se 1 (by rfl) ⟨1026332, by rfl⟩ : syracuseStep 1368443 = 2052665) B2052665
theorem B1368495 : Blo 1366502 1368495 := bstep (se 1 (by rfl) ⟨1026371, by rfl⟩ : syracuseStep 1368495 = 2052743) B2052743
theorem B4612571 : Blo 1366502 4612571 := bstep (se 1 (by rfl) ⟨3459428, by rfl⟩ : syracuseStep 4612571 = 6918857) B6918857
theorem B3891721 : Blo 1366502 3891721 := bstep (se 2 (by rfl) ⟨1459395, by rfl⟩ : syracuseStep 3891721 = 2918791) B2918791
theorem B10379987 : Blo 1366502 10379987 := bstep (se 1 (by rfl) ⟨7784990, by rfl⟩ : syracuseStep 10379987 = 15569981) B15569981
theorem B3556055 : Blo 1366502 3556055 := bstep (se 1 (by rfl) ⟨2667041, by rfl⟩ : syracuseStep 3556055 = 5334083) B5334083
theorem B5194489 : Blo 1366502 5194489 := bstep (se 2 (by rfl) ⟨1947933, by rfl⟩ : syracuseStep 5194489 = 3895867) B3895867
theorem B3892063 : Blo 1366502 3892063 := bstep (se 1 (by rfl) ⟨2919047, by rfl⟩ : syracuseStep 3892063 = 5838095) B5838095
theorem B24945515 : Blo 1366502 24945515 := bstep (se 1 (by rfl) ⟨18709136, by rfl⟩ : syracuseStep 24945515 = 37418273) B37418273
theorem B37421999 : Blo 1366502 37421999 := bstep (se 1 (by rfl) ⟨28066499, by rfl⟩ : syracuseStep 37421999 = 56132999) B56132999
theorem B2597807 : Blo 1366502 2597807 := bstep (se 1 (by rfl) ⟨1948355, by rfl⟩ : syracuseStep 2597807 = 3896711) B3896711
theorem B3285947 : Blo 1366502 3285947 := bstep (se 1 (by rfl) ⟨2464460, by rfl⟩ : syracuseStep 3285947 = 4928921) B4928921
theorem B7783397 : Blo 1366502 7783397 := bstep (se 4 (by rfl) ⟨729693, by rfl⟩ : syracuseStep 7783397 = 1459387) B1459387
theorem B16622657 : Blo 1366502 16622657 := bstep (se 2 (by rfl) ⟨6233496, by rfl⟩ : syracuseStep 16622657 = 12466993) B12466993
theorem B4613273 : Blo 1366502 4613273 := bstep (se 2 (by rfl) ⟨1729977, by rfl⟩ : syracuseStep 4613273 = 3459955) B3459955
theorem B9856399 : Blo 1366502 9856399 := bstep (se 1 (by rfl) ⟨7392299, by rfl⟩ : syracuseStep 9856399 = 14784599) B14784599
theorem B8767115 : Blo 1366502 8767115 := bstep (se 1 (by rfl) ⟨6575336, by rfl⟩ : syracuseStep 8767115 = 13150673) B13150673
theorem B3892951 : Blo 1366502 3892951 := bstep (se 1 (by rfl) ⟨2919713, by rfl⟩ : syracuseStep 3892951 = 5839427) B5839427
theorem B2049785 : Blo 1366502 2049785 := bstep (se 2 (by rfl) ⟨768669, by rfl⟩ : syracuseStep 2049785 = 1537339) B1537339
theorem B2049887 : Blo 1366502 2049887 := bstep (se 1 (by rfl) ⟨1537415, by rfl⟩ : syracuseStep 2049887 = 3074831) B3074831
theorem B2049899 : Blo 1366502 2049899 := bstep (se 1 (by rfl) ⟨1537424, by rfl⟩ : syracuseStep 2049899 = 3074849) B3074849
theorem B2770831 : Blo 1366502 2770831 := bstep (se 1 (by rfl) ⟨2078123, by rfl⟩ : syracuseStep 2770831 = 4156247) B4156247
theorem B1730479 : Blo 1366502 1730479 := bstep (se 1 (by rfl) ⟨1297859, by rfl⟩ : syracuseStep 1730479 = 2595719) B2595719
theorem B3893179 : Blo 1366502 3893179 := bstep (se 1 (by rfl) ⟨2919884, by rfl⟩ : syracuseStep 3893179 = 5839769) B5839769
theorem B1460263 : Blo 1366502 1460263 := bstep (se 1 (by rfl) ⟨1095197, by rfl⟩ : syracuseStep 1460263 = 2190395) B2190395
theorem B3893305 : Blo 1366502 3893305 := bstep (se 2 (by rfl) ⟨1459989, by rfl⟩ : syracuseStep 3893305 = 2919979) B2919979
theorem B2050127 : Blo 1366502 2050127 := bstep (se 1 (by rfl) ⟨1537595, by rfl⟩ : syracuseStep 2050127 = 3075191) B3075191
theorem B8431705 : Blo 1366502 8431705 := bstep (se 2 (by rfl) ⟨3161889, by rfl⟩ : syracuseStep 8431705 = 6323779) B6323779
theorem B5195933 : Blo 1366502 5195933 := bstep (se 3 (by rfl) ⟨974237, by rfl⟩ : syracuseStep 5195933 = 1948475) B1948475
theorem B5195947 : Blo 1366502 5195947 := bstep (se 1 (by rfl) ⟨3896960, by rfl⟩ : syracuseStep 5195947 = 7793921) B7793921
theorem B2050247 : Blo 1366502 2050247 := bstep (se 1 (by rfl) ⟨1537685, by rfl⟩ : syracuseStep 2050247 = 3075371) B3075371
theorem B8759603 : Blo 1366502 8759603 := bstep (se 1 (by rfl) ⟨6569702, by rfl⟩ : syracuseStep 8759603 = 13139405) B13139405
theorem B4614461 : Blo 1366502 4614461 := bstep (se 3 (by rfl) ⟨865211, by rfl⟩ : syracuseStep 4614461 = 1730423) B1730423
theorem B2050409 : Blo 1366502 2050409 := bstep (se 2 (by rfl) ⟨768903, by rfl⟩ : syracuseStep 2050409 = 1537807) B1537807
theorem B89860499 : Blo 1366502 89860499 := bstep (se 1 (by rfl) ⟨67395374, by rfl⟩ : syracuseStep 89860499 = 134790749) B134790749
theorem B24955289 : Blo 1366502 24955289 := bstep (se 2 (by rfl) ⟨9358233, by rfl⟩ : syracuseStep 24955289 = 18716467) B18716467
theorem B2050487 : Blo 1366502 2050487 := bstep (se 1 (by rfl) ⟨1537865, by rfl⟩ : syracuseStep 2050487 = 3075731) B3075731
theorem B8759755 : Blo 1366502 8759755 := bstep (se 1 (by rfl) ⟨6569816, by rfl⟩ : syracuseStep 8759755 = 13139633) B13139633
theorem B2050523 : Blo 1366502 2050523 := bstep (se 1 (by rfl) ⟨1537892, by rfl⟩ : syracuseStep 2050523 = 3075785) B3075785
theorem B7899707 : Blo 1366502 7899707 := bstep (se 1 (by rfl) ⟨5924780, by rfl⟩ : syracuseStep 7899707 = 11849561) B11849561
theorem B9349805 : Blo 1366502 9349805 := bstep (se 3 (by rfl) ⟨1753088, by rfl⟩ : syracuseStep 9349805 = 3506177) B3506177
theorem B3074759 : Blo 1366502 3074759 := bstep (se 1 (by rfl) ⟨2306069, by rfl⟩ : syracuseStep 3074759 = 4612139) B4612139
theorem B12479177 : Blo 1366502 12479177 := bstep (se 2 (by rfl) ⟨4679691, by rfl⟩ : syracuseStep 12479177 = 9359383) B9359383
theorem B5843785 : Blo 1366502 5843785 := bstep (se 2 (by rfl) ⟨2191419, by rfl⟩ : syracuseStep 5843785 = 4382839) B4382839
theorem B3459935 : Blo 1366502 3459935 := bstep (se 1 (by rfl) ⟨2594951, by rfl⟩ : syracuseStep 3459935 = 5189903) B5189903
theorem B32426897 : Blo 1366502 32426897 := bstep (se 2 (by rfl) ⟨12160086, by rfl⟩ : syracuseStep 32426897 = 24320173) B24320173
theorem B2050991 : Blo 1366502 2050991 := bstep (se 1 (by rfl) ⟨1538243, by rfl⟩ : syracuseStep 2050991 = 3076487) B3076487
theorem B1731547 : Blo 1366502 1731547 := bstep (se 1 (by rfl) ⟨1298660, by rfl⟩ : syracuseStep 1731547 = 2597321) B2597321
theorem B2051081 : Blo 1366502 2051081 := bstep (se 2 (by rfl) ⟨769155, by rfl⟩ : syracuseStep 2051081 = 1538311) B1538311
theorem B106597387 : Blo 1366502 106597387 := bstep (se 1 (by rfl) ⟨79948040, by rfl⟩ : syracuseStep 106597387 = 159896081) B159896081
theorem B2051111 : Blo 1366502 2051111 := bstep (se 1 (by rfl) ⟨1538333, by rfl⟩ : syracuseStep 2051111 = 3076667) B3076667
theorem B17534069 : Blo 1366502 17534069 := bstep (se 5 (by rfl) ⟨821909, by rfl⟩ : syracuseStep 17534069 = 1643819) B1643819
theorem B2051195 : Blo 1366502 2051195 := bstep (se 1 (by rfl) ⟨1538396, by rfl⟩ : syracuseStep 2051195 = 3076793) B3076793
theorem B4615325 : Blo 1366502 4615325 := bstep (se 3 (by rfl) ⟨865373, by rfl⟩ : syracuseStep 4615325 = 1730747) B1730747
theorem B3509495 : Blo 1366502 3509495 := bstep (se 1 (by rfl) ⟨2632121, by rfl⟩ : syracuseStep 3509495 = 5264243) B5264243
theorem B2051321 : Blo 1366502 2051321 := bstep (se 2 (by rfl) ⟨769245, by rfl⟩ : syracuseStep 2051321 = 1538491) B1538491
theorem B2051423 : Blo 1366502 2051423 := bstep (se 1 (by rfl) ⟨1538567, by rfl⟩ : syracuseStep 2051423 = 3077135) B3077135
theorem B2051435 : Blo 1366502 2051435 := bstep (se 1 (by rfl) ⟨1538576, by rfl⟩ : syracuseStep 2051435 = 3077153) B3077153
theorem B4926845 : Blo 1366502 4926845 := bstep (se 3 (by rfl) ⟨923783, by rfl⟩ : syracuseStep 4926845 = 1847567) B1847567
theorem B5189129 : Blo 1366502 5189129 := bstep (se 2 (by rfl) ⟨1945923, by rfl⟩ : syracuseStep 5189129 = 3891847) B3891847
theorem B3075623 : Blo 1366502 3075623 := bstep (se 1 (by rfl) ⟨2306717, by rfl⟩ : syracuseStep 3075623 = 4613435) B4613435
theorem B17763907 : Blo 1366502 17763907 := bstep (se 1 (by rfl) ⟨13322930, by rfl⟩ : syracuseStep 17763907 = 26645861) B26645861
theorem B2051663 : Blo 1366502 2051663 := bstep (se 1 (by rfl) ⟨1538747, by rfl⟩ : syracuseStep 2051663 = 3077495) B3077495
theorem B9858647 : Blo 1366502 9858647 := bstep (se 1 (by rfl) ⟨7393985, by rfl⟩ : syracuseStep 9858647 = 14787971) B14787971
theorem B37957207 : Blo 1366502 37957207 := bstep (se 1 (by rfl) ⟨28467905, by rfl⟩ : syracuseStep 37957207 = 56935811) B56935811
theorem B15568523 : Blo 1366502 15568523 := bstep (se 1 (by rfl) ⟨11676392, by rfl⟩ : syracuseStep 15568523 = 23352785) B23352785
theorem B4615865 : Blo 1366502 4615865 := bstep (se 2 (by rfl) ⟨1730949, by rfl⟩ : syracuseStep 4615865 = 3461899) B3461899
theorem B2051783 : Blo 1366502 2051783 := bstep (se 1 (by rfl) ⟨1538837, by rfl⟩ : syracuseStep 2051783 = 3077675) B3077675
theorem B5263147 : Blo 1366502 5263147 := bstep (se 1 (by rfl) ⟨3947360, by rfl⟩ : syracuseStep 5263147 = 7894721) B7894721
theorem B6926147 : Blo 1366502 6926147 := bstep (se 1 (by rfl) ⟨5194610, by rfl⟩ : syracuseStep 6926147 = 10389221) B10389221
theorem B2051945 : Blo 1366502 2051945 := bstep (se 2 (by rfl) ⟨769479, by rfl⟩ : syracuseStep 2051945 = 1538959) B1538959
theorem B3075947 : Blo 1366502 3075947 := bstep (se 1 (by rfl) ⟨2306960, by rfl⟩ : syracuseStep 3075947 = 4613921) B4613921
theorem B3076001 : Blo 1366502 3076001 := bstep (se 2 (by rfl) ⟨1153500, by rfl⟩ : syracuseStep 3076001 = 2307001) B2307001
theorem B3461039 : Blo 1366502 3461039 := bstep (se 1 (by rfl) ⟨2595779, by rfl⟩ : syracuseStep 3461039 = 5191559) B5191559
theorem B2305975 : Blo 1366502 2305975 := bstep (se 1 (by rfl) ⟨1729481, by rfl⟩ : syracuseStep 2305975 = 3458963) B3458963
theorem B2052023 : Blo 1366502 2052023 := bstep (se 1 (by rfl) ⟨1539017, by rfl⟩ : syracuseStep 2052023 = 3078035) B3078035
theorem B2052059 : Blo 1366502 2052059 := bstep (se 1 (by rfl) ⟨1539044, by rfl⟩ : syracuseStep 2052059 = 3078089) B3078089
theorem B2191369 : Blo 1366502 2191369 := bstep (se 2 (by rfl) ⟨821763, by rfl⟩ : syracuseStep 2191369 = 1643527) B1643527
theorem B19714063 : Blo 1366502 19714063 := bstep (se 1 (by rfl) ⟨14785547, by rfl⟩ : syracuseStep 19714063 = 29571095) B29571095
theorem B7393295 : Blo 1366502 7393295 := bstep (se 1 (by rfl) ⟨5544971, by rfl⟩ : syracuseStep 7393295 = 11089943) B11089943
theorem B10383389 : Blo 1366502 10383389 := bstep (se 3 (by rfl) ⟨1946885, by rfl⟩ : syracuseStep 10383389 = 3893771) B3893771
theorem B2306171 : Blo 1366502 2306171 := bstep (se 1 (by rfl) ⟨1729628, by rfl⟩ : syracuseStep 2306171 = 3459257) B3459257
theorem B3076343 : Blo 1366502 3076343 := bstep (se 1 (by rfl) ⟨2307257, by rfl⟩ : syracuseStep 3076343 = 4614515) B4614515
theorem B8761601 : Blo 1366502 8761601 := bstep (se 2 (by rfl) ⟨3285600, by rfl⟩ : syracuseStep 8761601 = 6571201) B6571201
theorem B4616459 : Blo 1366502 4616459 := bstep (se 1 (by rfl) ⟨3462344, by rfl⟩ : syracuseStep 4616459 = 6924689) B6924689
theorem B7786813 : Blo 1366502 7786813 := bstep (se 3 (by rfl) ⟨1460027, by rfl⟩ : syracuseStep 7786813 = 2920055) B2920055
theorem B5263759 : Blo 1366502 5263759 := bstep (se 1 (by rfl) ⟨3947819, by rfl⟩ : syracuseStep 5263759 = 7895639) B7895639
theorem B2052527 : Blo 1366502 2052527 := bstep (se 1 (by rfl) ⟨1539395, by rfl⟩ : syracuseStep 2052527 = 3078791) B3078791
theorem B2306569 : Blo 1366502 2306569 := bstep (se 2 (by rfl) ⟨864963, by rfl⟩ : syracuseStep 2306569 = 1729927) B1729927
theorem B2052617 : Blo 1366502 2052617 := bstep (se 2 (by rfl) ⟨769731, by rfl⟩ : syracuseStep 2052617 = 1539463) B1539463
theorem B4616729 : Blo 1366502 4616729 := bstep (se 2 (by rfl) ⟨1731273, by rfl⟩ : syracuseStep 4616729 = 3462547) B3462547
theorem B2052647 : Blo 1366502 2052647 := bstep (se 1 (by rfl) ⟨1539485, by rfl⟩ : syracuseStep 2052647 = 3078971) B3078971
theorem B2191951 : Blo 1366502 2191951 := bstep (se 1 (by rfl) ⟨1643963, by rfl⟩ : syracuseStep 2191951 = 3287927) B3287927
theorem B2052731 : Blo 1366502 2052731 := bstep (se 1 (by rfl) ⟨1539548, by rfl⟩ : syracuseStep 2052731 = 3079097) B3079097
theorem B2306731 : Blo 1366502 2306731 := bstep (se 1 (by rfl) ⟨1730048, by rfl⟩ : syracuseStep 2306731 = 3460097) B3460097
theorem B71054093 : Blo 1366502 71054093 := bstep (se 3 (by rfl) ⟨13322642, by rfl⟩ : syracuseStep 71054093 = 26645285) B26645285
theorem B3076937 : Blo 1366502 3076937 := bstep (se 2 (by rfl) ⟨1153851, by rfl⟩ : syracuseStep 3076937 = 2307703) B2307703
theorem B6919019 : Blo 1366502 6919019 := bstep (se 1 (by rfl) ⟨5189264, by rfl⟩ : syracuseStep 6919019 = 10378529) B10378529
theorem B5190587 : Blo 1366502 5190587 := bstep (se 1 (by rfl) ⟨3892940, by rfl⟩ : syracuseStep 5190587 = 7785881) B7785881
theorem B2307035 : Blo 1366502 2307035 := bstep (se 1 (by rfl) ⟨1730276, by rfl⟩ : syracuseStep 2307035 = 3460553) B3460553
theorem B2774035 : Blo 1366502 2774035 := bstep (se 1 (by rfl) ⟨2080526, by rfl⟩ : syracuseStep 2774035 = 4161053) B4161053
theorem B2462759 : Blo 1366502 2462759 := bstep (se 1 (by rfl) ⟨1847069, by rfl⟩ : syracuseStep 2462759 = 3694139) B3694139
theorem B3462223 : Blo 1366502 3462223 := bstep (se 1 (by rfl) ⟨2596667, by rfl⟩ : syracuseStep 3462223 = 5193335) B5193335
theorem B2307271 : Blo 1366502 2307271 := bstep (se 1 (by rfl) ⟨1730453, by rfl⟩ : syracuseStep 2307271 = 3460907) B3460907
theorem B1643719 : Blo 1366502 1643719 := bstep (se 1 (by rfl) ⟨1232789, by rfl⟩ : syracuseStep 1643719 = 2465579) B2465579
theorem B1537375 : Blo 1366502 1537375 := bstep (se 1 (by rfl) ⟨1153031, by rfl⟩ : syracuseStep 1537375 = 2306063) B2306063
theorem B2307433 : Blo 1366502 2307433 := bstep (se 2 (by rfl) ⟨865287, by rfl⟩ : syracuseStep 2307433 = 1730575) B1730575
theorem B9360755 : Blo 1366502 9360755 := bstep (se 1 (by rfl) ⟨7020566, by rfl⟩ : syracuseStep 9360755 = 14041133) B14041133
theorem B6919667 : Blo 1366502 6919667 := bstep (se 1 (by rfl) ⟨5189750, by rfl⟩ : syracuseStep 6919667 = 10379501) B10379501
theorem B3077729 : Blo 1366502 3077729 := bstep (se 2 (by rfl) ⟨1154148, by rfl⟩ : syracuseStep 3077729 = 2308297) B2308297
theorem B5264993 : Blo 1366502 5264993 := bstep (se 2 (by rfl) ⟨1974372, by rfl⟩ : syracuseStep 5264993 = 3948745) B3948745
theorem B4617863 : Blo 1366502 4617863 := bstep (se 1 (by rfl) ⟨3463397, by rfl⟩ : syracuseStep 4617863 = 6926795) B6926795
theorem B4617917 : Blo 1366502 4617917 := bstep (se 3 (by rfl) ⟨865859, by rfl⟩ : syracuseStep 4617917 = 1731719) B1731719
theorem B1537735 : Blo 1366502 1537735 := bstep (se 1 (by rfl) ⟨1153301, by rfl⟩ : syracuseStep 1537735 = 2306603) B2306603
theorem B3462871 : Blo 1366502 3462871 := bstep (se 1 (by rfl) ⟨2597153, by rfl⟩ : syracuseStep 3462871 = 5194307) B5194307
theorem B4618079 : Blo 1366502 4618079 := bstep (se 1 (by rfl) ⟨3463559, by rfl⟩ : syracuseStep 4618079 = 6927119) B6927119
theorem B3078071 : Blo 1366502 3078071 := bstep (se 1 (by rfl) ⟨2308553, by rfl⟩ : syracuseStep 3078071 = 4617107) B4617107
theorem B2594747 : Blo 1366502 2594747 := bstep (se 1 (by rfl) ⟨1946060, by rfl⟩ : syracuseStep 2594747 = 3892121) B3892121
theorem B2308027 : Blo 1366502 2308027 := bstep (se 1 (by rfl) ⟨1731020, by rfl⟩ : syracuseStep 2308027 = 3462041) B3462041
theorem B4618241 : Blo 1366502 4618241 := bstep (se 2 (by rfl) ⟨1731840, by rfl⟩ : syracuseStep 4618241 = 3463681) B3463681
theorem B4159495 : Blo 1366502 4159495 := bstep (se 1 (by rfl) ⟨3119621, by rfl⟩ : syracuseStep 4159495 = 6239243) B6239243
theorem B3463175 : Blo 1366502 3463175 := bstep (se 1 (by rfl) ⟨2597381, by rfl⟩ : syracuseStep 3463175 = 5194763) B5194763
theorem B2308135 : Blo 1366502 2308135 := bstep (se 1 (by rfl) ⟨1731101, by rfl⟩ : syracuseStep 2308135 = 3462203) B3462203
theorem B151820345 : Blo 1366502 151820345 := bstep (se 2 (by rfl) ⟨56932629, by rfl⟩ : syracuseStep 151820345 = 113865259) B113865259
theorem B17520947 : Blo 1366502 17520947 := bstep (se 1 (by rfl) ⟨13140710, by rfl⟩ : syracuseStep 17520947 = 26281421) B26281421
theorem B2595179 : Blo 1366502 2595179 := bstep (se 1 (by rfl) ⟨1946384, by rfl⟩ : syracuseStep 2595179 = 3892769) B3892769
theorem B2308459 : Blo 1366502 2308459 := bstep (se 1 (by rfl) ⟨1731344, by rfl⟩ : syracuseStep 2308459 = 3462689) B3462689
theorem B4381057 : Blo 1366502 4381057 := bstep (se 2 (by rfl) ⟨1642896, by rfl⟩ : syracuseStep 4381057 = 3285793) B3285793
theorem B2595233 : Blo 1366502 2595233 := bstep (se 2 (by rfl) ⟨973212, by rfl⟩ : syracuseStep 2595233 = 1946425) B1946425
theorem B3078665 : Blo 1366502 3078665 := bstep (se 2 (by rfl) ⟨1154499, by rfl⟩ : syracuseStep 3078665 = 2308999) B2308999
theorem B6240793 : Blo 1366502 6240793 := bstep (se 2 (by rfl) ⟨2340297, by rfl⟩ : syracuseStep 6240793 = 4680595) B4680595
theorem B1366567 : Blo 1366502 1366567 := bstep (se 1 (by rfl) ⟨1024925, by rfl⟩ : syracuseStep 1366567 = 2049851) B2049851
theorem B1538599 : Blo 1366502 1538599 := bstep (se 1 (by rfl) ⟨1153949, by rfl⟩ : syracuseStep 1538599 = 2307899) B2307899
theorem B1366607 : Blo 1366502 1366607 := bstep (se 1 (by rfl) ⟨1024955, by rfl⟩ : syracuseStep 1366607 = 2049911) B2049911
theorem B1366623 : Blo 1366502 1366623 := bstep (se 1 (by rfl) ⟨1024967, by rfl⟩ : syracuseStep 1366623 = 2049935) B2049935
theorem B1366651 : Blo 1366502 1366651 := bstep (se 1 (by rfl) ⟨1024988, by rfl⟩ : syracuseStep 1366651 = 2049977) B2049977
theorem B1366703 : Blo 1366502 1366703 := bstep (se 1 (by rfl) ⟨1025027, by rfl⟩ : syracuseStep 1366703 = 2050055) B2050055
theorem B1366727 : Blo 1366502 1366727 := bstep (se 1 (by rfl) ⟨1025045, by rfl⟩ : syracuseStep 1366727 = 2050091) B2050091
theorem B4930247 : Blo 1366502 4930247 := bstep (se 1 (by rfl) ⟨3697685, by rfl⟩ : syracuseStep 4930247 = 7395371) B7395371
theorem B11238097 : Blo 1366502 11238097 := bstep (se 2 (by rfl) ⟨4214286, by rfl⟩ : syracuseStep 11238097 = 8428573) B8428573
theorem B1366747 : Blo 1366502 1366747 := bstep (se 1 (by rfl) ⟨1025060, by rfl⟩ : syracuseStep 1366747 = 2050121) B2050121
theorem B6920963 : Blo 1366502 6920963 := bstep (se 1 (by rfl) ⟨5190722, by rfl⟩ : syracuseStep 6920963 = 10381445) B10381445
theorem B1366823 : Blo 1366502 1366823 := bstep (se 1 (by rfl) ⟨1025117, by rfl⟩ : syracuseStep 1366823 = 2050235) B2050235
theorem B1366863 : Blo 1366502 1366863 := bstep (se 1 (by rfl) ⟨1025147, by rfl⟩ : syracuseStep 1366863 = 2050295) B2050295
theorem B1366879 : Blo 1366502 1366879 := bstep (se 1 (by rfl) ⟨1025159, by rfl⟩ : syracuseStep 1366879 = 2050319) B2050319
theorem B3079007 : Blo 1366502 3079007 := bstep (se 1 (by rfl) ⟨2309255, by rfl⟩ : syracuseStep 3079007 = 4618511) B4618511
theorem B1366907 : Blo 1366502 1366907 := bstep (se 1 (by rfl) ⟨1025180, by rfl⟩ : syracuseStep 1366907 = 2050361) B2050361
theorem B1366959 : Blo 1366502 1366959 := bstep (se 1 (by rfl) ⟨1025219, by rfl⟩ : syracuseStep 1366959 = 2050439) B2050439
theorem B1366983 : Blo 1366502 1366983 := bstep (se 1 (by rfl) ⟨1025237, by rfl⟩ : syracuseStep 1366983 = 2050475) B2050475
theorem B1367003 : Blo 1366502 1367003 := bstep (se 1 (by rfl) ⟨1025252, by rfl⟩ : syracuseStep 1367003 = 2050505) B2050505
theorem B1367079 : Blo 1366502 1367079 := bstep (se 1 (by rfl) ⟨1025309, by rfl⟩ : syracuseStep 1367079 = 2050619) B2050619
theorem B14777423 : Blo 1366502 14777423 := bstep (se 1 (by rfl) ⟨11083067, by rfl⟩ : syracuseStep 14777423 = 22166135) B22166135
theorem B1367119 : Blo 1366502 1367119 := bstep (se 1 (by rfl) ⟨1025339, by rfl⟩ : syracuseStep 1367119 = 2050679) B2050679
theorem B1367135 : Blo 1366502 1367135 := bstep (se 1 (by rfl) ⟨1025351, by rfl⟩ : syracuseStep 1367135 = 2050703) B2050703
theorem B5192819 : Blo 1366502 5192819 := bstep (se 1 (by rfl) ⟨3894614, by rfl⟩ : syracuseStep 5192819 = 7789229) B7789229
theorem B1367163 : Blo 1366502 1367163 := bstep (se 1 (by rfl) ⟨1025372, by rfl⟩ : syracuseStep 1367163 = 2050745) B2050745
theorem B1367215 : Blo 1366502 1367215 := bstep (se 1 (by rfl) ⟨1025411, by rfl⟩ : syracuseStep 1367215 = 2050823) B2050823
theorem B9862337 : Blo 1366502 9862337 := bstep (se 2 (by rfl) ⟨3698376, by rfl⟩ : syracuseStep 9862337 = 7396753) B7396753
theorem B1367239 : Blo 1366502 1367239 := bstep (se 1 (by rfl) ⟨1025429, by rfl⟩ : syracuseStep 1367239 = 2050859) B2050859
theorem B1367259 : Blo 1366502 1367259 := bstep (se 1 (by rfl) ⟨1025444, by rfl⟩ : syracuseStep 1367259 = 2050889) B2050889
theorem B1367335 : Blo 1366502 1367335 := bstep (se 1 (by rfl) ⟨1025501, by rfl⟩ : syracuseStep 1367335 = 2051003) B2051003
theorem B1367375 : Blo 1366502 1367375 := bstep (se 1 (by rfl) ⟨1025531, by rfl⟩ : syracuseStep 1367375 = 2051063) B2051063
theorem B1367391 : Blo 1366502 1367391 := bstep (se 1 (by rfl) ⟨1025543, by rfl⟩ : syracuseStep 1367391 = 2051087) B2051087
theorem B2809193 : Blo 1366502 2809193 := bstep (se 2 (by rfl) ⟨1053447, by rfl⟩ : syracuseStep 2809193 = 2106895) B2106895
theorem B1367419 : Blo 1366502 1367419 := bstep (se 1 (by rfl) ⟨1025564, by rfl⟩ : syracuseStep 1367419 = 2051129) B2051129
theorem B1367471 : Blo 1366502 1367471 := bstep (se 1 (by rfl) ⟨1025603, by rfl⟩ : syracuseStep 1367471 = 2051207) B2051207
theorem B1367495 : Blo 1366502 1367495 := bstep (se 1 (by rfl) ⟨1025621, by rfl⟩ : syracuseStep 1367495 = 2051243) B2051243
theorem B1367515 : Blo 1366502 1367515 := bstep (se 1 (by rfl) ⟨1025636, by rfl⟩ : syracuseStep 1367515 = 2051273) B2051273
theorem B1367591 : Blo 1366502 1367591 := bstep (se 1 (by rfl) ⟨1025693, by rfl⟩ : syracuseStep 1367591 = 2051387) B2051387
theorem B1367631 : Blo 1366502 1367631 := bstep (se 1 (by rfl) ⟨1025723, by rfl⟩ : syracuseStep 1367631 = 2051447) B2051447
theorem B1367647 : Blo 1366502 1367647 := bstep (se 1 (by rfl) ⟨1025735, by rfl⟩ : syracuseStep 1367647 = 2051471) B2051471
theorem B1367675 : Blo 1366502 1367675 := bstep (se 1 (by rfl) ⟨1025756, by rfl⟩ : syracuseStep 1367675 = 2051513) B2051513
theorem B1367727 : Blo 1366502 1367727 := bstep (se 1 (by rfl) ⟨1025795, by rfl⟩ : syracuseStep 1367727 = 2051591) B2051591
theorem B1367751 : Blo 1366502 1367751 := bstep (se 1 (by rfl) ⟨1025813, by rfl⟩ : syracuseStep 1367751 = 2051627) B2051627
theorem B1367771 : Blo 1366502 1367771 := bstep (se 1 (by rfl) ⟨1025828, by rfl⟩ : syracuseStep 1367771 = 2051657) B2051657
theorem B2465527 : Blo 1366502 2465527 := bstep (se 1 (by rfl) ⟨1849145, by rfl⟩ : syracuseStep 2465527 = 3698291) B3698291
theorem B29556485 : Blo 1366502 29556485 := bstep (se 4 (by rfl) ⟨2770920, by rfl⟩ : syracuseStep 29556485 = 5541841) B5541841
theorem B1367847 : Blo 1366502 1367847 := bstep (se 1 (by rfl) ⟨1025885, by rfl⟩ : syracuseStep 1367847 = 2051771) B2051771
theorem B7110443 : Blo 1366502 7110443 := bstep (se 1 (by rfl) ⟨5332832, by rfl⟩ : syracuseStep 7110443 = 10665665) B10665665
theorem B4931401 : Blo 1366502 4931401 := bstep (se 2 (by rfl) ⟨1849275, by rfl⟩ : syracuseStep 4931401 = 3698551) B3698551
theorem B1367887 : Blo 1366502 1367887 := bstep (se 1 (by rfl) ⟨1025915, by rfl⟩ : syracuseStep 1367887 = 2051831) B2051831
theorem B1367903 : Blo 1366502 1367903 := bstep (se 1 (by rfl) ⟨1025927, by rfl⟩ : syracuseStep 1367903 = 2051855) B2051855
theorem B1367931 : Blo 1366502 1367931 := bstep (se 1 (by rfl) ⟨1025948, by rfl⟩ : syracuseStep 1367931 = 2051897) B2051897
theorem B22167431 : Blo 1366502 22167431 := bstep (se 1 (by rfl) ⟨16625573, by rfl⟩ : syracuseStep 22167431 = 33251147) B33251147
theorem B1367983 : Blo 1366502 1367983 := bstep (se 1 (by rfl) ⟨1025987, by rfl⟩ : syracuseStep 1367983 = 2051975) B2051975
theorem B1368007 : Blo 1366502 1368007 := bstep (se 1 (by rfl) ⟨1026005, by rfl⟩ : syracuseStep 1368007 = 2052011) B2052011
theorem B252731339 : Blo 1366502 252731339 := bstep (se 1 (by rfl) ⟨189548504, by rfl⟩ : syracuseStep 252731339 = 379097009) B379097009
theorem B1368027 : Blo 1366502 1368027 := bstep (se 1 (by rfl) ⟨1026020, by rfl⟩ : syracuseStep 1368027 = 2052041) B2052041
theorem B5545993 : Blo 1366502 5545993 := bstep (se 2 (by rfl) ⟨2079747, by rfl⟩ : syracuseStep 5545993 = 4159495) B4159495
theorem B6922259 : Blo 1366502 6922259 := bstep (se 1 (by rfl) ⟨5191694, by rfl⟩ : syracuseStep 6922259 = 10383389) B10383389
theorem B37945421 : Blo 1366502 37945421 := bstep (se 3 (by rfl) ⟨7114766, by rfl⟩ : syracuseStep 37945421 = 14229533) B14229533
theorem B5841067 : Blo 1366502 5841067 := bstep (se 1 (by rfl) ⟨4380800, by rfl⟩ : syracuseStep 5841067 = 8761601) B8761601
theorem B1368351 : Blo 1366502 1368351 := bstep (se 1 (by rfl) ⟨1026263, by rfl⟩ : syracuseStep 1368351 = 2052527) B2052527
theorem B1368411 : Blo 1366502 1368411 := bstep (se 1 (by rfl) ⟨1026308, by rfl⟩ : syracuseStep 1368411 = 2052617) B2052617
theorem B1368431 : Blo 1366502 1368431 := bstep (se 1 (by rfl) ⟨1026323, by rfl⟩ : syracuseStep 1368431 = 2052647) B2052647
theorem B11690405 : Blo 1366502 11690405 := bstep (se 4 (by rfl) ⟨1095975, by rfl⟩ : syracuseStep 11690405 = 2191951) B2191951
theorem B1368487 : Blo 1366502 1368487 := bstep (se 1 (by rfl) ⟨1026365, by rfl⟩ : syracuseStep 1368487 = 2052731) B2052731
theorem B5841409 : Blo 1366502 5841409 := bstep (se 2 (by rfl) ⟨2190528, by rfl⟩ : syracuseStep 5841409 = 4381057) B4381057
theorem B4612679 : Blo 1366502 4612679 := bstep (se 1 (by rfl) ⟨3459509, by rfl⟩ : syracuseStep 4612679 = 6919019) B6919019
theorem B16630343 : Blo 1366502 16630343 := bstep (se 1 (by rfl) ⟨12472757, by rfl⟩ : syracuseStep 16630343 = 24945515) B24945515
theorem B14984129 : Blo 1366502 14984129 := bstep (se 2 (by rfl) ⟨5619048, by rfl⟩ : syracuseStep 14984129 = 11238097) B11238097
theorem B4613111 : Blo 1366502 4613111 := bstep (se 1 (by rfl) ⟨3459833, by rfl⟩ : syracuseStep 4613111 = 6919667) B6919667
theorem B7791713 : Blo 1366502 7791713 := bstep (se 2 (by rfl) ⟨2921892, by rfl⟩ : syracuseStep 7791713 = 5843785) B5843785
theorem B1729831 : Blo 1366502 1729831 := bstep (se 1 (by rfl) ⟨1297373, by rfl⟩ : syracuseStep 1729831 = 2594747) B2594747
theorem B101213563 : Blo 1366502 101213563 := bstep (se 1 (by rfl) ⟨75910172, by rfl⟩ : syracuseStep 101213563 = 151820345) B151820345
theorem B1730155 : Blo 1366502 1730155 := bstep (se 1 (by rfl) ⟨1297616, by rfl⟩ : syracuseStep 1730155 = 2595233) B2595233
theorem B2049833 : Blo 1366502 2049833 := bstep (se 2 (by rfl) ⟨768687, by rfl⟩ : syracuseStep 2049833 = 1537375) B1537375
theorem B2049839 : Blo 1366502 2049839 := bstep (se 1 (by rfl) ⟨1537379, by rfl⟩ : syracuseStep 2049839 = 3074759) B3074759
theorem B3286831 : Blo 1366502 3286831 := bstep (se 1 (by rfl) ⟨2465123, by rfl⟩ : syracuseStep 3286831 = 4930247) B4930247
theorem B4613975 : Blo 1366502 4613975 := bstep (se 1 (by rfl) ⟨3460481, by rfl⟩ : syracuseStep 4613975 = 6920963) B6920963
theorem B13141865 : Blo 1366502 13141865 := bstep (se 2 (by rfl) ⟨4928199, by rfl⟩ : syracuseStep 13141865 = 9856399) B9856399
theorem B23685209 : Blo 1366502 23685209 := bstep (se 2 (by rfl) ⟨8881953, by rfl⟩ : syracuseStep 23685209 = 17763907) B17763907
theorem B2050313 : Blo 1366502 2050313 := bstep (se 2 (by rfl) ⟨768867, by rfl⟩ : syracuseStep 2050313 = 1537735) B1537735
theorem B3287369 : Blo 1366502 3287369 := bstep (se 2 (by rfl) ⟨1232763, by rfl⟩ : syracuseStep 3287369 = 2465527) B2465527
theorem B3459419 : Blo 1366502 3459419 := bstep (se 1 (by rfl) ⟨2594564, by rfl⟩ : syracuseStep 3459419 = 5189129) B5189129
theorem B2050415 : Blo 1366502 2050415 := bstep (se 1 (by rfl) ⟨1537811, by rfl⟩ : syracuseStep 2050415 = 3075623) B3075623
theorem B6572431 : Blo 1366502 6572431 := bstep (se 1 (by rfl) ⟨4929323, by rfl⟩ : syracuseStep 6572431 = 9858647) B9858647
theorem B19704323 : Blo 1366502 19704323 := bstep (se 1 (by rfl) ⟨14778242, by rfl⟩ : syracuseStep 19704323 = 29556485) B29556485
theorem B2050631 : Blo 1366502 2050631 := bstep (se 1 (by rfl) ⟨1537973, by rfl⟩ : syracuseStep 2050631 = 3075947) B3075947
theorem B3074633 : Blo 1366502 3074633 := bstep (se 2 (by rfl) ⟨1152987, by rfl⟩ : syracuseStep 3074633 = 2305975) B2305975
theorem B2050667 : Blo 1366502 2050667 := bstep (se 1 (by rfl) ⟨1538000, by rfl⟩ : syracuseStep 2050667 = 3076001) B3076001
theorem B168487559 : Blo 1366502 168487559 := bstep (se 1 (by rfl) ⟨126365669, by rfl⟩ : syracuseStep 168487559 = 252731339) B252731339
theorem B568519397 : Blo 1366502 568519397 := bstep (se 4 (by rfl) ⟨53298693, by rfl⟩ : syracuseStep 568519397 = 106597387) B106597387
theorem B3697427 : Blo 1366502 3697427 := bstep (se 1 (by rfl) ⟨2773070, by rfl⟩ : syracuseStep 3697427 = 5546141) B5546141
theorem B2050895 : Blo 1366502 2050895 := bstep (se 1 (by rfl) ⟨1538171, by rfl⟩ : syracuseStep 2050895 = 3076343) B3076343
theorem B6925175 : Blo 1366502 6925175 := bstep (se 1 (by rfl) ⟨5193881, by rfl⟩ : syracuseStep 6925175 = 10387763) B10387763
theorem B4615055 : Blo 1366502 4615055 := bstep (se 1 (by rfl) ⟨3461291, by rfl⟩ : syracuseStep 4615055 = 6922583) B6922583
theorem B3075047 : Blo 1366502 3075047 := bstep (se 1 (by rfl) ⟨2306285, by rfl⟩ : syracuseStep 3075047 = 4612571) B4612571
theorem B10382417 : Blo 1366502 10382417 := bstep (se 2 (by rfl) ⟨3893406, by rfl⟩ : syracuseStep 10382417 = 7786813) B7786813
theorem B44969093 : Blo 1366502 44969093 := bstep (se 4 (by rfl) ⟨4215852, by rfl⟩ : syracuseStep 44969093 = 8431705) B8431705
theorem B2370703 : Blo 1366502 2370703 := bstep (se 1 (by rfl) ⟨1778027, by rfl⟩ : syracuseStep 2370703 = 3556055) B3556055
theorem B26299565 : Blo 1366502 26299565 := bstep (se 3 (by rfl) ⟨4931168, by rfl⟩ : syracuseStep 26299565 = 9862337) B9862337
theorem B47369395 : Blo 1366502 47369395 := bstep (se 1 (by rfl) ⟨35527046, by rfl⟩ : syracuseStep 47369395 = 71054093) B71054093
theorem B2051291 : Blo 1366502 2051291 := bstep (se 1 (by rfl) ⟨1538468, by rfl⟩ : syracuseStep 2051291 = 3076937) B3076937
theorem B24947999 : Blo 1366502 24947999 := bstep (se 1 (by rfl) ⟨18710999, by rfl⟩ : syracuseStep 24947999 = 37421999) B37421999
theorem B1731871 : Blo 1366502 1731871 := bstep (se 1 (by rfl) ⟨1298903, by rfl⟩ : syracuseStep 1731871 = 2597807) B2597807
theorem B3460391 : Blo 1366502 3460391 := bstep (se 1 (by rfl) ⟨2595293, by rfl⟩ : syracuseStep 3460391 = 5190587) B5190587
theorem B5188931 : Blo 1366502 5188931 := bstep (se 1 (by rfl) ⟨3891698, by rfl⟩ : syracuseStep 5188931 = 7783397) B7783397
theorem B5188961 : Blo 1366502 5188961 := bstep (se 2 (by rfl) ⟨1945860, by rfl⟩ : syracuseStep 5188961 = 3891721) B3891721
theorem B3075425 : Blo 1366502 3075425 := bstep (se 2 (by rfl) ⟨1153284, by rfl⟩ : syracuseStep 3075425 = 2306569) B2306569
theorem B1641839 : Blo 1366502 1641839 := bstep (se 1 (by rfl) ⟨1231379, by rfl⟩ : syracuseStep 1641839 = 2462759) B2462759
theorem B2051465 : Blo 1366502 2051465 := bstep (se 2 (by rfl) ⟨769299, by rfl⟩ : syracuseStep 2051465 = 1538599) B1538599
theorem B3075515 : Blo 1366502 3075515 := bstep (se 1 (by rfl) ⟨2306636, by rfl⟩ : syracuseStep 3075515 = 4613273) B4613273
theorem B3075641 : Blo 1366502 3075641 := bstep (se 2 (by rfl) ⟨1153365, by rfl⟩ : syracuseStep 3075641 = 2306731) B2306731
theorem B6925985 : Blo 1366502 6925985 := bstep (se 2 (by rfl) ⟨2597244, by rfl⟩ : syracuseStep 6925985 = 5194489) B5194489
theorem B2051819 : Blo 1366502 2051819 := bstep (se 1 (by rfl) ⟨1538864, by rfl⟩ : syracuseStep 2051819 = 3077729) B3077729
theorem B3509995 : Blo 1366502 3509995 := bstep (se 1 (by rfl) ⟨2632496, by rfl⟩ : syracuseStep 3509995 = 5264993) B5264993
theorem B5844743 : Blo 1366502 5844743 := bstep (se 1 (by rfl) ⟨4383557, by rfl⟩ : syracuseStep 5844743 = 8767115) B8767115
theorem B5189417 : Blo 1366502 5189417 := bstep (se 2 (by rfl) ⟨1946031, by rfl⟩ : syracuseStep 5189417 = 3892063) B3892063
theorem B2052047 : Blo 1366502 2052047 := bstep (se 1 (by rfl) ⟨1539035, by rfl⟩ : syracuseStep 2052047 = 3078071) B3078071
theorem B3698713 : Blo 1366502 3698713 := bstep (se 2 (by rfl) ⟨1387017, by rfl⟩ : syracuseStep 3698713 = 2774035) B2774035
theorem B4616297 : Blo 1366502 4616297 := bstep (se 2 (by rfl) ⟨1731111, by rfl⟩ : syracuseStep 4616297 = 3462223) B3462223
theorem B3076307 : Blo 1366502 3076307 := bstep (se 1 (by rfl) ⟨2307230, by rfl⟩ : syracuseStep 3076307 = 4614461) B4614461
theorem B3076361 : Blo 1366502 3076361 := bstep (se 2 (by rfl) ⟨1153635, by rfl⟩ : syracuseStep 3076361 = 2307271) B2307271
theorem B2191625 : Blo 1366502 2191625 := bstep (se 2 (by rfl) ⟨821859, by rfl⟩ : syracuseStep 2191625 = 1643719) B1643719
theorem B2052443 : Blo 1366502 2052443 := bstep (se 1 (by rfl) ⟨1539332, by rfl⟩ : syracuseStep 2052443 = 3078665) B3078665
theorem B8319451 : Blo 1366502 8319451 := bstep (se 1 (by rfl) ⟨6239588, by rfl⟩ : syracuseStep 8319451 = 12479177) B12479177
theorem B3076577 : Blo 1366502 3076577 := bstep (se 2 (by rfl) ⟨1153716, by rfl⟩ : syracuseStep 3076577 = 2307433) B2307433
theorem B2306623 : Blo 1366502 2306623 := bstep (se 1 (by rfl) ⟨1729967, by rfl⟩ : syracuseStep 2306623 = 3459935) B3459935
theorem B2052671 : Blo 1366502 2052671 := bstep (se 1 (by rfl) ⟨1539503, by rfl⟩ : syracuseStep 2052671 = 3079007) B3079007
theorem B9851615 : Blo 1366502 9851615 := bstep (se 1 (by rfl) ⟨7388711, by rfl⟩ : syracuseStep 9851615 = 14777423) B14777423
theorem B3461879 : Blo 1366502 3461879 := bstep (se 1 (by rfl) ⟨2596409, by rfl⟩ : syracuseStep 3461879 = 5192819) B5192819
theorem B3076883 : Blo 1366502 3076883 := bstep (se 1 (by rfl) ⟨2307662, by rfl⟩ : syracuseStep 3076883 = 4615325) B4615325
theorem B2339663 : Blo 1366502 2339663 := bstep (se 1 (by rfl) ⟨1754747, by rfl⟩ : syracuseStep 2339663 = 3509495) B3509495
theorem B5190601 : Blo 1366502 5190601 := bstep (se 2 (by rfl) ⟨1946475, by rfl⟩ : syracuseStep 5190601 = 3892951) B3892951
theorem B4617161 : Blo 1366502 4617161 := bstep (se 2 (by rfl) ⟨1731435, by rfl⟩ : syracuseStep 4617161 = 3462871) B3462871
theorem B86471725 : Blo 1366502 86471725 := bstep (se 3 (by rfl) ⟨16213448, by rfl⟩ : syracuseStep 86471725 = 32426897) B32426897
theorem B7017529 : Blo 1366502 7017529 := bstep (se 2 (by rfl) ⟨2631573, by rfl⟩ : syracuseStep 7017529 = 5263147) B5263147
theorem B6575201 : Blo 1366502 6575201 := bstep (se 2 (by rfl) ⟨2465700, by rfl⟩ : syracuseStep 6575201 = 4931401) B4931401
theorem B3077243 : Blo 1366502 3077243 := bstep (se 1 (by rfl) ⟨2307932, by rfl⟩ : syracuseStep 3077243 = 4615865) B4615865
theorem B8762525 : Blo 1366502 8762525 := bstep (se 3 (by rfl) ⟨1642973, by rfl⟩ : syracuseStep 8762525 = 3285947) B3285947
theorem B4740295 : Blo 1366502 4740295 := bstep (se 1 (by rfl) ⟨3555221, by rfl⟩ : syracuseStep 4740295 = 7110443) B7110443
theorem B4617431 : Blo 1366502 4617431 := bstep (se 1 (by rfl) ⟨3463073, by rfl⟩ : syracuseStep 4617431 = 6926147) B6926147
theorem B2307305 : Blo 1366502 2307305 := bstep (se 2 (by rfl) ⟨865239, by rfl⟩ : syracuseStep 2307305 = 1730479) B1730479
theorem B5190905 : Blo 1366502 5190905 := bstep (se 2 (by rfl) ⟨1946589, by rfl⟩ : syracuseStep 5190905 = 3893179) B3893179
theorem B3077369 : Blo 1366502 3077369 := bstep (se 2 (by rfl) ⟨1154013, by rfl⟩ : syracuseStep 3077369 = 2308027) B2308027
theorem B2307359 : Blo 1366502 2307359 := bstep (se 1 (by rfl) ⟨1730519, by rfl⟩ : syracuseStep 2307359 = 3461039) B3461039
theorem B4928863 : Blo 1366502 4928863 := bstep (se 1 (by rfl) ⟨3696647, by rfl⟩ : syracuseStep 4928863 = 7393295) B7393295
theorem B3462497 : Blo 1366502 3462497 := bstep (se 2 (by rfl) ⟨1298436, by rfl⟩ : syracuseStep 3462497 = 2596873) B2596873
theorem B2921825 : Blo 1366502 2921825 := bstep (se 2 (by rfl) ⟨1095684, by rfl⟩ : syracuseStep 2921825 = 2191369) B2191369
theorem B26285417 : Blo 1366502 26285417 := bstep (se 2 (by rfl) ⟨9857031, by rfl⟩ : syracuseStep 26285417 = 19714063) B19714063
theorem B1947017 : Blo 1366502 1947017 := bstep (se 2 (by rfl) ⟨730131, by rfl⟩ : syracuseStep 1947017 = 1460263) B1460263
theorem B3077513 : Blo 1366502 3077513 := bstep (se 2 (by rfl) ⟨1154067, by rfl⟩ : syracuseStep 3077513 = 2308135) B2308135
theorem B5191073 : Blo 1366502 5191073 := bstep (se 2 (by rfl) ⟨1946652, by rfl⟩ : syracuseStep 5191073 = 3893305) B3893305
theorem B1537447 : Blo 1366502 1537447 := bstep (se 1 (by rfl) ⟨1153085, by rfl⟩ : syracuseStep 1537447 = 2306171) B2306171
theorem B3077639 : Blo 1366502 3077639 := bstep (se 1 (by rfl) ⟨2308229, by rfl⟩ : syracuseStep 3077639 = 4616459) B4616459
theorem B6927929 : Blo 1366502 6927929 := bstep (se 2 (by rfl) ⟨2597973, by rfl⟩ : syracuseStep 6927929 = 5195947) B5195947
theorem B3077819 : Blo 1366502 3077819 := bstep (se 1 (by rfl) ⟨2308364, by rfl⟩ : syracuseStep 3077819 = 4616729) B4616729
theorem B6919991 : Blo 1366502 6919991 := bstep (se 1 (by rfl) ⟨5189993, by rfl⟩ : syracuseStep 6919991 = 10379987) B10379987
theorem B3077945 : Blo 1366502 3077945 := bstep (se 2 (by rfl) ⟨1154229, by rfl⟩ : syracuseStep 3077945 = 2308459) B2308459
theorem B7018345 : Blo 1366502 7018345 := bstep (se 2 (by rfl) ⟨2631879, by rfl⟩ : syracuseStep 7018345 = 5263759) B5263759
theorem B11679673 : Blo 1366502 11679673 := bstep (se 2 (by rfl) ⟨4379877, by rfl⟩ : syracuseStep 11679673 = 8759755) B8759755
theorem B1538023 : Blo 1366502 1538023 := bstep (se 1 (by rfl) ⟨1153517, by rfl⟩ : syracuseStep 1538023 = 2307035) B2307035
theorem B8321057 : Blo 1366502 8321057 := bstep (se 2 (by rfl) ⟨3120396, by rfl⟩ : syracuseStep 8321057 = 6240793) B6240793
theorem B11081771 : Blo 1366502 11081771 := bstep (se 1 (by rfl) ⟨8311328, by rfl⟩ : syracuseStep 11081771 = 16622657) B16622657
theorem B6240503 : Blo 1366502 6240503 := bstep (se 1 (by rfl) ⟨4680377, by rfl⟩ : syracuseStep 6240503 = 9360755) B9360755
theorem B6920477 : Blo 1366502 6920477 := bstep (se 3 (by rfl) ⟨1297589, by rfl⟩ : syracuseStep 6920477 = 2595179) B2595179
theorem B3078575 : Blo 1366502 3078575 := bstep (se 1 (by rfl) ⟨2308931, by rfl⟩ : syracuseStep 3078575 = 4617863) B4617863
theorem B29964725 : Blo 1366502 29964725 := bstep (se 5 (by rfl) ⟨1404596, by rfl⟩ : syracuseStep 29964725 = 2809193) B2809193
theorem B3078611 : Blo 1366502 3078611 := bstep (se 1 (by rfl) ⟨2308958, by rfl⟩ : syracuseStep 3078611 = 4617917) B4617917
theorem B1366523 : Blo 1366502 1366523 := bstep (se 1 (by rfl) ⟨1024892, by rfl⟩ : syracuseStep 1366523 = 2049785) B2049785
theorem B1366591 : Blo 1366502 1366591 := bstep (se 1 (by rfl) ⟨1024943, by rfl⟩ : syracuseStep 1366591 = 2049887) B2049887
theorem B3078719 : Blo 1366502 3078719 := bstep (se 1 (by rfl) ⟨2309039, by rfl⟩ : syracuseStep 3078719 = 4618079) B4618079
theorem B1366599 : Blo 1366502 1366599 := bstep (se 1 (by rfl) ⟨1024949, by rfl⟩ : syracuseStep 1366599 = 2049899) B2049899
theorem B2308729 : Blo 1366502 2308729 := bstep (se 2 (by rfl) ⟨865773, by rfl⟩ : syracuseStep 2308729 = 1731547) B1731547
theorem B3078827 : Blo 1366502 3078827 := bstep (se 1 (by rfl) ⟨2309120, by rfl⟩ : syracuseStep 3078827 = 4618241) B4618241
theorem B2308783 : Blo 1366502 2308783 := bstep (se 1 (by rfl) ⟨1731587, by rfl⟩ : syracuseStep 2308783 = 3463175) B3463175
theorem B1366751 : Blo 1366502 1366751 := bstep (se 1 (by rfl) ⟨1025063, by rfl⟩ : syracuseStep 1366751 = 2050127) B2050127
theorem B3463955 : Blo 1366502 3463955 := bstep (se 1 (by rfl) ⟨2597966, by rfl⟩ : syracuseStep 3463955 = 5195933) B5195933
theorem B1366831 : Blo 1366502 1366831 := bstep (se 1 (by rfl) ⟨1025123, by rfl⟩ : syracuseStep 1366831 = 2050247) B2050247
theorem B5839735 : Blo 1366502 5839735 := bstep (se 1 (by rfl) ⟨4379801, by rfl⟩ : syracuseStep 5839735 = 8759603) B8759603
theorem B11680631 : Blo 1366502 11680631 := bstep (se 1 (by rfl) ⟨8760473, by rfl⟩ : syracuseStep 11680631 = 17520947) B17520947
theorem B1366939 : Blo 1366502 1366939 := bstep (se 1 (by rfl) ⟨1025204, by rfl⟩ : syracuseStep 1366939 = 2050409) B2050409
theorem B59906999 : Blo 1366502 59906999 := bstep (se 1 (by rfl) ⟨44930249, by rfl⟩ : syracuseStep 59906999 = 89860499) B89860499
theorem B16636859 : Blo 1366502 16636859 := bstep (se 1 (by rfl) ⟨12477644, by rfl⟩ : syracuseStep 16636859 = 24955289) B24955289
theorem B1366991 : Blo 1366502 1366991 := bstep (se 1 (by rfl) ⟨1025243, by rfl⟩ : syracuseStep 1366991 = 2050487) B2050487
theorem B1367015 : Blo 1366502 1367015 := bstep (se 1 (by rfl) ⟨1025261, by rfl⟩ : syracuseStep 1367015 = 2050523) B2050523
theorem B5266471 : Blo 1366502 5266471 := bstep (se 1 (by rfl) ⟨3949853, by rfl⟩ : syracuseStep 5266471 = 7899707) B7899707
theorem B6233203 : Blo 1366502 6233203 := bstep (se 1 (by rfl) ⟨4674902, by rfl⟩ : syracuseStep 6233203 = 9349805) B9349805
theorem B1367327 : Blo 1366502 1367327 := bstep (se 1 (by rfl) ⟨1025495, by rfl⟩ : syracuseStep 1367327 = 2050991) B2050991
theorem B1367387 : Blo 1366502 1367387 := bstep (se 1 (by rfl) ⟨1025540, by rfl⟩ : syracuseStep 1367387 = 2051081) B2051081
theorem B1367407 : Blo 1366502 1367407 := bstep (se 1 (by rfl) ⟨1025555, by rfl⟩ : syracuseStep 1367407 = 2051111) B2051111
theorem B11689379 : Blo 1366502 11689379 := bstep (se 1 (by rfl) ⟨8767034, by rfl⟩ : syracuseStep 11689379 = 17534069) B17534069
theorem B14777765 : Blo 1366502 14777765 := bstep (se 4 (by rfl) ⟨1385415, by rfl⟩ : syracuseStep 14777765 = 2770831) B2770831
theorem B1367463 : Blo 1366502 1367463 := bstep (se 1 (by rfl) ⟨1025597, by rfl⟩ : syracuseStep 1367463 = 2051195) B2051195
theorem B50609609 : Blo 1366502 50609609 := bstep (se 2 (by rfl) ⟨18978603, by rfl⟩ : syracuseStep 50609609 = 37957207) B37957207
theorem B1367547 : Blo 1366502 1367547 := bstep (se 1 (by rfl) ⟨1025660, by rfl⟩ : syracuseStep 1367547 = 2051321) B2051321
theorem B1367615 : Blo 1366502 1367615 := bstep (se 1 (by rfl) ⟨1025711, by rfl⟩ : syracuseStep 1367615 = 2051423) B2051423
theorem B1367623 : Blo 1366502 1367623 := bstep (se 1 (by rfl) ⟨1025717, by rfl⟩ : syracuseStep 1367623 = 2051435) B2051435
theorem B3284563 : Blo 1366502 3284563 := bstep (se 1 (by rfl) ⟨2463422, by rfl⟩ : syracuseStep 3284563 = 4926845) B4926845
theorem B1367775 : Blo 1366502 1367775 := bstep (se 1 (by rfl) ⟨1025831, by rfl⟩ : syracuseStep 1367775 = 2051663) B2051663
theorem B10379015 : Blo 1366502 10379015 := bstep (se 1 (by rfl) ⟨7784261, by rfl⟩ : syracuseStep 10379015 = 15568523) B15568523
theorem B1367855 : Blo 1366502 1367855 := bstep (se 1 (by rfl) ⟨1025891, by rfl⟩ : syracuseStep 1367855 = 2051783) B2051783
theorem B1367963 : Blo 1366502 1367963 := bstep (se 1 (by rfl) ⟨1025972, by rfl⟩ : syracuseStep 1367963 = 2051945) B2051945
theorem B14778287 : Blo 1366502 14778287 := bstep (se 1 (by rfl) ⟨11083715, by rfl⟩ : syracuseStep 14778287 = 22167431) B22167431
theorem B1368015 : Blo 1366502 1368015 := bstep (se 1 (by rfl) ⟨1026011, by rfl⟩ : syracuseStep 1368015 = 2052023) B2052023
theorem B1368039 : Blo 1366502 1368039 := bstep (se 1 (by rfl) ⟨1026029, by rfl⟩ : syracuseStep 1368039 = 2052059) B2052059
theorem B4931617 : Blo 1366502 4931617 := bstep (se 2 (by rfl) ⟨1849356, by rfl⟩ : syracuseStep 4931617 = 3698713) B3698713
theorem B25296947 : Blo 1366502 25296947 := bstep (se 1 (by rfl) ⟨18972710, by rfl⟩ : syracuseStep 25296947 = 37945421) B37945421
theorem B1368295 : Blo 1366502 1368295 := bstep (se 1 (by rfl) ⟨1026221, by rfl⟩ : syracuseStep 1368295 = 2052443) B2052443
theorem B1368447 : Blo 1366502 1368447 := bstep (se 1 (by rfl) ⟨1026335, by rfl⟩ : syracuseStep 1368447 = 2052671) B2052671
theorem B11092601 : Blo 1366502 11092601 := bstep (se 2 (by rfl) ⟨4159725, by rfl⟩ : syracuseStep 11092601 = 8319451) B8319451
theorem B5194475 : Blo 1366502 5194475 := bstep (se 1 (by rfl) ⟨3895856, by rfl⟩ : syracuseStep 5194475 = 7791713) B7791713
theorem B4383467 : Blo 1366502 4383467 := bstep (se 1 (by rfl) ⟨3287600, by rfl⟩ : syracuseStep 4383467 = 6575201) B6575201
theorem B5841683 : Blo 1366502 5841683 := bstep (se 1 (by rfl) ⟨4381262, by rfl⟩ : syracuseStep 5841683 = 8762525) B8762525
theorem B17523611 : Blo 1366502 17523611 := bstep (se 1 (by rfl) ⟨13142708, by rfl⟩ : syracuseStep 17523611 = 26285417) B26285417
theorem B4613327 : Blo 1366502 4613327 := bstep (se 1 (by rfl) ⟨3459995, by rfl⟩ : syracuseStep 4613327 = 6919991) B6919991
theorem B5547371 : Blo 1366502 5547371 := bstep (se 1 (by rfl) ⟨4160528, by rfl⟩ : syracuseStep 5547371 = 8321057) B8321057
theorem B7021961 : Blo 1366502 7021961 := bstep (se 2 (by rfl) ⟨2633235, by rfl⟩ : syracuseStep 7021961 = 5266471) B5266471
theorem B115295633 : Blo 1366502 115295633 := bstep (se 2 (by rfl) ⟨43235862, by rfl⟩ : syracuseStep 115295633 = 86471725) B86471725
theorem B9356705 : Blo 1366502 9356705 := bstep (se 2 (by rfl) ⟨3508764, by rfl⟩ : syracuseStep 9356705 = 7017529) B7017529
theorem B4613651 : Blo 1366502 4613651 := bstep (se 1 (by rfl) ⟨3460238, by rfl⟩ : syracuseStep 4613651 = 6920477) B6920477
theorem B2049755 : Blo 1366502 2049755 := bstep (se 1 (by rfl) ⟨1537316, by rfl⟩ : syracuseStep 2049755 = 3074633) B3074633
theorem B6571817 : Blo 1366502 6571817 := bstep (se 2 (by rfl) ⟨2464431, by rfl⟩ : syracuseStep 6571817 = 4928863) B4928863
theorem B379012931 : Blo 1366502 379012931 := bstep (se 1 (by rfl) ⟨284259698, by rfl⟩ : syracuseStep 379012931 = 568519397) B568519397
theorem B37431173 : Blo 1366502 37431173 := bstep (se 4 (by rfl) ⟨3509172, by rfl⟩ : syracuseStep 37431173 = 7018345) B7018345
theorem B2049929 : Blo 1366502 2049929 := bstep (se 2 (by rfl) ⟨768723, by rfl⟩ : syracuseStep 2049929 = 1537447) B1537447
theorem B2050031 : Blo 1366502 2050031 := bstep (se 1 (by rfl) ⟨1537523, by rfl⟩ : syracuseStep 2050031 = 3075047) B3075047
theorem B17533043 : Blo 1366502 17533043 := bstep (se 1 (by rfl) ⟨13149782, by rfl⟩ : syracuseStep 17533043 = 26299565) B26299565
theorem B16631999 : Blo 1366502 16631999 := bstep (se 1 (by rfl) ⟨12473999, by rfl⟩ : syracuseStep 16631999 = 24947999) B24947999
theorem B3459287 : Blo 1366502 3459287 := bstep (se 1 (by rfl) ⟨2594465, by rfl⟩ : syracuseStep 3459287 = 5188931) B5188931
theorem B3459307 : Blo 1366502 3459307 := bstep (se 1 (by rfl) ⟨2594480, by rfl⟩ : syracuseStep 3459307 = 5188961) B5188961
theorem B2050283 : Blo 1366502 2050283 := bstep (se 1 (by rfl) ⟨1537712, by rfl⟩ : syracuseStep 2050283 = 3075425) B3075425
theorem B7792919 : Blo 1366502 7792919 := bstep (se 1 (by rfl) ⟨5844689, by rfl⟩ : syracuseStep 7792919 = 11689379) B11689379
theorem B2050343 : Blo 1366502 2050343 := bstep (se 1 (by rfl) ⟨1537757, by rfl⟩ : syracuseStep 2050343 = 3075515) B3075515
theorem B4679993 : Blo 1366502 4679993 := bstep (se 2 (by rfl) ⟨1754997, by rfl⟩ : syracuseStep 4679993 = 3509995) B3509995
theorem B2050427 : Blo 1366502 2050427 := bstep (se 1 (by rfl) ⟨1537820, by rfl⟩ : syracuseStep 2050427 = 3075641) B3075641
theorem B3459611 : Blo 1366502 3459611 := bstep (se 1 (by rfl) ⟨2594708, by rfl⟩ : syracuseStep 3459611 = 5189417) B5189417
theorem B2050697 : Blo 1366502 2050697 := bstep (se 2 (by rfl) ⟨769011, by rfl⟩ : syracuseStep 2050697 = 1538023) B1538023
theorem B4614839 : Blo 1366502 4614839 := bstep (se 1 (by rfl) ⟨3461129, by rfl⟩ : syracuseStep 4614839 = 6922259) B6922259
theorem B2050871 : Blo 1366502 2050871 := bstep (se 1 (by rfl) ⟨1538153, by rfl⟩ : syracuseStep 2050871 = 3076307) B3076307
theorem B2050907 : Blo 1366502 2050907 := bstep (se 1 (by rfl) ⟨1538180, by rfl⟩ : syracuseStep 2050907 = 3076361) B3076361
theorem B1461083 : Blo 1366502 1461083 := bstep (se 1 (by rfl) ⟨1095812, by rfl⟩ : syracuseStep 1461083 = 2191625) B2191625
theorem B7793603 : Blo 1366502 7793603 := bstep (se 1 (by rfl) ⟨5845202, by rfl⟩ : syracuseStep 7793603 = 11690405) B11690405
theorem B2051051 : Blo 1366502 2051051 := bstep (se 1 (by rfl) ⟨1538288, by rfl⟩ : syracuseStep 2051051 = 3076577) B3076577
theorem B3075119 : Blo 1366502 3075119 := bstep (se 1 (by rfl) ⟨2306339, by rfl⟩ : syracuseStep 3075119 = 4612679) B4612679
theorem B11086895 : Blo 1366502 11086895 := bstep (se 1 (by rfl) ⟨8315171, by rfl⟩ : syracuseStep 11086895 = 16630343) B16630343
theorem B2051255 : Blo 1366502 2051255 := bstep (se 1 (by rfl) ⟨1538441, by rfl⟩ : syracuseStep 2051255 = 3076883) B3076883
theorem B9989419 : Blo 1366502 9989419 := bstep (se 1 (by rfl) ⟨7492064, by rfl⟩ : syracuseStep 9989419 = 14984129) B14984129
theorem B3075407 : Blo 1366502 3075407 := bstep (se 1 (by rfl) ⟨2306555, by rfl⟩ : syracuseStep 3075407 = 4613111) B4613111
theorem B2051495 : Blo 1366502 2051495 := bstep (se 1 (by rfl) ⟨1538621, by rfl⟩ : syracuseStep 2051495 = 3077243) B3077243
theorem B3075497 : Blo 1366502 3075497 := bstep (se 2 (by rfl) ⟨1153311, by rfl⟩ : syracuseStep 3075497 = 2306623) B2306623
theorem B3460603 : Blo 1366502 3460603 := bstep (se 1 (by rfl) ⟨2595452, by rfl⟩ : syracuseStep 3460603 = 5190905) B5190905
theorem B2051579 : Blo 1366502 2051579 := bstep (se 1 (by rfl) ⟨1538684, by rfl⟩ : syracuseStep 2051579 = 3077369) B3077369
theorem B2051675 : Blo 1366502 2051675 := bstep (se 1 (by rfl) ⟨1538756, by rfl⟩ : syracuseStep 2051675 = 3077513) B3077513
theorem B3460715 : Blo 1366502 3460715 := bstep (se 1 (by rfl) ⟨2595536, by rfl⟩ : syracuseStep 3460715 = 5191073) B5191073
theorem B2051759 : Blo 1366502 2051759 := bstep (se 1 (by rfl) ⟨1538819, by rfl⟩ : syracuseStep 2051759 = 3077639) B3077639
theorem B2051879 : Blo 1366502 2051879 := bstep (se 1 (by rfl) ⟨1538909, by rfl⟩ : syracuseStep 2051879 = 3077819) B3077819
theorem B7786313 : Blo 1366502 7786313 := bstep (se 2 (by rfl) ⟨2919867, by rfl⟩ : syracuseStep 7786313 = 5839735) B5839735
theorem B2051963 : Blo 1366502 2051963 := bstep (se 1 (by rfl) ⟨1538972, by rfl⟩ : syracuseStep 2051963 = 3077945) B3077945
theorem B3075983 : Blo 1366502 3075983 := bstep (se 1 (by rfl) ⟨2306987, by rfl⟩ : syracuseStep 3075983 = 4613975) B4613975
theorem B8761243 : Blo 1366502 8761243 := bstep (se 1 (by rfl) ⟨6570932, by rfl⟩ : syracuseStep 8761243 = 13141865) B13141865
theorem B15790139 : Blo 1366502 15790139 := bstep (se 1 (by rfl) ⟨11842604, by rfl⟩ : syracuseStep 15790139 = 23685209) B23685209
theorem B8310937 : Blo 1366502 8310937 := bstep (se 2 (by rfl) ⟨3116601, by rfl⟩ : syracuseStep 8310937 = 6233203) B6233203
theorem B2191579 : Blo 1366502 2191579 := bstep (se 1 (by rfl) ⟨1643684, by rfl⟩ : syracuseStep 2191579 = 3287369) B3287369
theorem B2306279 : Blo 1366502 2306279 := bstep (se 1 (by rfl) ⟨1729709, by rfl⟩ : syracuseStep 2306279 = 3459419) B3459419
theorem B6320393 : Blo 1366502 6320393 := bstep (se 2 (by rfl) ⟨2370147, by rfl⟩ : syracuseStep 6320393 = 4740295) B4740295
theorem B2052383 : Blo 1366502 2052383 := bstep (se 1 (by rfl) ⟨1539287, by rfl⟩ : syracuseStep 2052383 = 3078575) B3078575
theorem B19976483 : Blo 1366502 19976483 := bstep (se 1 (by rfl) ⟨14982362, by rfl⟩ : syracuseStep 19976483 = 29964725) B29964725
theorem B2052407 : Blo 1366502 2052407 := bstep (se 1 (by rfl) ⟨1539305, by rfl⟩ : syracuseStep 2052407 = 3078611) B3078611
theorem B13136215 : Blo 1366502 13136215 := bstep (se 1 (by rfl) ⟨9852161, by rfl⟩ : syracuseStep 13136215 = 19704323) B19704323
theorem B2052479 : Blo 1366502 2052479 := bstep (se 1 (by rfl) ⟨1539359, by rfl⟩ : syracuseStep 2052479 = 3078719) B3078719
theorem B2306441 : Blo 1366502 2306441 := bstep (se 2 (by rfl) ⟨864915, by rfl⟩ : syracuseStep 2306441 = 1729831) B1729831
theorem B112325039 : Blo 1366502 112325039 := bstep (se 1 (by rfl) ⟨84243779, by rfl⟩ : syracuseStep 112325039 = 168487559) B168487559
theorem B2052551 : Blo 1366502 2052551 := bstep (se 1 (by rfl) ⟨1539413, by rfl⟩ : syracuseStep 2052551 = 3078827) B3078827
theorem B134951417 : Blo 1366502 134951417 := bstep (se 2 (by rfl) ⟨50606781, by rfl⟩ : syracuseStep 134951417 = 101213563) B101213563
theorem B7787087 : Blo 1366502 7787087 := bstep (se 1 (by rfl) ⟨5840315, by rfl⟩ : syracuseStep 7787087 = 11680631) B11680631
theorem B4616783 : Blo 1366502 4616783 := bstep (se 1 (by rfl) ⟨3462587, by rfl⟩ : syracuseStep 4616783 = 6925175) B6925175
theorem B3076703 : Blo 1366502 3076703 := bstep (se 1 (by rfl) ⟨2307527, by rfl⟩ : syracuseStep 3076703 = 4615055) B4615055
theorem B29979395 : Blo 1366502 29979395 := bstep (se 1 (by rfl) ⟨22484546, by rfl⟩ : syracuseStep 29979395 = 44969093) B44969093
theorem B4379417 : Blo 1366502 4379417 := bstep (se 2 (by rfl) ⟨1642281, by rfl⟩ : syracuseStep 4379417 = 3284563) B3284563
theorem B2306873 : Blo 1366502 2306873 := bstep (se 2 (by rfl) ⟨865077, by rfl⟩ : syracuseStep 2306873 = 1730155) B1730155
theorem B2306927 : Blo 1366502 2306927 := bstep (se 1 (by rfl) ⟨1730195, by rfl⟩ : syracuseStep 2306927 = 3460391) B3460391
theorem B6239101 : Blo 1366502 6239101 := bstep (se 3 (by rfl) ⟨1169831, by rfl⟩ : syracuseStep 6239101 = 2339663) B2339663
theorem B9851843 : Blo 1366502 9851843 := bstep (se 1 (by rfl) ⟨7388882, by rfl⟩ : syracuseStep 9851843 = 14777765) B14777765
theorem B33739739 : Blo 1366502 33739739 := bstep (se 1 (by rfl) ⟨25304804, by rfl⟩ : syracuseStep 33739739 = 50609609) B50609609
theorem B4617323 : Blo 1366502 4617323 := bstep (se 1 (by rfl) ⟨3462992, by rfl⟩ : syracuseStep 4617323 = 6925985) B6925985
theorem B6919343 : Blo 1366502 6919343 := bstep (se 1 (by rfl) ⟨5189507, by rfl⟩ : syracuseStep 6919343 = 10379015) B10379015
theorem B3896495 : Blo 1366502 3896495 := bstep (se 1 (by rfl) ⟨2922371, by rfl⟩ : syracuseStep 3896495 = 5844743) B5844743
theorem B9852191 : Blo 1366502 9852191 := bstep (se 1 (by rfl) ⟨7389143, by rfl⟩ : syracuseStep 9852191 = 14778287) B14778287
theorem B7394657 : Blo 1366502 7394657 := bstep (se 2 (by rfl) ⟨2772996, by rfl⟩ : syracuseStep 7394657 = 5545993) B5545993
theorem B3077531 : Blo 1366502 3077531 := bstep (se 1 (by rfl) ⟨2308148, by rfl⟩ : syracuseStep 3077531 = 4616297) B4616297
theorem B7788089 : Blo 1366502 7788089 := bstep (se 2 (by rfl) ⟨2920533, by rfl⟩ : syracuseStep 7788089 = 5841067) B5841067
theorem B6567743 : Blo 1366502 6567743 := bstep (se 1 (by rfl) ⟨4925807, by rfl⟩ : syracuseStep 6567743 = 9851615) B9851615
theorem B2307919 : Blo 1366502 2307919 := bstep (se 1 (by rfl) ⟨1730939, by rfl⟩ : syracuseStep 2307919 = 3461879) B3461879
theorem B8763241 : Blo 1366502 8763241 := bstep (se 2 (by rfl) ⟨3286215, by rfl⟩ : syracuseStep 8763241 = 6572431) B6572431
theorem B3078107 : Blo 1366502 3078107 := bstep (se 1 (by rfl) ⟨2308580, by rfl⟩ : syracuseStep 3078107 = 4617161) B4617161
theorem B7788545 : Blo 1366502 7788545 := bstep (se 2 (by rfl) ⟨2920704, by rfl⟩ : syracuseStep 7788545 = 5841409) B5841409
theorem B3078287 : Blo 1366502 3078287 := bstep (se 1 (by rfl) ⟨2308715, by rfl⟩ : syracuseStep 3078287 = 4617431) B4617431
theorem B1538203 : Blo 1366502 1538203 := bstep (se 1 (by rfl) ⟨1153652, by rfl⟩ : syracuseStep 1538203 = 2307305) B2307305
theorem B3078305 : Blo 1366502 3078305 := bstep (se 2 (by rfl) ⟨1154364, by rfl⟩ : syracuseStep 3078305 = 2308729) B2308729
theorem B1538239 : Blo 1366502 1538239 := bstep (se 1 (by rfl) ⟨1153679, by rfl⟩ : syracuseStep 1538239 = 2307359) B2307359
theorem B3078377 : Blo 1366502 3078377 := bstep (se 2 (by rfl) ⟨1154391, by rfl⟩ : syracuseStep 3078377 = 2308783) B2308783
theorem B2308331 : Blo 1366502 2308331 := bstep (se 1 (by rfl) ⟨1731248, by rfl⟩ : syracuseStep 2308331 = 3462497) B3462497
theorem B1947883 : Blo 1366502 1947883 := bstep (se 1 (by rfl) ⟨1460912, by rfl⟩ : syracuseStep 1947883 = 2921825) B2921825
theorem B5192045 : Blo 1366502 5192045 := bstep (se 3 (by rfl) ⟨973508, by rfl⟩ : syracuseStep 5192045 = 1947017) B1947017
theorem B4618619 : Blo 1366502 4618619 := bstep (se 1 (by rfl) ⟨3463964, by rfl⟩ : syracuseStep 4618619 = 6927929) B6927929
theorem B17512949 : Blo 1366502 17512949 := bstep (se 5 (by rfl) ⟨820919, by rfl⟩ : syracuseStep 17512949 = 1641839) B1641839
theorem B1366555 : Blo 1366502 1366555 := bstep (se 1 (by rfl) ⟨1024916, by rfl⟩ : syracuseStep 1366555 = 2049833) B2049833
theorem B1366559 : Blo 1366502 1366559 := bstep (se 1 (by rfl) ⟨1024919, by rfl⟩ : syracuseStep 1366559 = 2049839) B2049839
theorem B6920801 : Blo 1366502 6920801 := bstep (se 2 (by rfl) ⟨2595300, by rfl⟩ : syracuseStep 6920801 = 5190601) B5190601
theorem B7387847 : Blo 1366502 7387847 := bstep (se 1 (by rfl) ⟨5540885, by rfl⟩ : syracuseStep 7387847 = 11081771) B11081771
theorem B4160335 : Blo 1366502 4160335 := bstep (se 1 (by rfl) ⟨3120251, by rfl⟩ : syracuseStep 4160335 = 6240503) B6240503
theorem B1366875 : Blo 1366502 1366875 := bstep (se 1 (by rfl) ⟨1025156, by rfl⟩ : syracuseStep 1366875 = 2050313) B2050313
theorem B3160937 : Blo 1366502 3160937 := bstep (se 2 (by rfl) ⟨1185351, by rfl⟩ : syracuseStep 3160937 = 2370703) B2370703
theorem B63159193 : Blo 1366502 63159193 := bstep (se 2 (by rfl) ⟨23684697, by rfl⟩ : syracuseStep 63159193 = 47369395) B47369395
theorem B1366943 : Blo 1366502 1366943 := bstep (se 1 (by rfl) ⟨1025207, by rfl⟩ : syracuseStep 1366943 = 2050415) B2050415
theorem B2309161 : Blo 1366502 2309161 := bstep (se 2 (by rfl) ⟨865935, by rfl⟩ : syracuseStep 2309161 = 1731871) B1731871
theorem B1367087 : Blo 1366502 1367087 := bstep (se 1 (by rfl) ⟨1025315, by rfl⟩ : syracuseStep 1367087 = 2050631) B2050631
theorem B1367111 : Blo 1366502 1367111 := bstep (se 1 (by rfl) ⟨1025333, by rfl⟩ : syracuseStep 1367111 = 2050667) B2050667
theorem B2464951 : Blo 1366502 2464951 := bstep (se 1 (by rfl) ⟨1848713, by rfl⟩ : syracuseStep 2464951 = 3697427) B3697427
theorem B2309303 : Blo 1366502 2309303 := bstep (se 1 (by rfl) ⟨1731977, by rfl⟩ : syracuseStep 2309303 = 3463955) B3463955
theorem B1367263 : Blo 1366502 1367263 := bstep (se 1 (by rfl) ⟨1025447, by rfl⟩ : syracuseStep 1367263 = 2050895) B2050895
theorem B11091239 : Blo 1366502 11091239 := bstep (se 1 (by rfl) ⟨8318429, by rfl⟩ : syracuseStep 11091239 = 16636859) B16636859
theorem B6921611 : Blo 1366502 6921611 := bstep (se 1 (by rfl) ⟨5191208, by rfl⟩ : syracuseStep 6921611 = 10382417) B10382417
theorem B1367527 : Blo 1366502 1367527 := bstep (se 1 (by rfl) ⟨1025645, by rfl⟩ : syracuseStep 1367527 = 2051291) B2051291
theorem B1367643 : Blo 1366502 1367643 := bstep (se 1 (by rfl) ⟨1025732, by rfl⟩ : syracuseStep 1367643 = 2051465) B2051465
theorem B4382441 : Blo 1366502 4382441 := bstep (se 2 (by rfl) ⟨1643415, by rfl⟩ : syracuseStep 4382441 = 3286831) B3286831
theorem B159751997 : Blo 1366502 159751997 := bstep (se 3 (by rfl) ⟨29953499, by rfl⟩ : syracuseStep 159751997 = 59906999) B59906999
theorem B1367879 : Blo 1366502 1367879 := bstep (se 1 (by rfl) ⟨1025909, by rfl⟩ : syracuseStep 1367879 = 2051819) B2051819
theorem B15572897 : Blo 1366502 15572897 := bstep (se 2 (by rfl) ⟨5839836, by rfl⟩ : syracuseStep 15572897 = 11679673) B11679673
theorem B1368031 : Blo 1366502 1368031 := bstep (se 1 (by rfl) ⟨1026023, by rfl⟩ : syracuseStep 1368031 = 2052047) B2052047
theorem B10526759 : Blo 1366502 10526759 := bstep (se 1 (by rfl) ⟨7895069, by rfl⟩ : syracuseStep 10526759 = 15790139) B15790139
theorem B1368255 : Blo 1366502 1368255 := bstep (se 1 (by rfl) ⟨1026191, by rfl⟩ : syracuseStep 1368255 = 2052383) B2052383
theorem B1368271 : Blo 1366502 1368271 := bstep (se 1 (by rfl) ⟨1026203, by rfl⟩ : syracuseStep 1368271 = 2052407) B2052407
theorem B1368319 : Blo 1366502 1368319 := bstep (se 1 (by rfl) ⟨1026239, by rfl⟩ : syracuseStep 1368319 = 2052479) B2052479
theorem B74883359 : Blo 1366502 74883359 := bstep (se 1 (by rfl) ⟨56162519, by rfl⟩ : syracuseStep 74883359 = 112325039) B112325039
theorem B1368367 : Blo 1366502 1368367 := bstep (se 1 (by rfl) ⟨1026275, by rfl⟩ : syracuseStep 1368367 = 2052551) B2052551
theorem B4612409 : Blo 1366502 4612409 := bstep (se 2 (by rfl) ⟨1729653, by rfl⟩ : syracuseStep 4612409 = 3459307) B3459307
theorem B2597177 : Blo 1366502 2597177 := bstep (se 2 (by rfl) ⟨973941, by rfl⟩ : syracuseStep 2597177 = 1947883) B1947883
theorem B17514953 : Blo 1366502 17514953 := bstep (se 2 (by rfl) ⟨6568107, by rfl⟩ : syracuseStep 17514953 = 13136215) B13136215
theorem B11682407 : Blo 1366502 11682407 := bstep (se 1 (by rfl) ⟨8761805, by rfl⟩ : syracuseStep 11682407 = 17523611) B17523611
theorem B4612895 : Blo 1366502 4612895 := bstep (se 1 (by rfl) ⟨3459671, by rfl⟩ : syracuseStep 4612895 = 6919343) B6919343
theorem B2597663 : Blo 1366502 2597663 := bstep (se 1 (by rfl) ⟨1948247, by rfl⟩ : syracuseStep 2597663 = 3896495) B3896495
theorem B19719085 : Blo 1366502 19719085 := bstep (se 3 (by rfl) ⟨3697328, by rfl⟩ : syracuseStep 19719085 = 7394657) B7394657
theorem B5547113 : Blo 1366502 5547113 := bstep (se 2 (by rfl) ⟨2080167, by rfl⟩ : syracuseStep 5547113 = 4160335) B4160335
theorem B252675287 : Blo 1366502 252675287 := bstep (se 1 (by rfl) ⟨189506465, by rfl⟩ : syracuseStep 252675287 = 379012931) B379012931
theorem B24954115 : Blo 1366502 24954115 := bstep (se 1 (by rfl) ⟨18715586, by rfl⟩ : syracuseStep 24954115 = 37431173) B37431173
theorem B5195279 : Blo 1366502 5195279 := bstep (se 1 (by rfl) ⟨3896459, by rfl⟩ : syracuseStep 5195279 = 7792919) B7792919
theorem B3286601 : Blo 1366502 3286601 := bstep (se 2 (by rfl) ⟨1232475, by rfl⟩ : syracuseStep 3286601 = 2464951) B2464951
theorem B11675299 : Blo 1366502 11675299 := bstep (se 1 (by rfl) ⟨8756474, by rfl⟩ : syracuseStep 11675299 = 17512949) B17512949
theorem B4613867 : Blo 1366502 4613867 := bstep (se 1 (by rfl) ⟨3460400, by rfl⟩ : syracuseStep 4613867 = 6920801) B6920801
theorem B4925231 : Blo 1366502 4925231 := bstep (se 1 (by rfl) ⟨3693923, by rfl⟩ : syracuseStep 4925231 = 7387847) B7387847
theorem B2107291 : Blo 1366502 2107291 := bstep (se 1 (by rfl) ⟨1580468, by rfl⟩ : syracuseStep 2107291 = 3160937) B3160937
theorem B5195735 : Blo 1366502 5195735 := bstep (se 1 (by rfl) ⟨3896801, by rfl⟩ : syracuseStep 5195735 = 7793603) B7793603
theorem B4614137 : Blo 1366502 4614137 := bstep (se 2 (by rfl) ⟨1730301, by rfl⟩ : syracuseStep 4614137 = 3460603) B3460603
theorem B2050079 : Blo 1366502 2050079 := bstep (se 1 (by rfl) ⟨1537559, by rfl⟩ : syracuseStep 2050079 = 3075119) B3075119
theorem B7391263 : Blo 1366502 7391263 := bstep (se 1 (by rfl) ⟨5543447, by rfl⟩ : syracuseStep 7391263 = 11086895) B11086895
theorem B2050271 : Blo 1366502 2050271 := bstep (se 1 (by rfl) ⟨1537703, by rfl⟩ : syracuseStep 2050271 = 3075407) B3075407
theorem B4614407 : Blo 1366502 4614407 := bstep (se 1 (by rfl) ⟨3460805, by rfl⟩ : syracuseStep 4614407 = 6921611) B6921611
theorem B2050331 : Blo 1366502 2050331 := bstep (se 1 (by rfl) ⟨1537748, by rfl⟩ : syracuseStep 2050331 = 3075497) B3075497
theorem B11684321 : Blo 1366502 11684321 := bstep (se 2 (by rfl) ⟨4381620, by rfl⟩ : syracuseStep 11684321 = 8763241) B8763241
theorem B2050655 : Blo 1366502 2050655 := bstep (se 1 (by rfl) ⟨1537991, by rfl⟩ : syracuseStep 2050655 = 3075983) B3075983
theorem B10381931 : Blo 1366502 10381931 := bstep (se 1 (by rfl) ⟨7786448, by rfl⟩ : syracuseStep 10381931 = 15572897) B15572897
theorem B4213595 : Blo 1366502 4213595 := bstep (se 1 (by rfl) ⟨3160196, by rfl⟩ : syracuseStep 4213595 = 6320393) B6320393
theorem B2050937 : Blo 1366502 2050937 := bstep (se 2 (by rfl) ⟨769101, by rfl⟩ : syracuseStep 2050937 = 1538203) B1538203
theorem B2050985 : Blo 1366502 2050985 := bstep (se 2 (by rfl) ⟨769119, by rfl⟩ : syracuseStep 2050985 = 1538239) B1538239
theorem B89967611 : Blo 1366502 89967611 := bstep (se 1 (by rfl) ⟨67475708, by rfl⟩ : syracuseStep 89967611 = 134951417) B134951417
theorem B2051135 : Blo 1366502 2051135 := bstep (se 1 (by rfl) ⟨1538351, by rfl⟩ : syracuseStep 2051135 = 3076703) B3076703
theorem B3894455 : Blo 1366502 3894455 := bstep (se 1 (by rfl) ⟨2920841, by rfl⟩ : syracuseStep 3894455 = 5841683) B5841683
theorem B2919611 : Blo 1366502 2919611 := bstep (se 1 (by rfl) ⟨2189708, by rfl⟩ : syracuseStep 2919611 = 4379417) B4379417
theorem B3075551 : Blo 1366502 3075551 := bstep (se 1 (by rfl) ⟨2306663, by rfl⟩ : syracuseStep 3075551 = 4613327) B4613327
theorem B4681307 : Blo 1366502 4681307 := bstep (se 1 (by rfl) ⟨3510980, by rfl⟩ : syracuseStep 4681307 = 7021961) B7021961
theorem B2051687 : Blo 1366502 2051687 := bstep (se 1 (by rfl) ⟨1538765, by rfl⟩ : syracuseStep 2051687 = 3077531) B3077531
theorem B6237803 : Blo 1366502 6237803 := bstep (se 1 (by rfl) ⟨4678352, by rfl⟩ : syracuseStep 6237803 = 9356705) B9356705
theorem B3075767 : Blo 1366502 3075767 := bstep (se 1 (by rfl) ⟨2306825, by rfl⟩ : syracuseStep 3075767 = 4613651) B4613651
theorem B8318801 : Blo 1366502 8318801 := bstep (se 2 (by rfl) ⟨3119550, by rfl⟩ : syracuseStep 8318801 = 6239101) B6239101
theorem B4378495 : Blo 1366502 4378495 := bstep (se 1 (by rfl) ⟨3283871, by rfl⟩ : syracuseStep 4378495 = 6567743) B6567743
theorem B2052071 : Blo 1366502 2052071 := bstep (se 1 (by rfl) ⟨1539053, by rfl⟩ : syracuseStep 2052071 = 3078107) B3078107
theorem B2052191 : Blo 1366502 2052191 := bstep (se 1 (by rfl) ⟨1539143, by rfl⟩ : syracuseStep 2052191 = 3078287) B3078287
theorem B2052203 : Blo 1366502 2052203 := bstep (se 1 (by rfl) ⟨1539152, by rfl⟩ : syracuseStep 2052203 = 3078305) B3078305
theorem B11087999 : Blo 1366502 11087999 := bstep (se 1 (by rfl) ⟨8315999, by rfl⟩ : syracuseStep 11087999 = 16631999) B16631999
theorem B2306191 : Blo 1366502 2306191 := bstep (se 1 (by rfl) ⟨1729643, by rfl⟩ : syracuseStep 2306191 = 3459287) B3459287
theorem B2052251 : Blo 1366502 2052251 := bstep (se 1 (by rfl) ⟨1539188, by rfl⟩ : syracuseStep 2052251 = 3078377) B3078377
theorem B3461363 : Blo 1366502 3461363 := bstep (se 1 (by rfl) ⟨2596022, by rfl⟩ : syracuseStep 3461363 = 5192045) B5192045
theorem B2306407 : Blo 1366502 2306407 := bstep (se 1 (by rfl) ⟨1729805, by rfl⟩ : syracuseStep 2306407 = 3459611) B3459611
theorem B3076559 : Blo 1366502 3076559 := bstep (se 1 (by rfl) ⟨2307419, by rfl⟩ : syracuseStep 3076559 = 4614839) B4614839
theorem B7394159 : Blo 1366502 7394159 := bstep (se 1 (by rfl) ⟨5545619, by rfl⟩ : syracuseStep 7394159 = 11091239) B11091239
theorem B3896221 : Blo 1366502 3896221 := bstep (se 3 (by rfl) ⟨730541, by rfl⟩ : syracuseStep 3896221 = 1461083) B1461083
theorem B2307143 : Blo 1366502 2307143 := bstep (se 1 (by rfl) ⟨1730357, by rfl⟩ : syracuseStep 2307143 = 3460715) B3460715
theorem B3077225 : Blo 1366502 3077225 := bstep (se 2 (by rfl) ⟨1153959, by rfl⟩ : syracuseStep 3077225 = 2307919) B2307919
theorem B2921627 : Blo 1366502 2921627 := bstep (se 1 (by rfl) ⟨2191220, by rfl⟩ : syracuseStep 2921627 = 4382441) B4382441
theorem B106501331 : Blo 1366502 106501331 := bstep (se 1 (by rfl) ⟨79875998, by rfl⟩ : syracuseStep 106501331 = 159751997) B159751997
theorem B5190875 : Blo 1366502 5190875 := bstep (se 1 (by rfl) ⟨3893156, by rfl⟩ : syracuseStep 5190875 = 7786313) B7786313
theorem B16864631 : Blo 1366502 16864631 := bstep (se 1 (by rfl) ⟨12648473, by rfl⟩ : syracuseStep 16864631 = 25296947) B25296947
theorem B6575489 : Blo 1366502 6575489 := bstep (se 2 (by rfl) ⟨2465808, by rfl⟩ : syracuseStep 6575489 = 4931617) B4931617
theorem B1537519 : Blo 1366502 1537519 := bstep (se 1 (by rfl) ⟨1153139, by rfl⟩ : syracuseStep 1537519 = 2306279) B2306279
theorem B13317655 : Blo 1366502 13317655 := bstep (se 1 (by rfl) ⟨9988241, by rfl⟩ : syracuseStep 13317655 = 19976483) B19976483
theorem B11081249 : Blo 1366502 11081249 := bstep (se 2 (by rfl) ⟨4155468, by rfl⟩ : syracuseStep 11081249 = 8310937) B8310937
theorem B1537627 : Blo 1366502 1537627 := bstep (se 1 (by rfl) ⟨1153220, by rfl⟩ : syracuseStep 1537627 = 2306441) B2306441
theorem B5191391 : Blo 1366502 5191391 := bstep (se 1 (by rfl) ⟨3893543, by rfl⟩ : syracuseStep 5191391 = 7787087) B7787087
theorem B3077855 : Blo 1366502 3077855 := bstep (se 1 (by rfl) ⟨2308391, by rfl⟩ : syracuseStep 3077855 = 4616783) B4616783
theorem B7395067 : Blo 1366502 7395067 := bstep (se 1 (by rfl) ⟨5546300, by rfl⟩ : syracuseStep 7395067 = 11092601) B11092601
theorem B3462983 : Blo 1366502 3462983 := bstep (se 1 (by rfl) ⟨2597237, by rfl⟩ : syracuseStep 3462983 = 5194475) B5194475
theorem B2922311 : Blo 1366502 2922311 := bstep (se 1 (by rfl) ⟨2191733, by rfl⟩ : syracuseStep 2922311 = 4383467) B4383467
theorem B19986263 : Blo 1366502 19986263 := bstep (se 1 (by rfl) ⟨14989697, by rfl⟩ : syracuseStep 19986263 = 29979395) B29979395
theorem B1537915 : Blo 1366502 1537915 := bstep (se 1 (by rfl) ⟨1153436, by rfl⟩ : syracuseStep 1537915 = 2306873) B2306873
theorem B1537951 : Blo 1366502 1537951 := bstep (se 1 (by rfl) ⟨1153463, by rfl⟩ : syracuseStep 1537951 = 2306927) B2306927
theorem B6567895 : Blo 1366502 6567895 := bstep (se 1 (by rfl) ⟨4925921, by rfl⟩ : syracuseStep 6567895 = 9851843) B9851843
theorem B22493159 : Blo 1366502 22493159 := bstep (se 1 (by rfl) ⟨16869869, by rfl⟩ : syracuseStep 22493159 = 33739739) B33739739
theorem B3078215 : Blo 1366502 3078215 := bstep (se 1 (by rfl) ⟨2308661, by rfl⟩ : syracuseStep 3078215 = 4617323) B4617323
theorem B6568127 : Blo 1366502 6568127 := bstep (se 1 (by rfl) ⟨4926095, by rfl⟩ : syracuseStep 6568127 = 9852191) B9852191
theorem B76863755 : Blo 1366502 76863755 := bstep (se 1 (by rfl) ⟨57647816, by rfl⟩ : syracuseStep 76863755 = 115295633) B115295633
theorem B14792989 : Blo 1366502 14792989 := bstep (se 3 (by rfl) ⟨2773685, by rfl⟩ : syracuseStep 14792989 = 5547371) B5547371
theorem B5192059 : Blo 1366502 5192059 := bstep (se 1 (by rfl) ⟨3894044, by rfl⟩ : syracuseStep 5192059 = 7788089) B7788089
theorem B11688421 : Blo 1366502 11688421 := bstep (se 4 (by rfl) ⟨1095789, by rfl⟩ : syracuseStep 11688421 = 2191579) B2191579
theorem B1366503 : Blo 1366502 1366503 := bstep (se 1 (by rfl) ⟨1024877, by rfl⟩ : syracuseStep 1366503 = 2049755) B2049755
theorem B4381211 : Blo 1366502 4381211 := bstep (se 1 (by rfl) ⟨3285908, by rfl⟩ : syracuseStep 4381211 = 6571817) B6571817
theorem B84212257 : Blo 1366502 84212257 := bstep (se 2 (by rfl) ⟨31579596, by rfl⟩ : syracuseStep 84212257 = 63159193) B63159193
theorem B1366619 : Blo 1366502 1366619 := bstep (se 1 (by rfl) ⟨1024964, by rfl⟩ : syracuseStep 1366619 = 2049929) B2049929
theorem B1366687 : Blo 1366502 1366687 := bstep (se 1 (by rfl) ⟨1025015, by rfl⟩ : syracuseStep 1366687 = 2050031) B2050031
theorem B5192363 : Blo 1366502 5192363 := bstep (se 1 (by rfl) ⟨3894272, by rfl⟩ : syracuseStep 5192363 = 7788545) B7788545
theorem B3078881 : Blo 1366502 3078881 := bstep (se 2 (by rfl) ⟨1154580, by rfl⟩ : syracuseStep 3078881 = 2309161) B2309161
theorem B11688695 : Blo 1366502 11688695 := bstep (se 1 (by rfl) ⟨8766521, by rfl⟩ : syracuseStep 11688695 = 17533043) B17533043
theorem B1366855 : Blo 1366502 1366855 := bstep (se 1 (by rfl) ⟨1025141, by rfl⟩ : syracuseStep 1366855 = 2050283) B2050283
theorem B1538887 : Blo 1366502 1538887 := bstep (se 1 (by rfl) ⟨1154165, by rfl⟩ : syracuseStep 1538887 = 2308331) B2308331
theorem B1366895 : Blo 1366502 1366895 := bstep (se 1 (by rfl) ⟨1025171, by rfl⟩ : syracuseStep 1366895 = 2050343) B2050343
theorem B3119995 : Blo 1366502 3119995 := bstep (se 1 (by rfl) ⟨2339996, by rfl⟩ : syracuseStep 3119995 = 4679993) B4679993
theorem B1366951 : Blo 1366502 1366951 := bstep (se 1 (by rfl) ⟨1025213, by rfl⟩ : syracuseStep 1366951 = 2050427) B2050427
theorem B3079079 : Blo 1366502 3079079 := bstep (se 1 (by rfl) ⟨2309309, by rfl⟩ : syracuseStep 3079079 = 4618619) B4618619
theorem B13319225 : Blo 1366502 13319225 := bstep (se 2 (by rfl) ⟨4994709, by rfl⟩ : syracuseStep 13319225 = 9989419) B9989419
theorem B1367131 : Blo 1366502 1367131 := bstep (se 1 (by rfl) ⟨1025348, by rfl⟩ : syracuseStep 1367131 = 2050697) B2050697
theorem B1367247 : Blo 1366502 1367247 := bstep (se 1 (by rfl) ⟨1025435, by rfl⟩ : syracuseStep 1367247 = 2050871) B2050871
theorem B1367271 : Blo 1366502 1367271 := bstep (se 1 (by rfl) ⟨1025453, by rfl⟩ : syracuseStep 1367271 = 2050907) B2050907
theorem B1367367 : Blo 1366502 1367367 := bstep (se 1 (by rfl) ⟨1025525, by rfl⟩ : syracuseStep 1367367 = 2051051) B2051051
theorem B1367503 : Blo 1366502 1367503 := bstep (se 1 (by rfl) ⟨1025627, by rfl⟩ : syracuseStep 1367503 = 2051255) B2051255
theorem B1539535 : Blo 1366502 1539535 := bstep (se 1 (by rfl) ⟨1154651, by rfl⟩ : syracuseStep 1539535 = 2309303) B2309303
theorem B1367663 : Blo 1366502 1367663 := bstep (se 1 (by rfl) ⟨1025747, by rfl⟩ : syracuseStep 1367663 = 2051495) B2051495
theorem B1367719 : Blo 1366502 1367719 := bstep (se 1 (by rfl) ⟨1025789, by rfl⟩ : syracuseStep 1367719 = 2051579) B2051579
theorem B1367783 : Blo 1366502 1367783 := bstep (se 1 (by rfl) ⟨1025837, by rfl⟩ : syracuseStep 1367783 = 2051675) B2051675
theorem B1367839 : Blo 1366502 1367839 := bstep (se 1 (by rfl) ⟨1025879, by rfl⟩ : syracuseStep 1367839 = 2051759) B2051759
theorem B1367919 : Blo 1366502 1367919 := bstep (se 1 (by rfl) ⟨1025939, by rfl⟩ : syracuseStep 1367919 = 2051879) B2051879
theorem B11681657 : Blo 1366502 11681657 := bstep (se 2 (by rfl) ⟨4380621, by rfl⟩ : syracuseStep 11681657 = 8761243) B8761243
theorem B1367975 : Blo 1366502 1367975 := bstep (se 1 (by rfl) ⟨1025981, by rfl⟩ : syracuseStep 1367975 = 2051963) B2051963
theorem B9855017 : Blo 1366502 9855017 := bstep (se 2 (by rfl) ⟨3695631, by rfl⟩ : syracuseStep 9855017 = 7391263) B7391263
theorem B1368127 : Blo 1366502 1368127 := bstep (se 1 (by rfl) ⟨1026095, by rfl⟩ : syracuseStep 1368127 = 2052191) B2052191
theorem B1368135 : Blo 1366502 1368135 := bstep (se 1 (by rfl) ⟨1026101, by rfl⟩ : syracuseStep 1368135 = 2052203) B2052203
theorem B1368167 : Blo 1366502 1368167 := bstep (se 1 (by rfl) ⟨1026125, by rfl⟩ : syracuseStep 1368167 = 2052251) B2052251
theorem B49922239 : Blo 1366502 49922239 := bstep (se 1 (by rfl) ⟨37441679, by rfl⟩ : syracuseStep 49922239 = 74883359) B74883359
theorem B7791005 : Blo 1366502 7791005 := bstep (se 3 (by rfl) ⟨1460813, by rfl⟩ : syracuseStep 7791005 = 2921627) B2921627
theorem B6922745 : Blo 1366502 6922745 := bstep (se 2 (by rfl) ⟨2596029, by rfl⟩ : syracuseStep 6922745 = 5192059) B5192059
theorem B71000887 : Blo 1366502 71000887 := bstep (se 1 (by rfl) ⟨53250665, by rfl⟩ : syracuseStep 71000887 = 106501331) B106501331
theorem B4383659 : Blo 1366502 4383659 := bstep (se 1 (by rfl) ⟨3287744, by rfl⟩ : syracuseStep 4383659 = 6575489) B6575489
theorem B5194961 : Blo 1366502 5194961 := bstep (se 2 (by rfl) ⟨1948110, by rfl⟩ : syracuseStep 5194961 = 3896221) B3896221
theorem B51242503 : Blo 1366502 51242503 := bstep (se 1 (by rfl) ⟨38431877, by rfl⟩ : syracuseStep 51242503 = 76863755) B76863755
theorem B7792463 : Blo 1366502 7792463 := bstep (se 1 (by rfl) ⟨5844347, by rfl⟩ : syracuseStep 7792463 = 11688695) B11688695
theorem B2050025 : Blo 1366502 2050025 := bstep (se 2 (by rfl) ⟨768759, by rfl⟩ : syracuseStep 2050025 = 1537519) B1537519
theorem B2050169 : Blo 1366502 2050169 := bstep (se 2 (by rfl) ⟨768813, by rfl⟩ : syracuseStep 2050169 = 1537627) B1537627
theorem B15567065 : Blo 1366502 15567065 := bstep (se 2 (by rfl) ⟨5837649, by rfl⟩ : syracuseStep 15567065 = 11675299) B11675299
theorem B2050367 : Blo 1366502 2050367 := bstep (se 1 (by rfl) ⟨1537775, by rfl⟩ : syracuseStep 2050367 = 3075551) B3075551
theorem B2050511 : Blo 1366502 2050511 := bstep (se 1 (by rfl) ⟨1537883, by rfl⟩ : syracuseStep 2050511 = 3075767) B3075767
theorem B2050553 : Blo 1366502 2050553 := bstep (se 2 (by rfl) ⟨768957, by rfl⟩ : syracuseStep 2050553 = 1537915) B1537915
theorem B2050601 : Blo 1366502 2050601 := bstep (se 2 (by rfl) ⟨768975, by rfl⟩ : syracuseStep 2050601 = 1537951) B1537951
theorem B7391999 : Blo 1366502 7391999 := bstep (se 1 (by rfl) ⟨5543999, by rfl⟩ : syracuseStep 7391999 = 11087999) B11087999
theorem B3074921 : Blo 1366502 3074921 := bstep (se 2 (by rfl) ⟨1153095, by rfl⟩ : syracuseStep 3074921 = 2306191) B2306191
theorem B3074939 : Blo 1366502 3074939 := bstep (se 1 (by rfl) ⟨2306204, by rfl⟩ : syracuseStep 3074939 = 4612409) B4612409
theorem B1731451 : Blo 1366502 1731451 := bstep (se 1 (by rfl) ⟨1298588, by rfl⟩ : syracuseStep 1731451 = 2597177) B2597177
theorem B11676635 : Blo 1366502 11676635 := bstep (se 1 (by rfl) ⟨8757476, by rfl⟩ : syracuseStep 11676635 = 17514953) B17514953
theorem B2051039 : Blo 1366502 2051039 := bstep (se 1 (by rfl) ⟨1538279, by rfl⟩ : syracuseStep 2051039 = 3076559) B3076559
theorem B3075209 : Blo 1366502 3075209 := bstep (se 2 (by rfl) ⟨1153203, by rfl⟩ : syracuseStep 3075209 = 2306407) B2306407
theorem B7785629 : Blo 1366502 7785629 := bstep (se 3 (by rfl) ⟨1459805, by rfl⟩ : syracuseStep 7785629 = 2919611) B2919611
theorem B3075263 : Blo 1366502 3075263 := bstep (se 1 (by rfl) ⟨2306447, by rfl⟩ : syracuseStep 3075263 = 4612895) B4612895
theorem B1731775 : Blo 1366502 1731775 := bstep (se 1 (by rfl) ⟨1298831, by rfl⟩ : syracuseStep 1731775 = 2597663) B2597663
theorem B15584561 : Blo 1366502 15584561 := bstep (se 2 (by rfl) ⟨5844210, by rfl⟩ : syracuseStep 15584561 = 11688421) B11688421
theorem B112283009 : Blo 1366502 112283009 := bstep (se 2 (by rfl) ⟨42106128, by rfl⟩ : syracuseStep 112283009 = 84212257) B84212257
theorem B2051483 : Blo 1366502 2051483 := bstep (se 1 (by rfl) ⟨1538612, by rfl⟩ : syracuseStep 2051483 = 3077225) B3077225
theorem B3698075 : Blo 1366502 3698075 := bstep (se 1 (by rfl) ⟨2773556, by rfl⟩ : syracuseStep 3698075 = 5547113) B5547113
theorem B3460583 : Blo 1366502 3460583 := bstep (se 1 (by rfl) ⟨2595437, by rfl⟩ : syracuseStep 3460583 = 5190875) B5190875
theorem B11243087 : Blo 1366502 11243087 := bstep (se 1 (by rfl) ⟨8432315, by rfl⟩ : syracuseStep 11243087 = 16864631) B16864631
theorem B2191067 : Blo 1366502 2191067 := bstep (se 1 (by rfl) ⟨1643300, by rfl⟩ : syracuseStep 2191067 = 3286601) B3286601
theorem B2051849 : Blo 1366502 2051849 := bstep (se 2 (by rfl) ⟨769443, by rfl⟩ : syracuseStep 2051849 = 1538887) B1538887
theorem B3460927 : Blo 1366502 3460927 := bstep (se 1 (by rfl) ⟨2595695, by rfl⟩ : syracuseStep 3460927 = 5191391) B5191391
theorem B2051903 : Blo 1366502 2051903 := bstep (se 1 (by rfl) ⟨1538927, by rfl⟩ : syracuseStep 2051903 = 3077855) B3077855
theorem B3075911 : Blo 1366502 3075911 := bstep (se 1 (by rfl) ⟨2306933, by rfl⟩ : syracuseStep 3075911 = 4613867) B4613867
theorem B13324175 : Blo 1366502 13324175 := bstep (se 1 (by rfl) ⟨9993131, by rfl⟩ : syracuseStep 13324175 = 19986263) B19986263
theorem B26292113 : Blo 1366502 26292113 := bstep (se 2 (by rfl) ⟨9859542, by rfl⟩ : syracuseStep 26292113 = 19719085) B19719085
theorem B39440357 : Blo 1366502 39440357 := bstep (se 4 (by rfl) ⟨3697533, by rfl⟩ : syracuseStep 39440357 = 7395067) B7395067
theorem B14995439 : Blo 1366502 14995439 := bstep (se 1 (by rfl) ⟨11246579, by rfl⟩ : syracuseStep 14995439 = 22493159) B22493159
theorem B3076091 : Blo 1366502 3076091 := bstep (se 1 (by rfl) ⟨2307068, by rfl⟩ : syracuseStep 3076091 = 4614137) B4614137
theorem B2052143 : Blo 1366502 2052143 := bstep (se 1 (by rfl) ⟨1539107, by rfl⟩ : syracuseStep 2052143 = 3078215) B3078215
theorem B4378751 : Blo 1366502 4378751 := bstep (se 1 (by rfl) ⟨3284063, by rfl⟩ : syracuseStep 4378751 = 6568127) B6568127
theorem B3076271 : Blo 1366502 3076271 := bstep (se 1 (by rfl) ⟨2307203, by rfl⟩ : syracuseStep 3076271 = 4614407) B4614407
theorem B33272153 : Blo 1366502 33272153 := bstep (se 2 (by rfl) ⟨12477057, by rfl⟩ : syracuseStep 33272153 = 24954115) B24954115
theorem B2920807 : Blo 1366502 2920807 := bstep (se 1 (by rfl) ⟨2190605, by rfl⟩ : syracuseStep 2920807 = 4381211) B4381211
theorem B3461575 : Blo 1366502 3461575 := bstep (se 1 (by rfl) ⟨2596181, by rfl⟩ : syracuseStep 3461575 = 5192363) B5192363
theorem B2052587 : Blo 1366502 2052587 := bstep (se 1 (by rfl) ⟨1539440, by rfl⟩ : syracuseStep 2052587 = 3078881) B3078881
theorem B2052713 : Blo 1366502 2052713 := bstep (se 2 (by rfl) ⟨769767, by rfl⟩ : syracuseStep 2052713 = 1539535) B1539535
theorem B2052719 : Blo 1366502 2052719 := bstep (se 1 (by rfl) ⟨1539539, by rfl⟩ : syracuseStep 2052719 = 3079079) B3079079
theorem B59978407 : Blo 1366502 59978407 := bstep (se 1 (by rfl) ⟨44983805, by rfl⟩ : syracuseStep 59978407 = 89967611) B89967611
theorem B17756873 : Blo 1366502 17756873 := bstep (se 2 (by rfl) ⟨6658827, by rfl⟩ : syracuseStep 17756873 = 13317655) B13317655
theorem B4158535 : Blo 1366502 4158535 := bstep (se 1 (by rfl) ⟨3118901, by rfl⟩ : syracuseStep 4158535 = 6237803) B6237803
theorem B5837993 : Blo 1366502 5837993 := bstep (se 2 (by rfl) ⟨2189247, by rfl⟩ : syracuseStep 5837993 = 4378495) B4378495
theorem B7787771 : Blo 1366502 7787771 := bstep (se 1 (by rfl) ⟨5840828, by rfl⟩ : syracuseStep 7787771 = 11681657) B11681657
theorem B7017839 : Blo 1366502 7017839 := bstep (se 1 (by rfl) ⟨5263379, by rfl⟩ : syracuseStep 7017839 = 10526759) B10526759
theorem B2307575 : Blo 1366502 2307575 := bstep (se 1 (by rfl) ⟨1730681, by rfl⟩ : syracuseStep 2307575 = 3461363) B3461363
theorem B19723985 : Blo 1366502 19723985 := bstep (se 2 (by rfl) ⟨7396494, by rfl⟩ : syracuseStep 19723985 = 14792989) B14792989
theorem B7788271 : Blo 1366502 7788271 := bstep (se 1 (by rfl) ⟨5841203, by rfl⟩ : syracuseStep 7788271 = 11682407) B11682407
theorem B4929439 : Blo 1366502 4929439 := bstep (se 1 (by rfl) ⟨3697079, by rfl⟩ : syracuseStep 4929439 = 7394159) B7394159
theorem B1538095 : Blo 1366502 1538095 := bstep (se 1 (by rfl) ⟨1153571, by rfl⟩ : syracuseStep 1538095 = 2307143) B2307143
theorem B168450191 : Blo 1366502 168450191 := bstep (se 1 (by rfl) ⟨126337643, by rfl⟩ : syracuseStep 168450191 = 252675287) B252675287
theorem B3463519 : Blo 1366502 3463519 := bstep (se 1 (by rfl) ⟨2597639, by rfl⟩ : syracuseStep 3463519 = 5195279) B5195279
theorem B7387499 : Blo 1366502 7387499 := bstep (se 1 (by rfl) ⟨5540624, by rfl⟩ : syracuseStep 7387499 = 11081249) B11081249
theorem B4159993 : Blo 1366502 4159993 := bstep (se 2 (by rfl) ⟨1559997, by rfl⟩ : syracuseStep 4159993 = 3119995) B3119995
theorem B3283487 : Blo 1366502 3283487 := bstep (se 1 (by rfl) ⟨2462615, by rfl⟩ : syracuseStep 3283487 = 4925231) B4925231
theorem B2308655 : Blo 1366502 2308655 := bstep (se 1 (by rfl) ⟨1731491, by rfl⟩ : syracuseStep 2308655 = 3462983) B3462983
theorem B1948207 : Blo 1366502 1948207 := bstep (se 1 (by rfl) ⟨1461155, by rfl⟩ : syracuseStep 1948207 = 2922311) B2922311
theorem B3463823 : Blo 1366502 3463823 := bstep (se 1 (by rfl) ⟨2597867, by rfl⟩ : syracuseStep 3463823 = 5195735) B5195735
theorem B1366719 : Blo 1366502 1366719 := bstep (se 1 (by rfl) ⟨1025039, by rfl⟩ : syracuseStep 1366719 = 2050079) B2050079
theorem B1366847 : Blo 1366502 1366847 := bstep (se 1 (by rfl) ⟨1025135, by rfl⟩ : syracuseStep 1366847 = 2050271) B2050271
theorem B1366887 : Blo 1366502 1366887 := bstep (se 1 (by rfl) ⟨1025165, by rfl⟩ : syracuseStep 1366887 = 2050331) B2050331
theorem B7789547 : Blo 1366502 7789547 := bstep (se 1 (by rfl) ⟨5842160, by rfl⟩ : syracuseStep 7789547 = 11684321) B11684321
theorem B1367103 : Blo 1366502 1367103 := bstep (se 1 (by rfl) ⟨1025327, by rfl⟩ : syracuseStep 1367103 = 2050655) B2050655
theorem B6921287 : Blo 1366502 6921287 := bstep (se 1 (by rfl) ⟨5190965, by rfl⟩ : syracuseStep 6921287 = 10381931) B10381931
theorem B2809063 : Blo 1366502 2809063 := bstep (se 1 (by rfl) ⟨2106797, by rfl⟩ : syracuseStep 2809063 = 4213595) B4213595
theorem B1367291 : Blo 1366502 1367291 := bstep (se 1 (by rfl) ⟨1025468, by rfl⟩ : syracuseStep 1367291 = 2050937) B2050937
theorem B1367323 : Blo 1366502 1367323 := bstep (se 1 (by rfl) ⟨1025492, by rfl⟩ : syracuseStep 1367323 = 2050985) B2050985
theorem B8879483 : Blo 1366502 8879483 := bstep (se 1 (by rfl) ⟨6659612, by rfl⟩ : syracuseStep 8879483 = 13319225) B13319225
theorem B1367423 : Blo 1366502 1367423 := bstep (se 1 (by rfl) ⟨1025567, by rfl⟩ : syracuseStep 1367423 = 2051135) B2051135
theorem B2596303 : Blo 1366502 2596303 := bstep (se 1 (by rfl) ⟨1947227, by rfl⟩ : syracuseStep 2596303 = 3894455) B3894455
theorem B3120871 : Blo 1366502 3120871 := bstep (se 1 (by rfl) ⟨2340653, by rfl⟩ : syracuseStep 3120871 = 4681307) B4681307
theorem B1367791 : Blo 1366502 1367791 := bstep (se 1 (by rfl) ⟨1025843, by rfl⟩ : syracuseStep 1367791 = 2051687) B2051687
theorem B2809721 : Blo 1366502 2809721 := bstep (se 2 (by rfl) ⟨1053645, by rfl⟩ : syracuseStep 2809721 = 2107291) B2107291
theorem B5545867 : Blo 1366502 5545867 := bstep (se 1 (by rfl) ⟨4159400, by rfl⟩ : syracuseStep 5545867 = 8318801) B8318801
theorem B8757193 : Blo 1366502 8757193 := bstep (se 2 (by rfl) ⟨3283947, by rfl⟩ : syracuseStep 8757193 = 6567895) B6567895
theorem B1368047 : Blo 1366502 1368047 := bstep (se 1 (by rfl) ⟨1026035, by rfl⟩ : syracuseStep 1368047 = 2052071) B2052071
theorem B6570011 : Blo 1366502 6570011 := bstep (se 1 (by rfl) ⟨4927508, by rfl⟩ : syracuseStep 6570011 = 9855017) B9855017
theorem B1368095 : Blo 1366502 1368095 := bstep (se 1 (by rfl) ⟨1026071, by rfl⟩ : syracuseStep 1368095 = 2052143) B2052143
theorem B5194003 : Blo 1366502 5194003 := bstep (se 1 (by rfl) ⟨3895502, by rfl⟩ : syracuseStep 5194003 = 7791005) B7791005
theorem B1368391 : Blo 1366502 1368391 := bstep (se 1 (by rfl) ⟨1026293, by rfl⟩ : syracuseStep 1368391 = 2052587) B2052587
theorem B1368475 : Blo 1366502 1368475 := bstep (se 1 (by rfl) ⟨1026356, by rfl⟩ : syracuseStep 1368475 = 2052713) B2052713
theorem B1368479 : Blo 1366502 1368479 := bstep (se 1 (by rfl) ⟨1026359, by rfl⟩ : syracuseStep 1368479 = 2052719) B2052719
theorem B11837915 : Blo 1366502 11837915 := bstep (se 1 (by rfl) ⟨8878436, by rfl⟩ : syracuseStep 11837915 = 17756873) B17756873
theorem B5546657 : Blo 1366502 5546657 := bstep (se 2 (by rfl) ⟨2079996, by rfl⟩ : syracuseStep 5546657 = 4159993) B4159993
theorem B2597609 : Blo 1366502 2597609 := bstep (se 2 (by rfl) ⟨974103, by rfl⟩ : syracuseStep 2597609 = 1948207) B1948207
theorem B3891995 : Blo 1366502 3891995 := bstep (se 1 (by rfl) ⟨2918996, by rfl⟩ : syracuseStep 3891995 = 5837993) B5837993
theorem B79971209 : Blo 1366502 79971209 := bstep (se 2 (by rfl) ⟨29989203, by rfl⟩ : syracuseStep 79971209 = 59978407) B59978407
theorem B4678559 : Blo 1366502 4678559 := bstep (se 1 (by rfl) ⟨3508919, by rfl⟩ : syracuseStep 4678559 = 7017839) B7017839
theorem B94667849 : Blo 1366502 94667849 := bstep (se 2 (by rfl) ⟨35500443, by rfl⟩ : syracuseStep 94667849 = 71000887) B71000887
theorem B13149323 : Blo 1366502 13149323 := bstep (se 1 (by rfl) ⟨9861992, by rfl⟩ : syracuseStep 13149323 = 19723985) B19723985
theorem B5194975 : Blo 1366502 5194975 := bstep (se 1 (by rfl) ⟨3896231, by rfl⟩ : syracuseStep 5194975 = 7792463) B7792463
theorem B4924999 : Blo 1366502 4924999 := bstep (se 1 (by rfl) ⟨3693749, by rfl⟩ : syracuseStep 4924999 = 7387499) B7387499
theorem B2188991 : Blo 1366502 2188991 := bstep (se 1 (by rfl) ⟨1641743, by rfl⟩ : syracuseStep 2188991 = 3283487) B3283487
theorem B2049947 : Blo 1366502 2049947 := bstep (se 1 (by rfl) ⟨1537460, by rfl⟩ : syracuseStep 2049947 = 3074921) B3074921
theorem B2049959 : Blo 1366502 2049959 := bstep (se 1 (by rfl) ⟨1537469, by rfl⟩ : syracuseStep 2049959 = 3074939) B3074939
theorem B7784423 : Blo 1366502 7784423 := bstep (se 1 (by rfl) ⟨5838317, by rfl⟩ : syracuseStep 7784423 = 11676635) B11676635
theorem B68323337 : Blo 1366502 68323337 := bstep (se 2 (by rfl) ⟨25621251, by rfl⟩ : syracuseStep 68323337 = 51242503) B51242503
theorem B4614191 : Blo 1366502 4614191 := bstep (se 1 (by rfl) ⟨3460643, by rfl⟩ : syracuseStep 4614191 = 6921287) B6921287
theorem B2050139 : Blo 1366502 2050139 := bstep (se 1 (by rfl) ⟨1537604, by rfl⟩ : syracuseStep 2050139 = 3075209) B3075209
theorem B2050175 : Blo 1366502 2050175 := bstep (se 1 (by rfl) ⟨1537631, by rfl⟩ : syracuseStep 2050175 = 3075263) B3075263
theorem B10389707 : Blo 1366502 10389707 := bstep (se 1 (by rfl) ⟨7792280, by rfl⟩ : syracuseStep 10389707 = 15584561) B15584561
theorem B4614569 : Blo 1366502 4614569 := bstep (se 2 (by rfl) ⟨1730463, by rfl⟩ : syracuseStep 4614569 = 3460927) B3460927
theorem B1460711 : Blo 1366502 1460711 := bstep (se 1 (by rfl) ⟨1095533, by rfl⟩ : syracuseStep 1460711 = 2191067) B2191067
theorem B6572585 : Blo 1366502 6572585 := bstep (se 2 (by rfl) ⟨2464719, by rfl⟩ : syracuseStep 6572585 = 4929439) B4929439
theorem B2050607 : Blo 1366502 2050607 := bstep (se 1 (by rfl) ⟨1537955, by rfl⟩ : syracuseStep 2050607 = 3075911) B3075911
theorem B8882783 : Blo 1366502 8882783 := bstep (se 1 (by rfl) ⟨6662087, by rfl⟩ : syracuseStep 8882783 = 13324175) B13324175
theorem B11676257 : Blo 1366502 11676257 := bstep (se 2 (by rfl) ⟨4378596, by rfl⟩ : syracuseStep 11676257 = 8757193) B8757193
theorem B9996959 : Blo 1366502 9996959 := bstep (se 1 (by rfl) ⟨7497719, by rfl⟩ : syracuseStep 9996959 = 14995439) B14995439
theorem B2050727 : Blo 1366502 2050727 := bstep (se 1 (by rfl) ⟨1538045, by rfl⟩ : syracuseStep 2050727 = 3076091) B3076091
theorem B2050793 : Blo 1366502 2050793 := bstep (se 2 (by rfl) ⟨769047, by rfl⟩ : syracuseStep 2050793 = 1538095) B1538095
theorem B2919167 : Blo 1366502 2919167 := bstep (se 1 (by rfl) ⟨2189375, by rfl⟩ : syracuseStep 2919167 = 4378751) B4378751
theorem B2050847 : Blo 1366502 2050847 := bstep (se 1 (by rfl) ⟨1538135, by rfl⟩ : syracuseStep 2050847 = 3076271) B3076271
theorem B66562985 : Blo 1366502 66562985 := bstep (se 2 (by rfl) ⟨24961119, by rfl⟩ : syracuseStep 66562985 = 49922239) B49922239
theorem B4615163 : Blo 1366502 4615163 := bstep (se 1 (by rfl) ⟨3461372, by rfl⟩ : syracuseStep 4615163 = 6922745) B6922745
theorem B3894409 : Blo 1366502 3894409 := bstep (se 2 (by rfl) ⟨1460403, by rfl⟩ : syracuseStep 3894409 = 2920807) B2920807
theorem B4615433 : Blo 1366502 4615433 := bstep (se 2 (by rfl) ⟨1730787, by rfl⟩ : syracuseStep 4615433 = 3461575) B3461575
theorem B112300127 : Blo 1366502 112300127 := bstep (se 1 (by rfl) ⟨84225095, by rfl⟩ : syracuseStep 112300127 = 168450191) B168450191
theorem B4927999 : Blo 1366502 4927999 := bstep (se 1 (by rfl) ⟨3695999, by rfl⟩ : syracuseStep 4927999 = 7391999) B7391999
theorem B3461737 : Blo 1366502 3461737 := bstep (se 2 (by rfl) ⟨1298151, by rfl⟩ : syracuseStep 3461737 = 2596303) B2596303
theorem B5190419 : Blo 1366502 5190419 := bstep (se 1 (by rfl) ⟨3892814, by rfl⟩ : syracuseStep 5190419 = 7785629) B7785629
theorem B5919655 : Blo 1366502 5919655 := bstep (se 1 (by rfl) ⟨4439741, by rfl⟩ : syracuseStep 5919655 = 8879483) B8879483
theorem B74855339 : Blo 1366502 74855339 := bstep (se 1 (by rfl) ⟨56141504, by rfl⟩ : syracuseStep 74855339 = 112283009) B112283009
theorem B10384361 : Blo 1366502 10384361 := bstep (se 2 (by rfl) ⟨3894135, by rfl⟩ : syracuseStep 10384361 = 7788271) B7788271
theorem B2307055 : Blo 1366502 2307055 := bstep (se 1 (by rfl) ⟨1730291, by rfl⟩ : syracuseStep 2307055 = 3460583) B3460583
theorem B7394489 : Blo 1366502 7394489 := bstep (se 2 (by rfl) ⟨2772933, by rfl⟩ : syracuseStep 7394489 = 5545867) B5545867
theorem B1873147 : Blo 1366502 1873147 := bstep (se 1 (by rfl) ⟨1404860, by rfl⟩ : syracuseStep 1873147 = 2809721) B2809721
theorem B17528075 : Blo 1366502 17528075 := bstep (se 1 (by rfl) ⟨13146056, by rfl⟩ : syracuseStep 17528075 = 26292113) B26292113
theorem B26293571 : Blo 1366502 26293571 := bstep (se 1 (by rfl) ⟨19720178, by rfl⟩ : syracuseStep 26293571 = 39440357) B39440357
theorem B22181435 : Blo 1366502 22181435 := bstep (se 1 (by rfl) ⟨16636076, by rfl⟩ : syracuseStep 22181435 = 33272153) B33272153
theorem B4618025 : Blo 1366502 4618025 := bstep (se 2 (by rfl) ⟨1731759, by rfl⟩ : syracuseStep 4618025 = 3463519) B3463519
theorem B3463307 : Blo 1366502 3463307 := bstep (se 1 (by rfl) ⟨2597480, by rfl⟩ : syracuseStep 3463307 = 5194961) B5194961
theorem B5191847 : Blo 1366502 5191847 := bstep (se 1 (by rfl) ⟨3893885, by rfl⟩ : syracuseStep 5191847 = 7787771) B7787771
theorem B1538383 : Blo 1366502 1538383 := bstep (se 1 (by rfl) ⟨1153787, by rfl⟩ : syracuseStep 1538383 = 2307575) B2307575
theorem B9861533 : Blo 1366502 9861533 := bstep (se 3 (by rfl) ⟨1849037, by rfl⟩ : syracuseStep 9861533 = 3698075) B3698075
theorem B2308601 : Blo 1366502 2308601 := bstep (se 2 (by rfl) ⟨865725, by rfl⟩ : syracuseStep 2308601 = 1731451) B1731451
theorem B14981669 : Blo 1366502 14981669 := bstep (se 4 (by rfl) ⟨1404531, by rfl⟩ : syracuseStep 14981669 = 2809063) B2809063
theorem B1366683 : Blo 1366502 1366683 := bstep (se 1 (by rfl) ⟨1025012, by rfl⟩ : syracuseStep 1366683 = 2050025) B2050025
theorem B1366779 : Blo 1366502 1366779 := bstep (se 1 (by rfl) ⟨1025084, by rfl⟩ : syracuseStep 1366779 = 2050169) B2050169
theorem B5544713 : Blo 1366502 5544713 := bstep (se 2 (by rfl) ⟨2079267, by rfl⟩ : syracuseStep 5544713 = 4158535) B4158535
theorem B10378043 : Blo 1366502 10378043 := bstep (se 1 (by rfl) ⟨7783532, by rfl⟩ : syracuseStep 10378043 = 15567065) B15567065
theorem B1366911 : Blo 1366502 1366911 := bstep (se 1 (by rfl) ⟨1025183, by rfl⟩ : syracuseStep 1366911 = 2050367) B2050367
theorem B2309033 : Blo 1366502 2309033 := bstep (se 2 (by rfl) ⟨865887, by rfl⟩ : syracuseStep 2309033 = 1731775) B1731775
theorem B1367007 : Blo 1366502 1367007 := bstep (se 1 (by rfl) ⟨1025255, by rfl⟩ : syracuseStep 1367007 = 2050511) B2050511
theorem B1367035 : Blo 1366502 1367035 := bstep (se 1 (by rfl) ⟨1025276, by rfl⟩ : syracuseStep 1367035 = 2050553) B2050553
theorem B1367067 : Blo 1366502 1367067 := bstep (se 1 (by rfl) ⟨1025300, by rfl⟩ : syracuseStep 1367067 = 2050601) B2050601
theorem B1539103 : Blo 1366502 1539103 := bstep (se 1 (by rfl) ⟨1154327, by rfl⟩ : syracuseStep 1539103 = 2308655) B2308655
theorem B2309215 : Blo 1366502 2309215 := bstep (se 1 (by rfl) ⟨1731911, by rfl⟩ : syracuseStep 2309215 = 3463823) B3463823
theorem B1367359 : Blo 1366502 1367359 := bstep (se 1 (by rfl) ⟨1025519, by rfl⟩ : syracuseStep 1367359 = 2051039) B2051039
theorem B5193031 : Blo 1366502 5193031 := bstep (se 1 (by rfl) ⟨3894773, by rfl⟩ : syracuseStep 5193031 = 7789547) B7789547
theorem B1367655 : Blo 1366502 1367655 := bstep (se 1 (by rfl) ⟨1025741, by rfl⟩ : syracuseStep 1367655 = 2051483) B2051483
theorem B4161161 : Blo 1366502 4161161 := bstep (se 2 (by rfl) ⟨1560435, by rfl⟩ : syracuseStep 4161161 = 3120871) B3120871
theorem B7495391 : Blo 1366502 7495391 := bstep (se 1 (by rfl) ⟨5621543, by rfl⟩ : syracuseStep 7495391 = 11243087) B11243087
theorem B11689757 : Blo 1366502 11689757 := bstep (se 3 (by rfl) ⟨2191829, by rfl⟩ : syracuseStep 11689757 = 4383659) B4383659
theorem B1367899 : Blo 1366502 1367899 := bstep (se 1 (by rfl) ⟨1025924, by rfl⟩ : syracuseStep 1367899 = 2051849) B2051849
theorem B1367935 : Blo 1366502 1367935 := bstep (se 1 (by rfl) ⟨1025951, by rfl⟩ : syracuseStep 1367935 = 2051903) B2051903
theorem B74866751 : Blo 1366502 74866751 := bstep (se 1 (by rfl) ⟨56150063, by rfl⟩ : syracuseStep 74866751 = 112300127) B112300127
theorem B53314139 : Blo 1366502 53314139 := bstep (se 1 (by rfl) ⟨39985604, by rfl⟩ : syracuseStep 53314139 = 79971209) B79971209
theorem B6922907 : Blo 1366502 6922907 := bstep (se 1 (by rfl) ⟨5192180, by rfl⟩ : syracuseStep 6922907 = 10384361) B10384361
theorem B6570665 : Blo 1366502 6570665 := bstep (se 2 (by rfl) ⟨2463999, by rfl⟩ : syracuseStep 6570665 = 4927999) B4927999
theorem B63111899 : Blo 1366502 63111899 := bstep (se 1 (by rfl) ⟨47333924, by rfl⟩ : syracuseStep 63111899 = 94667849) B94667849
theorem B8766215 : Blo 1366502 8766215 := bstep (se 1 (by rfl) ⟨6574661, by rfl⟩ : syracuseStep 8766215 = 13149323) B13149323
theorem B14787623 : Blo 1366502 14787623 := bstep (se 1 (by rfl) ⟨11090717, by rfl⟩ : syracuseStep 14787623 = 22181435) B22181435
theorem B45548891 : Blo 1366502 45548891 := bstep (se 1 (by rfl) ⟨34161668, by rfl⟩ : syracuseStep 45548891 = 68323337) B68323337
theorem B9987779 : Blo 1366502 9987779 := bstep (se 1 (by rfl) ⟨7490834, by rfl⟩ : syracuseStep 9987779 = 14981669) B14981669
theorem B7784171 : Blo 1366502 7784171 := bstep (se 1 (by rfl) ⟨5838128, by rfl⟩ : syracuseStep 7784171 = 11676257) B11676257
theorem B6924041 : Blo 1366502 6924041 := bstep (se 2 (by rfl) ⟨2596515, by rfl⟩ : syracuseStep 6924041 = 5193031) B5193031
theorem B3696475 : Blo 1366502 3696475 := bstep (se 1 (by rfl) ⟨2772356, by rfl⟩ : syracuseStep 3696475 = 5544713) B5544713
theorem B7793171 : Blo 1366502 7793171 := bstep (se 1 (by rfl) ⟨5844878, by rfl⟩ : syracuseStep 7793171 = 11689757) B11689757
theorem B7891943 : Blo 1366502 7891943 := bstep (se 1 (by rfl) ⟨5918957, by rfl⟩ : syracuseStep 7891943 = 11837915) B11837915
theorem B6925337 : Blo 1366502 6925337 := bstep (se 2 (by rfl) ⟨2597001, by rfl⟩ : syracuseStep 6925337 = 5194003) B5194003
theorem B2051177 : Blo 1366502 2051177 := bstep (se 2 (by rfl) ⟨769191, by rfl⟩ : syracuseStep 2051177 = 1538383) B1538383
theorem B3460279 : Blo 1366502 3460279 := bstep (se 1 (by rfl) ⟨2595209, by rfl⟩ : syracuseStep 3460279 = 5190419) B5190419
theorem B4615649 : Blo 1366502 4615649 := bstep (se 2 (by rfl) ⟨1730868, by rfl⟩ : syracuseStep 4615649 = 3461737) B3461737
theorem B11685383 : Blo 1366502 11685383 := bstep (se 1 (by rfl) ⟨8764037, by rfl⟩ : syracuseStep 11685383 = 17528075) B17528075
theorem B7892873 : Blo 1366502 7892873 := bstep (se 2 (by rfl) ⟨2959827, by rfl⟩ : syracuseStep 7892873 = 5919655) B5919655
theorem B3895229 : Blo 1366502 3895229 := bstep (se 3 (by rfl) ⟨730355, by rfl⟩ : syracuseStep 3895229 = 1460711) B1460711
theorem B3076073 : Blo 1366502 3076073 := bstep (se 2 (by rfl) ⟨1153527, by rfl⟩ : syracuseStep 3076073 = 2307055) B2307055
theorem B5189615 : Blo 1366502 5189615 := bstep (se 1 (by rfl) ⟨3892211, by rfl⟩ : syracuseStep 5189615 = 7784423) B7784423
theorem B3076127 : Blo 1366502 3076127 := bstep (se 1 (by rfl) ⟨2307095, by rfl⟩ : syracuseStep 3076127 = 4614191) B4614191
theorem B2052137 : Blo 1366502 2052137 := bstep (se 2 (by rfl) ⟨769551, by rfl⟩ : syracuseStep 2052137 = 1539103) B1539103
theorem B3461231 : Blo 1366502 3461231 := bstep (se 1 (by rfl) ⟨2595923, by rfl⟩ : syracuseStep 3461231 = 5191847) B5191847
theorem B6926471 : Blo 1366502 6926471 := bstep (se 1 (by rfl) ⟨5194853, by rfl⟩ : syracuseStep 6926471 = 10389707) B10389707
theorem B6574355 : Blo 1366502 6574355 := bstep (se 1 (by rfl) ⟨4930766, by rfl⟩ : syracuseStep 6574355 = 9861533) B9861533
theorem B3076379 : Blo 1366502 3076379 := bstep (se 1 (by rfl) ⟨2307284, by rfl⟩ : syracuseStep 3076379 = 4614569) B4614569
theorem B6926633 : Blo 1366502 6926633 := bstep (se 2 (by rfl) ⟨2597487, by rfl⟩ : syracuseStep 6926633 = 5194975) B5194975
theorem B14791085 : Blo 1366502 14791085 := bstep (se 3 (by rfl) ⟨2773328, by rfl⟩ : syracuseStep 14791085 = 5546657) B5546657
theorem B6664639 : Blo 1366502 6664639 := bstep (se 1 (by rfl) ⟨4998479, by rfl⟩ : syracuseStep 6664639 = 9996959) B9996959
theorem B5837309 : Blo 1366502 5837309 := bstep (se 3 (by rfl) ⟨1094495, by rfl⟩ : syracuseStep 5837309 = 2188991) B2188991
theorem B1946111 : Blo 1366502 1946111 := bstep (se 1 (by rfl) ⟨1459583, by rfl⟩ : syracuseStep 1946111 = 2919167) B2919167
theorem B6918695 : Blo 1366502 6918695 := bstep (se 1 (by rfl) ⟨5189021, by rfl⟩ : syracuseStep 6918695 = 10378043) B10378043
theorem B6926957 : Blo 1366502 6926957 := bstep (se 3 (by rfl) ⟨1298804, by rfl⟩ : syracuseStep 6926957 = 2597609) B2597609
theorem B3076775 : Blo 1366502 3076775 := bstep (se 1 (by rfl) ⟨2307581, by rfl⟩ : syracuseStep 3076775 = 4615163) B4615163
theorem B6566665 : Blo 1366502 6566665 := bstep (se 2 (by rfl) ⟨2462499, by rfl⟩ : syracuseStep 6566665 = 4924999) B4924999
theorem B3076955 : Blo 1366502 3076955 := bstep (se 1 (by rfl) ⟨2307716, by rfl⟩ : syracuseStep 3076955 = 4615433) B4615433
theorem B2774107 : Blo 1366502 2774107 := bstep (se 1 (by rfl) ⟨2080580, by rfl⟩ : syracuseStep 2774107 = 4161161) B4161161
theorem B177501293 : Blo 1366502 177501293 := bstep (se 3 (by rfl) ⟨33281492, by rfl⟩ : syracuseStep 177501293 = 66562985) B66562985
theorem B4380007 : Blo 1366502 4380007 := bstep (se 1 (by rfl) ⟨3285005, by rfl⟩ : syracuseStep 4380007 = 6570011) B6570011
theorem B2594663 : Blo 1366502 2594663 := bstep (se 1 (by rfl) ⟨1945997, by rfl⟩ : syracuseStep 2594663 = 3891995) B3891995
theorem B3119039 : Blo 1366502 3119039 := bstep (se 1 (by rfl) ⟨2339279, by rfl⟩ : syracuseStep 3119039 = 4678559) B4678559
theorem B49903559 : Blo 1366502 49903559 := bstep (se 1 (by rfl) ⟨37427669, by rfl⟩ : syracuseStep 49903559 = 74855339) B74855339
theorem B4929659 : Blo 1366502 4929659 := bstep (se 1 (by rfl) ⟨3697244, by rfl⟩ : syracuseStep 4929659 = 7394489) B7394489
theorem B17529047 : Blo 1366502 17529047 := bstep (se 1 (by rfl) ⟨13146785, by rfl⟩ : syracuseStep 17529047 = 26293571) B26293571
theorem B3078683 : Blo 1366502 3078683 := bstep (se 1 (by rfl) ⟨2309012, by rfl⟩ : syracuseStep 3078683 = 4618025) B4618025
theorem B1366631 : Blo 1366502 1366631 := bstep (se 1 (by rfl) ⟨1024973, by rfl⟩ : syracuseStep 1366631 = 2049947) B2049947
theorem B1366639 : Blo 1366502 1366639 := bstep (se 1 (by rfl) ⟨1024979, by rfl⟩ : syracuseStep 1366639 = 2049959) B2049959
theorem B1366759 : Blo 1366502 1366759 := bstep (se 1 (by rfl) ⟨1025069, by rfl⟩ : syracuseStep 1366759 = 2050139) B2050139
theorem B1366783 : Blo 1366502 1366783 := bstep (se 1 (by rfl) ⟨1025087, by rfl⟩ : syracuseStep 1366783 = 2050175) B2050175
theorem B2308871 : Blo 1366502 2308871 := bstep (se 1 (by rfl) ⟨1731653, by rfl⟩ : syracuseStep 2308871 = 3463307) B3463307
theorem B3078953 : Blo 1366502 3078953 := bstep (se 2 (by rfl) ⟨1154607, by rfl⟩ : syracuseStep 3078953 = 2309215) B2309215
theorem B5192545 : Blo 1366502 5192545 := bstep (se 2 (by rfl) ⟨1947204, by rfl⟩ : syracuseStep 5192545 = 3894409) B3894409
theorem B2497529 : Blo 1366502 2497529 := bstep (se 2 (by rfl) ⟨936573, by rfl⟩ : syracuseStep 2497529 = 1873147) B1873147
theorem B1539067 : Blo 1366502 1539067 := bstep (se 1 (by rfl) ⟨1154300, by rfl⟩ : syracuseStep 1539067 = 2308601) B2308601
theorem B4381723 : Blo 1366502 4381723 := bstep (se 1 (by rfl) ⟨3286292, by rfl⟩ : syracuseStep 4381723 = 6572585) B6572585
theorem B1367071 : Blo 1366502 1367071 := bstep (se 1 (by rfl) ⟨1025303, by rfl⟩ : syracuseStep 1367071 = 2050607) B2050607
theorem B5921855 : Blo 1366502 5921855 := bstep (se 1 (by rfl) ⟨4441391, by rfl⟩ : syracuseStep 5921855 = 8882783) B8882783
theorem B1367151 : Blo 1366502 1367151 := bstep (se 1 (by rfl) ⟨1025363, by rfl⟩ : syracuseStep 1367151 = 2050727) B2050727
theorem B1367195 : Blo 1366502 1367195 := bstep (se 1 (by rfl) ⟨1025396, by rfl⟩ : syracuseStep 1367195 = 2050793) B2050793
theorem B1367231 : Blo 1366502 1367231 := bstep (se 1 (by rfl) ⟨1025423, by rfl⟩ : syracuseStep 1367231 = 2050847) B2050847
theorem B1539355 : Blo 1366502 1539355 := bstep (se 1 (by rfl) ⟨1154516, by rfl⟩ : syracuseStep 1539355 = 2309033) B2309033
theorem B4996927 : Blo 1366502 4996927 := bstep (se 1 (by rfl) ⟨3747695, by rfl⟩ : syracuseStep 4996927 = 7495391) B7495391
theorem B1368091 : Blo 1366502 1368091 := bstep (se 1 (by rfl) ⟨1026068, by rfl⟩ : syracuseStep 1368091 = 2052137) B2052137
theorem B4382903 : Blo 1366502 4382903 := bstep (se 1 (by rfl) ⟨3287177, by rfl⟩ : syracuseStep 4382903 = 6574355) B6574355
theorem B3891539 : Blo 1366502 3891539 := bstep (se 1 (by rfl) ⟨2918654, by rfl⟩ : syracuseStep 3891539 = 5837309) B5837309
theorem B4612463 : Blo 1366502 4612463 := bstep (se 1 (by rfl) ⟨3459347, by rfl⟩ : syracuseStep 4612463 = 6918695) B6918695
theorem B14795237 : Blo 1366502 14795237 := bstep (se 4 (by rfl) ⟨1387053, by rfl⟩ : syracuseStep 14795237 = 2774107) B2774107
theorem B118334195 : Blo 1366502 118334195 := bstep (se 1 (by rfl) ⟨88750646, by rfl⟩ : syracuseStep 118334195 = 177501293) B177501293
theorem B6923393 : Blo 1366502 6923393 := bstep (se 2 (by rfl) ⟨2596272, by rfl⟩ : syracuseStep 6923393 = 5192545) B5192545
theorem B1729775 : Blo 1366502 1729775 := bstep (se 1 (by rfl) ⟨1297331, by rfl⟩ : syracuseStep 1729775 = 2594663) B2594663
theorem B33269039 : Blo 1366502 33269039 := bstep (se 1 (by rfl) ⟨24951779, by rfl⟩ : syracuseStep 33269039 = 49903559) B49903559
theorem B5842297 : Blo 1366502 5842297 := bstep (se 2 (by rfl) ⟨2190861, by rfl⟩ : syracuseStep 5842297 = 4381723) B4381723
theorem B3286439 : Blo 1366502 3286439 := bstep (se 1 (by rfl) ⟨2464829, by rfl⟩ : syracuseStep 3286439 = 4929659) B4929659
theorem B4613705 : Blo 1366502 4613705 := bstep (se 2 (by rfl) ⟨1730139, by rfl⟩ : syracuseStep 4613705 = 3460279) B3460279
theorem B5195447 : Blo 1366502 5195447 := bstep (se 1 (by rfl) ⟨3896585, by rfl⟩ : syracuseStep 5195447 = 7793171) B7793171
theorem B168298397 : Blo 1366502 168298397 := bstep (se 3 (by rfl) ⟨31555949, by rfl⟩ : syracuseStep 168298397 = 63111899) B63111899
theorem B1665019 : Blo 1366502 1665019 := bstep (se 1 (by rfl) ⟨1248764, by rfl⟩ : syracuseStep 1665019 = 2497529) B2497529
theorem B6662569 : Blo 1366502 6662569 := bstep (se 2 (by rfl) ⟨2498463, by rfl⟩ : syracuseStep 6662569 = 4996927) B4996927
theorem B5261915 : Blo 1366502 5261915 := bstep (se 1 (by rfl) ⟨3946436, by rfl⟩ : syracuseStep 5261915 = 7892873) B7892873
theorem B2050715 : Blo 1366502 2050715 := bstep (se 1 (by rfl) ⟨1538036, by rfl⟩ : syracuseStep 2050715 = 3076073) B3076073
theorem B3459743 : Blo 1366502 3459743 := bstep (se 1 (by rfl) ⟨2594807, by rfl⟩ : syracuseStep 3459743 = 5189615) B5189615
theorem B2050751 : Blo 1366502 2050751 := bstep (se 1 (by rfl) ⟨1538063, by rfl⟩ : syracuseStep 2050751 = 3076127) B3076127
theorem B2050919 : Blo 1366502 2050919 := bstep (se 1 (by rfl) ⟨1538189, by rfl⟩ : syracuseStep 2050919 = 3076379) B3076379
theorem B4615271 : Blo 1366502 4615271 := bstep (se 1 (by rfl) ⟨3461453, by rfl⟩ : syracuseStep 4615271 = 6922907) B6922907
theorem B2051183 : Blo 1366502 2051183 := bstep (se 1 (by rfl) ⟨1538387, by rfl⟩ : syracuseStep 2051183 = 3076775) B3076775
theorem B5844143 : Blo 1366502 5844143 := bstep (se 1 (by rfl) ⟨4383107, by rfl⟩ : syracuseStep 5844143 = 8766215) B8766215
theorem B2051303 : Blo 1366502 2051303 := bstep (se 1 (by rfl) ⟨1538477, by rfl⟩ : syracuseStep 2051303 = 3076955) B3076955
theorem B5189447 : Blo 1366502 5189447 := bstep (se 1 (by rfl) ⟨3892085, by rfl⟩ : syracuseStep 5189447 = 7784171) B7784171
theorem B4616027 : Blo 1366502 4616027 := bstep (se 1 (by rfl) ⟨3462020, by rfl⟩ : syracuseStep 4616027 = 6924041) B6924041
theorem B2052089 : Blo 1366502 2052089 := bstep (se 2 (by rfl) ⟨769533, by rfl⟩ : syracuseStep 2052089 = 1539067) B1539067
theorem B5189629 : Blo 1366502 5189629 := bstep (se 3 (by rfl) ⟨973055, by rfl⟩ : syracuseStep 5189629 = 1946111) B1946111
theorem B11686031 : Blo 1366502 11686031 := bstep (se 1 (by rfl) ⟨8764523, by rfl⟩ : syracuseStep 11686031 = 17529047) B17529047
theorem B2052455 : Blo 1366502 2052455 := bstep (se 1 (by rfl) ⟨1539341, by rfl⟩ : syracuseStep 2052455 = 3078683) B3078683
theorem B2052473 : Blo 1366502 2052473 := bstep (se 2 (by rfl) ⟨769677, by rfl⟩ : syracuseStep 2052473 = 1539355) B1539355
theorem B2052635 : Blo 1366502 2052635 := bstep (se 1 (by rfl) ⟨1539476, by rfl⟩ : syracuseStep 2052635 = 3078953) B3078953
theorem B4616891 : Blo 1366502 4616891 := bstep (se 1 (by rfl) ⟨3462668, by rfl⟩ : syracuseStep 4616891 = 6925337) B6925337
theorem B3077099 : Blo 1366502 3077099 := bstep (se 1 (by rfl) ⟨2307824, by rfl⟩ : syracuseStep 3077099 = 4615649) B4615649
theorem B4928633 : Blo 1366502 4928633 := bstep (se 2 (by rfl) ⟨1848237, by rfl⟩ : syracuseStep 4928633 = 3696475) B3696475
theorem B49911167 : Blo 1366502 49911167 := bstep (se 1 (by rfl) ⟨37433375, by rfl⟩ : syracuseStep 49911167 = 74866751) B74866751
theorem B2307487 : Blo 1366502 2307487 := bstep (se 1 (by rfl) ⟨1730615, by rfl⟩ : syracuseStep 2307487 = 3461231) B3461231
theorem B4617647 : Blo 1366502 4617647 := bstep (se 1 (by rfl) ⟨3463235, by rfl⟩ : syracuseStep 4617647 = 6926471) B6926471
theorem B39433661 : Blo 1366502 39433661 := bstep (se 3 (by rfl) ⟨7393811, by rfl⟩ : syracuseStep 39433661 = 14787623) B14787623
theorem B4617755 : Blo 1366502 4617755 := bstep (se 1 (by rfl) ⟨3463316, by rfl⟩ : syracuseStep 4617755 = 6926633) B6926633
theorem B9860723 : Blo 1366502 9860723 := bstep (se 1 (by rfl) ⟨7395542, by rfl⟩ : syracuseStep 9860723 = 14791085) B14791085
theorem B35542759 : Blo 1366502 35542759 := bstep (se 1 (by rfl) ⟨26657069, by rfl⟩ : syracuseStep 35542759 = 53314139) B53314139
theorem B4617971 : Blo 1366502 4617971 := bstep (se 1 (by rfl) ⟨3463478, by rfl⟩ : syracuseStep 4617971 = 6926957) B6926957
theorem B4380443 : Blo 1366502 4380443 := bstep (se 1 (by rfl) ⟨3285332, by rfl⟩ : syracuseStep 4380443 = 6570665) B6570665
theorem B8886185 : Blo 1366502 8886185 := bstep (se 2 (by rfl) ⟨3332319, by rfl⟩ : syracuseStep 8886185 = 6664639) B6664639
theorem B30365927 : Blo 1366502 30365927 := bstep (se 1 (by rfl) ⟨22774445, by rfl⟩ : syracuseStep 30365927 = 45548891) B45548891
theorem B8755553 : Blo 1366502 8755553 := bstep (se 2 (by rfl) ⟨3283332, by rfl⟩ : syracuseStep 8755553 = 6566665) B6566665
theorem B6658519 : Blo 1366502 6658519 := bstep (se 1 (by rfl) ⟨4993889, by rfl⟩ : syracuseStep 6658519 = 9987779) B9987779
theorem B2079359 : Blo 1366502 2079359 := bstep (se 1 (by rfl) ⟨1559519, by rfl⟩ : syracuseStep 2079359 = 3119039) B3119039
theorem B5840009 : Blo 1366502 5840009 := bstep (se 2 (by rfl) ⟨2190003, by rfl⟩ : syracuseStep 5840009 = 4380007) B4380007
theorem B1539247 : Blo 1366502 1539247 := bstep (se 1 (by rfl) ⟨1154435, by rfl⟩ : syracuseStep 1539247 = 2308871) B2308871
theorem B3947903 : Blo 1366502 3947903 := bstep (se 1 (by rfl) ⟨2960927, by rfl⟩ : syracuseStep 3947903 = 5921855) B5921855
theorem B1367451 : Blo 1366502 1367451 := bstep (se 1 (by rfl) ⟨1025588, by rfl⟩ : syracuseStep 1367451 = 2051177) B2051177
theorem B7790255 : Blo 1366502 7790255 := bstep (se 1 (by rfl) ⟨5842691, by rfl⟩ : syracuseStep 7790255 = 11685383) B11685383
theorem B10387277 : Blo 1366502 10387277 := bstep (se 3 (by rfl) ⟨1947614, by rfl⟩ : syracuseStep 10387277 = 3895229) B3895229
theorem B21045181 : Blo 1366502 21045181 := bstep (se 3 (by rfl) ⟨3945971, by rfl⟩ : syracuseStep 21045181 = 7891943) B7891943
theorem B7790687 : Blo 1366502 7790687 := bstep (se 1 (by rfl) ⟨5843015, by rfl⟩ : syracuseStep 7790687 = 11686031) B11686031
theorem B1368303 : Blo 1366502 1368303 := bstep (se 1 (by rfl) ⟨1026227, by rfl⟩ : syracuseStep 1368303 = 2052455) B2052455
theorem B1368315 : Blo 1366502 1368315 := bstep (se 1 (by rfl) ⟨1026236, by rfl⟩ : syracuseStep 1368315 = 2052473) B2052473
theorem B9863491 : Blo 1366502 9863491 := bstep (se 1 (by rfl) ⟨7397618, by rfl⟩ : syracuseStep 9863491 = 14795237) B14795237
theorem B1368423 : Blo 1366502 1368423 := bstep (se 1 (by rfl) ⟨1026317, by rfl⟩ : syracuseStep 1368423 = 2052635) B2052635
theorem B78889463 : Blo 1366502 78889463 := bstep (se 1 (by rfl) ⟨59167097, by rfl⟩ : syracuseStep 78889463 = 118334195) B118334195
theorem B4612733 : Blo 1366502 4612733 := bstep (se 3 (by rfl) ⟨864887, by rfl⟩ : syracuseStep 4612733 = 1729775) B1729775
theorem B3285755 : Blo 1366502 3285755 := bstep (se 1 (by rfl) ⟨2464316, by rfl⟩ : syracuseStep 3285755 = 4928633) B4928633
theorem B26289107 : Blo 1366502 26289107 := bstep (se 1 (by rfl) ⟨19716830, by rfl⟩ : syracuseStep 26289107 = 39433661) B39433661
theorem B112198931 : Blo 1366502 112198931 := bstep (se 1 (by rfl) ⟨84149198, by rfl⟩ : syracuseStep 112198931 = 168298397) B168298397
theorem B5924123 : Blo 1366502 5924123 := bstep (se 1 (by rfl) ⟨4443092, by rfl⟩ : syracuseStep 5924123 = 8886185) B8886185
theorem B20243951 : Blo 1366502 20243951 := bstep (se 1 (by rfl) ⟨15182963, by rfl⟩ : syracuseStep 20243951 = 30365927) B30365927
theorem B3507943 : Blo 1366502 3507943 := bstep (se 1 (by rfl) ⟨2630957, by rfl⟩ : syracuseStep 3507943 = 5261915) B5261915
theorem B1386239 : Blo 1366502 1386239 := bstep (se 1 (by rfl) ⟨1039679, by rfl⟩ : syracuseStep 1386239 = 2079359) B2079359
theorem B3893339 : Blo 1366502 3893339 := bstep (se 1 (by rfl) ⟨2920004, by rfl⟩ : syracuseStep 3893339 = 5840009) B5840009
theorem B2631935 : Blo 1366502 2631935 := bstep (se 1 (by rfl) ⟨1973951, by rfl⟩ : syracuseStep 2631935 = 3947903) B3947903
theorem B3459631 : Blo 1366502 3459631 := bstep (se 1 (by rfl) ⟨2594723, by rfl⟩ : syracuseStep 3459631 = 5189447) B5189447
theorem B6924851 : Blo 1366502 6924851 := bstep (se 1 (by rfl) ⟨5193638, by rfl⟩ : syracuseStep 6924851 = 10387277) B10387277
theorem B28060241 : Blo 1366502 28060241 := bstep (se 2 (by rfl) ⟨10522590, by rfl⟩ : syracuseStep 28060241 = 21045181) B21045181
theorem B3074975 : Blo 1366502 3074975 := bstep (se 1 (by rfl) ⟨2306231, by rfl⟩ : syracuseStep 3074975 = 4612463) B4612463
theorem B8883425 : Blo 1366502 8883425 := bstep (se 2 (by rfl) ⟨3331284, by rfl⟩ : syracuseStep 8883425 = 6662569) B6662569
theorem B2051399 : Blo 1366502 2051399 := bstep (se 1 (by rfl) ⟨1538549, by rfl⟩ : syracuseStep 2051399 = 3077099) B3077099
theorem B4615595 : Blo 1366502 4615595 := bstep (se 1 (by rfl) ⟨3461696, by rfl⟩ : syracuseStep 4615595 = 6923393) B6923393
theorem B22179359 : Blo 1366502 22179359 := bstep (se 1 (by rfl) ⟨16634519, by rfl⟩ : syracuseStep 22179359 = 33269039) B33269039
theorem B2190959 : Blo 1366502 2190959 := bstep (se 1 (by rfl) ⟨1643219, by rfl⟩ : syracuseStep 2190959 = 3286439) B3286439
theorem B3075803 : Blo 1366502 3075803 := bstep (se 1 (by rfl) ⟨2306852, by rfl⟩ : syracuseStep 3075803 = 4613705) B4613705
theorem B6573815 : Blo 1366502 6573815 := bstep (se 1 (by rfl) ⟨4930361, by rfl⟩ : syracuseStep 6573815 = 9860723) B9860723
theorem B2920295 : Blo 1366502 2920295 := bstep (se 1 (by rfl) ⟨2190221, by rfl⟩ : syracuseStep 2920295 = 4380443) B4380443
theorem B2052329 : Blo 1366502 2052329 := bstep (se 2 (by rfl) ⟨769623, by rfl⟩ : syracuseStep 2052329 = 1539247) B1539247
theorem B5837035 : Blo 1366502 5837035 := bstep (se 1 (by rfl) ⟨4377776, by rfl⟩ : syracuseStep 5837035 = 8755553) B8755553
theorem B2306495 : Blo 1366502 2306495 := bstep (se 1 (by rfl) ⟨1729871, by rfl⟩ : syracuseStep 2306495 = 3459743) B3459743
theorem B3076649 : Blo 1366502 3076649 := bstep (se 2 (by rfl) ⟨1153743, by rfl⟩ : syracuseStep 3076649 = 2307487) B2307487
theorem B3076847 : Blo 1366502 3076847 := bstep (se 1 (by rfl) ⟨2307635, by rfl⟩ : syracuseStep 3076847 = 4615271) B4615271
theorem B3896095 : Blo 1366502 3896095 := bstep (se 1 (by rfl) ⟨2922071, by rfl⟩ : syracuseStep 3896095 = 5844143) B5844143
theorem B3077351 : Blo 1366502 3077351 := bstep (se 1 (by rfl) ⟨2308013, by rfl⟩ : syracuseStep 3077351 = 4616027) B4616027
theorem B6919505 : Blo 1366502 6919505 := bstep (se 2 (by rfl) ⟨2594814, by rfl⟩ : syracuseStep 6919505 = 5189629) B5189629
theorem B2921935 : Blo 1366502 2921935 := bstep (se 1 (by rfl) ⟨2191451, by rfl⟩ : syracuseStep 2921935 = 4382903) B4382903
theorem B2594359 : Blo 1366502 2594359 := bstep (se 1 (by rfl) ⟨1945769, by rfl⟩ : syracuseStep 2594359 = 3891539) B3891539
theorem B3077927 : Blo 1366502 3077927 := bstep (se 1 (by rfl) ⟨2308445, by rfl⟩ : syracuseStep 3077927 = 4616891) B4616891
theorem B8878025 : Blo 1366502 8878025 := bstep (se 2 (by rfl) ⟨3329259, by rfl⟩ : syracuseStep 8878025 = 6658519) B6658519
theorem B33274111 : Blo 1366502 33274111 := bstep (se 1 (by rfl) ⟨24955583, by rfl⟩ : syracuseStep 33274111 = 49911167) B49911167
theorem B3078431 : Blo 1366502 3078431 := bstep (se 1 (by rfl) ⟨2308823, by rfl⟩ : syracuseStep 3078431 = 4617647) B4617647
theorem B3078503 : Blo 1366502 3078503 := bstep (se 1 (by rfl) ⟨2308877, by rfl⟩ : syracuseStep 3078503 = 4617755) B4617755
theorem B3463631 : Blo 1366502 3463631 := bstep (se 1 (by rfl) ⟨2597723, by rfl⟩ : syracuseStep 3463631 = 5195447) B5195447
theorem B3078647 : Blo 1366502 3078647 := bstep (se 1 (by rfl) ⟨2308985, by rfl⟩ : syracuseStep 3078647 = 4617971) B4617971
theorem B1367143 : Blo 1366502 1367143 := bstep (se 1 (by rfl) ⟨1025357, by rfl⟩ : syracuseStep 1367143 = 2050715) B2050715
theorem B1367167 : Blo 1366502 1367167 := bstep (se 1 (by rfl) ⟨1025375, by rfl⟩ : syracuseStep 1367167 = 2050751) B2050751
theorem B7789729 : Blo 1366502 7789729 := bstep (se 2 (by rfl) ⟨2921148, by rfl⟩ : syracuseStep 7789729 = 5842297) B5842297
theorem B1367279 : Blo 1366502 1367279 := bstep (se 1 (by rfl) ⟨1025459, by rfl⟩ : syracuseStep 1367279 = 2050919) B2050919
theorem B1367455 : Blo 1366502 1367455 := bstep (se 1 (by rfl) ⟨1025591, by rfl⟩ : syracuseStep 1367455 = 2051183) B2051183
theorem B1367535 : Blo 1366502 1367535 := bstep (se 1 (by rfl) ⟨1025651, by rfl⟩ : syracuseStep 1367535 = 2051303) B2051303
theorem B47390345 : Blo 1366502 47390345 := bstep (se 2 (by rfl) ⟨17771379, by rfl⟩ : syracuseStep 47390345 = 35542759) B35542759
theorem B5193503 : Blo 1366502 5193503 := bstep (se 1 (by rfl) ⟨3895127, by rfl⟩ : syracuseStep 5193503 = 7790255) B7790255
theorem B2220025 : Blo 1366502 2220025 := bstep (se 2 (by rfl) ⟨832509, by rfl⟩ : syracuseStep 2220025 = 1665019) B1665019
theorem B1368059 : Blo 1366502 1368059 := bstep (se 1 (by rfl) ⟨1026044, by rfl⟩ : syracuseStep 1368059 = 2052089) B2052089
theorem B5193791 : Blo 1366502 5193791 := bstep (se 1 (by rfl) ⟨3895343, by rfl⟩ : syracuseStep 5193791 = 7790687) B7790687
theorem B1368219 : Blo 1366502 1368219 := bstep (se 1 (by rfl) ⟨1026164, by rfl⟩ : syracuseStep 1368219 = 2052329) B2052329
theorem B7782713 : Blo 1366502 7782713 := bstep (se 2 (by rfl) ⟨2918517, by rfl⟩ : syracuseStep 7782713 = 5837035) B5837035
theorem B52592975 : Blo 1366502 52592975 := bstep (se 1 (by rfl) ⟨39444731, by rfl⟩ : syracuseStep 52592975 = 78889463) B78889463
theorem B4612841 : Blo 1366502 4612841 := bstep (se 2 (by rfl) ⟨1729815, by rfl⟩ : syracuseStep 4612841 = 3459631) B3459631
theorem B3949415 : Blo 1366502 3949415 := bstep (se 1 (by rfl) ⟨2962061, by rfl⟩ : syracuseStep 3949415 = 5924123) B5924123
theorem B4613003 : Blo 1366502 4613003 := bstep (se 1 (by rfl) ⟨3459752, by rfl⟩ : syracuseStep 4613003 = 6919505) B6919505
theorem B5194793 : Blo 1366502 5194793 := bstep (se 2 (by rfl) ⟨1948047, by rfl⟩ : syracuseStep 5194793 = 3896095) B3896095
theorem B74827309 : Blo 1366502 74827309 := bstep (se 3 (by rfl) ⟨14030120, by rfl⟩ : syracuseStep 74827309 = 28060241) B28060241
theorem B2049983 : Blo 1366502 2049983 := bstep (se 1 (by rfl) ⟨1537487, by rfl⟩ : syracuseStep 2049983 = 3074975) B3074975
theorem B3459145 : Blo 1366502 3459145 := bstep (se 2 (by rfl) ⟨1297179, by rfl⟩ : syracuseStep 3459145 = 2594359) B2594359
theorem B1460639 : Blo 1366502 1460639 := bstep (se 1 (by rfl) ⟨1095479, by rfl⟩ : syracuseStep 1460639 = 2190959) B2190959
theorem B2050535 : Blo 1366502 2050535 := bstep (se 1 (by rfl) ⟨1537901, by rfl⟩ : syracuseStep 2050535 = 3075803) B3075803
theorem B2960033 : Blo 1366502 2960033 := bstep (se 2 (by rfl) ⟨1110012, by rfl⟩ : syracuseStep 2960033 = 2220025) B2220025
theorem B2051099 : Blo 1366502 2051099 := bstep (se 1 (by rfl) ⟨1538324, by rfl⟩ : syracuseStep 2051099 = 3076649) B3076649
theorem B3075155 : Blo 1366502 3075155 := bstep (se 1 (by rfl) ⟨2306366, by rfl⟩ : syracuseStep 3075155 = 4612733) B4612733
theorem B13151321 : Blo 1366502 13151321 := bstep (se 2 (by rfl) ⟨4931745, by rfl⟩ : syracuseStep 13151321 = 9863491) B9863491
theorem B2051231 : Blo 1366502 2051231 := bstep (se 1 (by rfl) ⟨1538423, by rfl⟩ : syracuseStep 2051231 = 3076847) B3076847
theorem B2190503 : Blo 1366502 2190503 := bstep (se 1 (by rfl) ⟨1642877, by rfl⟩ : syracuseStep 2190503 = 3285755) B3285755
theorem B17526071 : Blo 1366502 17526071 := bstep (se 1 (by rfl) ⟨13144553, by rfl⟩ : syracuseStep 17526071 = 26289107) B26289107
theorem B2051567 : Blo 1366502 2051567 := bstep (se 1 (by rfl) ⟨1538675, by rfl⟩ : syracuseStep 2051567 = 3077351) B3077351
theorem B13495967 : Blo 1366502 13495967 := bstep (se 1 (by rfl) ⟨10121975, by rfl⟩ : syracuseStep 13495967 = 20243951) B20243951
theorem B2051951 : Blo 1366502 2051951 := bstep (se 1 (by rfl) ⟨1538963, by rfl⟩ : syracuseStep 2051951 = 3077927) B3077927
theorem B5918683 : Blo 1366502 5918683 := bstep (se 1 (by rfl) ⟨4439012, by rfl⟩ : syracuseStep 5918683 = 8878025) B8878025
theorem B2052287 : Blo 1366502 2052287 := bstep (se 1 (by rfl) ⟨1539215, by rfl⟩ : syracuseStep 2052287 = 3078431) B3078431
theorem B2052335 : Blo 1366502 2052335 := bstep (se 1 (by rfl) ⟨1539251, by rfl⟩ : syracuseStep 2052335 = 3078503) B3078503
theorem B2052431 : Blo 1366502 2052431 := bstep (se 1 (by rfl) ⟨1539323, by rfl⟩ : syracuseStep 2052431 = 3078647) B3078647
theorem B4616567 : Blo 1366502 4616567 := bstep (se 1 (by rfl) ⟨3462425, by rfl⟩ : syracuseStep 4616567 = 6924851) B6924851
theorem B3895913 : Blo 1366502 3895913 := bstep (se 2 (by rfl) ⟨1460967, by rfl⟩ : syracuseStep 3895913 = 2921935) B2921935
theorem B3077063 : Blo 1366502 3077063 := bstep (se 1 (by rfl) ⟨2307797, by rfl⟩ : syracuseStep 3077063 = 4615595) B4615595
theorem B31593563 : Blo 1366502 31593563 := bstep (se 1 (by rfl) ⟨23695172, by rfl⟩ : syracuseStep 31593563 = 47390345) B47390345
theorem B3462335 : Blo 1366502 3462335 := bstep (se 1 (by rfl) ⟨2596751, by rfl⟩ : syracuseStep 3462335 = 5193503) B5193503
theorem B1946863 : Blo 1366502 1946863 := bstep (se 1 (by rfl) ⟨1460147, by rfl⟩ : syracuseStep 1946863 = 2920295) B2920295
theorem B1537663 : Blo 1366502 1537663 := bstep (se 1 (by rfl) ⟨1153247, by rfl⟩ : syracuseStep 1537663 = 2306495) B2306495
theorem B44365481 : Blo 1366502 44365481 := bstep (se 2 (by rfl) ⟨16637055, by rfl⟩ : syracuseStep 44365481 = 33274111) B33274111
theorem B7018493 : Blo 1366502 7018493 := bstep (se 3 (by rfl) ⟨1315967, by rfl⟩ : syracuseStep 7018493 = 2631935) B2631935
theorem B74799287 : Blo 1366502 74799287 := bstep (se 1 (by rfl) ⟨56099465, by rfl⟩ : syracuseStep 74799287 = 112198931) B112198931
theorem B2595559 : Blo 1366502 2595559 := bstep (se 1 (by rfl) ⟨1946669, by rfl⟩ : syracuseStep 2595559 = 3893339) B3893339
theorem B10386305 : Blo 1366502 10386305 := bstep (se 2 (by rfl) ⟨3894864, by rfl⟩ : syracuseStep 10386305 = 7789729) B7789729
theorem B2309087 : Blo 1366502 2309087 := bstep (se 1 (by rfl) ⟨1731815, by rfl⟩ : syracuseStep 2309087 = 3463631) B3463631
theorem B5922283 : Blo 1366502 5922283 := bstep (se 1 (by rfl) ⟨4441712, by rfl⟩ : syracuseStep 5922283 = 8883425) B8883425
theorem B1367599 : Blo 1366502 1367599 := bstep (se 1 (by rfl) ⟨1025699, by rfl⟩ : syracuseStep 1367599 = 2051399) B2051399
theorem B4677257 : Blo 1366502 4677257 := bstep (se 2 (by rfl) ⟨1753971, by rfl⟩ : syracuseStep 4677257 = 3507943) B3507943
theorem B14786239 : Blo 1366502 14786239 := bstep (se 1 (by rfl) ⟨11089679, by rfl⟩ : syracuseStep 14786239 = 22179359) B22179359
theorem B4382543 : Blo 1366502 4382543 := bstep (se 1 (by rfl) ⟨3286907, by rfl⟩ : syracuseStep 4382543 = 6573815) B6573815
theorem B14786549 : Blo 1366502 14786549 := bstep (se 5 (by rfl) ⟨693119, by rfl⟩ : syracuseStep 14786549 = 1386239) B1386239
theorem B4612193 : Blo 1366502 4612193 := bstep (se 2 (by rfl) ⟨1729572, by rfl⟩ : syracuseStep 4612193 = 3459145) B3459145
theorem B1368191 : Blo 1366502 1368191 := bstep (se 1 (by rfl) ⟨1026143, by rfl⟩ : syracuseStep 1368191 = 2052287) B2052287
theorem B1368223 : Blo 1366502 1368223 := bstep (se 1 (by rfl) ⟨1026167, by rfl⟩ : syracuseStep 1368223 = 2052335) B2052335
theorem B35061983 : Blo 1366502 35061983 := bstep (se 1 (by rfl) ⟨26296487, by rfl⟩ : syracuseStep 35061983 = 52592975) B52592975
theorem B1368287 : Blo 1366502 1368287 := bstep (se 1 (by rfl) ⟨1026215, by rfl⟩ : syracuseStep 1368287 = 2052431) B2052431
theorem B2597275 : Blo 1366502 2597275 := bstep (se 1 (by rfl) ⟨1947956, by rfl⟩ : syracuseStep 2597275 = 3895913) B3895913
theorem B5841341 : Blo 1366502 5841341 := bstep (se 3 (by rfl) ⟨1095251, by rfl⟩ : syracuseStep 5841341 = 2190503) B2190503
theorem B21062375 : Blo 1366502 21062375 := bstep (se 1 (by rfl) ⟨15796781, by rfl⟩ : syracuseStep 21062375 = 31593563) B31593563
theorem B49866191 : Blo 1366502 49866191 := bstep (se 1 (by rfl) ⟨37399643, by rfl⟩ : syracuseStep 49866191 = 74799287) B74799287
theorem B31573685 : Blo 1366502 31573685 := bstep (se 5 (by rfl) ⟨1480016, by rfl⟩ : syracuseStep 31573685 = 2960033) B2960033
theorem B6924203 : Blo 1366502 6924203 := bstep (se 1 (by rfl) ⟨5193152, by rfl⟩ : syracuseStep 6924203 = 10386305) B10386305
theorem B2050103 : Blo 1366502 2050103 := bstep (se 1 (by rfl) ⟨1537577, by rfl⟩ : syracuseStep 2050103 = 3075155) B3075155
theorem B8767547 : Blo 1366502 8767547 := bstep (se 1 (by rfl) ⟨6575660, by rfl⟩ : syracuseStep 8767547 = 13151321) B13151321
theorem B2050217 : Blo 1366502 2050217 := bstep (se 2 (by rfl) ⟨768831, by rfl⟩ : syracuseStep 2050217 = 1537663) B1537663
theorem B11684047 : Blo 1366502 11684047 := bstep (se 1 (by rfl) ⟨8763035, by rfl⟩ : syracuseStep 11684047 = 17526071) B17526071
theorem B8997311 : Blo 1366502 8997311 := bstep (se 1 (by rfl) ⟨6747983, by rfl⟩ : syracuseStep 8997311 = 13495967) B13495967
theorem B7891577 : Blo 1366502 7891577 := bstep (se 2 (by rfl) ⟨2959341, by rfl⟩ : syracuseStep 7891577 = 5918683) B5918683
theorem B9857699 : Blo 1366502 9857699 := bstep (se 1 (by rfl) ⟨7393274, by rfl⟩ : syracuseStep 9857699 = 14786549) B14786549
theorem B5188475 : Blo 1366502 5188475 := bstep (se 1 (by rfl) ⟨3891356, by rfl⟩ : syracuseStep 5188475 = 7782713) B7782713
theorem B3075227 : Blo 1366502 3075227 := bstep (se 1 (by rfl) ⟨2306420, by rfl⟩ : syracuseStep 3075227 = 4612841) B4612841
theorem B2632943 : Blo 1366502 2632943 := bstep (se 1 (by rfl) ⟨1974707, by rfl⟩ : syracuseStep 2632943 = 3949415) B3949415
theorem B3075335 : Blo 1366502 3075335 := bstep (se 1 (by rfl) ⟨2306501, by rfl⟩ : syracuseStep 3075335 = 4613003) B4613003
theorem B2051375 : Blo 1366502 2051375 := bstep (se 1 (by rfl) ⟨1538531, by rfl⟩ : syracuseStep 2051375 = 3077063) B3077063
theorem B3460745 : Blo 1366502 3460745 := bstep (se 2 (by rfl) ⟨1297779, by rfl⟩ : syracuseStep 3460745 = 2595559) B2595559
theorem B3895037 : Blo 1366502 3895037 := bstep (se 3 (by rfl) ⟨730319, by rfl⟩ : syracuseStep 3895037 = 1460639) B1460639
theorem B29576987 : Blo 1366502 29576987 := bstep (se 1 (by rfl) ⟨22182740, by rfl⟩ : syracuseStep 29576987 = 44365481) B44365481
theorem B11686781 : Blo 1366502 11686781 := bstep (se 3 (by rfl) ⟨2191271, by rfl⟩ : syracuseStep 11686781 = 4382543) B4382543
theorem B19714985 : Blo 1366502 19714985 := bstep (se 2 (by rfl) ⟨7393119, by rfl⟩ : syracuseStep 19714985 = 14786239) B14786239
theorem B3118171 : Blo 1366502 3118171 := bstep (se 1 (by rfl) ⟨2338628, by rfl⟩ : syracuseStep 3118171 = 4677257) B4677257
theorem B18715981 : Blo 1366502 18715981 := bstep (se 3 (by rfl) ⟨3509246, by rfl⟩ : syracuseStep 18715981 = 7018493) B7018493
theorem B3462527 : Blo 1366502 3462527 := bstep (se 1 (by rfl) ⟨2596895, by rfl⟩ : syracuseStep 3462527 = 5193791) B5193791
theorem B3077711 : Blo 1366502 3077711 := bstep (se 1 (by rfl) ⟨2308283, by rfl⟩ : syracuseStep 3077711 = 4616567) B4616567
theorem B3463195 : Blo 1366502 3463195 := bstep (se 1 (by rfl) ⟨2597396, by rfl⟩ : syracuseStep 3463195 = 5194793) B5194793
theorem B2308223 : Blo 1366502 2308223 := bstep (se 1 (by rfl) ⟨1731167, by rfl⟩ : syracuseStep 2308223 = 3462335) B3462335
theorem B1366655 : Blo 1366502 1366655 := bstep (se 1 (by rfl) ⟨1024991, by rfl⟩ : syracuseStep 1366655 = 2049983) B2049983
theorem B2595817 : Blo 1366502 2595817 := bstep (se 2 (by rfl) ⟨973431, by rfl⟩ : syracuseStep 2595817 = 1946863) B1946863
theorem B1367023 : Blo 1366502 1367023 := bstep (se 1 (by rfl) ⟨1025267, by rfl⟩ : syracuseStep 1367023 = 2050535) B2050535
theorem B7896377 : Blo 1366502 7896377 := bstep (se 2 (by rfl) ⟨2961141, by rfl⟩ : syracuseStep 7896377 = 5922283) B5922283
theorem B1539391 : Blo 1366502 1539391 := bstep (se 1 (by rfl) ⟨1154543, by rfl⟩ : syracuseStep 1539391 = 2309087) B2309087
theorem B1367399 : Blo 1366502 1367399 := bstep (se 1 (by rfl) ⟨1025549, by rfl⟩ : syracuseStep 1367399 = 2051099) B2051099
theorem B99769745 : Blo 1366502 99769745 := bstep (se 2 (by rfl) ⟨37413654, by rfl⟩ : syracuseStep 99769745 = 74827309) B74827309
theorem B1367487 : Blo 1366502 1367487 := bstep (se 1 (by rfl) ⟨1025615, by rfl⟩ : syracuseStep 1367487 = 2051231) B2051231
theorem B1367711 : Blo 1366502 1367711 := bstep (se 1 (by rfl) ⟨1025783, by rfl⟩ : syracuseStep 1367711 = 2051567) B2051567
theorem B1367967 : Blo 1366502 1367967 := bstep (se 1 (by rfl) ⟨1025975, by rfl⟩ : syracuseStep 1367967 = 2051951) B2051951
theorem B14041583 : Blo 1366502 14041583 := bstep (se 1 (by rfl) ⟨10531187, by rfl⟩ : syracuseStep 14041583 = 21062375) B21062375
theorem B7791187 : Blo 1366502 7791187 := bstep (se 1 (by rfl) ⟨5843390, by rfl⟩ : syracuseStep 7791187 = 11686781) B11686781
theorem B33244127 : Blo 1366502 33244127 := bstep (se 1 (by rfl) ⟨24933095, by rfl⟩ : syracuseStep 33244127 = 49866191) B49866191
theorem B5998207 : Blo 1366502 5998207 := bstep (se 1 (by rfl) ⟨4498655, by rfl⟩ : syracuseStep 5998207 = 8997311) B8997311
theorem B5261051 : Blo 1366502 5261051 := bstep (se 1 (by rfl) ⟨3945788, by rfl⟩ : syracuseStep 5261051 = 7891577) B7891577
theorem B24954641 : Blo 1366502 24954641 := bstep (se 2 (by rfl) ⟨9357990, by rfl⟩ : syracuseStep 24954641 = 18715981) B18715981
theorem B6571799 : Blo 1366502 6571799 := bstep (se 1 (by rfl) ⟨4928849, by rfl⟩ : syracuseStep 6571799 = 9857699) B9857699
theorem B3458983 : Blo 1366502 3458983 := bstep (se 1 (by rfl) ⟨2594237, by rfl⟩ : syracuseStep 3458983 = 5188475) B5188475
theorem B2050151 : Blo 1366502 2050151 := bstep (se 1 (by rfl) ⟨1537613, by rfl⟩ : syracuseStep 2050151 = 3075227) B3075227
theorem B1755295 : Blo 1366502 1755295 := bstep (se 1 (by rfl) ⟨1316471, by rfl⟩ : syracuseStep 1755295 = 2632943) B2632943
theorem B2050223 : Blo 1366502 2050223 := bstep (se 1 (by rfl) ⟨1537667, by rfl⟩ : syracuseStep 2050223 = 3075335) B3075335
theorem B66513163 : Blo 1366502 66513163 := bstep (se 1 (by rfl) ⟨49884872, by rfl⟩ : syracuseStep 66513163 = 99769745) B99769745
theorem B3074795 : Blo 1366502 3074795 := bstep (se 1 (by rfl) ⟨2306096, by rfl⟩ : syracuseStep 3074795 = 4612193) B4612193
theorem B23374655 : Blo 1366502 23374655 := bstep (se 1 (by rfl) ⟨17530991, by rfl⟩ : syracuseStep 23374655 = 35061983) B35061983
theorem B3894227 : Blo 1366502 3894227 := bstep (se 1 (by rfl) ⟨2920670, by rfl⟩ : syracuseStep 3894227 = 5841341) B5841341
theorem B13143323 : Blo 1366502 13143323 := bstep (se 1 (by rfl) ⟨9857492, by rfl⟩ : syracuseStep 13143323 = 19714985) B19714985
theorem B21057005 : Blo 1366502 21057005 := bstep (se 3 (by rfl) ⟨3948188, by rfl⟩ : syracuseStep 21057005 = 7896377) B7896377
theorem B2051807 : Blo 1366502 2051807 := bstep (se 1 (by rfl) ⟨1538855, by rfl⟩ : syracuseStep 2051807 = 3077711) B3077711
theorem B4616135 : Blo 1366502 4616135 := bstep (se 1 (by rfl) ⟨3462101, by rfl⟩ : syracuseStep 4616135 = 6924203) B6924203
theorem B3461089 : Blo 1366502 3461089 := bstep (se 2 (by rfl) ⟨1297908, by rfl⟩ : syracuseStep 3461089 = 2595817) B2595817
theorem B5845031 : Blo 1366502 5845031 := bstep (se 1 (by rfl) ⟨4383773, by rfl⟩ : syracuseStep 5845031 = 8767547) B8767547
theorem B4157561 : Blo 1366502 4157561 := bstep (se 2 (by rfl) ⟨1559085, by rfl⟩ : syracuseStep 4157561 = 3118171) B3118171
theorem B2052521 : Blo 1366502 2052521 := bstep (se 2 (by rfl) ⟨769695, by rfl⟩ : syracuseStep 2052521 = 1539391) B1539391
theorem B2307163 : Blo 1366502 2307163 := bstep (se 1 (by rfl) ⟨1730372, by rfl⟩ : syracuseStep 2307163 = 3460745) B3460745
theorem B4617593 : Blo 1366502 4617593 := bstep (se 2 (by rfl) ⟨1731597, by rfl⟩ : syracuseStep 4617593 = 3463195) B3463195
theorem B15578729 : Blo 1366502 15578729 := bstep (se 2 (by rfl) ⟨5842023, by rfl⟩ : syracuseStep 15578729 = 11684047) B11684047
theorem B3463033 : Blo 1366502 3463033 := bstep (se 2 (by rfl) ⟨1298637, by rfl⟩ : syracuseStep 3463033 = 2597275) B2597275
theorem B2308351 : Blo 1366502 2308351 := bstep (se 1 (by rfl) ⟨1731263, by rfl⟩ : syracuseStep 2308351 = 3462527) B3462527
theorem B1366735 : Blo 1366502 1366735 := bstep (se 1 (by rfl) ⟨1025051, by rfl⟩ : syracuseStep 1366735 = 2050103) B2050103
theorem B1538815 : Blo 1366502 1538815 := bstep (se 1 (by rfl) ⟨1154111, by rfl⟩ : syracuseStep 1538815 = 2308223) B2308223
theorem B1366811 : Blo 1366502 1366811 := bstep (se 1 (by rfl) ⟨1025108, by rfl⟩ : syracuseStep 1366811 = 2050217) B2050217
theorem B84196493 : Blo 1366502 84196493 := bstep (se 3 (by rfl) ⟨15786842, by rfl⟩ : syracuseStep 84196493 = 31573685) B31573685
theorem B1367583 : Blo 1366502 1367583 := bstep (se 1 (by rfl) ⟨1025687, by rfl⟩ : syracuseStep 1367583 = 2051375) B2051375
theorem B2596691 : Blo 1366502 2596691 := bstep (se 1 (by rfl) ⟨1947518, by rfl⟩ : syracuseStep 2596691 = 3895037) B3895037
theorem B19717991 : Blo 1366502 19717991 := bstep (se 1 (by rfl) ⟨14788493, by rfl⟩ : syracuseStep 19717991 = 29576987) B29576987
theorem B1368347 : Blo 1366502 1368347 := bstep (se 1 (by rfl) ⟨1026260, by rfl⟩ : syracuseStep 1368347 = 2052521) B2052521
theorem B37446293 : Blo 1366502 37446293 := bstep (se 6 (by rfl) ⟨877647, by rfl⟩ : syracuseStep 37446293 = 1755295) B1755295
theorem B10388249 : Blo 1366502 10388249 := bstep (se 2 (by rfl) ⟨3895593, by rfl⟩ : syracuseStep 10388249 = 7791187) B7791187
theorem B2049863 : Blo 1366502 2049863 := bstep (se 1 (by rfl) ⟨1537397, by rfl⟩ : syracuseStep 2049863 = 3074795) B3074795
theorem B15583103 : Blo 1366502 15583103 := bstep (se 1 (by rfl) ⟨11687327, by rfl⟩ : syracuseStep 15583103 = 23374655) B23374655
theorem B7997609 : Blo 1366502 7997609 := bstep (se 2 (by rfl) ⟨2999103, by rfl⟩ : syracuseStep 7997609 = 5998207) B5998207
theorem B1731127 : Blo 1366502 1731127 := bstep (se 1 (by rfl) ⟨1298345, by rfl⟩ : syracuseStep 1731127 = 2596691) B2596691
theorem B4614785 : Blo 1366502 4614785 := bstep (se 2 (by rfl) ⟨1730544, by rfl⟩ : syracuseStep 4614785 = 3461089) B3461089
theorem B2771707 : Blo 1366502 2771707 := bstep (se 1 (by rfl) ⟨2078780, by rfl⟩ : syracuseStep 2771707 = 4157561) B4157561
theorem B22162751 : Blo 1366502 22162751 := bstep (se 1 (by rfl) ⟨16622063, by rfl⟩ : syracuseStep 22162751 = 33244127) B33244127
theorem B35048861 : Blo 1366502 35048861 := bstep (se 3 (by rfl) ⟨6571661, by rfl⟩ : syracuseStep 35048861 = 13143323) B13143323
theorem B2051753 : Blo 1366502 2051753 := bstep (se 2 (by rfl) ⟨769407, by rfl⟩ : syracuseStep 2051753 = 1538815) B1538815
theorem B3076217 : Blo 1366502 3076217 := bstep (se 2 (by rfl) ⟨1153581, by rfl⟩ : syracuseStep 3076217 = 2307163) B2307163
theorem B14029469 : Blo 1366502 14029469 := bstep (se 3 (by rfl) ⟨2630525, by rfl⟩ : syracuseStep 14029469 = 5261051) B5261051
theorem B14038003 : Blo 1366502 14038003 := bstep (se 1 (by rfl) ⟨10528502, by rfl⟩ : syracuseStep 14038003 = 21057005) B21057005
theorem B4617377 : Blo 1366502 4617377 := bstep (se 2 (by rfl) ⟨1731516, by rfl⟩ : syracuseStep 4617377 = 3463033) B3463033
theorem B13145327 : Blo 1366502 13145327 := bstep (se 1 (by rfl) ⟨9858995, by rfl⟩ : syracuseStep 13145327 = 19717991) B19717991
theorem B3077423 : Blo 1366502 3077423 := bstep (se 1 (by rfl) ⟨2308067, by rfl⟩ : syracuseStep 3077423 = 4616135) B4616135
theorem B3896687 : Blo 1366502 3896687 := bstep (se 1 (by rfl) ⟨2922515, by rfl⟩ : syracuseStep 3896687 = 5845031) B5845031
theorem B9361055 : Blo 1366502 9361055 := bstep (se 1 (by rfl) ⟨7020791, by rfl⟩ : syracuseStep 9361055 = 14041583) B14041583
theorem B3077801 : Blo 1366502 3077801 := bstep (se 2 (by rfl) ⟨1154175, by rfl⟩ : syracuseStep 3077801 = 2308351) B2308351
theorem B88684217 : Blo 1366502 88684217 := bstep (se 2 (by rfl) ⟨33256581, by rfl⟩ : syracuseStep 88684217 = 66513163) B66513163
theorem B3078395 : Blo 1366502 3078395 := bstep (se 1 (by rfl) ⟨2308796, by rfl⟩ : syracuseStep 3078395 = 4617593) B4617593
theorem B10385819 : Blo 1366502 10385819 := bstep (se 1 (by rfl) ⟨7789364, by rfl⟩ : syracuseStep 10385819 = 15578729) B15578729
theorem B16636427 : Blo 1366502 16636427 := bstep (se 1 (by rfl) ⟨12477320, by rfl⟩ : syracuseStep 16636427 = 24954641) B24954641
theorem B4381199 : Blo 1366502 4381199 := bstep (se 1 (by rfl) ⟨3285899, by rfl⟩ : syracuseStep 4381199 = 6571799) B6571799
theorem B1366767 : Blo 1366502 1366767 := bstep (se 1 (by rfl) ⟨1025075, by rfl⟩ : syracuseStep 1366767 = 2050151) B2050151
theorem B1366815 : Blo 1366502 1366815 := bstep (se 1 (by rfl) ⟨1025111, by rfl⟩ : syracuseStep 1366815 = 2050223) B2050223
theorem B2596151 : Blo 1366502 2596151 := bstep (se 1 (by rfl) ⟨1947113, by rfl⟩ : syracuseStep 2596151 = 3894227) B3894227
theorem B56130995 : Blo 1366502 56130995 := bstep (se 1 (by rfl) ⟨42098246, by rfl⟩ : syracuseStep 56130995 = 84196493) B84196493
theorem B1367871 : Blo 1366502 1367871 := bstep (se 1 (by rfl) ⟨1025903, by rfl⟩ : syracuseStep 1367871 = 2051807) B2051807
theorem B4611977 : Blo 1366502 4611977 := bstep (se 2 (by rfl) ⟨1729491, by rfl⟩ : syracuseStep 4611977 = 3458983) B3458983
theorem B6923069 : Blo 1366502 6923069 := bstep (se 3 (by rfl) ⟨1298075, by rfl⟩ : syracuseStep 6923069 = 2596151) B2596151
theorem B3695609 : Blo 1366502 3695609 := bstep (se 2 (by rfl) ⟨1385853, by rfl⟩ : syracuseStep 3695609 = 2771707) B2771707
theorem B59122811 : Blo 1366502 59122811 := bstep (se 1 (by rfl) ⟨44342108, by rfl⟩ : syracuseStep 59122811 = 88684217) B88684217
theorem B10388735 : Blo 1366502 10388735 := bstep (se 1 (by rfl) ⟨7791551, by rfl⟩ : syracuseStep 10388735 = 15583103) B15583103
theorem B6923879 : Blo 1366502 6923879 := bstep (se 1 (by rfl) ⟨5192909, by rfl⟩ : syracuseStep 6923879 = 10385819) B10385819
theorem B24962813 : Blo 1366502 24962813 := bstep (se 3 (by rfl) ⟨4680527, by rfl⟩ : syracuseStep 24962813 = 9361055) B9361055
theorem B23365907 : Blo 1366502 23365907 := bstep (se 1 (by rfl) ⟨17524430, by rfl⟩ : syracuseStep 23365907 = 35048861) B35048861
theorem B3074651 : Blo 1366502 3074651 := bstep (se 1 (by rfl) ⟨2305988, by rfl⟩ : syracuseStep 3074651 = 4611977) B4611977
theorem B2050811 : Blo 1366502 2050811 := bstep (se 1 (by rfl) ⟨1538108, by rfl⟩ : syracuseStep 2050811 = 3076217) B3076217
theorem B24964195 : Blo 1366502 24964195 := bstep (se 1 (by rfl) ⟨18723146, by rfl⟩ : syracuseStep 24964195 = 37446293) B37446293
theorem B6925499 : Blo 1366502 6925499 := bstep (se 1 (by rfl) ⟨5194124, by rfl⟩ : syracuseStep 6925499 = 10388249) B10388249
theorem B2051615 : Blo 1366502 2051615 := bstep (se 1 (by rfl) ⟨1538711, by rfl⟩ : syracuseStep 2051615 = 3077423) B3077423
theorem B10391165 : Blo 1366502 10391165 := bstep (se 3 (by rfl) ⟨1948343, by rfl⟩ : syracuseStep 10391165 = 3896687) B3896687
theorem B2051867 : Blo 1366502 2051867 := bstep (se 1 (by rfl) ⟨1538900, by rfl⟩ : syracuseStep 2051867 = 3077801) B3077801
theorem B2052263 : Blo 1366502 2052263 := bstep (se 1 (by rfl) ⟨1539197, by rfl⟩ : syracuseStep 2052263 = 3078395) B3078395
theorem B2920799 : Blo 1366502 2920799 := bstep (se 1 (by rfl) ⟨2190599, by rfl⟩ : syracuseStep 2920799 = 4381199) B4381199
theorem B3076523 : Blo 1366502 3076523 := bstep (se 1 (by rfl) ⟨2307392, by rfl⟩ : syracuseStep 3076523 = 4614785) B4614785
theorem B14775167 : Blo 1366502 14775167 := bstep (se 1 (by rfl) ⟨11081375, by rfl⟩ : syracuseStep 14775167 = 22162751) B22162751
theorem B9352979 : Blo 1366502 9352979 := bstep (se 1 (by rfl) ⟨7014734, by rfl⟩ : syracuseStep 9352979 = 14029469) B14029469
theorem B2308169 : Blo 1366502 2308169 := bstep (se 2 (by rfl) ⟨865563, by rfl⟩ : syracuseStep 2308169 = 1731127) B1731127
theorem B3078251 : Blo 1366502 3078251 := bstep (se 1 (by rfl) ⟨2308688, by rfl⟩ : syracuseStep 3078251 = 4617377) B4617377
theorem B8763551 : Blo 1366502 8763551 := bstep (se 1 (by rfl) ⟨6572663, by rfl⟩ : syracuseStep 8763551 = 13145327) B13145327
theorem B149682653 : Blo 1366502 149682653 := bstep (se 3 (by rfl) ⟨28065497, by rfl⟩ : syracuseStep 149682653 = 56130995) B56130995
theorem B1366575 : Blo 1366502 1366575 := bstep (se 1 (by rfl) ⟨1024931, by rfl⟩ : syracuseStep 1366575 = 2049863) B2049863
theorem B18717337 : Blo 1366502 18717337 := bstep (se 2 (by rfl) ⟨7019001, by rfl⟩ : syracuseStep 18717337 = 14038003) B14038003
theorem B5331739 : Blo 1366502 5331739 := bstep (se 1 (by rfl) ⟨3998804, by rfl⟩ : syracuseStep 5331739 = 7997609) B7997609
theorem B11090951 : Blo 1366502 11090951 := bstep (se 1 (by rfl) ⟨8318213, by rfl⟩ : syracuseStep 11090951 = 16636427) B16636427
theorem B1367835 : Blo 1366502 1367835 := bstep (se 1 (by rfl) ⟨1025876, by rfl⟩ : syracuseStep 1367835 = 2051753) B2051753
theorem B1368175 : Blo 1366502 1368175 := bstep (se 1 (by rfl) ⟨1026131, by rfl⟩ : syracuseStep 1368175 = 2052263) B2052263
theorem B6235319 : Blo 1366502 6235319 := bstep (se 1 (by rfl) ⟨4676489, by rfl⟩ : syracuseStep 6235319 = 9352979) B9352979
theorem B5842367 : Blo 1366502 5842367 := bstep (se 1 (by rfl) ⟨4381775, by rfl⟩ : syracuseStep 5842367 = 8763551) B8763551
theorem B33285593 : Blo 1366502 33285593 := bstep (se 2 (by rfl) ⟨12482097, by rfl⟩ : syracuseStep 33285593 = 24964195) B24964195
theorem B99788435 : Blo 1366502 99788435 := bstep (se 1 (by rfl) ⟨74841326, by rfl⟩ : syracuseStep 99788435 = 149682653) B149682653
theorem B2049767 : Blo 1366502 2049767 := bstep (se 1 (by rfl) ⟨1537325, by rfl⟩ : syracuseStep 2049767 = 3074651) B3074651
theorem B2051015 : Blo 1366502 2051015 := bstep (se 1 (by rfl) ⟨1538261, by rfl⟩ : syracuseStep 2051015 = 3076523) B3076523
theorem B4615379 : Blo 1366502 4615379 := bstep (se 1 (by rfl) ⟨3461534, by rfl⟩ : syracuseStep 4615379 = 6923069) B6923069
theorem B39415207 : Blo 1366502 39415207 := bstep (se 1 (by rfl) ⟨29561405, by rfl⟩ : syracuseStep 39415207 = 59122811) B59122811
theorem B6925823 : Blo 1366502 6925823 := bstep (se 1 (by rfl) ⟨5194367, by rfl⟩ : syracuseStep 6925823 = 10388735) B10388735
theorem B4615919 : Blo 1366502 4615919 := bstep (se 1 (by rfl) ⟨3461939, by rfl⟩ : syracuseStep 4615919 = 6923879) B6923879
theorem B16641875 : Blo 1366502 16641875 := bstep (se 1 (by rfl) ⟨12481406, by rfl⟩ : syracuseStep 16641875 = 24962813) B24962813
theorem B2052167 : Blo 1366502 2052167 := bstep (se 1 (by rfl) ⟨1539125, by rfl⟩ : syracuseStep 2052167 = 3078251) B3078251
theorem B15577271 : Blo 1366502 15577271 := bstep (se 1 (by rfl) ⟨11682953, by rfl⟩ : syracuseStep 15577271 = 23365907) B23365907
theorem B7393967 : Blo 1366502 7393967 := bstep (se 1 (by rfl) ⟨5545475, by rfl⟩ : syracuseStep 7393967 = 11090951) B11090951
theorem B4616999 : Blo 1366502 4616999 := bstep (se 1 (by rfl) ⟨3462749, by rfl⟩ : syracuseStep 4616999 = 6925499) B6925499
theorem B39400445 : Blo 1366502 39400445 := bstep (se 3 (by rfl) ⟨7387583, by rfl⟩ : syracuseStep 39400445 = 14775167) B14775167
theorem B6927443 : Blo 1366502 6927443 := bstep (se 1 (by rfl) ⟨5195582, by rfl⟩ : syracuseStep 6927443 = 10391165) B10391165
theorem B2463739 : Blo 1366502 2463739 := bstep (se 1 (by rfl) ⟨1847804, by rfl⟩ : syracuseStep 2463739 = 3695609) B3695609
theorem B99825797 : Blo 1366502 99825797 := bstep (se 4 (by rfl) ⟨9358668, by rfl⟩ : syracuseStep 99825797 = 18717337) B18717337
theorem B7788797 : Blo 1366502 7788797 := bstep (se 3 (by rfl) ⟨1460399, by rfl⟩ : syracuseStep 7788797 = 2920799) B2920799
theorem B7108985 : Blo 1366502 7108985 := bstep (se 2 (by rfl) ⟨2665869, by rfl⟩ : syracuseStep 7108985 = 5331739) B5331739
theorem B1538779 : Blo 1366502 1538779 := bstep (se 1 (by rfl) ⟨1154084, by rfl⟩ : syracuseStep 1538779 = 2308169) B2308169
theorem B1367207 : Blo 1366502 1367207 := bstep (se 1 (by rfl) ⟨1025405, by rfl⟩ : syracuseStep 1367207 = 2050811) B2050811
theorem B1367743 : Blo 1366502 1367743 := bstep (se 1 (by rfl) ⟨1025807, by rfl⟩ : syracuseStep 1367743 = 2051615) B2051615
theorem B1367911 : Blo 1366502 1367911 := bstep (se 1 (by rfl) ⟨1025933, by rfl⟩ : syracuseStep 1367911 = 2051867) B2051867
theorem B1368111 : Blo 1366502 1368111 := bstep (se 1 (by rfl) ⟨1026083, by rfl⟩ : syracuseStep 1368111 = 2052167) B2052167
theorem B18957293 : Blo 1366502 18957293 := bstep (se 3 (by rfl) ⟨3554492, by rfl⟩ : syracuseStep 18957293 = 7108985) B7108985
theorem B52553609 : Blo 1366502 52553609 := bstep (se 2 (by rfl) ⟨19707603, by rfl⟩ : syracuseStep 52553609 = 39415207) B39415207
theorem B11094583 : Blo 1366502 11094583 := bstep (se 1 (by rfl) ⟨8320937, by rfl⟩ : syracuseStep 11094583 = 16641875) B16641875
theorem B26266963 : Blo 1366502 26266963 := bstep (se 1 (by rfl) ⟨19700222, by rfl⟩ : syracuseStep 26266963 = 39400445) B39400445
theorem B2051705 : Blo 1366502 2051705 := bstep (se 2 (by rfl) ⟨769389, by rfl⟩ : syracuseStep 2051705 = 1538779) B1538779
theorem B3894911 : Blo 1366502 3894911 := bstep (se 1 (by rfl) ⟨2921183, by rfl⟩ : syracuseStep 3894911 = 5842367) B5842367
theorem B3076919 : Blo 1366502 3076919 := bstep (se 1 (by rfl) ⟨2307689, by rfl⟩ : syracuseStep 3076919 = 4615379) B4615379
theorem B4617215 : Blo 1366502 4617215 := bstep (se 1 (by rfl) ⟨3462911, by rfl⟩ : syracuseStep 4617215 = 6925823) B6925823
theorem B3077279 : Blo 1366502 3077279 := bstep (se 1 (by rfl) ⟨2307959, by rfl⟩ : syracuseStep 3077279 = 4615919) B4615919
theorem B10384847 : Blo 1366502 10384847 := bstep (se 1 (by rfl) ⟨7788635, by rfl⟩ : syracuseStep 10384847 = 15577271) B15577271
theorem B4929311 : Blo 1366502 4929311 := bstep (se 1 (by rfl) ⟨3696983, by rfl⟩ : syracuseStep 4929311 = 7393967) B7393967
theorem B16627517 : Blo 1366502 16627517 := bstep (se 3 (by rfl) ⟨3117659, by rfl⟩ : syracuseStep 16627517 = 6235319) B6235319
theorem B3077999 : Blo 1366502 3077999 := bstep (se 1 (by rfl) ⟨2308499, by rfl⟩ : syracuseStep 3077999 = 4616999) B4616999
theorem B4618295 : Blo 1366502 4618295 := bstep (se 1 (by rfl) ⟨3463721, by rfl⟩ : syracuseStep 4618295 = 6927443) B6927443
theorem B22190395 : Blo 1366502 22190395 := bstep (se 1 (by rfl) ⟨16642796, by rfl⟩ : syracuseStep 22190395 = 33285593) B33285593
theorem B66525623 : Blo 1366502 66525623 := bstep (se 1 (by rfl) ⟨49894217, by rfl⟩ : syracuseStep 66525623 = 99788435) B99788435
theorem B1366511 : Blo 1366502 1366511 := bstep (se 1 (by rfl) ⟨1024883, by rfl⟩ : syracuseStep 1366511 = 2049767) B2049767
theorem B66550531 : Blo 1366502 66550531 := bstep (se 1 (by rfl) ⟨49912898, by rfl⟩ : syracuseStep 66550531 = 99825797) B99825797
theorem B5192531 : Blo 1366502 5192531 := bstep (se 1 (by rfl) ⟨3894398, by rfl⟩ : syracuseStep 5192531 = 7788797) B7788797
theorem B1367343 : Blo 1366502 1367343 := bstep (se 1 (by rfl) ⟨1025507, by rfl⟩ : syracuseStep 1367343 = 2051015) B2051015
theorem B13139941 : Blo 1366502 13139941 := bstep (se 4 (by rfl) ⟨1231869, by rfl⟩ : syracuseStep 13139941 = 2463739) B2463739
theorem B6923231 : Blo 1366502 6923231 := bstep (se 1 (by rfl) ⟨5192423, by rfl⟩ : syracuseStep 6923231 = 10384847) B10384847
theorem B3286207 : Blo 1366502 3286207 := bstep (se 1 (by rfl) ⟨2464655, by rfl⟩ : syracuseStep 3286207 = 4929311) B4929311
theorem B11085011 : Blo 1366502 11085011 := bstep (se 1 (by rfl) ⟨8313758, by rfl⟩ : syracuseStep 11085011 = 16627517) B16627517
theorem B35022617 : Blo 1366502 35022617 := bstep (se 2 (by rfl) ⟨13133481, by rfl⟩ : syracuseStep 35022617 = 26266963) B26266963
theorem B2051279 : Blo 1366502 2051279 := bstep (se 1 (by rfl) ⟨1538459, by rfl⟩ : syracuseStep 2051279 = 3076919) B3076919
theorem B2051519 : Blo 1366502 2051519 := bstep (se 1 (by rfl) ⟨1538639, by rfl⟩ : syracuseStep 2051519 = 3077279) B3077279
theorem B2051999 : Blo 1366502 2051999 := bstep (se 1 (by rfl) ⟨1538999, by rfl⟩ : syracuseStep 2051999 = 3077999) B3077999
theorem B3461687 : Blo 1366502 3461687 := bstep (se 1 (by rfl) ⟨2596265, by rfl⟩ : syracuseStep 3461687 = 5192531) B5192531
theorem B17519921 : Blo 1366502 17519921 := bstep (se 2 (by rfl) ⟨6569970, by rfl⟩ : syracuseStep 17519921 = 13139941) B13139941
theorem B29587193 : Blo 1366502 29587193 := bstep (se 2 (by rfl) ⟨11095197, by rfl⟩ : syracuseStep 29587193 = 22190395) B22190395
theorem B12638195 : Blo 1366502 12638195 := bstep (se 1 (by rfl) ⟨9478646, by rfl⟩ : syracuseStep 12638195 = 18957293) B18957293
theorem B3078143 : Blo 1366502 3078143 := bstep (se 1 (by rfl) ⟨2308607, by rfl⟩ : syracuseStep 3078143 = 4617215) B4617215
theorem B14792777 : Blo 1366502 14792777 := bstep (se 2 (by rfl) ⟨5547291, by rfl⟩ : syracuseStep 14792777 = 11094583) B11094583
theorem B88734041 : Blo 1366502 88734041 := bstep (se 2 (by rfl) ⟨33275265, by rfl⟩ : syracuseStep 88734041 = 66550531) B66550531
theorem B35035739 : Blo 1366502 35035739 := bstep (se 1 (by rfl) ⟨26276804, by rfl⟩ : syracuseStep 35035739 = 52553609) B52553609
theorem B3078863 : Blo 1366502 3078863 := bstep (se 1 (by rfl) ⟨2309147, by rfl⟩ : syracuseStep 3078863 = 4618295) B4618295
theorem B44350415 : Blo 1366502 44350415 := bstep (se 1 (by rfl) ⟨33262811, by rfl⟩ : syracuseStep 44350415 = 66525623) B66525623
theorem B1367803 : Blo 1366502 1367803 := bstep (se 1 (by rfl) ⟨1025852, by rfl⟩ : syracuseStep 1367803 = 2051705) B2051705
theorem B2596607 : Blo 1366502 2596607 := bstep (se 1 (by rfl) ⟨1947455, by rfl⟩ : syracuseStep 2596607 = 3894911) B3894911
theorem B7390007 : Blo 1366502 7390007 := bstep (se 1 (by rfl) ⟨5542505, by rfl⟩ : syracuseStep 7390007 = 11085011) B11085011
theorem B23348411 : Blo 1366502 23348411 := bstep (se 1 (by rfl) ⟨17511308, by rfl⟩ : syracuseStep 23348411 = 35022617) B35022617
theorem B59156027 : Blo 1366502 59156027 := bstep (se 1 (by rfl) ⟨44367020, by rfl⟩ : syracuseStep 59156027 = 88734041) B88734041
theorem B23357159 : Blo 1366502 23357159 := bstep (se 1 (by rfl) ⟨17517869, by rfl⟩ : syracuseStep 23357159 = 35035739) B35035739
theorem B29566943 : Blo 1366502 29566943 := bstep (se 1 (by rfl) ⟨22175207, by rfl⟩ : syracuseStep 29566943 = 44350415) B44350415
theorem B1731071 : Blo 1366502 1731071 := bstep (se 1 (by rfl) ⟨1298303, by rfl⟩ : syracuseStep 1731071 = 2596607) B2596607
theorem B4615487 : Blo 1366502 4615487 := bstep (se 1 (by rfl) ⟨3461615, by rfl⟩ : syracuseStep 4615487 = 6923231) B6923231
theorem B8425463 : Blo 1366502 8425463 := bstep (se 1 (by rfl) ⟨6319097, by rfl⟩ : syracuseStep 8425463 = 12638195) B12638195
theorem B2052095 : Blo 1366502 2052095 := bstep (se 1 (by rfl) ⟨1539071, by rfl⟩ : syracuseStep 2052095 = 3078143) B3078143
theorem B2052575 : Blo 1366502 2052575 := bstep (se 1 (by rfl) ⟨1539431, by rfl⟩ : syracuseStep 2052575 = 3078863) B3078863
theorem B2307791 : Blo 1366502 2307791 := bstep (se 1 (by rfl) ⟨1730843, by rfl⟩ : syracuseStep 2307791 = 3461687) B3461687
theorem B11679947 : Blo 1366502 11679947 := bstep (se 1 (by rfl) ⟨8759960, by rfl⟩ : syracuseStep 11679947 = 17519921) B17519921
theorem B19724795 : Blo 1366502 19724795 := bstep (se 1 (by rfl) ⟨14793596, by rfl⟩ : syracuseStep 19724795 = 29587193) B29587193
theorem B9861851 : Blo 1366502 9861851 := bstep (se 1 (by rfl) ⟨7396388, by rfl⟩ : syracuseStep 9861851 = 14792777) B14792777
theorem B4381609 : Blo 1366502 4381609 := bstep (se 2 (by rfl) ⟨1643103, by rfl⟩ : syracuseStep 4381609 = 3286207) B3286207
theorem B1367519 : Blo 1366502 1367519 := bstep (se 1 (by rfl) ⟨1025639, by rfl⟩ : syracuseStep 1367519 = 2051279) B2051279
theorem B1367679 : Blo 1366502 1367679 := bstep (se 1 (by rfl) ⟨1025759, by rfl⟩ : syracuseStep 1367679 = 2051519) B2051519
theorem B1367999 : Blo 1366502 1367999 := bstep (se 1 (by rfl) ⟨1025999, by rfl⟩ : syracuseStep 1367999 = 2051999) B2051999
theorem B1368383 : Blo 1366502 1368383 := bstep (se 1 (by rfl) ⟨1026287, by rfl⟩ : syracuseStep 1368383 = 2052575) B2052575
theorem B15565607 : Blo 1366502 15565607 := bstep (se 1 (by rfl) ⟨11674205, by rfl⟩ : syracuseStep 15565607 = 23348411) B23348411
theorem B39437351 : Blo 1366502 39437351 := bstep (se 1 (by rfl) ⟨29578013, by rfl⟩ : syracuseStep 39437351 = 59156027) B59156027
theorem B5842145 : Blo 1366502 5842145 := bstep (se 2 (by rfl) ⟨2190804, by rfl⟩ : syracuseStep 5842145 = 4381609) B4381609
theorem B19711295 : Blo 1366502 19711295 := bstep (se 1 (by rfl) ⟨14783471, by rfl⟩ : syracuseStep 19711295 = 29566943) B29566943
theorem B13149863 : Blo 1366502 13149863 := bstep (se 1 (by rfl) ⟨9862397, by rfl⟩ : syracuseStep 13149863 = 19724795) B19724795
theorem B4926671 : Blo 1366502 4926671 := bstep (se 1 (by rfl) ⟨3695003, by rfl⟩ : syracuseStep 4926671 = 7390007) B7390007
theorem B4616189 : Blo 1366502 4616189 := bstep (se 3 (by rfl) ⟨865535, by rfl⟩ : syracuseStep 4616189 = 1731071) B1731071
theorem B7786631 : Blo 1366502 7786631 := bstep (se 1 (by rfl) ⟨5839973, by rfl⟩ : syracuseStep 7786631 = 11679947) B11679947
theorem B6574567 : Blo 1366502 6574567 := bstep (se 1 (by rfl) ⟨4930925, by rfl⟩ : syracuseStep 6574567 = 9861851) B9861851
theorem B3076991 : Blo 1366502 3076991 := bstep (se 1 (by rfl) ⟨2307743, by rfl⟩ : syracuseStep 3076991 = 4615487) B4615487
theorem B22467901 : Blo 1366502 22467901 := bstep (se 3 (by rfl) ⟨4212731, by rfl⟩ : syracuseStep 22467901 = 8425463) B8425463
theorem B1538527 : Blo 1366502 1538527 := bstep (se 1 (by rfl) ⟨1153895, by rfl⟩ : syracuseStep 1538527 = 2307791) B2307791
theorem B15571439 : Blo 1366502 15571439 := bstep (se 1 (by rfl) ⟨11678579, by rfl⟩ : syracuseStep 15571439 = 23357159) B23357159
theorem B1368063 : Blo 1366502 1368063 := bstep (se 1 (by rfl) ⟨1026047, by rfl⟩ : syracuseStep 1368063 = 2052095) B2052095
theorem B8766089 : Blo 1366502 8766089 := bstep (se 2 (by rfl) ⟨3287283, by rfl⟩ : syracuseStep 8766089 = 6574567) B6574567
theorem B13140863 : Blo 1366502 13140863 := bstep (se 1 (by rfl) ⟨9855647, by rfl⟩ : syracuseStep 13140863 = 19711295) B19711295
theorem B8766575 : Blo 1366502 8766575 := bstep (se 1 (by rfl) ⟨6574931, by rfl⟩ : syracuseStep 8766575 = 13149863) B13149863
theorem B10380959 : Blo 1366502 10380959 := bstep (se 1 (by rfl) ⟨7785719, by rfl⟩ : syracuseStep 10380959 = 15571439) B15571439
theorem B2051327 : Blo 1366502 2051327 := bstep (se 1 (by rfl) ⟨1538495, by rfl⟩ : syracuseStep 2051327 = 3076991) B3076991
theorem B2051369 : Blo 1366502 2051369 := bstep (se 2 (by rfl) ⟨769263, by rfl⟩ : syracuseStep 2051369 = 1538527) B1538527
theorem B26291567 : Blo 1366502 26291567 := bstep (se 1 (by rfl) ⟨19718675, by rfl⟩ : syracuseStep 26291567 = 39437351) B39437351
theorem B3894763 : Blo 1366502 3894763 := bstep (se 1 (by rfl) ⟨2921072, by rfl⟩ : syracuseStep 3894763 = 5842145) B5842145
theorem B3077459 : Blo 1366502 3077459 := bstep (se 1 (by rfl) ⟨2308094, by rfl⟩ : syracuseStep 3077459 = 4616189) B4616189
theorem B5191087 : Blo 1366502 5191087 := bstep (se 1 (by rfl) ⟨3893315, by rfl⟩ : syracuseStep 5191087 = 7786631) B7786631
theorem B10377071 : Blo 1366502 10377071 := bstep (se 1 (by rfl) ⟨7782803, by rfl⟩ : syracuseStep 10377071 = 15565607) B15565607
theorem B29957201 : Blo 1366502 29957201 := bstep (se 2 (by rfl) ⟨11233950, by rfl⟩ : syracuseStep 29957201 = 22467901) B22467901
theorem B3284447 : Blo 1366502 3284447 := bstep (se 1 (by rfl) ⟨2463335, by rfl⟩ : syracuseStep 3284447 = 4926671) B4926671
theorem B8758525 : Blo 1366502 8758525 := bstep (se 3 (by rfl) ⟨1642223, by rfl⟩ : syracuseStep 8758525 = 3284447) B3284447
theorem B5844059 : Blo 1366502 5844059 := bstep (se 1 (by rfl) ⟨4383044, by rfl⟩ : syracuseStep 5844059 = 8766089) B8766089
theorem B8760575 : Blo 1366502 8760575 := bstep (se 1 (by rfl) ⟨6570431, by rfl⟩ : syracuseStep 8760575 = 13140863) B13140863
theorem B5844383 : Blo 1366502 5844383 := bstep (se 1 (by rfl) ⟨4383287, by rfl⟩ : syracuseStep 5844383 = 8766575) B8766575
theorem B2051639 : Blo 1366502 2051639 := bstep (se 1 (by rfl) ⟨1538729, by rfl⟩ : syracuseStep 2051639 = 3077459) B3077459
theorem B6918047 : Blo 1366502 6918047 := bstep (se 1 (by rfl) ⟨5188535, by rfl⟩ : syracuseStep 6918047 = 10377071) B10377071
theorem B17527711 : Blo 1366502 17527711 := bstep (se 1 (by rfl) ⟨13145783, by rfl⟩ : syracuseStep 17527711 = 26291567) B26291567
theorem B6920639 : Blo 1366502 6920639 := bstep (se 1 (by rfl) ⟨5190479, by rfl⟩ : syracuseStep 6920639 = 10380959) B10380959
theorem B6921449 : Blo 1366502 6921449 := bstep (se 2 (by rfl) ⟨2595543, by rfl⟩ : syracuseStep 6921449 = 5191087) B5191087
theorem B5193017 : Blo 1366502 5193017 := bstep (se 2 (by rfl) ⟨1947381, by rfl⟩ : syracuseStep 5193017 = 3894763) B3894763
theorem B19971467 : Blo 1366502 19971467 := bstep (se 1 (by rfl) ⟨14978600, by rfl⟩ : syracuseStep 19971467 = 29957201) B29957201
theorem B1367551 : Blo 1366502 1367551 := bstep (se 1 (by rfl) ⟨1025663, by rfl⟩ : syracuseStep 1367551 = 2051327) B2051327
theorem B1367579 : Blo 1366502 1367579 := bstep (se 1 (by rfl) ⟨1025684, by rfl⟩ : syracuseStep 1367579 = 2051369) B2051369
theorem B4613759 : Blo 1366502 4613759 := bstep (se 1 (by rfl) ⟨3460319, by rfl⟩ : syracuseStep 4613759 = 6920639) B6920639
theorem B4614299 : Blo 1366502 4614299 := bstep (se 1 (by rfl) ⟨3460724, by rfl⟩ : syracuseStep 4614299 = 6921449) B6921449
theorem B13314311 : Blo 1366502 13314311 := bstep (se 1 (by rfl) ⟨9985733, by rfl⟩ : syracuseStep 13314311 = 19971467) B19971467
theorem B11678033 : Blo 1366502 11678033 := bstep (se 2 (by rfl) ⟨4379262, by rfl⟩ : syracuseStep 11678033 = 8758525) B8758525
theorem B3896039 : Blo 1366502 3896039 := bstep (se 1 (by rfl) ⟨2922029, by rfl⟩ : syracuseStep 3896039 = 5844059) B5844059
theorem B3462011 : Blo 1366502 3462011 := bstep (se 1 (by rfl) ⟨2596508, by rfl⟩ : syracuseStep 3462011 = 5193017) B5193017
theorem B3896255 : Blo 1366502 3896255 := bstep (se 1 (by rfl) ⟨2922191, by rfl⟩ : syracuseStep 3896255 = 5844383) B5844383
theorem B23361533 : Blo 1366502 23361533 := bstep (se 3 (by rfl) ⟨4380287, by rfl⟩ : syracuseStep 23361533 = 8760575) B8760575
theorem B23370281 : Blo 1366502 23370281 := bstep (se 2 (by rfl) ⟨8763855, by rfl⟩ : syracuseStep 23370281 = 17527711) B17527711
theorem B1367759 : Blo 1366502 1367759 := bstep (se 1 (by rfl) ⟨1025819, by rfl⟩ : syracuseStep 1367759 = 2051639) B2051639
theorem B4612031 : Blo 1366502 4612031 := bstep (se 1 (by rfl) ⟨3459023, by rfl⟩ : syracuseStep 4612031 = 6918047) B6918047
theorem B2597359 : Blo 1366502 2597359 := bstep (se 1 (by rfl) ⟨1948019, by rfl⟩ : syracuseStep 2597359 = 3896039) B3896039
theorem B2597503 : Blo 1366502 2597503 := bstep (se 1 (by rfl) ⟨1948127, by rfl⟩ : syracuseStep 2597503 = 3896255) B3896255
theorem B15574355 : Blo 1366502 15574355 := bstep (se 1 (by rfl) ⟨11680766, by rfl⟩ : syracuseStep 15574355 = 23361533) B23361533
theorem B3074687 : Blo 1366502 3074687 := bstep (se 1 (by rfl) ⟨2306015, by rfl⟩ : syracuseStep 3074687 = 4612031) B4612031
theorem B7785355 : Blo 1366502 7785355 := bstep (se 1 (by rfl) ⟨5839016, by rfl⟩ : syracuseStep 7785355 = 11678033) B11678033
theorem B3075839 : Blo 1366502 3075839 := bstep (se 1 (by rfl) ⟨2306879, by rfl⟩ : syracuseStep 3075839 = 4613759) B4613759
theorem B3076199 : Blo 1366502 3076199 := bstep (se 1 (by rfl) ⟨2307149, by rfl⟩ : syracuseStep 3076199 = 4614299) B4614299
theorem B8876207 : Blo 1366502 8876207 := bstep (se 1 (by rfl) ⟨6657155, by rfl⟩ : syracuseStep 8876207 = 13314311) B13314311
theorem B2308007 : Blo 1366502 2308007 := bstep (se 1 (by rfl) ⟨1731005, by rfl⟩ : syracuseStep 2308007 = 3462011) B3462011
theorem B15580187 : Blo 1366502 15580187 := bstep (se 1 (by rfl) ⟨11685140, by rfl⟩ : syracuseStep 15580187 = 23370281) B23370281
theorem B10380473 : Blo 1366502 10380473 := bstep (se 2 (by rfl) ⟨3892677, by rfl⟩ : syracuseStep 10380473 = 7785355) B7785355
theorem B2049791 : Blo 1366502 2049791 := bstep (se 1 (by rfl) ⟨1537343, by rfl⟩ : syracuseStep 2049791 = 3074687) B3074687
theorem B2050559 : Blo 1366502 2050559 := bstep (se 1 (by rfl) ⟨1537919, by rfl⟩ : syracuseStep 2050559 = 3075839) B3075839
theorem B2050799 : Blo 1366502 2050799 := bstep (se 1 (by rfl) ⟨1538099, by rfl⟩ : syracuseStep 2050799 = 3076199) B3076199
theorem B5917471 : Blo 1366502 5917471 := bstep (se 1 (by rfl) ⟨4438103, by rfl⟩ : syracuseStep 5917471 = 8876207) B8876207
theorem B10382903 : Blo 1366502 10382903 := bstep (se 1 (by rfl) ⟨7787177, by rfl⟩ : syracuseStep 10382903 = 15574355) B15574355
theorem B3463145 : Blo 1366502 3463145 := bstep (se 2 (by rfl) ⟨1298679, by rfl⟩ : syracuseStep 3463145 = 2597359) B2597359
theorem B3463337 : Blo 1366502 3463337 := bstep (se 2 (by rfl) ⟨1298751, by rfl⟩ : syracuseStep 3463337 = 2597503) B2597503
theorem B1538671 : Blo 1366502 1538671 := bstep (se 1 (by rfl) ⟨1154003, by rfl⟩ : syracuseStep 1538671 = 2308007) B2308007
theorem B10386791 : Blo 1366502 10386791 := bstep (se 1 (by rfl) ⟨7790093, by rfl⟩ : syracuseStep 10386791 = 15580187) B15580187
theorem B126239381 : Blo 1366502 126239381 := bstep (se 6 (by rfl) ⟨2958735, by rfl⟩ : syracuseStep 126239381 = 5917471) B5917471
theorem B6924527 : Blo 1366502 6924527 := bstep (se 1 (by rfl) ⟨5193395, by rfl⟩ : syracuseStep 6924527 = 10386791) B10386791
theorem B2051561 : Blo 1366502 2051561 := bstep (se 2 (by rfl) ⟨769335, by rfl⟩ : syracuseStep 2051561 = 1538671) B1538671
theorem B6920315 : Blo 1366502 6920315 := bstep (se 1 (by rfl) ⟨5190236, by rfl⟩ : syracuseStep 6920315 = 10380473) B10380473
theorem B1366527 : Blo 1366502 1366527 := bstep (se 1 (by rfl) ⟨1024895, by rfl⟩ : syracuseStep 1366527 = 2049791) B2049791
theorem B2308763 : Blo 1366502 2308763 := bstep (se 1 (by rfl) ⟨1731572, by rfl⟩ : syracuseStep 2308763 = 3463145) B3463145
theorem B2308891 : Blo 1366502 2308891 := bstep (se 1 (by rfl) ⟨1731668, by rfl⟩ : syracuseStep 2308891 = 3463337) B3463337
theorem B1367039 : Blo 1366502 1367039 := bstep (se 1 (by rfl) ⟨1025279, by rfl⟩ : syracuseStep 1367039 = 2050559) B2050559
theorem B1367199 : Blo 1366502 1367199 := bstep (se 1 (by rfl) ⟨1025399, by rfl⟩ : syracuseStep 1367199 = 2050799) B2050799
theorem B6921935 : Blo 1366502 6921935 := bstep (se 1 (by rfl) ⟨5191451, by rfl⟩ : syracuseStep 6921935 = 10382903) B10382903
theorem B4613543 : Blo 1366502 4613543 := bstep (se 1 (by rfl) ⟨3460157, by rfl⟩ : syracuseStep 4613543 = 6920315) B6920315
theorem B4614623 : Blo 1366502 4614623 := bstep (se 1 (by rfl) ⟨3460967, by rfl⟩ : syracuseStep 4614623 = 6921935) B6921935
theorem B84159587 : Blo 1366502 84159587 := bstep (se 1 (by rfl) ⟨63119690, by rfl⟩ : syracuseStep 84159587 = 126239381) B126239381
theorem B4616351 : Blo 1366502 4616351 := bstep (se 1 (by rfl) ⟨3462263, by rfl⟩ : syracuseStep 4616351 = 6924527) B6924527
theorem B3078521 : Blo 1366502 3078521 := bstep (se 2 (by rfl) ⟨1154445, by rfl⟩ : syracuseStep 3078521 = 2308891) B2308891
theorem B1539175 : Blo 1366502 1539175 := bstep (se 1 (by rfl) ⟨1154381, by rfl⟩ : syracuseStep 1539175 = 2308763) B2308763
theorem B1367707 : Blo 1366502 1367707 := bstep (se 1 (by rfl) ⟨1025780, by rfl⟩ : syracuseStep 1367707 = 2051561) B2051561
theorem B3075695 : Blo 1366502 3075695 := bstep (se 1 (by rfl) ⟨2306771, by rfl⟩ : syracuseStep 3075695 = 4613543) B4613543
theorem B2052233 : Blo 1366502 2052233 := bstep (se 2 (by rfl) ⟨769587, by rfl⟩ : syracuseStep 2052233 = 1539175) B1539175
theorem B2052347 : Blo 1366502 2052347 := bstep (se 1 (by rfl) ⟨1539260, by rfl⟩ : syracuseStep 2052347 = 3078521) B3078521
theorem B3076415 : Blo 1366502 3076415 := bstep (se 1 (by rfl) ⟨2307311, by rfl⟩ : syracuseStep 3076415 = 4614623) B4614623
theorem B3077567 : Blo 1366502 3077567 := bstep (se 1 (by rfl) ⟨2308175, by rfl⟩ : syracuseStep 3077567 = 4616351) B4616351
theorem B56106391 : Blo 1366502 56106391 := bstep (se 1 (by rfl) ⟨42079793, by rfl⟩ : syracuseStep 56106391 = 84159587) B84159587
theorem B1368155 : Blo 1366502 1368155 := bstep (se 1 (by rfl) ⟨1026116, by rfl⟩ : syracuseStep 1368155 = 2052233) B2052233
theorem B1368231 : Blo 1366502 1368231 := bstep (se 1 (by rfl) ⟨1026173, by rfl⟩ : syracuseStep 1368231 = 2052347) B2052347
theorem B2050463 : Blo 1366502 2050463 := bstep (se 1 (by rfl) ⟨1537847, by rfl⟩ : syracuseStep 2050463 = 3075695) B3075695
theorem B2050943 : Blo 1366502 2050943 := bstep (se 1 (by rfl) ⟨1538207, by rfl⟩ : syracuseStep 2050943 = 3076415) B3076415
theorem B2051711 : Blo 1366502 2051711 := bstep (se 1 (by rfl) ⟨1538783, by rfl⟩ : syracuseStep 2051711 = 3077567) B3077567
theorem B74808521 : Blo 1366502 74808521 := bstep (se 2 (by rfl) ⟨28053195, by rfl⟩ : syracuseStep 74808521 = 56106391) B56106391
theorem B1366975 : Blo 1366502 1366975 := bstep (se 1 (by rfl) ⟨1025231, by rfl⟩ : syracuseStep 1366975 = 2050463) B2050463
theorem B1367295 : Blo 1366502 1367295 := bstep (se 1 (by rfl) ⟨1025471, by rfl⟩ : syracuseStep 1367295 = 2050943) B2050943
theorem B49872347 : Blo 1366502 49872347 := bstep (se 1 (by rfl) ⟨37404260, by rfl⟩ : syracuseStep 49872347 = 74808521) B74808521
theorem B1367807 : Blo 1366502 1367807 := bstep (se 1 (by rfl) ⟨1025855, by rfl⟩ : syracuseStep 1367807 = 2051711) B2051711
theorem B33248231 : Blo 1366502 33248231 := bstep (se 1 (by rfl) ⟨24936173, by rfl⟩ : syracuseStep 33248231 = 49872347) B49872347
theorem B22165487 : Blo 1366502 22165487 := bstep (se 1 (by rfl) ⟨16624115, by rfl⟩ : syracuseStep 22165487 = 33248231) B33248231
theorem B14776991 : Blo 1366502 14776991 := bstep (se 1 (by rfl) ⟨11082743, by rfl⟩ : syracuseStep 14776991 = 22165487) B22165487
theorem B9851327 : Blo 1366502 9851327 := bstep (se 1 (by rfl) ⟨7388495, by rfl⟩ : syracuseStep 9851327 = 14776991) B14776991
theorem B6567551 : Blo 1366502 6567551 := bstep (se 1 (by rfl) ⟨4925663, by rfl⟩ : syracuseStep 6567551 = 9851327) B9851327
theorem B4378367 : Blo 1366502 4378367 := bstep (se 1 (by rfl) ⟨3283775, by rfl⟩ : syracuseStep 4378367 = 6567551) B6567551
theorem B2918911 : Blo 1366502 2918911 := bstep (se 1 (by rfl) ⟨2189183, by rfl⟩ : syracuseStep 2918911 = 4378367) B4378367
theorem B3891881 : Blo 1366502 3891881 := bstep (se 2 (by rfl) ⟨1459455, by rfl⟩ : syracuseStep 3891881 = 2918911) B2918911
theorem B2594587 : Blo 1366502 2594587 := bstep (se 1 (by rfl) ⟨1945940, by rfl⟩ : syracuseStep 2594587 = 3891881) B3891881
theorem B3459449 : Blo 1366502 3459449 := bstep (se 2 (by rfl) ⟨1297293, by rfl⟩ : syracuseStep 3459449 = 2594587) B2594587
theorem B2306299 : Blo 1366502 2306299 := bstep (se 1 (by rfl) ⟨1729724, by rfl⟩ : syracuseStep 2306299 = 3459449) B3459449
theorem B3075065 : Blo 1366502 3075065 := bstep (se 2 (by rfl) ⟨1153149, by rfl⟩ : syracuseStep 3075065 = 2306299) B2306299
theorem B2050043 : Blo 1366502 2050043 := bstep (se 1 (by rfl) ⟨1537532, by rfl⟩ : syracuseStep 2050043 = 3075065) B3075065
theorem B1366695 : Blo 1366502 1366695 := bstep (se 1 (by rfl) ⟨1025021, by rfl⟩ : syracuseStep 1366695 = 2050043) B2050043

theorem C0 (j : ℕ) (h1 : 341625 ≤ j) (h2 : j ≤ 342124) : Blo 1366502 (4 * j + 3) := by
  interval_cases j
  · exact B1366503
  · exact B1366507
  · exact B1366511
  · exact B1366515
  · exact B1366519
  · exact B1366523
  · exact B1366527
  · exact B1366531
  · exact B1366535
  · exact B1366539
  · exact B1366543
  · exact B1366547
  · exact B1366551
  · exact B1366555
  · exact B1366559
  · exact B1366563
  · exact B1366567
  · exact B1366571
  · exact B1366575
  · exact B1366579
  · exact B1366583
  · exact B1366587
  · exact B1366591
  · exact B1366595
  · exact B1366599
  · exact B1366603
  · exact B1366607
  · exact B1366611
  · exact B1366615
  · exact B1366619
  · exact B1366623
  · exact B1366627
  · exact B1366631
  · exact B1366635
  · exact B1366639
  · exact B1366643
  · exact B1366647
  · exact B1366651
  · exact B1366655
  · exact B1366659
  · exact B1366663
  · exact B1366667
  · exact B1366671
  · exact B1366675
  · exact B1366679
  · exact B1366683
  · exact B1366687
  · exact B1366691
  · exact B1366695
  · exact B1366699
  · exact B1366703
  · exact B1366707
  · exact B1366711
  · exact B1366715
  · exact B1366719
  · exact B1366723
  · exact B1366727
  · exact B1366731
  · exact B1366735
  · exact B1366739
  · exact B1366743
  · exact B1366747
  · exact B1366751
  · exact B1366755
  · exact B1366759
  · exact B1366763
  · exact B1366767
  · exact B1366771
  · exact B1366775
  · exact B1366779
  · exact B1366783
  · exact B1366787
  · exact B1366791
  · exact B1366795
  · exact B1366799
  · exact B1366803
  · exact B1366807
  · exact B1366811
  · exact B1366815
  · exact B1366819
  · exact B1366823
  · exact B1366827
  · exact B1366831
  · exact B1366835
  · exact B1366839
  · exact B1366843
  · exact B1366847
  · exact B1366851
  · exact B1366855
  · exact B1366859
  · exact B1366863
  · exact B1366867
  · exact B1366871
  · exact B1366875
  · exact B1366879
  · exact B1366883
  · exact B1366887
  · exact B1366891
  · exact B1366895
  · exact B1366899
  · exact B1366903
  · exact B1366907
  · exact B1366911
  · exact B1366915
  · exact B1366919
  · exact B1366923
  · exact B1366927
  · exact B1366931
  · exact B1366935
  · exact B1366939
  · exact B1366943
  · exact B1366947
  · exact B1366951
  · exact B1366955
  · exact B1366959
  · exact B1366963
  · exact B1366967
  · exact B1366971
  · exact B1366975
  · exact B1366979
  · exact B1366983
  · exact B1366987
  · exact B1366991
  · exact B1366995
  · exact B1366999
  · exact B1367003
  · exact B1367007
  · exact B1367011
  · exact B1367015
  · exact B1367019
  · exact B1367023
  · exact B1367027
  · exact B1367031
  · exact B1367035
  · exact B1367039
  · exact B1367043
  · exact B1367047
  · exact B1367051
  · exact B1367055
  · exact B1367059
  · exact B1367063
  · exact B1367067
  · exact B1367071
  · exact B1367075
  · exact B1367079
  · exact B1367083
  · exact B1367087
  · exact B1367091
  · exact B1367095
  · exact B1367099
  · exact B1367103
  · exact B1367107
  · exact B1367111
  · exact B1367115
  · exact B1367119
  · exact B1367123
  · exact B1367127
  · exact B1367131
  · exact B1367135
  · exact B1367139
  · exact B1367143
  · exact B1367147
  · exact B1367151
  · exact B1367155
  · exact B1367159
  · exact B1367163
  · exact B1367167
  · exact B1367171
  · exact B1367175
  · exact B1367179
  · exact B1367183
  · exact B1367187
  · exact B1367191
  · exact B1367195
  · exact B1367199
  · exact B1367203
  · exact B1367207
  · exact B1367211
  · exact B1367215
  · exact B1367219
  · exact B1367223
  · exact B1367227
  · exact B1367231
  · exact B1367235
  · exact B1367239
  · exact B1367243
  · exact B1367247
  · exact B1367251
  · exact B1367255
  · exact B1367259
  · exact B1367263
  · exact B1367267
  · exact B1367271
  · exact B1367275
  · exact B1367279
  · exact B1367283
  · exact B1367287
  · exact B1367291
  · exact B1367295
  · exact B1367299
  · exact B1367303
  · exact B1367307
  · exact B1367311
  · exact B1367315
  · exact B1367319
  · exact B1367323
  · exact B1367327
  · exact B1367331
  · exact B1367335
  · exact B1367339
  · exact B1367343
  · exact B1367347
  · exact B1367351
  · exact B1367355
  · exact B1367359
  · exact B1367363
  · exact B1367367
  · exact B1367371
  · exact B1367375
  · exact B1367379
  · exact B1367383
  · exact B1367387
  · exact B1367391
  · exact B1367395
  · exact B1367399
  · exact B1367403
  · exact B1367407
  · exact B1367411
  · exact B1367415
  · exact B1367419
  · exact B1367423
  · exact B1367427
  · exact B1367431
  · exact B1367435
  · exact B1367439
  · exact B1367443
  · exact B1367447
  · exact B1367451
  · exact B1367455
  · exact B1367459
  · exact B1367463
  · exact B1367467
  · exact B1367471
  · exact B1367475
  · exact B1367479
  · exact B1367483
  · exact B1367487
  · exact B1367491
  · exact B1367495
  · exact B1367499
  · exact B1367503
  · exact B1367507
  · exact B1367511
  · exact B1367515
  · exact B1367519
  · exact B1367523
  · exact B1367527
  · exact B1367531
  · exact B1367535
  · exact B1367539
  · exact B1367543
  · exact B1367547
  · exact B1367551
  · exact B1367555
  · exact B1367559
  · exact B1367563
  · exact B1367567
  · exact B1367571
  · exact B1367575
  · exact B1367579
  · exact B1367583
  · exact B1367587
  · exact B1367591
  · exact B1367595
  · exact B1367599
  · exact B1367603
  · exact B1367607
  · exact B1367611
  · exact B1367615
  · exact B1367619
  · exact B1367623
  · exact B1367627
  · exact B1367631
  · exact B1367635
  · exact B1367639
  · exact B1367643
  · exact B1367647
  · exact B1367651
  · exact B1367655
  · exact B1367659
  · exact B1367663
  · exact B1367667
  · exact B1367671
  · exact B1367675
  · exact B1367679
  · exact B1367683
  · exact B1367687
  · exact B1367691
  · exact B1367695
  · exact B1367699
  · exact B1367703
  · exact B1367707
  · exact B1367711
  · exact B1367715
  · exact B1367719
  · exact B1367723
  · exact B1367727
  · exact B1367731
  · exact B1367735
  · exact B1367739
  · exact B1367743
  · exact B1367747
  · exact B1367751
  · exact B1367755
  · exact B1367759
  · exact B1367763
  · exact B1367767
  · exact B1367771
  · exact B1367775
  · exact B1367779
  · exact B1367783
  · exact B1367787
  · exact B1367791
  · exact B1367795
  · exact B1367799
  · exact B1367803
  · exact B1367807
  · exact B1367811
  · exact B1367815
  · exact B1367819
  · exact B1367823
  · exact B1367827
  · exact B1367831
  · exact B1367835
  · exact B1367839
  · exact B1367843
  · exact B1367847
  · exact B1367851
  · exact B1367855
  · exact B1367859
  · exact B1367863
  · exact B1367867
  · exact B1367871
  · exact B1367875
  · exact B1367879
  · exact B1367883
  · exact B1367887
  · exact B1367891
  · exact B1367895
  · exact B1367899
  · exact B1367903
  · exact B1367907
  · exact B1367911
  · exact B1367915
  · exact B1367919
  · exact B1367923
  · exact B1367927
  · exact B1367931
  · exact B1367935
  · exact B1367939
  · exact B1367943
  · exact B1367947
  · exact B1367951
  · exact B1367955
  · exact B1367959
  · exact B1367963
  · exact B1367967
  · exact B1367971
  · exact B1367975
  · exact B1367979
  · exact B1367983
  · exact B1367987
  · exact B1367991
  · exact B1367995
  · exact B1367999
  · exact B1368003
  · exact B1368007
  · exact B1368011
  · exact B1368015
  · exact B1368019
  · exact B1368023
  · exact B1368027
  · exact B1368031
  · exact B1368035
  · exact B1368039
  · exact B1368043
  · exact B1368047
  · exact B1368051
  · exact B1368055
  · exact B1368059
  · exact B1368063
  · exact B1368067
  · exact B1368071
  · exact B1368075
  · exact B1368079
  · exact B1368083
  · exact B1368087
  · exact B1368091
  · exact B1368095
  · exact B1368099
  · exact B1368103
  · exact B1368107
  · exact B1368111
  · exact B1368115
  · exact B1368119
  · exact B1368123
  · exact B1368127
  · exact B1368131
  · exact B1368135
  · exact B1368139
  · exact B1368143
  · exact B1368147
  · exact B1368151
  · exact B1368155
  · exact B1368159
  · exact B1368163
  · exact B1368167
  · exact B1368171
  · exact B1368175
  · exact B1368179
  · exact B1368183
  · exact B1368187
  · exact B1368191
  · exact B1368195
  · exact B1368199
  · exact B1368203
  · exact B1368207
  · exact B1368211
  · exact B1368215
  · exact B1368219
  · exact B1368223
  · exact B1368227
  · exact B1368231
  · exact B1368235
  · exact B1368239
  · exact B1368243
  · exact B1368247
  · exact B1368251
  · exact B1368255
  · exact B1368259
  · exact B1368263
  · exact B1368267
  · exact B1368271
  · exact B1368275
  · exact B1368279
  · exact B1368283
  · exact B1368287
  · exact B1368291
  · exact B1368295
  · exact B1368299
  · exact B1368303
  · exact B1368307
  · exact B1368311
  · exact B1368315
  · exact B1368319
  · exact B1368323
  · exact B1368327
  · exact B1368331
  · exact B1368335
  · exact B1368339
  · exact B1368343
  · exact B1368347
  · exact B1368351
  · exact B1368355
  · exact B1368359
  · exact B1368363
  · exact B1368367
  · exact B1368371
  · exact B1368375
  · exact B1368379
  · exact B1368383
  · exact B1368387
  · exact B1368391
  · exact B1368395
  · exact B1368399
  · exact B1368403
  · exact B1368407
  · exact B1368411
  · exact B1368415
  · exact B1368419
  · exact B1368423
  · exact B1368427
  · exact B1368431
  · exact B1368435
  · exact B1368439
  · exact B1368443
  · exact B1368447
  · exact B1368451
  · exact B1368455
  · exact B1368459
  · exact B1368463
  · exact B1368467
  · exact B1368471
  · exact B1368475
  · exact B1368479
  · exact B1368483
  · exact B1368487
  · exact B1368491
  · exact B1368495
  · exact B1368499

theorem solution (m : ℕ) (hlo : 1366502 ≤ m) (hhi : m ≤ 1368502) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 341625 ≤ j := by omega
    have hj2 : j ≤ 342124 := by omega
    have hb : Blo 1366502 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
