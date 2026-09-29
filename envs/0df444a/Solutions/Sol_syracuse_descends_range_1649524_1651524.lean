-- Prove2me | solution 1 for syracuse_descends_range_1649524_1651524
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:17:33.324417+00:00
-- url     : https://prove2.me/submissions/fae1f8af-f683-4a8b-8124-8bc8d84ff365

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


theorem B2088985 : Blo 1649524 2088985 := bbase (se 2 (by rfl) ⟨783369, by rfl⟩ : syracuseStep 2088985 = 1566739) (by norm_num)
theorem B5947445 : Blo 1649524 5947445 := bbase (se 5 (by rfl) ⟨278786, by rfl⟩ : syracuseStep 5947445 = 557573) (by norm_num)
theorem B2785333 : Blo 1649524 2785333 := bbase (se 5 (by rfl) ⟨130562, by rfl⟩ : syracuseStep 2785333 = 261125) (by norm_num)
theorem B30097493 : Blo 1649524 30097493 := bbase (se 8 (by rfl) ⟨176352, by rfl⟩ : syracuseStep 30097493 = 352705) (by norm_num)
theorem B2678885 : Blo 1649524 2678885 := bbase (se 4 (by rfl) ⟨251145, by rfl⟩ : syracuseStep 2678885 = 502291) (by norm_num)
theorem B2089081 : Blo 1649524 2089081 := bbase (se 2 (by rfl) ⟨783405, by rfl⟩ : syracuseStep 2089081 = 1566811) (by norm_num)
theorem B5570693 : Blo 1649524 5570693 := bbase (se 4 (by rfl) ⟨522252, by rfl⟩ : syracuseStep 5570693 = 1044505) (by norm_num)
theorem B2785421 : Blo 1649524 2785421 := bbase (se 3 (by rfl) ⟨522266, by rfl⟩ : syracuseStep 2785421 = 1044533) (by norm_num)
theorem B7930021 : Blo 1649524 7930021 := bbase (se 4 (by rfl) ⟨743439, by rfl⟩ : syracuseStep 7930021 = 1486879) (by norm_num)
theorem B4178101 : Blo 1649524 4178101 := bbase (se 5 (by rfl) ⟨195848, by rfl⟩ : syracuseStep 4178101 = 391697) (by norm_num)
theorem B6267077 : Blo 1649524 6267077 := bbase (se 4 (by rfl) ⟨587538, by rfl⟩ : syracuseStep 6267077 = 1175077) (by norm_num)
theorem B6029525 : Blo 1649524 6029525 := bbase (se 7 (by rfl) ⟨70658, by rfl⟩ : syracuseStep 6029525 = 141317) (by norm_num)
theorem B3965165 : Blo 1649524 3965165 := bbase (se 3 (by rfl) ⟨743468, by rfl⟩ : syracuseStep 3965165 = 1486937) (by norm_num)
theorem B3391741 : Blo 1649524 3391741 := bbase (se 3 (by rfl) ⟨635951, by rfl⟩ : syracuseStep 3391741 = 1271903) (by norm_num)
theorem B2785549 : Blo 1649524 2785549 := bbase (se 3 (by rfl) ⟨522290, by rfl⟩ : syracuseStep 2785549 = 1044581) (by norm_num)
theorem B9404693 : Blo 1649524 9404693 := bbase (se 6 (by rfl) ⟨220422, by rfl⟩ : syracuseStep 9404693 = 440845) (by norm_num)
theorem B4178213 : Blo 1649524 4178213 := bbase (se 4 (by rfl) ⟨391707, by rfl⟩ : syracuseStep 4178213 = 783415) (by norm_num)
theorem B1696037 : Blo 1649524 1696037 := bbase (se 4 (by rfl) ⟨159003, by rfl⟩ : syracuseStep 1696037 = 318007) (by norm_num)
theorem B2089253 : Blo 1649524 2089253 := bbase (se 4 (by rfl) ⟨195867, by rfl⟩ : syracuseStep 2089253 = 391735) (by norm_num)
theorem B2474309 : Blo 1649524 2474309 := bbase (se 4 (by rfl) ⟨231966, by rfl⟩ : syracuseStep 2474309 = 463933) (by norm_num)
theorem B1810765 : Blo 1649524 1810765 := bbase (se 3 (by rfl) ⟨339518, by rfl⟩ : syracuseStep 1810765 = 679037) (by norm_num)
theorem B1761625 : Blo 1649524 1761625 := bbase (se 2 (by rfl) ⟨660609, by rfl⟩ : syracuseStep 1761625 = 1321219) (by norm_num)
theorem B2474333 : Blo 1649524 2474333 := bbase (se 3 (by rfl) ⟨463937, by rfl⟩ : syracuseStep 2474333 = 927875) (by norm_num)
theorem B2089309 : Blo 1649524 2089309 := bbase (se 3 (by rfl) ⟨391745, by rfl⟩ : syracuseStep 2089309 = 783491) (by norm_num)
theorem B2785637 : Blo 1649524 2785637 := bbase (se 4 (by rfl) ⟨261153, by rfl⟩ : syracuseStep 2785637 = 522307) (by norm_num)
theorem B2474357 : Blo 1649524 2474357 := bbase (se 5 (by rfl) ⟨115985, by rfl⟩ : syracuseStep 2474357 = 231971) (by norm_num)
theorem B2474381 : Blo 1649524 2474381 := bbase (se 3 (by rfl) ⟨463946, by rfl⟩ : syracuseStep 2474381 = 927893) (by norm_num)
theorem B1761697 : Blo 1649524 1761697 := bbase (se 2 (by rfl) ⟨660636, by rfl⟩ : syracuseStep 1761697 = 1321273) (by norm_num)
theorem B2474405 : Blo 1649524 2474405 := bbase (se 4 (by rfl) ⟨231975, by rfl⟩ : syracuseStep 2474405 = 463951) (by norm_num)
theorem B2474429 : Blo 1649524 2474429 := bbase (se 3 (by rfl) ⟨463955, by rfl⟩ : syracuseStep 2474429 = 927911) (by norm_num)
theorem B2089405 : Blo 1649524 2089405 := bbase (se 3 (by rfl) ⟨391763, by rfl⟩ : syracuseStep 2089405 = 783527) (by norm_num)
theorem B3711437 : Blo 1649524 3711437 := bbase (se 3 (by rfl) ⟨695894, by rfl⟩ : syracuseStep 3711437 = 1391789) (by norm_num)
theorem B2474453 : Blo 1649524 2474453 := bbase (se 7 (by rfl) ⟨28997, by rfl⟩ : syracuseStep 2474453 = 57995) (by norm_num)
theorem B6267365 : Blo 1649524 6267365 := bbase (se 4 (by rfl) ⟨587565, by rfl⟩ : syracuseStep 6267365 = 1175131) (by norm_num)
theorem B4178405 : Blo 1649524 4178405 := bbase (se 4 (by rfl) ⟨391725, by rfl⟩ : syracuseStep 4178405 = 783451) (by norm_num)
theorem B2785765 : Blo 1649524 2785765 := bbase (se 4 (by rfl) ⟨261165, by rfl⟩ : syracuseStep 2785765 = 522331) (by norm_num)
theorem B2474477 : Blo 1649524 2474477 := bbase (se 3 (by rfl) ⟨463964, by rfl⟩ : syracuseStep 2474477 = 927929) (by norm_num)
theorem B2474501 : Blo 1649524 2474501 := bbase (se 4 (by rfl) ⟨231984, by rfl⟩ : syracuseStep 2474501 = 463969) (by norm_num)
theorem B3965453 : Blo 1649524 3965453 := bbase (se 3 (by rfl) ⟨743522, by rfl⟩ : syracuseStep 3965453 = 1487045) (by norm_num)
theorem B3711509 : Blo 1649524 3711509 := bbase (se 6 (by rfl) ⟨86988, by rfl⟩ : syracuseStep 3711509 = 173977) (by norm_num)
theorem B2474525 : Blo 1649524 2474525 := bbase (se 3 (by rfl) ⟨463973, by rfl⟩ : syracuseStep 2474525 = 927947) (by norm_num)
theorem B2474549 : Blo 1649524 2474549 := bbase (se 5 (by rfl) ⟨115994, by rfl⟩ : syracuseStep 2474549 = 231989) (by norm_num)
theorem B5571125 : Blo 1649524 5571125 := bbase (se 5 (by rfl) ⟨261146, by rfl⟩ : syracuseStep 5571125 = 522293) (by norm_num)
theorem B2785853 : Blo 1649524 2785853 := bbase (se 3 (by rfl) ⟨522347, by rfl⟩ : syracuseStep 2785853 = 1044695) (by norm_num)
theorem B1933897 : Blo 1649524 1933897 := bbase (se 2 (by rfl) ⟨725211, by rfl⟩ : syracuseStep 1933897 = 1450423) (by norm_num)
theorem B2474573 : Blo 1649524 2474573 := bbase (se 3 (by rfl) ⟨463982, by rfl⟩ : syracuseStep 2474573 = 927965) (by norm_num)
theorem B3711581 : Blo 1649524 3711581 := bbase (se 3 (by rfl) ⟨695921, by rfl⟩ : syracuseStep 3711581 = 1391843) (by norm_num)
theorem B2474597 : Blo 1649524 2474597 := bbase (se 4 (by rfl) ⟨231993, by rfl⟩ : syracuseStep 2474597 = 463987) (by norm_num)
theorem B2089577 : Blo 1649524 2089577 := bbase (se 2 (by rfl) ⟨783591, by rfl⟩ : syracuseStep 2089577 = 1567183) (by norm_num)
theorem B3523189 : Blo 1649524 3523189 := bbase (se 5 (by rfl) ⟨165149, by rfl⟩ : syracuseStep 3523189 = 330299) (by norm_num)
theorem B2474621 : Blo 1649524 2474621 := bbase (se 3 (by rfl) ⟨463991, by rfl⟩ : syracuseStep 2474621 = 927983) (by norm_num)
theorem B1983101 : Blo 1649524 1983101 := bbase (se 3 (by rfl) ⟨371831, by rfl⟩ : syracuseStep 1983101 = 743663) (by norm_num)
theorem B2474645 : Blo 1649524 2474645 := bbase (se 6 (by rfl) ⟨57999, by rfl⟩ : syracuseStep 2474645 = 115999) (by norm_num)
theorem B2089633 : Blo 1649524 2089633 := bbase (se 2 (by rfl) ⟨783612, by rfl⟩ : syracuseStep 2089633 = 1567225) (by norm_num)
theorem B3711653 : Blo 1649524 3711653 := bbase (se 4 (by rfl) ⟨347967, by rfl⟩ : syracuseStep 3711653 = 695935) (by norm_num)
theorem B2474669 : Blo 1649524 2474669 := bbase (se 3 (by rfl) ⟨464000, by rfl⟩ : syracuseStep 2474669 = 928001) (by norm_num)
theorem B2785981 : Blo 1649524 2785981 := bbase (se 3 (by rfl) ⟨522371, by rfl⟩ : syracuseStep 2785981 = 1044743) (by norm_num)
theorem B2474693 : Blo 1649524 2474693 := bbase (se 4 (by rfl) ⟨232002, by rfl⟩ : syracuseStep 2474693 = 464005) (by norm_num)
theorem B2974421 : Blo 1649524 2974421 := bbase (se 7 (by rfl) ⟨34856, by rfl⟩ : syracuseStep 2974421 = 69713) (by norm_num)
theorem B2474717 : Blo 1649524 2474717 := bbase (se 3 (by rfl) ⟨464009, by rfl⟩ : syracuseStep 2474717 = 928019) (by norm_num)
theorem B3711725 : Blo 1649524 3711725 := bbase (se 3 (by rfl) ⟨695948, by rfl⟩ : syracuseStep 3711725 = 1391897) (by norm_num)
theorem B2474741 : Blo 1649524 2474741 := bbase (se 5 (by rfl) ⟨116003, by rfl⟩ : syracuseStep 2474741 = 232007) (by norm_num)
theorem B2089729 : Blo 1649524 2089729 := bbase (se 2 (by rfl) ⟨783648, by rfl⟩ : syracuseStep 2089729 = 1567297) (by norm_num)
theorem B2474765 : Blo 1649524 2474765 := bbase (se 3 (by rfl) ⟨464018, by rfl⟩ : syracuseStep 2474765 = 928037) (by norm_num)
theorem B7144213 : Blo 1649524 7144213 := bbase (se 6 (by rfl) ⟨167442, by rfl⟩ : syracuseStep 7144213 = 334885) (by norm_num)
theorem B1762069 : Blo 1649524 1762069 := bbase (se 6 (by rfl) ⟨41298, by rfl⟩ : syracuseStep 1762069 = 82597) (by norm_num)
theorem B2786069 : Blo 1649524 2786069 := bbase (se 6 (by rfl) ⟨65298, by rfl⟩ : syracuseStep 2786069 = 130597) (by norm_num)
theorem B2474789 : Blo 1649524 2474789 := bbase (se 4 (by rfl) ⟨232011, by rfl⟩ : syracuseStep 2474789 = 464023) (by norm_num)
theorem B3711797 : Blo 1649524 3711797 := bbase (se 5 (by rfl) ⟨173990, by rfl⟩ : syracuseStep 3711797 = 347981) (by norm_num)
theorem B2474813 : Blo 1649524 2474813 := bbase (se 3 (by rfl) ⟨464027, by rfl⟩ : syracuseStep 2474813 = 928055) (by norm_num)
theorem B4178749 : Blo 1649524 4178749 := bbase (se 3 (by rfl) ⟨783515, by rfl⟩ : syracuseStep 4178749 = 1567031) (by norm_num)
theorem B1983313 : Blo 1649524 1983313 := bbase (se 2 (by rfl) ⟨743742, by rfl⟩ : syracuseStep 1983313 = 1487485) (by norm_num)
theorem B2474837 : Blo 1649524 2474837 := bbase (se 9 (by rfl) ⟨7250, by rfl⟩ : syracuseStep 2474837 = 14501) (by norm_num)
theorem B2474861 : Blo 1649524 2474861 := bbase (se 3 (by rfl) ⟨464036, by rfl⟩ : syracuseStep 2474861 = 928073) (by norm_num)
theorem B3711869 : Blo 1649524 3711869 := bbase (se 3 (by rfl) ⟨695975, by rfl⟩ : syracuseStep 3711869 = 1391951) (by norm_num)
theorem B2474885 : Blo 1649524 2474885 := bbase (se 4 (by rfl) ⟨232020, by rfl⟩ : syracuseStep 2474885 = 464041) (by norm_num)
theorem B2786197 : Blo 1649524 2786197 := bbase (se 6 (by rfl) ⟨65301, by rfl⟩ : syracuseStep 2786197 = 130603) (by norm_num)
theorem B2474909 : Blo 1649524 2474909 := bbase (se 3 (by rfl) ⟨464045, by rfl⟩ : syracuseStep 2474909 = 928091) (by norm_num)
theorem B4178861 : Blo 1649524 4178861 := bbase (se 3 (by rfl) ⟨783536, by rfl⟩ : syracuseStep 4178861 = 1567073) (by norm_num)
theorem B2089901 : Blo 1649524 2089901 := bbase (se 3 (by rfl) ⟨391856, by rfl⟩ : syracuseStep 2089901 = 783713) (by norm_num)
theorem B2474933 : Blo 1649524 2474933 := bbase (se 5 (by rfl) ⟨116012, by rfl⟩ : syracuseStep 2474933 = 232025) (by norm_num)
theorem B2974645 : Blo 1649524 2974645 := bbase (se 5 (by rfl) ⟨139436, by rfl⟩ : syracuseStep 2974645 = 278873) (by norm_num)
theorem B3711941 : Blo 1649524 3711941 := bbase (se 4 (by rfl) ⟨347994, by rfl⟩ : syracuseStep 3711941 = 695989) (by norm_num)
theorem B2474957 : Blo 1649524 2474957 := bbase (se 3 (by rfl) ⟨464054, by rfl⟩ : syracuseStep 2474957 = 928109) (by norm_num)
theorem B1983457 : Blo 1649524 1983457 := bbase (se 2 (by rfl) ⟨743796, by rfl⟩ : syracuseStep 1983457 = 1487593) (by norm_num)
theorem B2474981 : Blo 1649524 2474981 := bbase (se 4 (by rfl) ⟨232029, by rfl⟩ : syracuseStep 2474981 = 464059) (by norm_num)
theorem B5571557 : Blo 1649524 5571557 := bbase (se 4 (by rfl) ⟨522333, by rfl⟩ : syracuseStep 5571557 = 1044667) (by norm_num)
theorem B2089957 : Blo 1649524 2089957 := bbase (se 4 (by rfl) ⟨195933, by rfl⟩ : syracuseStep 2089957 = 391867) (by norm_num)
theorem B2786285 : Blo 1649524 2786285 := bbase (se 3 (by rfl) ⟨522428, by rfl⟩ : syracuseStep 2786285 = 1044857) (by norm_num)
theorem B2475005 : Blo 1649524 2475005 := bbase (se 3 (by rfl) ⟨464063, by rfl⟩ : syracuseStep 2475005 = 928127) (by norm_num)
theorem B3712013 : Blo 1649524 3712013 := bbase (se 3 (by rfl) ⟨696002, by rfl⟩ : syracuseStep 3712013 = 1392005) (by norm_num)
theorem B2475029 : Blo 1649524 2475029 := bbase (se 6 (by rfl) ⟨58008, by rfl⟩ : syracuseStep 2475029 = 116017) (by norm_num)
theorem B2475053 : Blo 1649524 2475053 := bbase (se 3 (by rfl) ⟨464072, by rfl⟩ : syracuseStep 2475053 = 928145) (by norm_num)
theorem B2475077 : Blo 1649524 2475077 := bbase (se 4 (by rfl) ⟨232038, by rfl⟩ : syracuseStep 2475077 = 464077) (by norm_num)
theorem B2090053 : Blo 1649524 2090053 := bbase (se 4 (by rfl) ⟨195942, by rfl⟩ : syracuseStep 2090053 = 391885) (by norm_num)
theorem B3712085 : Blo 1649524 3712085 := bbase (se 8 (by rfl) ⟨21750, by rfl⟩ : syracuseStep 3712085 = 43501) (by norm_num)
theorem B2475101 : Blo 1649524 2475101 := bbase (se 3 (by rfl) ⟨464081, by rfl⟩ : syracuseStep 2475101 = 928163) (by norm_num)
theorem B4179053 : Blo 1649524 4179053 := bbase (se 3 (by rfl) ⟨783572, by rfl⟩ : syracuseStep 4179053 = 1567145) (by norm_num)
theorem B2786413 : Blo 1649524 2786413 := bbase (se 3 (by rfl) ⟨522452, by rfl⟩ : syracuseStep 2786413 = 1044905) (by norm_num)
theorem B2475125 : Blo 1649524 2475125 := bbase (se 5 (by rfl) ⟨116021, by rfl⟩ : syracuseStep 2475125 = 232043) (by norm_num)
theorem B2475149 : Blo 1649524 2475149 := bbase (se 3 (by rfl) ⟨464090, by rfl⟩ : syracuseStep 2475149 = 928181) (by norm_num)
theorem B1762445 : Blo 1649524 1762445 := bbase (se 3 (by rfl) ⟨330458, by rfl⟩ : syracuseStep 1762445 = 660917) (by norm_num)
theorem B3712157 : Blo 1649524 3712157 := bbase (se 3 (by rfl) ⟨696029, by rfl⟩ : syracuseStep 3712157 = 1392059) (by norm_num)
theorem B2475173 : Blo 1649524 2475173 := bbase (se 4 (by rfl) ⟨232047, by rfl⟩ : syracuseStep 2475173 = 464095) (by norm_num)
theorem B2475197 : Blo 1649524 2475197 := bbase (se 3 (by rfl) ⟨464099, by rfl⟩ : syracuseStep 2475197 = 928199) (by norm_num)
theorem B2786501 : Blo 1649524 2786501 := bbase (se 4 (by rfl) ⟨261234, by rfl⟩ : syracuseStep 2786501 = 522469) (by norm_num)
theorem B2475221 : Blo 1649524 2475221 := bbase (se 7 (by rfl) ⟨29006, by rfl⟩ : syracuseStep 2475221 = 58013) (by norm_num)
theorem B1762517 : Blo 1649524 1762517 := bbase (se 7 (by rfl) ⟨20654, by rfl⟩ : syracuseStep 1762517 = 41309) (by norm_num)
theorem B3712229 : Blo 1649524 3712229 := bbase (se 4 (by rfl) ⟨348021, by rfl⟩ : syracuseStep 3712229 = 696043) (by norm_num)
theorem B8357093 : Blo 1649524 8357093 := bbase (se 4 (by rfl) ⟨783477, by rfl⟩ : syracuseStep 8357093 = 1566955) (by norm_num)
theorem B2475245 : Blo 1649524 2475245 := bbase (se 3 (by rfl) ⟨464108, by rfl⟩ : syracuseStep 2475245 = 928217) (by norm_num)
theorem B2475269 : Blo 1649524 2475269 := bbase (se 4 (by rfl) ⟨232056, by rfl⟩ : syracuseStep 2475269 = 464113) (by norm_num)
theorem B2475293 : Blo 1649524 2475293 := bbase (se 3 (by rfl) ⟨464117, by rfl⟩ : syracuseStep 2475293 = 928235) (by norm_num)
theorem B3712301 : Blo 1649524 3712301 := bbase (se 3 (by rfl) ⟨696056, by rfl⟩ : syracuseStep 3712301 = 1392113) (by norm_num)
theorem B2475317 : Blo 1649524 2475317 := bbase (se 5 (by rfl) ⟨116030, by rfl⟩ : syracuseStep 2475317 = 232061) (by norm_num)
theorem B3015997 : Blo 1649524 3015997 := bbase (se 3 (by rfl) ⟨565499, by rfl⟩ : syracuseStep 3015997 = 1130999) (by norm_num)
theorem B2786629 : Blo 1649524 2786629 := bbase (se 4 (by rfl) ⟨261246, by rfl⟩ : syracuseStep 2786629 = 522493) (by norm_num)
theorem B2475341 : Blo 1649524 2475341 := bbase (se 3 (by rfl) ⟨464126, by rfl⟩ : syracuseStep 2475341 = 928253) (by norm_num)
theorem B2475365 : Blo 1649524 2475365 := bbase (se 4 (by rfl) ⟨232065, by rfl⟩ : syracuseStep 2475365 = 464131) (by norm_num)
theorem B3712373 : Blo 1649524 3712373 := bbase (se 5 (by rfl) ⟨174017, by rfl⟩ : syracuseStep 3712373 = 348035) (by norm_num)
theorem B2475389 : Blo 1649524 2475389 := bbase (se 3 (by rfl) ⟨464135, by rfl⟩ : syracuseStep 2475389 = 928271) (by norm_num)
theorem B1762705 : Blo 1649524 1762705 := bbase (se 2 (by rfl) ⟨661014, by rfl⟩ : syracuseStep 1762705 = 1322029) (by norm_num)
theorem B2475413 : Blo 1649524 2475413 := bbase (se 6 (by rfl) ⟨58017, by rfl⟩ : syracuseStep 2475413 = 116035) (by norm_num)
theorem B5571989 : Blo 1649524 5571989 := bbase (se 6 (by rfl) ⟨130593, by rfl⟩ : syracuseStep 5571989 = 261187) (by norm_num)
theorem B2786717 : Blo 1649524 2786717 := bbase (se 3 (by rfl) ⟨522509, by rfl⟩ : syracuseStep 2786717 = 1045019) (by norm_num)
theorem B2475437 : Blo 1649524 2475437 := bbase (se 3 (by rfl) ⟨464144, by rfl⟩ : syracuseStep 2475437 = 928289) (by norm_num)
theorem B2860469 : Blo 1649524 2860469 := bbase (se 5 (by rfl) ⟨134084, by rfl⟩ : syracuseStep 2860469 = 268169) (by norm_num)
theorem B3712445 : Blo 1649524 3712445 := bbase (se 3 (by rfl) ⟨696083, by rfl⟩ : syracuseStep 3712445 = 1392167) (by norm_num)
theorem B2475461 : Blo 1649524 2475461 := bbase (se 4 (by rfl) ⟨232074, by rfl⟩ : syracuseStep 2475461 = 464149) (by norm_num)
theorem B4179397 : Blo 1649524 4179397 := bbase (se 4 (by rfl) ⟨391818, by rfl⟩ : syracuseStep 4179397 = 783637) (by norm_num)
theorem B2475485 : Blo 1649524 2475485 := bbase (se 3 (by rfl) ⟨464153, by rfl⟩ : syracuseStep 2475485 = 928307) (by norm_num)
theorem B3524077 : Blo 1649524 3524077 := bbase (se 3 (by rfl) ⟨660764, by rfl⟩ : syracuseStep 3524077 = 1321529) (by norm_num)
theorem B2475509 : Blo 1649524 2475509 := bbase (se 5 (by rfl) ⟨116039, by rfl⟩ : syracuseStep 2475509 = 232079) (by norm_num)
theorem B3712517 : Blo 1649524 3712517 := bbase (se 4 (by rfl) ⟨348048, by rfl⟩ : syracuseStep 3712517 = 696097) (by norm_num)
theorem B2229773 : Blo 1649524 2229773 := bbase (se 3 (by rfl) ⟨418082, by rfl⟩ : syracuseStep 2229773 = 836165) (by norm_num)
theorem B2475533 : Blo 1649524 2475533 := bbase (se 3 (by rfl) ⟨464162, by rfl⟩ : syracuseStep 2475533 = 928325) (by norm_num)
theorem B2786845 : Blo 1649524 2786845 := bbase (se 3 (by rfl) ⟨522533, by rfl⟩ : syracuseStep 2786845 = 1045067) (by norm_num)
theorem B2475557 : Blo 1649524 2475557 := bbase (se 4 (by rfl) ⟨232083, by rfl⟩ : syracuseStep 2475557 = 464167) (by norm_num)
theorem B4179509 : Blo 1649524 4179509 := bbase (se 5 (by rfl) ⟨195914, by rfl⟩ : syracuseStep 4179509 = 391829) (by norm_num)
theorem B2475581 : Blo 1649524 2475581 := bbase (se 3 (by rfl) ⟨464171, by rfl⟩ : syracuseStep 2475581 = 928343) (by norm_num)
theorem B1762889 : Blo 1649524 1762889 := bbase (se 2 (by rfl) ⟨661083, by rfl⟩ : syracuseStep 1762889 = 1322167) (by norm_num)
theorem B3712589 : Blo 1649524 3712589 := bbase (se 3 (by rfl) ⟨696110, by rfl⟩ : syracuseStep 3712589 = 1392221) (by norm_num)
theorem B2475605 : Blo 1649524 2475605 := bbase (se 8 (by rfl) ⟨14505, by rfl⟩ : syracuseStep 2475605 = 29011) (by norm_num)
theorem B2475629 : Blo 1649524 2475629 := bbase (se 3 (by rfl) ⟨464180, by rfl⟩ : syracuseStep 2475629 = 928361) (by norm_num)
theorem B2786933 : Blo 1649524 2786933 := bbase (se 5 (by rfl) ⟨130637, by rfl⟩ : syracuseStep 2786933 = 261275) (by norm_num)
theorem B2475653 : Blo 1649524 2475653 := bbase (se 4 (by rfl) ⟨232092, by rfl⟩ : syracuseStep 2475653 = 464185) (by norm_num)
theorem B6268549 : Blo 1649524 6268549 := bbase (se 4 (by rfl) ⟨587676, by rfl⟩ : syracuseStep 6268549 = 1175353) (by norm_num)
theorem B1672849 : Blo 1649524 1672849 := bbase (se 2 (by rfl) ⟨627318, by rfl⟩ : syracuseStep 1672849 = 1254637) (by norm_num)
theorem B3712661 : Blo 1649524 3712661 := bbase (se 6 (by rfl) ⟨87015, by rfl⟩ : syracuseStep 3712661 = 174031) (by norm_num)
theorem B2475677 : Blo 1649524 2475677 := bbase (se 3 (by rfl) ⟨464189, by rfl⟩ : syracuseStep 2475677 = 928379) (by norm_num)
theorem B2475701 : Blo 1649524 2475701 := bbase (se 5 (by rfl) ⟨116048, by rfl⟩ : syracuseStep 2475701 = 232097) (by norm_num)
theorem B2475725 : Blo 1649524 2475725 := bbase (se 3 (by rfl) ⟨464198, by rfl⟩ : syracuseStep 2475725 = 928397) (by norm_num)
theorem B3712733 : Blo 1649524 3712733 := bbase (se 3 (by rfl) ⟨696137, by rfl⟩ : syracuseStep 3712733 = 1392275) (by norm_num)
theorem B2475749 : Blo 1649524 2475749 := bbase (se 4 (by rfl) ⟨232101, by rfl⟩ : syracuseStep 2475749 = 464203) (by norm_num)
theorem B4179701 : Blo 1649524 4179701 := bbase (se 5 (by rfl) ⟨195923, by rfl⟩ : syracuseStep 4179701 = 391847) (by norm_num)
theorem B2475773 : Blo 1649524 2475773 := bbase (se 3 (by rfl) ⟨464207, by rfl⟩ : syracuseStep 2475773 = 928415) (by norm_num)
theorem B2475797 : Blo 1649524 2475797 := bbase (se 6 (by rfl) ⟨58026, by rfl⟩ : syracuseStep 2475797 = 116053) (by norm_num)
theorem B3712805 : Blo 1649524 3712805 := bbase (se 4 (by rfl) ⟨348075, by rfl⟩ : syracuseStep 3712805 = 696151) (by norm_num)
theorem B2475821 : Blo 1649524 2475821 := bbase (se 3 (by rfl) ⟨464216, by rfl⟩ : syracuseStep 2475821 = 928433) (by norm_num)
theorem B2475845 : Blo 1649524 2475845 := bbase (se 4 (by rfl) ⟨232110, by rfl⟩ : syracuseStep 2475845 = 464221) (by norm_num)
theorem B5572421 : Blo 1649524 5572421 := bbase (se 4 (by rfl) ⟨522414, by rfl⟩ : syracuseStep 5572421 = 1044829) (by norm_num)
theorem B3344213 : Blo 1649524 3344213 := bbase (se 9 (by rfl) ⟨9797, by rfl⟩ : syracuseStep 3344213 = 19595) (by norm_num)
theorem B2475869 : Blo 1649524 2475869 := bbase (se 3 (by rfl) ⟨464225, by rfl⟩ : syracuseStep 2475869 = 928451) (by norm_num)
theorem B3712877 : Blo 1649524 3712877 := bbase (se 3 (by rfl) ⟨696164, by rfl⟩ : syracuseStep 3712877 = 1392329) (by norm_num)
theorem B2475893 : Blo 1649524 2475893 := bbase (se 5 (by rfl) ⟨116057, by rfl⟩ : syracuseStep 2475893 = 232115) (by norm_num)
theorem B2475917 : Blo 1649524 2475917 := bbase (se 3 (by rfl) ⟨464234, by rfl⟩ : syracuseStep 2475917 = 928469) (by norm_num)
theorem B2475941 : Blo 1649524 2475941 := bbase (se 4 (by rfl) ⟨232119, by rfl⟩ : syracuseStep 2475941 = 464239) (by norm_num)
theorem B3712949 : Blo 1649524 3712949 := bbase (se 5 (by rfl) ⟨174044, by rfl⟩ : syracuseStep 3712949 = 348089) (by norm_num)
theorem B6268853 : Blo 1649524 6268853 := bbase (se 5 (by rfl) ⟨293852, by rfl⟩ : syracuseStep 6268853 = 587705) (by norm_num)
theorem B2475965 : Blo 1649524 2475965 := bbase (se 3 (by rfl) ⟨464243, by rfl⟩ : syracuseStep 2475965 = 928487) (by norm_num)
theorem B2475989 : Blo 1649524 2475989 := bbase (se 7 (by rfl) ⟨29015, by rfl⟩ : syracuseStep 2475989 = 58031) (by norm_num)
theorem B3524573 : Blo 1649524 3524573 := bbase (se 3 (by rfl) ⟨660857, by rfl⟩ : syracuseStep 3524573 = 1321715) (by norm_num)
theorem B5285861 : Blo 1649524 5285861 := bbase (se 4 (by rfl) ⟨495549, by rfl⟩ : syracuseStep 5285861 = 991099) (by norm_num)
theorem B2476013 : Blo 1649524 2476013 := bbase (se 3 (by rfl) ⟨464252, by rfl⟩ : syracuseStep 2476013 = 928505) (by norm_num)
theorem B3713021 : Blo 1649524 3713021 := bbase (se 3 (by rfl) ⟨696191, by rfl⟩ : syracuseStep 3713021 = 1392383) (by norm_num)
theorem B2476037 : Blo 1649524 2476037 := bbase (se 4 (by rfl) ⟨232128, by rfl⟩ : syracuseStep 2476037 = 464257) (by norm_num)
theorem B2476061 : Blo 1649524 2476061 := bbase (se 3 (by rfl) ⟨464261, by rfl⟩ : syracuseStep 2476061 = 928523) (by norm_num)
theorem B2476085 : Blo 1649524 2476085 := bbase (se 5 (by rfl) ⟨116066, by rfl⟩ : syracuseStep 2476085 = 232133) (by norm_num)
theorem B3713093 : Blo 1649524 3713093 := bbase (se 4 (by rfl) ⟨348102, by rfl⟩ : syracuseStep 3713093 = 696205) (by norm_num)
theorem B2476109 : Blo 1649524 2476109 := bbase (se 3 (by rfl) ⟨464270, by rfl⟩ : syracuseStep 2476109 = 928541) (by norm_num)
theorem B4180045 : Blo 1649524 4180045 := bbase (se 3 (by rfl) ⟨783758, by rfl⟩ : syracuseStep 4180045 = 1567517) (by norm_num)
theorem B2476133 : Blo 1649524 2476133 := bbase (se 4 (by rfl) ⟨232137, by rfl⟩ : syracuseStep 2476133 = 464275) (by norm_num)
theorem B2476157 : Blo 1649524 2476157 := bbase (se 3 (by rfl) ⟨464279, by rfl⟩ : syracuseStep 2476157 = 928559) (by norm_num)
theorem B6695045 : Blo 1649524 6695045 := bbase (se 4 (by rfl) ⟨627660, by rfl⟩ : syracuseStep 6695045 = 1255321) (by norm_num)
theorem B3713165 : Blo 1649524 3713165 := bbase (se 3 (by rfl) ⟨696218, by rfl⟩ : syracuseStep 3713165 = 1392437) (by norm_num)
theorem B2476181 : Blo 1649524 2476181 := bbase (se 6 (by rfl) ⟨58035, by rfl⟩ : syracuseStep 2476181 = 116071) (by norm_num)
theorem B2476205 : Blo 1649524 2476205 := bbase (se 3 (by rfl) ⟨464288, by rfl⟩ : syracuseStep 2476205 = 928577) (by norm_num)
theorem B8472757 : Blo 1649524 8472757 := bbase (se 5 (by rfl) ⟨397160, by rfl⟩ : syracuseStep 8472757 = 794321) (by norm_num)
theorem B4180157 : Blo 1649524 4180157 := bbase (se 3 (by rfl) ⟨783779, by rfl⟩ : syracuseStep 4180157 = 1567559) (by norm_num)
theorem B2476229 : Blo 1649524 2476229 := bbase (se 4 (by rfl) ⟨232146, by rfl⟩ : syracuseStep 2476229 = 464293) (by norm_num)
theorem B3713237 : Blo 1649524 3713237 := bbase (se 7 (by rfl) ⟨43514, by rfl⟩ : syracuseStep 3713237 = 87029) (by norm_num)
theorem B2476253 : Blo 1649524 2476253 := bbase (se 3 (by rfl) ⟨464297, by rfl⟩ : syracuseStep 2476253 = 928595) (by norm_num)
theorem B2476277 : Blo 1649524 2476277 := bbase (se 5 (by rfl) ⟨116075, by rfl⟩ : syracuseStep 2476277 = 232151) (by norm_num)
theorem B5572853 : Blo 1649524 5572853 := bbase (se 5 (by rfl) ⟨261227, by rfl⟩ : syracuseStep 5572853 = 522455) (by norm_num)
theorem B2476301 : Blo 1649524 2476301 := bbase (se 3 (by rfl) ⟨464306, by rfl⟩ : syracuseStep 2476301 = 928613) (by norm_num)
theorem B3713309 : Blo 1649524 3713309 := bbase (se 3 (by rfl) ⟨696245, by rfl⟩ : syracuseStep 3713309 = 1392491) (by norm_num)
theorem B2976029 : Blo 1649524 2976029 := bbase (se 3 (by rfl) ⟨558005, by rfl⟩ : syracuseStep 2976029 = 1116011) (by norm_num)
theorem B2476325 : Blo 1649524 2476325 := bbase (se 4 (by rfl) ⟨232155, by rfl⟩ : syracuseStep 2476325 = 464311) (by norm_num)
theorem B3131693 : Blo 1649524 3131693 := bbase (se 3 (by rfl) ⟨587192, by rfl⟩ : syracuseStep 3131693 = 1174385) (by norm_num)
theorem B2476349 : Blo 1649524 2476349 := bbase (se 3 (by rfl) ⟨464315, by rfl⟩ : syracuseStep 2476349 = 928631) (by norm_num)
theorem B2476373 : Blo 1649524 2476373 := bbase (se 10 (by rfl) ⟨3627, by rfl⟩ : syracuseStep 2476373 = 7255) (by norm_num)
theorem B3713381 : Blo 1649524 3713381 := bbase (se 4 (by rfl) ⟨348129, by rfl⟩ : syracuseStep 3713381 = 696259) (by norm_num)
theorem B2476397 : Blo 1649524 2476397 := bbase (se 3 (by rfl) ⟨464324, by rfl⟩ : syracuseStep 2476397 = 928649) (by norm_num)
theorem B4180349 : Blo 1649524 4180349 := bbase (se 3 (by rfl) ⟨783815, by rfl⟩ : syracuseStep 4180349 = 1567631) (by norm_num)
theorem B2476421 : Blo 1649524 2476421 := bbase (se 4 (by rfl) ⟨232164, by rfl⟩ : syracuseStep 2476421 = 464329) (by norm_num)
theorem B2476445 : Blo 1649524 2476445 := bbase (se 3 (by rfl) ⟨464333, by rfl⟩ : syracuseStep 2476445 = 928667) (by norm_num)
theorem B3713453 : Blo 1649524 3713453 := bbase (se 3 (by rfl) ⟨696272, by rfl⟩ : syracuseStep 3713453 = 1392545) (by norm_num)
theorem B4762037 : Blo 1649524 4762037 := bbase (se 5 (by rfl) ⟨223220, by rfl⟩ : syracuseStep 4762037 = 446441) (by norm_num)
theorem B2476469 : Blo 1649524 2476469 := bbase (se 5 (by rfl) ⟨116084, by rfl⟩ : syracuseStep 2476469 = 232169) (by norm_num)
theorem B2476493 : Blo 1649524 2476493 := bbase (se 3 (by rfl) ⟨464342, by rfl⟩ : syracuseStep 2476493 = 928685) (by norm_num)
theorem B3344861 : Blo 1649524 3344861 := bbase (se 3 (by rfl) ⟨627161, by rfl⟩ : syracuseStep 3344861 = 1254323) (by norm_num)
theorem B2476517 : Blo 1649524 2476517 := bbase (se 4 (by rfl) ⟨232173, by rfl⟩ : syracuseStep 2476517 = 464347) (by norm_num)
theorem B3762677 : Blo 1649524 3762677 := bbase (se 5 (by rfl) ⟨176375, by rfl⟩ : syracuseStep 3762677 = 352751) (by norm_num)
theorem B3713525 : Blo 1649524 3713525 := bbase (se 5 (by rfl) ⟨174071, by rfl⟩ : syracuseStep 3713525 = 348143) (by norm_num)
theorem B8358389 : Blo 1649524 8358389 := bbase (se 5 (by rfl) ⟨391799, by rfl⟩ : syracuseStep 8358389 = 783599) (by norm_num)
theorem B2476541 : Blo 1649524 2476541 := bbase (se 3 (by rfl) ⟨464351, by rfl⟩ : syracuseStep 2476541 = 928703) (by norm_num)
theorem B2476565 : Blo 1649524 2476565 := bbase (se 6 (by rfl) ⟨58044, by rfl⟩ : syracuseStep 2476565 = 116089) (by norm_num)
theorem B2476589 : Blo 1649524 2476589 := bbase (se 3 (by rfl) ⟨464360, by rfl⟩ : syracuseStep 2476589 = 928721) (by norm_num)
theorem B3713597 : Blo 1649524 3713597 := bbase (se 3 (by rfl) ⟨696299, by rfl⟩ : syracuseStep 3713597 = 1392599) (by norm_num)
theorem B2476613 : Blo 1649524 2476613 := bbase (se 4 (by rfl) ⟨232182, by rfl⟩ : syracuseStep 2476613 = 464365) (by norm_num)
theorem B2476637 : Blo 1649524 2476637 := bbase (se 3 (by rfl) ⟨464369, by rfl⟩ : syracuseStep 2476637 = 928739) (by norm_num)
theorem B2476661 : Blo 1649524 2476661 := bbase (se 5 (by rfl) ⟨116093, by rfl⟩ : syracuseStep 2476661 = 232187) (by norm_num)
theorem B3713669 : Blo 1649524 3713669 := bbase (se 4 (by rfl) ⟨348156, by rfl⟩ : syracuseStep 3713669 = 696313) (by norm_num)
theorem B2476685 : Blo 1649524 2476685 := bbase (se 3 (by rfl) ⟨464378, by rfl⟩ : syracuseStep 2476685 = 928757) (by norm_num)
theorem B2476709 : Blo 1649524 2476709 := bbase (se 4 (by rfl) ⟨232191, by rfl⟩ : syracuseStep 2476709 = 464383) (by norm_num)
theorem B5573285 : Blo 1649524 5573285 := bbase (se 4 (by rfl) ⟨522495, by rfl⟩ : syracuseStep 5573285 = 1044991) (by norm_num)
theorem B2476733 : Blo 1649524 2476733 := bbase (se 3 (by rfl) ⟨464387, by rfl⟩ : syracuseStep 2476733 = 928775) (by norm_num)
theorem B3713741 : Blo 1649524 3713741 := bbase (se 3 (by rfl) ⟨696326, by rfl⟩ : syracuseStep 3713741 = 1392653) (by norm_num)
theorem B2476757 : Blo 1649524 2476757 := bbase (se 7 (by rfl) ⟨29024, by rfl⟩ : syracuseStep 2476757 = 58049) (by norm_num)
theorem B5286629 : Blo 1649524 5286629 := bbase (se 4 (by rfl) ⟨495621, by rfl⟩ : syracuseStep 5286629 = 991243) (by norm_num)
theorem B2476781 : Blo 1649524 2476781 := bbase (se 3 (by rfl) ⟨464396, by rfl⟩ : syracuseStep 2476781 = 928793) (by norm_num)
theorem B2476805 : Blo 1649524 2476805 := bbase (se 4 (by rfl) ⟨232200, by rfl⟩ : syracuseStep 2476805 = 464401) (by norm_num)
theorem B3713813 : Blo 1649524 3713813 := bbase (se 6 (by rfl) ⟨87042, by rfl⟩ : syracuseStep 3713813 = 174085) (by norm_num)
theorem B20081429 : Blo 1649524 20081429 := bbase (se 6 (by rfl) ⟨470658, by rfl⟩ : syracuseStep 20081429 = 941317) (by norm_num)
theorem B2476829 : Blo 1649524 2476829 := bbase (se 3 (by rfl) ⟨464405, by rfl⟩ : syracuseStep 2476829 = 928811) (by norm_num)
theorem B2476853 : Blo 1649524 2476853 := bbase (se 5 (by rfl) ⟨116102, by rfl⟩ : syracuseStep 2476853 = 232205) (by norm_num)
theorem B3525437 : Blo 1649524 3525437 := bbase (se 3 (by rfl) ⟨661019, by rfl⟩ : syracuseStep 3525437 = 1322039) (by norm_num)
theorem B2476877 : Blo 1649524 2476877 := bbase (se 3 (by rfl) ⟨464414, by rfl⟩ : syracuseStep 2476877 = 928829) (by norm_num)
theorem B3713885 : Blo 1649524 3713885 := bbase (se 3 (by rfl) ⟨696353, by rfl⟩ : syracuseStep 3713885 = 1392707) (by norm_num)
theorem B2476901 : Blo 1649524 2476901 := bbase (se 4 (by rfl) ⟨232209, by rfl⟩ : syracuseStep 2476901 = 464419) (by norm_num)
theorem B2476925 : Blo 1649524 2476925 := bbase (se 3 (by rfl) ⟨464423, by rfl⟩ : syracuseStep 2476925 = 928847) (by norm_num)
theorem B2231173 : Blo 1649524 2231173 := bbase (se 4 (by rfl) ⟨209172, by rfl⟩ : syracuseStep 2231173 = 418345) (by norm_num)
theorem B2509717 : Blo 1649524 2509717 := bbase (se 6 (by rfl) ⟨58821, by rfl⟩ : syracuseStep 2509717 = 117643) (by norm_num)
theorem B2476949 : Blo 1649524 2476949 := bbase (se 6 (by rfl) ⟨58053, by rfl⟩ : syracuseStep 2476949 = 116107) (by norm_num)
theorem B3713957 : Blo 1649524 3713957 := bbase (se 4 (by rfl) ⟨348183, by rfl⟩ : syracuseStep 3713957 = 696367) (by norm_num)
theorem B2476973 : Blo 1649524 2476973 := bbase (se 3 (by rfl) ⟨464432, by rfl⟩ : syracuseStep 2476973 = 928865) (by norm_num)
theorem B2476997 : Blo 1649524 2476997 := bbase (se 4 (by rfl) ⟨232218, by rfl⟩ : syracuseStep 2476997 = 464437) (by norm_num)
theorem B3525581 : Blo 1649524 3525581 := bbase (se 3 (by rfl) ⟨661046, by rfl⟩ : syracuseStep 3525581 = 1322093) (by norm_num)
theorem B31738837 : Blo 1649524 31738837 := bbase (se 7 (by rfl) ⟨371939, by rfl⟩ : syracuseStep 31738837 = 743879) (by norm_num)
theorem B2477021 : Blo 1649524 2477021 := bbase (se 3 (by rfl) ⟨464441, by rfl⟩ : syracuseStep 2477021 = 928883) (by norm_num)
theorem B3574757 : Blo 1649524 3574757 := bbase (se 4 (by rfl) ⟨335133, by rfl⟩ : syracuseStep 3574757 = 670267) (by norm_num)
theorem B2116589 : Blo 1649524 2116589 := bbase (se 3 (by rfl) ⟨396860, by rfl⟩ : syracuseStep 2116589 = 793721) (by norm_num)
theorem B3714029 : Blo 1649524 3714029 := bbase (se 3 (by rfl) ⟨696380, by rfl⟩ : syracuseStep 3714029 = 1392761) (by norm_num)
theorem B2477045 : Blo 1649524 2477045 := bbase (se 5 (by rfl) ⟨116111, by rfl⟩ : syracuseStep 2477045 = 232223) (by norm_num)
theorem B2477069 : Blo 1649524 2477069 := bbase (se 3 (by rfl) ⟨464450, by rfl⟩ : syracuseStep 2477069 = 928901) (by norm_num)
theorem B3132445 : Blo 1649524 3132445 := bbase (se 3 (by rfl) ⟨587333, by rfl⟩ : syracuseStep 3132445 = 1174667) (by norm_num)
theorem B2477093 : Blo 1649524 2477093 := bbase (se 4 (by rfl) ⟨232227, by rfl⟩ : syracuseStep 2477093 = 464455) (by norm_num)
theorem B3714101 : Blo 1649524 3714101 := bbase (se 5 (by rfl) ⟨174098, by rfl⟩ : syracuseStep 3714101 = 348197) (by norm_num)
theorem B2477117 : Blo 1649524 2477117 := bbase (se 3 (by rfl) ⟨464459, by rfl⟩ : syracuseStep 2477117 = 928919) (by norm_num)
theorem B2477141 : Blo 1649524 2477141 := bbase (se 8 (by rfl) ⟨14514, by rfl⟩ : syracuseStep 2477141 = 29029) (by norm_num)
theorem B5573717 : Blo 1649524 5573717 := bbase (se 8 (by rfl) ⟨32658, by rfl⟩ : syracuseStep 5573717 = 65317) (by norm_num)
theorem B2477165 : Blo 1649524 2477165 := bbase (se 3 (by rfl) ⟨464468, by rfl⟩ : syracuseStep 2477165 = 928937) (by norm_num)
theorem B3714173 : Blo 1649524 3714173 := bbase (se 3 (by rfl) ⟨696407, by rfl⟩ : syracuseStep 3714173 = 1392815) (by norm_num)
theorem B2477189 : Blo 1649524 2477189 := bbase (se 4 (by rfl) ⟨232236, by rfl⟩ : syracuseStep 2477189 = 464473) (by norm_num)
theorem B2477213 : Blo 1649524 2477213 := bbase (se 3 (by rfl) ⟨464477, by rfl⟩ : syracuseStep 2477213 = 928955) (by norm_num)
theorem B3132589 : Blo 1649524 3132589 := bbase (se 3 (by rfl) ⟨587360, by rfl⟩ : syracuseStep 3132589 = 1174721) (by norm_num)
theorem B2477237 : Blo 1649524 2477237 := bbase (se 5 (by rfl) ⟨116120, by rfl⟩ : syracuseStep 2477237 = 232241) (by norm_num)
theorem B3714245 : Blo 1649524 3714245 := bbase (se 4 (by rfl) ⟨348210, by rfl⟩ : syracuseStep 3714245 = 696421) (by norm_num)
theorem B2477261 : Blo 1649524 2477261 := bbase (se 3 (by rfl) ⟨464486, by rfl⟩ : syracuseStep 2477261 = 928973) (by norm_num)
theorem B5287141 : Blo 1649524 5287141 := bbase (se 4 (by rfl) ⟨495669, by rfl⟩ : syracuseStep 5287141 = 991339) (by norm_num)
theorem B2477285 : Blo 1649524 2477285 := bbase (se 4 (by rfl) ⟨232245, by rfl⟩ : syracuseStep 2477285 = 464491) (by norm_num)
theorem B3714317 : Blo 1649524 3714317 := bbase (se 3 (by rfl) ⟨696434, by rfl⟩ : syracuseStep 3714317 = 1392869) (by norm_num)
theorem B3132749 : Blo 1649524 3132749 := bbase (se 3 (by rfl) ⟨587390, by rfl⟩ : syracuseStep 3132749 = 1174781) (by norm_num)
theorem B3714389 : Blo 1649524 3714389 := bbase (se 11 (by rfl) ⟨2720, by rfl⟩ : syracuseStep 3714389 = 5441) (by norm_num)
theorem B7048565 : Blo 1649524 7048565 := bbase (se 5 (by rfl) ⟨330401, by rfl⟩ : syracuseStep 7048565 = 660803) (by norm_num)
theorem B3714461 : Blo 1649524 3714461 := bbase (se 3 (by rfl) ⟨696461, by rfl⟩ : syracuseStep 3714461 = 1392923) (by norm_num)
theorem B6688165 : Blo 1649524 6688165 := bbase (se 4 (by rfl) ⟨627015, by rfl⟩ : syracuseStep 6688165 = 1254031) (by norm_num)
theorem B3132893 : Blo 1649524 3132893 := bbase (se 3 (by rfl) ⟨587417, by rfl⟩ : syracuseStep 3132893 = 1174835) (by norm_num)
theorem B3714533 : Blo 1649524 3714533 := bbase (se 4 (by rfl) ⟨348237, by rfl⟩ : syracuseStep 3714533 = 696475) (by norm_num)
theorem B3714605 : Blo 1649524 3714605 := bbase (se 3 (by rfl) ⟨696488, by rfl⟩ : syracuseStep 3714605 = 1392977) (by norm_num)
theorem B3714677 : Blo 1649524 3714677 := bbase (se 5 (by rfl) ⟨174125, by rfl⟩ : syracuseStep 3714677 = 348251) (by norm_num)
theorem B3526325 : Blo 1649524 3526325 := bbase (se 5 (by rfl) ⟨165296, by rfl⟩ : syracuseStep 3526325 = 330593) (by norm_num)
theorem B3714749 : Blo 1649524 3714749 := bbase (se 3 (by rfl) ⟨696515, by rfl⟩ : syracuseStep 3714749 = 1393031) (by norm_num)
theorem B4697813 : Blo 1649524 4697813 := bbase (se 7 (by rfl) ⟨55052, by rfl⟩ : syracuseStep 4697813 = 110105) (by norm_num)
theorem B3133181 : Blo 1649524 3133181 := bbase (se 3 (by rfl) ⟨587471, by rfl⟩ : syracuseStep 3133181 = 1174943) (by norm_num)
theorem B3714821 : Blo 1649524 3714821 := bbase (se 4 (by rfl) ⟨348264, by rfl⟩ : syracuseStep 3714821 = 696529) (by norm_num)
theorem B8359685 : Blo 1649524 8359685 := bbase (se 4 (by rfl) ⟨783720, by rfl⟩ : syracuseStep 8359685 = 1567441) (by norm_num)
theorem B3764029 : Blo 1649524 3764029 := bbase (se 3 (by rfl) ⟨705755, by rfl⟩ : syracuseStep 3764029 = 1411511) (by norm_num)
theorem B3714893 : Blo 1649524 3714893 := bbase (se 3 (by rfl) ⟨696542, by rfl⟩ : syracuseStep 3714893 = 1393085) (by norm_num)
theorem B26767189 : Blo 1649524 26767189 := bbase (se 9 (by rfl) ⟨78419, by rfl⟩ : syracuseStep 26767189 = 156839) (by norm_num)
theorem B3133333 : Blo 1649524 3133333 := bbase (se 6 (by rfl) ⟨73437, by rfl⟩ : syracuseStep 3133333 = 146875) (by norm_num)
theorem B3714965 : Blo 1649524 3714965 := bbase (se 6 (by rfl) ⟨87069, by rfl⟩ : syracuseStep 3714965 = 174139) (by norm_num)
theorem B3715037 : Blo 1649524 3715037 := bbase (se 3 (by rfl) ⟨696569, by rfl⟩ : syracuseStep 3715037 = 1393139) (by norm_num)
theorem B3715109 : Blo 1649524 3715109 := bbase (se 4 (by rfl) ⟨348291, by rfl⟩ : syracuseStep 3715109 = 696583) (by norm_num)
theorem B2822221 : Blo 1649524 2822221 := bbase (se 3 (by rfl) ⟨529166, by rfl⟩ : syracuseStep 2822221 = 1058333) (by norm_num)
theorem B3346517 : Blo 1649524 3346517 := bbase (se 8 (by rfl) ⟨19608, by rfl⟩ : syracuseStep 3346517 = 39217) (by norm_num)
theorem B3715181 : Blo 1649524 3715181 := bbase (se 3 (by rfl) ⟨696596, by rfl⟩ : syracuseStep 3715181 = 1393193) (by norm_num)
theorem B2117749 : Blo 1649524 2117749 := bbase (se 5 (by rfl) ⟨99269, by rfl⟩ : syracuseStep 2117749 = 198539) (by norm_num)
theorem B7245941 : Blo 1649524 7245941 := bbase (se 5 (by rfl) ⟨339653, by rfl⟩ : syracuseStep 7245941 = 679307) (by norm_num)
theorem B2510981 : Blo 1649524 2510981 := bbase (se 4 (by rfl) ⟨235404, by rfl⟩ : syracuseStep 2510981 = 470809) (by norm_num)
theorem B8351909 : Blo 1649524 8351909 := bbase (se 4 (by rfl) ⟨782991, by rfl⟩ : syracuseStep 8351909 = 1565983) (by norm_num)
theorem B3715253 : Blo 1649524 3715253 := bbase (se 5 (by rfl) ⟨174152, by rfl⟩ : syracuseStep 3715253 = 348305) (by norm_num)
theorem B3133637 : Blo 1649524 3133637 := bbase (se 4 (by rfl) ⟨293778, by rfl⟩ : syracuseStep 3133637 = 587557) (by norm_num)
theorem B1855741 : Blo 1649524 1855741 := bbase (se 3 (by rfl) ⟨347951, by rfl⟩ : syracuseStep 1855741 = 695903) (by norm_num)
theorem B3715325 : Blo 1649524 3715325 := bbase (se 3 (by rfl) ⟨696623, by rfl⟩ : syracuseStep 3715325 = 1393247) (by norm_num)
theorem B1855777 : Blo 1649524 1855777 := bbase (se 2 (by rfl) ⟨695916, by rfl⟩ : syracuseStep 1855777 = 1391833) (by norm_num)
theorem B1855813 : Blo 1649524 1855813 := bbase (se 4 (by rfl) ⟨173982, by rfl⟩ : syracuseStep 1855813 = 347965) (by norm_num)
theorem B3715397 : Blo 1649524 3715397 := bbase (se 4 (by rfl) ⟨348318, by rfl⟩ : syracuseStep 3715397 = 696637) (by norm_num)
theorem B14102869 : Blo 1649524 14102869 := bbase (se 10 (by rfl) ⟨20658, by rfl⟩ : syracuseStep 14102869 = 41317) (by norm_num)
theorem B1855849 : Blo 1649524 1855849 := bbase (se 2 (by rfl) ⟨695943, by rfl⟩ : syracuseStep 1855849 = 1391887) (by norm_num)
theorem B6689141 : Blo 1649524 6689141 := bbase (se 5 (by rfl) ⟨313553, by rfl⟩ : syracuseStep 6689141 = 627107) (by norm_num)
theorem B1855885 : Blo 1649524 1855885 := bbase (se 3 (by rfl) ⟨347978, by rfl⟩ : syracuseStep 1855885 = 695957) (by norm_num)
theorem B3715469 : Blo 1649524 3715469 := bbase (se 3 (by rfl) ⟨696650, by rfl⟩ : syracuseStep 3715469 = 1393301) (by norm_num)
theorem B6263189 : Blo 1649524 6263189 := bbase (se 6 (by rfl) ⟨146793, by rfl⟩ : syracuseStep 6263189 = 293587) (by norm_num)
theorem B3527077 : Blo 1649524 3527077 := bbase (se 4 (by rfl) ⟨330663, by rfl⟩ : syracuseStep 3527077 = 661327) (by norm_num)
theorem B1855921 : Blo 1649524 1855921 := bbase (se 2 (by rfl) ⟨695970, by rfl⟩ : syracuseStep 1855921 = 1391941) (by norm_num)
theorem B1855957 : Blo 1649524 1855957 := bbase (se 7 (by rfl) ⟨21749, by rfl⟩ : syracuseStep 1855957 = 43499) (by norm_num)
theorem B3715541 : Blo 1649524 3715541 := bbase (se 7 (by rfl) ⟨43541, by rfl⟩ : syracuseStep 3715541 = 87083) (by norm_num)
theorem B1855993 : Blo 1649524 1855993 := bbase (se 2 (by rfl) ⟨695997, by rfl⟩ : syracuseStep 1855993 = 1391995) (by norm_num)
theorem B1856029 : Blo 1649524 1856029 := bbase (se 3 (by rfl) ⟨348005, by rfl⟩ : syracuseStep 1856029 = 696011) (by norm_num)
theorem B3715613 : Blo 1649524 3715613 := bbase (se 3 (by rfl) ⟨696677, by rfl⟩ : syracuseStep 3715613 = 1393355) (by norm_num)
theorem B7524917 : Blo 1649524 7524917 := bbase (se 5 (by rfl) ⟨352730, by rfl⟩ : syracuseStep 7524917 = 705461) (by norm_num)
theorem B6689333 : Blo 1649524 6689333 := bbase (se 5 (by rfl) ⟨313562, by rfl⟩ : syracuseStep 6689333 = 627125) (by norm_num)
theorem B3527221 : Blo 1649524 3527221 := bbase (se 5 (by rfl) ⟨165338, by rfl⟩ : syracuseStep 3527221 = 330677) (by norm_num)
theorem B1856065 : Blo 1649524 1856065 := bbase (se 2 (by rfl) ⟨696024, by rfl⟩ : syracuseStep 1856065 = 1392049) (by norm_num)
theorem B1856101 : Blo 1649524 1856101 := bbase (se 4 (by rfl) ⟨174009, by rfl⟩ : syracuseStep 1856101 = 348019) (by norm_num)
theorem B2544229 : Blo 1649524 2544229 := bbase (se 4 (by rfl) ⟨238521, by rfl⟩ : syracuseStep 2544229 = 477043) (by norm_num)
theorem B3715685 : Blo 1649524 3715685 := bbase (se 4 (by rfl) ⟨348345, by rfl⟩ : syracuseStep 3715685 = 696691) (by norm_num)
theorem B7934597 : Blo 1649524 7934597 := bbase (se 4 (by rfl) ⟨743868, by rfl⟩ : syracuseStep 7934597 = 1487737) (by norm_num)
theorem B1856137 : Blo 1649524 1856137 := bbase (se 2 (by rfl) ⟨696051, by rfl⟩ : syracuseStep 1856137 = 1392103) (by norm_num)
theorem B10572437 : Blo 1649524 10572437 := bbase (se 6 (by rfl) ⟨247791, by rfl⟩ : syracuseStep 10572437 = 495583) (by norm_num)
theorem B1856173 : Blo 1649524 1856173 := bbase (se 3 (by rfl) ⟨348032, by rfl⟩ : syracuseStep 1856173 = 696065) (by norm_num)
theorem B3715757 : Blo 1649524 3715757 := bbase (se 3 (by rfl) ⟨696704, by rfl⟩ : syracuseStep 3715757 = 1393409) (by norm_num)
theorem B6263477 : Blo 1649524 6263477 := bbase (se 5 (by rfl) ⟨293600, by rfl⟩ : syracuseStep 6263477 = 587201) (by norm_num)
theorem B3764933 : Blo 1649524 3764933 := bbase (se 4 (by rfl) ⟨352962, by rfl⟩ : syracuseStep 3764933 = 705925) (by norm_num)
theorem B1856209 : Blo 1649524 1856209 := bbase (se 2 (by rfl) ⟨696078, by rfl⟩ : syracuseStep 1856209 = 1392157) (by norm_num)
theorem B1856245 : Blo 1649524 1856245 := bbase (se 5 (by rfl) ⟨87011, by rfl⟩ : syracuseStep 1856245 = 174023) (by norm_num)
theorem B3715829 : Blo 1649524 3715829 := bbase (se 5 (by rfl) ⟨174179, by rfl⟩ : syracuseStep 3715829 = 348359) (by norm_num)
theorem B5567237 : Blo 1649524 5567237 := bbase (se 4 (by rfl) ⟨521928, by rfl⟩ : syracuseStep 5567237 = 1043857) (by norm_num)
theorem B1856281 : Blo 1649524 1856281 := bbase (se 2 (by rfl) ⟨696105, by rfl⟩ : syracuseStep 1856281 = 1392211) (by norm_num)
theorem B2118457 : Blo 1649524 2118457 := bbase (se 2 (by rfl) ⟨794421, by rfl⟩ : syracuseStep 2118457 = 1588843) (by norm_num)
theorem B1856317 : Blo 1649524 1856317 := bbase (se 3 (by rfl) ⟨348059, by rfl⟩ : syracuseStep 1856317 = 696119) (by norm_num)
theorem B3715901 : Blo 1649524 3715901 := bbase (se 3 (by rfl) ⟨696731, by rfl⟩ : syracuseStep 3715901 = 1393463) (by norm_num)
theorem B3765085 : Blo 1649524 3765085 := bbase (se 3 (by rfl) ⟨705953, by rfl⟩ : syracuseStep 3765085 = 1411907) (by norm_num)
theorem B1856353 : Blo 1649524 1856353 := bbase (se 2 (by rfl) ⟨696132, by rfl⟩ : syracuseStep 1856353 = 1392265) (by norm_num)
theorem B1856389 : Blo 1649524 1856389 := bbase (se 4 (by rfl) ⟨174036, by rfl⟩ : syracuseStep 1856389 = 348073) (by norm_num)
theorem B1856425 : Blo 1649524 1856425 := bbase (se 2 (by rfl) ⟨696159, by rfl⟩ : syracuseStep 1856425 = 1392319) (by norm_num)
theorem B5288885 : Blo 1649524 5288885 := bbase (se 5 (by rfl) ⟨247916, by rfl⟩ : syracuseStep 5288885 = 495833) (by norm_num)
theorem B3134389 : Blo 1649524 3134389 := bbase (se 5 (by rfl) ⟨146924, by rfl⟩ : syracuseStep 3134389 = 293849) (by norm_num)
theorem B1856461 : Blo 1649524 1856461 := bbase (se 3 (by rfl) ⟨348086, by rfl⟩ : syracuseStep 1856461 = 696173) (by norm_num)
theorem B1856497 : Blo 1649524 1856497 := bbase (se 2 (by rfl) ⟨696186, by rfl⟩ : syracuseStep 1856497 = 1392373) (by norm_num)
theorem B1856533 : Blo 1649524 1856533 := bbase (se 6 (by rfl) ⟨43512, by rfl⟩ : syracuseStep 1856533 = 87025) (by norm_num)
theorem B1856569 : Blo 1649524 1856569 := bbase (se 2 (by rfl) ⟨696213, by rfl⟩ : syracuseStep 1856569 = 1392427) (by norm_num)
theorem B3134533 : Blo 1649524 3134533 := bbase (se 4 (by rfl) ⟨293862, by rfl⟩ : syracuseStep 3134533 = 587725) (by norm_num)
theorem B1856605 : Blo 1649524 1856605 := bbase (se 3 (by rfl) ⟨348113, by rfl⟩ : syracuseStep 1856605 = 696227) (by norm_num)
theorem B7050341 : Blo 1649524 7050341 := bbase (se 4 (by rfl) ⟨660969, by rfl⟩ : syracuseStep 7050341 = 1321939) (by norm_num)
theorem B5289077 : Blo 1649524 5289077 := bbase (se 5 (by rfl) ⟨247925, by rfl⟩ : syracuseStep 5289077 = 495851) (by norm_num)
theorem B1856641 : Blo 1649524 1856641 := bbase (se 2 (by rfl) ⟨696240, by rfl⟩ : syracuseStep 1856641 = 1392481) (by norm_num)
theorem B1856677 : Blo 1649524 1856677 := bbase (se 4 (by rfl) ⟨174063, by rfl⟩ : syracuseStep 1856677 = 348127) (by norm_num)
theorem B5567669 : Blo 1649524 5567669 := bbase (se 5 (by rfl) ⟨260984, by rfl⟩ : syracuseStep 5567669 = 521969) (by norm_num)
theorem B1856713 : Blo 1649524 1856713 := bbase (se 2 (by rfl) ⟨696267, by rfl⟩ : syracuseStep 1856713 = 1392535) (by norm_num)
theorem B3134693 : Blo 1649524 3134693 := bbase (se 4 (by rfl) ⟨293877, by rfl⟩ : syracuseStep 3134693 = 587755) (by norm_num)
theorem B1856749 : Blo 1649524 1856749 := bbase (se 3 (by rfl) ⟨348140, by rfl⟩ : syracuseStep 1856749 = 696281) (by norm_num)
theorem B4699397 : Blo 1649524 4699397 := bbase (se 4 (by rfl) ⟨440568, by rfl⟩ : syracuseStep 4699397 = 881137) (by norm_num)
theorem B1856785 : Blo 1649524 1856785 := bbase (se 2 (by rfl) ⟨696294, by rfl⟩ : syracuseStep 1856785 = 1392589) (by norm_num)
theorem B1856821 : Blo 1649524 1856821 := bbase (se 5 (by rfl) ⟨87038, by rfl⟩ : syracuseStep 1856821 = 174077) (by norm_num)
theorem B3347773 : Blo 1649524 3347773 := bbase (se 3 (by rfl) ⟨627707, by rfl⟩ : syracuseStep 3347773 = 1255415) (by norm_num)
theorem B1856857 : Blo 1649524 1856857 := bbase (se 2 (by rfl) ⟨696321, by rfl⟩ : syracuseStep 1856857 = 1392643) (by norm_num)
theorem B3134837 : Blo 1649524 3134837 := bbase (se 5 (by rfl) ⟨146945, by rfl⟩ : syracuseStep 3134837 = 293891) (by norm_num)
theorem B1856893 : Blo 1649524 1856893 := bbase (se 3 (by rfl) ⟨348167, by rfl⟩ : syracuseStep 1856893 = 696335) (by norm_num)
theorem B12539285 : Blo 1649524 12539285 := bbase (se 6 (by rfl) ⟨293889, by rfl⟩ : syracuseStep 12539285 = 587779) (by norm_num)
theorem B1856929 : Blo 1649524 1856929 := bbase (se 2 (by rfl) ⟨696348, by rfl⟩ : syracuseStep 1856929 = 1392697) (by norm_num)
theorem B1881517 : Blo 1649524 1881517 := bbase (se 3 (by rfl) ⟨352784, by rfl⟩ : syracuseStep 1881517 = 705569) (by norm_num)
theorem B8353205 : Blo 1649524 8353205 := bbase (se 5 (by rfl) ⟨391556, by rfl⟩ : syracuseStep 8353205 = 783113) (by norm_num)
theorem B1856965 : Blo 1649524 1856965 := bbase (se 4 (by rfl) ⟨174090, by rfl⟩ : syracuseStep 1856965 = 348181) (by norm_num)
theorem B7927253 : Blo 1649524 7927253 := bbase (se 7 (by rfl) ⟨92897, by rfl⟩ : syracuseStep 7927253 = 185795) (by norm_num)
theorem B1857001 : Blo 1649524 1857001 := bbase (se 2 (by rfl) ⟨696375, by rfl⟩ : syracuseStep 1857001 = 1392751) (by norm_num)
theorem B1857037 : Blo 1649524 1857037 := bbase (se 3 (by rfl) ⟨348194, by rfl⟩ : syracuseStep 1857037 = 696389) (by norm_num)
theorem B13391381 : Blo 1649524 13391381 := bbase (se 6 (by rfl) ⟨313860, by rfl⟩ : syracuseStep 13391381 = 627721) (by norm_num)
theorem B1857073 : Blo 1649524 1857073 := bbase (se 2 (by rfl) ⟨696402, by rfl⟩ : syracuseStep 1857073 = 1392805) (by norm_num)
theorem B2643533 : Blo 1649524 2643533 := bbase (se 3 (by rfl) ⟨495662, by rfl⟩ : syracuseStep 2643533 = 991325) (by norm_num)
theorem B1857109 : Blo 1649524 1857109 := bbase (se 8 (by rfl) ⟨10881, by rfl⟩ : syracuseStep 1857109 = 21763) (by norm_num)
theorem B5568101 : Blo 1649524 5568101 := bbase (se 4 (by rfl) ⟨522009, by rfl⟩ : syracuseStep 5568101 = 1044019) (by norm_num)
theorem B1857145 : Blo 1649524 1857145 := bbase (se 2 (by rfl) ⟨696429, by rfl⟩ : syracuseStep 1857145 = 1392859) (by norm_num)
theorem B4175509 : Blo 1649524 4175509 := bbase (se 6 (by rfl) ⟨97863, by rfl⟩ : syracuseStep 4175509 = 195727) (by norm_num)
theorem B3135125 : Blo 1649524 3135125 := bbase (se 6 (by rfl) ⟨73479, by rfl⟩ : syracuseStep 3135125 = 146959) (by norm_num)
theorem B1857181 : Blo 1649524 1857181 := bbase (se 3 (by rfl) ⟨348221, by rfl⟩ : syracuseStep 1857181 = 696443) (by norm_num)
theorem B1857217 : Blo 1649524 1857217 := bbase (se 2 (by rfl) ⟨696456, by rfl⟩ : syracuseStep 1857217 = 1392913) (by norm_num)
theorem B1857253 : Blo 1649524 1857253 := bbase (se 4 (by rfl) ⟨174117, by rfl⟩ : syracuseStep 1857253 = 348235) (by norm_num)
theorem B4175621 : Blo 1649524 4175621 := bbase (se 4 (by rfl) ⟨391464, by rfl⟩ : syracuseStep 4175621 = 782929) (by norm_num)
theorem B1857289 : Blo 1649524 1857289 := bbase (se 2 (by rfl) ⟨696483, by rfl⟩ : syracuseStep 1857289 = 1392967) (by norm_num)
theorem B2643725 : Blo 1649524 2643725 := bbase (se 3 (by rfl) ⟨495698, by rfl⟩ : syracuseStep 2643725 = 991397) (by norm_num)
theorem B1857325 : Blo 1649524 1857325 := bbase (se 3 (by rfl) ⟨348248, by rfl⟩ : syracuseStep 1857325 = 696497) (by norm_num)
theorem B3135277 : Blo 1649524 3135277 := bbase (se 3 (by rfl) ⟨587864, by rfl⟩ : syracuseStep 3135277 = 1175729) (by norm_num)
theorem B12531509 : Blo 1649524 12531509 := bbase (se 5 (by rfl) ⟨587414, by rfl⟩ : syracuseStep 12531509 = 1174829) (by norm_num)
theorem B1857361 : Blo 1649524 1857361 := bbase (se 2 (by rfl) ⟨696510, by rfl⟩ : syracuseStep 1857361 = 1393021) (by norm_num)
theorem B6264661 : Blo 1649524 6264661 := bbase (se 9 (by rfl) ⟨18353, by rfl⟩ : syracuseStep 6264661 = 36707) (by norm_num)
theorem B1857397 : Blo 1649524 1857397 := bbase (se 5 (by rfl) ⟨87065, by rfl⟩ : syracuseStep 1857397 = 174131) (by norm_num)
theorem B2348941 : Blo 1649524 2348941 := bbase (se 3 (by rfl) ⟨440426, by rfl⟩ : syracuseStep 2348941 = 880853) (by norm_num)
theorem B2643853 : Blo 1649524 2643853 := bbase (se 3 (by rfl) ⟨495722, by rfl⟩ : syracuseStep 2643853 = 991445) (by norm_num)
theorem B1857433 : Blo 1649524 1857433 := bbase (se 2 (by rfl) ⟨696537, by rfl⟩ : syracuseStep 1857433 = 1393075) (by norm_num)
theorem B4700069 : Blo 1649524 4700069 := bbase (se 4 (by rfl) ⟨440631, by rfl⟩ : syracuseStep 4700069 = 881263) (by norm_num)
theorem B1857469 : Blo 1649524 1857469 := bbase (se 3 (by rfl) ⟨348275, by rfl⟩ : syracuseStep 1857469 = 696551) (by norm_num)
theorem B4175813 : Blo 1649524 4175813 := bbase (se 4 (by rfl) ⟨391482, by rfl⟩ : syracuseStep 4175813 = 782965) (by norm_num)
theorem B18806741 : Blo 1649524 18806741 := bbase (se 7 (by rfl) ⟨220391, by rfl⟩ : syracuseStep 18806741 = 440783) (by norm_num)
theorem B1857505 : Blo 1649524 1857505 := bbase (se 2 (by rfl) ⟨696564, by rfl⟩ : syracuseStep 1857505 = 1393129) (by norm_num)
theorem B1857541 : Blo 1649524 1857541 := bbase (se 4 (by rfl) ⟨174144, by rfl⟩ : syracuseStep 1857541 = 348289) (by norm_num)
theorem B5568533 : Blo 1649524 5568533 := bbase (se 6 (by rfl) ⟨130512, by rfl⟩ : syracuseStep 5568533 = 261025) (by norm_num)
theorem B1857577 : Blo 1649524 1857577 := bbase (se 2 (by rfl) ⟨696591, by rfl⟩ : syracuseStep 1857577 = 1393183) (by norm_num)
theorem B7051333 : Blo 1649524 7051333 := bbase (se 4 (by rfl) ⟨661062, by rfl⟩ : syracuseStep 7051333 = 1322125) (by norm_num)
theorem B1857613 : Blo 1649524 1857613 := bbase (se 3 (by rfl) ⟨348302, by rfl⟩ : syracuseStep 1857613 = 696605) (by norm_num)
theorem B2349157 : Blo 1649524 2349157 := bbase (se 4 (by rfl) ⟨220233, by rfl⟩ : syracuseStep 2349157 = 440467) (by norm_num)
theorem B1857649 : Blo 1649524 1857649 := bbase (se 2 (by rfl) ⟨696618, by rfl⟩ : syracuseStep 1857649 = 1393237) (by norm_num)
theorem B12384373 : Blo 1649524 12384373 := bbase (se 5 (by rfl) ⟨580517, by rfl⟩ : syracuseStep 12384373 = 1161035) (by norm_num)
theorem B6264965 : Blo 1649524 6264965 := bbase (se 4 (by rfl) ⟨587340, by rfl⟩ : syracuseStep 6264965 = 1174681) (by norm_num)
theorem B1882261 : Blo 1649524 1882261 := bbase (se 6 (by rfl) ⟨44115, by rfl⟩ : syracuseStep 1882261 = 88231) (by norm_num)
theorem B1857685 : Blo 1649524 1857685 := bbase (se 6 (by rfl) ⟨43539, by rfl⟩ : syracuseStep 1857685 = 87079) (by norm_num)
theorem B1857721 : Blo 1649524 1857721 := bbase (se 2 (by rfl) ⟨696645, by rfl⟩ : syracuseStep 1857721 = 1393291) (by norm_num)
theorem B1857757 : Blo 1649524 1857757 := bbase (se 3 (by rfl) ⟨348329, by rfl⟩ : syracuseStep 1857757 = 696659) (by norm_num)
theorem B1857793 : Blo 1649524 1857793 := bbase (se 2 (by rfl) ⟨696672, by rfl⟩ : syracuseStep 1857793 = 1393345) (by norm_num)
theorem B14104853 : Blo 1649524 14104853 := bbase (se 6 (by rfl) ⟨330582, by rfl⟩ : syracuseStep 14104853 = 661165) (by norm_num)
theorem B4176157 : Blo 1649524 4176157 := bbase (se 3 (by rfl) ⟨783029, by rfl⟩ : syracuseStep 4176157 = 1566059) (by norm_num)
theorem B1857829 : Blo 1649524 1857829 := bbase (se 4 (by rfl) ⟨174171, by rfl⟩ : syracuseStep 1857829 = 348343) (by norm_num)
theorem B1857865 : Blo 1649524 1857865 := bbase (se 2 (by rfl) ⟨696699, by rfl⟩ : syracuseStep 1857865 = 1393399) (by norm_num)
theorem B4700501 : Blo 1649524 4700501 := bbase (se 10 (by rfl) ⟨6885, by rfl⟩ : syracuseStep 4700501 = 13771) (by norm_num)
theorem B1857901 : Blo 1649524 1857901 := bbase (se 3 (by rfl) ⟨348356, by rfl⟩ : syracuseStep 1857901 = 696713) (by norm_num)
theorem B2783605 : Blo 1649524 2783605 := bbase (se 5 (by rfl) ⟨130481, by rfl⟩ : syracuseStep 2783605 = 260963) (by norm_num)
theorem B4176269 : Blo 1649524 4176269 := bbase (se 3 (by rfl) ⟨783050, by rfl⟩ : syracuseStep 4176269 = 1566101) (by norm_num)
theorem B1857937 : Blo 1649524 1857937 := bbase (se 2 (by rfl) ⟨696726, by rfl⟩ : syracuseStep 1857937 = 1393453) (by norm_num)
theorem B5568965 : Blo 1649524 5568965 := bbase (se 4 (by rfl) ⟨522090, by rfl⟩ : syracuseStep 5568965 = 1044181) (by norm_num)
theorem B2783693 : Blo 1649524 2783693 := bbase (se 3 (by rfl) ⟨521942, by rfl⟩ : syracuseStep 2783693 = 1043885) (by norm_num)
theorem B2349533 : Blo 1649524 2349533 := bbase (se 3 (by rfl) ⟨440537, by rfl⟩ : syracuseStep 2349533 = 881075) (by norm_num)
theorem B2644493 : Blo 1649524 2644493 := bbase (se 3 (by rfl) ⟨495842, by rfl⟩ : syracuseStep 2644493 = 991685) (by norm_num)
theorem B11893301 : Blo 1649524 11893301 := bbase (se 5 (by rfl) ⟨557498, by rfl⟩ : syracuseStep 11893301 = 1114997) (by norm_num)
theorem B5020213 : Blo 1649524 5020213 := bbase (se 5 (by rfl) ⟨235322, by rfl⟩ : syracuseStep 5020213 = 470645) (by norm_num)
theorem B2783821 : Blo 1649524 2783821 := bbase (se 3 (by rfl) ⟨521966, by rfl⟩ : syracuseStep 2783821 = 1043933) (by norm_num)
theorem B4176461 : Blo 1649524 4176461 := bbase (se 3 (by rfl) ⟨783086, by rfl⟩ : syracuseStep 4176461 = 1566173) (by norm_num)
theorem B4463189 : Blo 1649524 4463189 := bbase (se 8 (by rfl) ⟨26151, by rfl⟩ : syracuseStep 4463189 = 52303) (by norm_num)
theorem B9394805 : Blo 1649524 9394805 := bbase (se 5 (by rfl) ⟨440381, by rfl⟩ : syracuseStep 9394805 = 880763) (by norm_num)
theorem B4020853 : Blo 1649524 4020853 := bbase (se 5 (by rfl) ⟨188477, by rfl⟩ : syracuseStep 4020853 = 376955) (by norm_num)
theorem B2783909 : Blo 1649524 2783909 := bbase (se 4 (by rfl) ⟨260991, by rfl⟩ : syracuseStep 2783909 = 521983) (by norm_num)
theorem B8354501 : Blo 1649524 8354501 := bbase (se 4 (by rfl) ⟨783234, by rfl⟩ : syracuseStep 8354501 = 1566469) (by norm_num)
theorem B2087689 : Blo 1649524 2087689 := bbase (se 2 (by rfl) ⟨782883, by rfl⟩ : syracuseStep 2087689 = 1565767) (by norm_num)
theorem B2784037 : Blo 1649524 2784037 := bbase (se 4 (by rfl) ⟨261003, by rfl⟩ : syracuseStep 2784037 = 522007) (by norm_num)
theorem B2087785 : Blo 1649524 2087785 := bbase (se 2 (by rfl) ⟨782919, by rfl⟩ : syracuseStep 2087785 = 1565839) (by norm_num)
theorem B5569397 : Blo 1649524 5569397 := bbase (se 5 (by rfl) ⟨261065, by rfl⟩ : syracuseStep 5569397 = 522131) (by norm_num)
theorem B2784125 : Blo 1649524 2784125 := bbase (se 3 (by rfl) ⟨522023, by rfl⟩ : syracuseStep 2784125 = 1044047) (by norm_num)
theorem B4176805 : Blo 1649524 4176805 := bbase (se 4 (by rfl) ⟨391575, by rfl⟩ : syracuseStep 4176805 = 783151) (by norm_num)
theorem B4463525 : Blo 1649524 4463525 := bbase (se 4 (by rfl) ⟨418455, by rfl⟩ : syracuseStep 4463525 = 836911) (by norm_num)
theorem B10312661 : Blo 1649524 10312661 := bbase (se 7 (by rfl) ⟨120851, by rfl⟩ : syracuseStep 10312661 = 241703) (by norm_num)
theorem B2644949 : Blo 1649524 2644949 := bbase (se 7 (by rfl) ⟨30995, by rfl⟩ : syracuseStep 2644949 = 61991) (by norm_num)
theorem B2145253 : Blo 1649524 2145253 := bbase (se 4 (by rfl) ⟨201117, by rfl⟩ : syracuseStep 2145253 = 402235) (by norm_num)
theorem B2784253 : Blo 1649524 2784253 := bbase (se 3 (by rfl) ⟨522047, by rfl⟩ : syracuseStep 2784253 = 1044095) (by norm_num)
theorem B2087957 : Blo 1649524 2087957 := bbase (se 6 (by rfl) ⟨48936, by rfl⟩ : syracuseStep 2087957 = 97873) (by norm_num)
theorem B4176917 : Blo 1649524 4176917 := bbase (se 6 (by rfl) ⟨97896, by rfl⟩ : syracuseStep 4176917 = 195793) (by norm_num)
theorem B4701253 : Blo 1649524 4701253 := bbase (se 4 (by rfl) ⟨440742, by rfl⟩ : syracuseStep 4701253 = 881485) (by norm_num)
theorem B2088013 : Blo 1649524 2088013 := bbase (se 3 (by rfl) ⟨391502, by rfl⟩ : syracuseStep 2088013 = 783005) (by norm_num)
theorem B2784341 : Blo 1649524 2784341 := bbase (se 8 (by rfl) ⟨16314, by rfl⟩ : syracuseStep 2784341 = 32629) (by norm_num)
theorem B3013733 : Blo 1649524 3013733 := bbase (se 4 (by rfl) ⟨282537, by rfl⟩ : syracuseStep 3013733 = 565075) (by norm_num)
theorem B3964069 : Blo 1649524 3964069 := bbase (se 4 (by rfl) ⟨371631, by rfl⟩ : syracuseStep 3964069 = 743263) (by norm_num)
theorem B2088109 : Blo 1649524 2088109 := bbase (se 3 (by rfl) ⟨391520, by rfl⟩ : syracuseStep 2088109 = 783041) (by norm_num)
theorem B2645173 : Blo 1649524 2645173 := bbase (se 5 (by rfl) ⟨123992, by rfl⟩ : syracuseStep 2645173 = 247985) (by norm_num)
theorem B4021445 : Blo 1649524 4021445 := bbase (se 4 (by rfl) ⟨377010, by rfl⟩ : syracuseStep 4021445 = 754021) (by norm_num)
theorem B2784469 : Blo 1649524 2784469 := bbase (se 7 (by rfl) ⟨32630, by rfl⟩ : syracuseStep 2784469 = 65261) (by norm_num)
theorem B4177109 : Blo 1649524 4177109 := bbase (se 7 (by rfl) ⟨48950, by rfl⟩ : syracuseStep 4177109 = 97901) (by norm_num)
theorem B8043749 : Blo 1649524 8043749 := bbase (se 4 (by rfl) ⟨754101, by rfl⟩ : syracuseStep 8043749 = 1508203) (by norm_num)
theorem B2645237 : Blo 1649524 2645237 := bbase (se 5 (by rfl) ⟨123995, by rfl⟩ : syracuseStep 2645237 = 247991) (by norm_num)
theorem B5569829 : Blo 1649524 5569829 := bbase (se 4 (by rfl) ⟨522171, by rfl⟩ : syracuseStep 5569829 = 1044343) (by norm_num)
theorem B2784557 : Blo 1649524 2784557 := bbase (se 3 (by rfl) ⟨522104, by rfl⟩ : syracuseStep 2784557 = 1044209) (by norm_num)
theorem B2088281 : Blo 1649524 2088281 := bbase (se 2 (by rfl) ⟨783105, by rfl⟩ : syracuseStep 2088281 = 1566211) (by norm_num)
theorem B4234613 : Blo 1649524 4234613 := bbase (se 5 (by rfl) ⟨198497, by rfl⟩ : syracuseStep 4234613 = 396995) (by norm_num)
theorem B2645365 : Blo 1649524 2645365 := bbase (se 5 (by rfl) ⟨124001, by rfl⟩ : syracuseStep 2645365 = 248003) (by norm_num)
theorem B2088337 : Blo 1649524 2088337 := bbase (se 2 (by rfl) ⟨783126, by rfl⟩ : syracuseStep 2088337 = 1566253) (by norm_num)
theorem B4521365 : Blo 1649524 4521365 := bbase (se 6 (by rfl) ⟨105969, by rfl⟩ : syracuseStep 4521365 = 211939) (by norm_num)
theorem B10722709 : Blo 1649524 10722709 := bbase (se 6 (by rfl) ⟨251313, by rfl⟩ : syracuseStep 10722709 = 502627) (by norm_num)
theorem B3390893 : Blo 1649524 3390893 := bbase (se 3 (by rfl) ⟨635792, by rfl⟩ : syracuseStep 3390893 = 1271585) (by norm_num)
theorem B2784685 : Blo 1649524 2784685 := bbase (se 3 (by rfl) ⟨522128, by rfl⟩ : syracuseStep 2784685 = 1044257) (by norm_num)
theorem B2973125 : Blo 1649524 2973125 := bbase (se 4 (by rfl) ⟨278730, by rfl⟩ : syracuseStep 2973125 = 557461) (by norm_num)
theorem B2579941 : Blo 1649524 2579941 := bbase (se 4 (by rfl) ⟨241869, by rfl⟩ : syracuseStep 2579941 = 483739) (by norm_num)
theorem B2088433 : Blo 1649524 2088433 := bbase (se 2 (by rfl) ⟨783162, by rfl⟩ : syracuseStep 2088433 = 1566325) (by norm_num)
theorem B2784773 : Blo 1649524 2784773 := bbase (se 4 (by rfl) ⟨261072, by rfl⟩ : syracuseStep 2784773 = 522145) (by norm_num)
theorem B4177453 : Blo 1649524 4177453 := bbase (se 3 (by rfl) ⟨783272, by rfl⟩ : syracuseStep 4177453 = 1566545) (by norm_num)
theorem B2784901 : Blo 1649524 2784901 := bbase (se 4 (by rfl) ⟨261084, by rfl⟩ : syracuseStep 2784901 = 522169) (by norm_num)
theorem B16948885 : Blo 1649524 16948885 := bbase (se 6 (by rfl) ⟨397239, by rfl⟩ : syracuseStep 16948885 = 794479) (by norm_num)
theorem B2973341 : Blo 1649524 2973341 := bbase (se 3 (by rfl) ⟨557501, by rfl⟩ : syracuseStep 2973341 = 1115003) (by norm_num)
theorem B2088605 : Blo 1649524 2088605 := bbase (se 3 (by rfl) ⟨391613, by rfl⟩ : syracuseStep 2088605 = 783227) (by norm_num)
theorem B4177565 : Blo 1649524 4177565 := bbase (se 3 (by rfl) ⟨783293, by rfl⟩ : syracuseStep 4177565 = 1566587) (by norm_num)
theorem B2088661 : Blo 1649524 2088661 := bbase (se 7 (by rfl) ⟨24476, by rfl⟩ : syracuseStep 2088661 = 48953) (by norm_num)
theorem B5570261 : Blo 1649524 5570261 := bbase (se 7 (by rfl) ⟨65276, by rfl⟩ : syracuseStep 5570261 = 130553) (by norm_num)
theorem B2784989 : Blo 1649524 2784989 := bbase (se 3 (by rfl) ⟨522185, by rfl⟩ : syracuseStep 2784989 = 1044371) (by norm_num)
theorem B2088757 : Blo 1649524 2088757 := bbase (se 5 (by rfl) ⟨97910, by rfl⟩ : syracuseStep 2088757 = 195821) (by norm_num)
theorem B2785117 : Blo 1649524 2785117 := bbase (se 3 (by rfl) ⟨522209, by rfl⟩ : syracuseStep 2785117 = 1044419) (by norm_num)
theorem B4177757 : Blo 1649524 4177757 := bbase (se 3 (by rfl) ⟨783329, by rfl⟩ : syracuseStep 4177757 = 1566659) (by norm_num)
theorem B3964781 : Blo 1649524 3964781 := bbase (se 3 (by rfl) ⟨743396, by rfl⟩ : syracuseStep 3964781 = 1486793) (by norm_num)
theorem B2350957 : Blo 1649524 2350957 := bbase (se 3 (by rfl) ⟨440804, by rfl⟩ : syracuseStep 2350957 = 881609) (by norm_num)
theorem B5021573 : Blo 1649524 5021573 := bbase (se 4 (by rfl) ⟨470772, by rfl⟩ : syracuseStep 5021573 = 941545) (by norm_num)
theorem B5947285 : Blo 1649524 5947285 := bbase (se 6 (by rfl) ⟨139389, by rfl⟩ : syracuseStep 5947285 = 278779) (by norm_num)
theorem B2785205 : Blo 1649524 2785205 := bbase (se 5 (by rfl) ⟨130556, by rfl⟩ : syracuseStep 2785205 = 261113) (by norm_num)
theorem B8355797 : Blo 1649524 8355797 := bbase (se 7 (by rfl) ⟨97919, by rfl⟩ : syracuseStep 8355797 = 195839) (by norm_num)
theorem B2088929 : Blo 1649524 2088929 := bbase (se 2 (by rfl) ⟨783348, by rfl⟩ : syracuseStep 2088929 = 1566697) (by norm_num)
theorem B2785313 : Blo 1649524 2785313 := bstep (se 2 (by rfl) ⟨1044492, by rfl⟩ : syracuseStep 2785313 = 2088985) B2088985
theorem B3964963 : Blo 1649524 3964963 := bstep (se 1 (by rfl) ⟨2973722, by rfl⟩ : syracuseStep 3964963 = 5947445) B5947445
theorem B1785923 : Blo 1649524 1785923 := bstep (se 1 (by rfl) ⟨1339442, by rfl⟩ : syracuseStep 1785923 = 2678885) B2678885
theorem B4178051 : Blo 1649524 4178051 := bstep (se 1 (by rfl) ⟨3133538, by rfl⟩ : syracuseStep 4178051 = 6267077) B6267077
theorem B2089091 : Blo 1649524 2089091 := bstep (se 1 (by rfl) ⟨1566818, by rfl⟩ : syracuseStep 2089091 = 3133637) B3133637
theorem B2785441 : Blo 1649524 2785441 := bstep (se 2 (by rfl) ⟨1044540, by rfl⟩ : syracuseStep 2785441 = 2089081) B2089081
theorem B2785475 : Blo 1649524 2785475 := bstep (se 1 (by rfl) ⟨2089106, by rfl⟩ : syracuseStep 2785475 = 4178213) B4178213
theorem B5570801 : Blo 1649524 5570801 := bstep (se 2 (by rfl) ⟨2089050, by rfl⟩ : syracuseStep 5570801 = 4178101) B4178101
theorem B11297009 : Blo 1649524 11297009 := bstep (se 2 (by rfl) ⟨4236378, by rfl⟩ : syracuseStep 11297009 = 8472757) B8472757
theorem B18800909 : Blo 1649524 18800909 := bstep (se 3 (by rfl) ⟨3525170, by rfl⟩ : syracuseStep 18800909 = 7050341) B7050341
theorem B2474291 : Blo 1649524 2474291 := bstep (se 1 (by rfl) ⟨1855718, by rfl⟩ : syracuseStep 2474291 = 3711437) B3711437
theorem B4178243 : Blo 1649524 4178243 := bstep (se 1 (by rfl) ⟨3133682, by rfl⟩ : syracuseStep 4178243 = 6267365) B6267365
theorem B2785603 : Blo 1649524 2785603 := bstep (se 1 (by rfl) ⟨2089202, by rfl⟩ : syracuseStep 2785603 = 4178405) B4178405
theorem B2474321 : Blo 1649524 2474321 := bstep (se 2 (by rfl) ⟨927870, by rfl⟩ : syracuseStep 2474321 = 1855741) B1855741
theorem B4522321 : Blo 1649524 4522321 := bstep (se 2 (by rfl) ⟨1695870, by rfl⟩ : syracuseStep 4522321 = 3391741) B3391741
theorem B2474339 : Blo 1649524 2474339 := bstep (se 1 (by rfl) ⟨1855754, by rfl⟩ : syracuseStep 2474339 = 3711509) B3711509
theorem B2474369 : Blo 1649524 2474369 := bstep (se 2 (by rfl) ⟨927888, by rfl⟩ : syracuseStep 2474369 = 1855777) B1855777
theorem B2474387 : Blo 1649524 2474387 := bstep (se 1 (by rfl) ⟨1855790, by rfl⟩ : syracuseStep 2474387 = 3711581) B3711581
theorem B2474417 : Blo 1649524 2474417 := bstep (se 2 (by rfl) ⟨927906, by rfl⟩ : syracuseStep 2474417 = 1855813) B1855813
theorem B2474435 : Blo 1649524 2474435 := bstep (se 1 (by rfl) ⟨1855826, by rfl⟩ : syracuseStep 2474435 = 3711653) B3711653
theorem B2785745 : Blo 1649524 2785745 := bstep (se 2 (by rfl) ⟨1044654, by rfl⟩ : syracuseStep 2785745 = 2089309) B2089309
theorem B2474465 : Blo 1649524 2474465 := bstep (se 2 (by rfl) ⟨927924, by rfl⟩ : syracuseStep 2474465 = 1855849) B1855849
theorem B3711473 : Blo 1649524 3711473 := bstep (se 2 (by rfl) ⟨1391802, by rfl⟩ : syracuseStep 3711473 = 2783605) B2783605
theorem B2474483 : Blo 1649524 2474483 := bstep (se 1 (by rfl) ⟨1855862, by rfl⟩ : syracuseStep 2474483 = 3711725) B3711725
theorem B3711491 : Blo 1649524 3711491 := bstep (se 1 (by rfl) ⟨2783618, by rfl⟩ : syracuseStep 3711491 = 5567237) B5567237
theorem B2474513 : Blo 1649524 2474513 := bstep (se 2 (by rfl) ⟨927942, by rfl⟩ : syracuseStep 2474513 = 1855885) B1855885
theorem B2474531 : Blo 1649524 2474531 := bstep (se 1 (by rfl) ⟨1855898, by rfl⟩ : syracuseStep 2474531 = 3711797) B3711797
theorem B4702769 : Blo 1649524 4702769 := bstep (se 2 (by rfl) ⟨1763538, by rfl⟩ : syracuseStep 4702769 = 3527077) B3527077
theorem B2474561 : Blo 1649524 2474561 := bstep (se 2 (by rfl) ⟨927960, by rfl⟩ : syracuseStep 2474561 = 1855921) B1855921
theorem B2785873 : Blo 1649524 2785873 := bstep (se 2 (by rfl) ⟨1044702, by rfl⟩ : syracuseStep 2785873 = 2089405) B2089405
theorem B2474579 : Blo 1649524 2474579 := bstep (se 1 (by rfl) ⟨1855934, by rfl⟩ : syracuseStep 2474579 = 3711869) B3711869
theorem B2474609 : Blo 1649524 2474609 := bstep (se 2 (by rfl) ⟨927978, by rfl⟩ : syracuseStep 2474609 = 1855957) B1855957
theorem B2785907 : Blo 1649524 2785907 := bstep (se 1 (by rfl) ⟨2089430, by rfl⟩ : syracuseStep 2785907 = 4178861) B4178861
theorem B2474627 : Blo 1649524 2474627 := bstep (se 1 (by rfl) ⟨1855970, by rfl⟩ : syracuseStep 2474627 = 3711941) B3711941
theorem B7053965 : Blo 1649524 7053965 := bstep (se 3 (by rfl) ⟨1322618, by rfl⟩ : syracuseStep 7053965 = 2645237) B2645237
theorem B2474657 : Blo 1649524 2474657 := bstep (se 2 (by rfl) ⟨927996, by rfl⟩ : syracuseStep 2474657 = 1855993) B1855993
theorem B2474675 : Blo 1649524 2474675 := bstep (se 1 (by rfl) ⟨1856006, by rfl⟩ : syracuseStep 2474675 = 3712013) B3712013
theorem B2474705 : Blo 1649524 2474705 := bstep (se 2 (by rfl) ⟨928014, by rfl⟩ : syracuseStep 2474705 = 1856029) B1856029
theorem B2474723 : Blo 1649524 2474723 := bstep (se 1 (by rfl) ⟨1856042, by rfl⟩ : syracuseStep 2474723 = 3712085) B3712085
theorem B6693617 : Blo 1649524 6693617 := bstep (se 2 (by rfl) ⟨2510106, by rfl⟩ : syracuseStep 6693617 = 5020213) B5020213
theorem B2786035 : Blo 1649524 2786035 := bstep (se 1 (by rfl) ⟨2089526, by rfl⟩ : syracuseStep 2786035 = 4179053) B4179053
theorem B4702961 : Blo 1649524 4702961 := bstep (se 2 (by rfl) ⟨1763610, by rfl⟩ : syracuseStep 4702961 = 3527221) B3527221
theorem B2474753 : Blo 1649524 2474753 := bstep (se 2 (by rfl) ⟨928032, by rfl⟩ : syracuseStep 2474753 = 1856065) B1856065
theorem B5571341 : Blo 1649524 5571341 := bstep (se 3 (by rfl) ⟨1044626, by rfl⟩ : syracuseStep 5571341 = 2089253) B2089253
theorem B3711761 : Blo 1649524 3711761 := bstep (se 2 (by rfl) ⟨1391910, by rfl⟩ : syracuseStep 3711761 = 2783821) B2783821
theorem B2474771 : Blo 1649524 2474771 := bstep (se 1 (by rfl) ⟨1856078, by rfl⟩ : syracuseStep 2474771 = 3712157) B3712157
theorem B3711779 : Blo 1649524 3711779 := bstep (se 1 (by rfl) ⟨2783834, by rfl⟩ : syracuseStep 3711779 = 5567669) B5567669
theorem B2474801 : Blo 1649524 2474801 := bstep (se 2 (by rfl) ⟨928050, by rfl⟩ : syracuseStep 2474801 = 1856101) B1856101
theorem B2474819 : Blo 1649524 2474819 := bstep (se 1 (by rfl) ⟨1856114, by rfl⟩ : syracuseStep 2474819 = 3712229) B3712229
theorem B5571395 : Blo 1649524 5571395 := bstep (se 1 (by rfl) ⟨4178546, by rfl⟩ : syracuseStep 5571395 = 8357093) B8357093
theorem B2089795 : Blo 1649524 2089795 := bstep (se 1 (by rfl) ⟨1567346, by rfl⟩ : syracuseStep 2089795 = 3134693) B3134693
theorem B2474849 : Blo 1649524 2474849 := bstep (se 2 (by rfl) ⟨928068, by rfl⟩ : syracuseStep 2474849 = 1856137) B1856137
theorem B2474867 : Blo 1649524 2474867 := bstep (se 1 (by rfl) ⟨1856150, by rfl⟩ : syracuseStep 2474867 = 3712301) B3712301
theorem B2786177 : Blo 1649524 2786177 := bstep (se 2 (by rfl) ⟨1044816, by rfl⟩ : syracuseStep 2786177 = 2089633) B2089633
theorem B2474897 : Blo 1649524 2474897 := bstep (se 2 (by rfl) ⟨928086, by rfl⟩ : syracuseStep 2474897 = 1856173) B1856173
theorem B2474915 : Blo 1649524 2474915 := bstep (se 1 (by rfl) ⟨1856186, by rfl⟩ : syracuseStep 2474915 = 3712373) B3712373
theorem B2089891 : Blo 1649524 2089891 := bstep (se 1 (by rfl) ⟨1567418, by rfl⟩ : syracuseStep 2089891 = 3134837) B3134837
theorem B2474945 : Blo 1649524 2474945 := bstep (se 2 (by rfl) ⟨928104, by rfl⟩ : syracuseStep 2474945 = 1856209) B1856209
theorem B2474963 : Blo 1649524 2474963 := bstep (se 1 (by rfl) ⟨1856222, by rfl⟩ : syracuseStep 2474963 = 3712445) B3712445
theorem B5284835 : Blo 1649524 5284835 := bstep (se 1 (by rfl) ⟨3963626, by rfl⟩ : syracuseStep 5284835 = 7927253) B7927253
theorem B2474993 : Blo 1649524 2474993 := bstep (se 2 (by rfl) ⟨928122, by rfl⟩ : syracuseStep 2474993 = 1856245) B1856245
theorem B2786305 : Blo 1649524 2786305 := bstep (se 2 (by rfl) ⟨1044864, by rfl⟩ : syracuseStep 2786305 = 2089729) B2089729
theorem B2475011 : Blo 1649524 2475011 := bstep (se 1 (by rfl) ⟨1856258, by rfl⟩ : syracuseStep 2475011 = 3712517) B3712517
theorem B2475041 : Blo 1649524 2475041 := bstep (se 2 (by rfl) ⟨928140, by rfl⟩ : syracuseStep 2475041 = 1856281) B1856281
theorem B2786339 : Blo 1649524 2786339 := bstep (se 1 (by rfl) ⟨2089754, by rfl⟩ : syracuseStep 2786339 = 4179509) B4179509
theorem B3712049 : Blo 1649524 3712049 := bstep (se 2 (by rfl) ⟨1392018, by rfl⟩ : syracuseStep 3712049 = 2784037) B2784037
theorem B2475059 : Blo 1649524 2475059 := bstep (se 1 (by rfl) ⟨1856294, by rfl⟩ : syracuseStep 2475059 = 3712589) B3712589
theorem B1762355 : Blo 1649524 1762355 := bstep (se 1 (by rfl) ⟨1321766, by rfl⟩ : syracuseStep 1762355 = 2643533) B2643533
theorem B3712067 : Blo 1649524 3712067 := bstep (se 1 (by rfl) ⟨2784050, by rfl⟩ : syracuseStep 3712067 = 5568101) B5568101
theorem B2475089 : Blo 1649524 2475089 := bstep (se 2 (by rfl) ⟨928158, by rfl⟩ : syracuseStep 2475089 = 1856317) B1856317
theorem B5571665 : Blo 1649524 5571665 := bstep (se 2 (by rfl) ⟨2089374, by rfl⟩ : syracuseStep 5571665 = 4178749) B4178749
theorem B2475107 : Blo 1649524 2475107 := bstep (se 1 (by rfl) ⟨1856330, by rfl⟩ : syracuseStep 2475107 = 3712661) B3712661
theorem B2475137 : Blo 1649524 2475137 := bstep (se 2 (by rfl) ⟨928176, by rfl⟩ : syracuseStep 2475137 = 1856353) B1856353
theorem B12698765 : Blo 1649524 12698765 := bstep (se 3 (by rfl) ⟨2381018, by rfl⟩ : syracuseStep 12698765 = 4762037) B4762037
theorem B2475155 : Blo 1649524 2475155 := bstep (se 1 (by rfl) ⟨1856366, by rfl⟩ : syracuseStep 2475155 = 3712733) B3712733
theorem B2786467 : Blo 1649524 2786467 := bstep (se 1 (by rfl) ⟨2089850, by rfl⟩ : syracuseStep 2786467 = 4179701) B4179701
theorem B2475185 : Blo 1649524 2475185 := bstep (se 2 (by rfl) ⟨928194, by rfl⟩ : syracuseStep 2475185 = 1856389) B1856389
theorem B2974897 : Blo 1649524 2974897 := bstep (se 2 (by rfl) ⟨1115586, by rfl⟩ : syracuseStep 2974897 = 2231173) B2231173
theorem B1762483 : Blo 1649524 1762483 := bstep (se 1 (by rfl) ⟨1321862, by rfl⟩ : syracuseStep 1762483 = 2643725) B2643725
theorem B2475203 : Blo 1649524 2475203 := bstep (se 1 (by rfl) ⟨1856402, by rfl⟩ : syracuseStep 2475203 = 3712805) B3712805
theorem B2475233 : Blo 1649524 2475233 := bstep (se 2 (by rfl) ⟨928212, by rfl⟩ : syracuseStep 2475233 = 1856425) B1856425
theorem B2229475 : Blo 1649524 2229475 := bstep (se 1 (by rfl) ⟨1672106, by rfl⟩ : syracuseStep 2229475 = 3344213) B3344213
theorem B3966193 : Blo 1649524 3966193 := bstep (se 2 (by rfl) ⟨1487322, by rfl⟩ : syracuseStep 3966193 = 2974645) B2974645
theorem B4179185 : Blo 1649524 4179185 := bstep (se 2 (by rfl) ⟨1567194, by rfl⟩ : syracuseStep 4179185 = 3134389) B3134389
theorem B2475251 : Blo 1649524 2475251 := bstep (se 1 (by rfl) ⟨1856438, by rfl⟩ : syracuseStep 2475251 = 3712877) B3712877
theorem B2475281 : Blo 1649524 2475281 := bstep (se 2 (by rfl) ⟨928230, by rfl⟩ : syracuseStep 2475281 = 1856461) B1856461
theorem B2475299 : Blo 1649524 2475299 := bstep (se 1 (by rfl) ⟨1856474, by rfl⟩ : syracuseStep 2475299 = 3712949) B3712949
theorem B4179235 : Blo 1649524 4179235 := bstep (se 1 (by rfl) ⟨3134426, by rfl⟩ : syracuseStep 4179235 = 6268853) B6268853
theorem B2860337 : Blo 1649524 2860337 := bstep (se 2 (by rfl) ⟨1072626, by rfl⟩ : syracuseStep 2860337 = 2145253) B2145253
theorem B2786609 : Blo 1649524 2786609 := bstep (se 2 (by rfl) ⟨1044978, by rfl⟩ : syracuseStep 2786609 = 2089957) B2089957
theorem B2475329 : Blo 1649524 2475329 := bstep (se 2 (by rfl) ⟨928248, by rfl⟩ : syracuseStep 2475329 = 1856497) B1856497
theorem B3523907 : Blo 1649524 3523907 := bstep (se 1 (by rfl) ⟨2642930, by rfl⟩ : syracuseStep 3523907 = 5285861) B5285861
theorem B3712337 : Blo 1649524 3712337 := bstep (se 2 (by rfl) ⟨1392126, by rfl⟩ : syracuseStep 3712337 = 2784253) B2784253
theorem B2475347 : Blo 1649524 2475347 := bstep (se 1 (by rfl) ⟨1856510, by rfl⟩ : syracuseStep 2475347 = 3713021) B3713021
theorem B3712355 : Blo 1649524 3712355 := bstep (se 1 (by rfl) ⟨2784266, by rfl⟩ : syracuseStep 3712355 = 5568533) B5568533
theorem B2475377 : Blo 1649524 2475377 := bstep (se 2 (by rfl) ⟨928266, by rfl⟩ : syracuseStep 2475377 = 1856533) B1856533
theorem B2475395 : Blo 1649524 2475395 := bstep (se 1 (by rfl) ⟨1856546, by rfl⟩ : syracuseStep 2475395 = 3713093) B3713093
theorem B2475425 : Blo 1649524 2475425 := bstep (se 2 (by rfl) ⟨928284, by rfl⟩ : syracuseStep 2475425 = 1856569) B1856569
theorem B6268337 : Blo 1649524 6268337 := bstep (se 2 (by rfl) ⟨2350626, by rfl⟩ : syracuseStep 6268337 = 4701253) B4701253
theorem B4179377 : Blo 1649524 4179377 := bstep (se 2 (by rfl) ⟨1567266, by rfl⟩ : syracuseStep 4179377 = 3134533) B3134533
theorem B2475443 : Blo 1649524 2475443 := bstep (se 1 (by rfl) ⟨1856582, by rfl⟩ : syracuseStep 2475443 = 3713165) B3713165
theorem B2786737 : Blo 1649524 2786737 := bstep (se 2 (by rfl) ⟨1045026, by rfl⟩ : syracuseStep 2786737 = 2090053) B2090053
theorem B2475473 : Blo 1649524 2475473 := bstep (se 2 (by rfl) ⟨928302, by rfl⟩ : syracuseStep 2475473 = 1856605) B1856605
theorem B2786771 : Blo 1649524 2786771 := bstep (se 1 (by rfl) ⟨2090078, by rfl⟩ : syracuseStep 2786771 = 4180157) B4180157
theorem B2475491 : Blo 1649524 2475491 := bstep (se 1 (by rfl) ⟨1856618, by rfl⟩ : syracuseStep 2475491 = 3713237) B3713237
theorem B2475521 : Blo 1649524 2475521 := bstep (se 2 (by rfl) ⟨928320, by rfl⟩ : syracuseStep 2475521 = 1856641) B1856641
theorem B2475539 : Blo 1649524 2475539 := bstep (se 1 (by rfl) ⟨1856654, by rfl⟩ : syracuseStep 2475539 = 3713309) B3713309
theorem B1984019 : Blo 1649524 1984019 := bstep (se 1 (by rfl) ⟨1488014, by rfl⟩ : syracuseStep 1984019 = 2976029) B2976029
theorem B5285425 : Blo 1649524 5285425 := bstep (se 2 (by rfl) ⟨1982034, by rfl⟩ : syracuseStep 5285425 = 3964069) B3964069
theorem B2475569 : Blo 1649524 2475569 := bstep (se 2 (by rfl) ⟨928338, by rfl⟩ : syracuseStep 2475569 = 1856677) B1856677
theorem B2475587 : Blo 1649524 2475587 := bstep (se 1 (by rfl) ⟨1856690, by rfl⟩ : syracuseStep 2475587 = 3713381) B3713381
theorem B2786899 : Blo 1649524 2786899 := bstep (se 1 (by rfl) ⟨2090174, by rfl⟩ : syracuseStep 2786899 = 4180349) B4180349
theorem B2475617 : Blo 1649524 2475617 := bstep (se 2 (by rfl) ⟨928356, by rfl⟩ : syracuseStep 2475617 = 1856713) B1856713
theorem B5572205 : Blo 1649524 5572205 := bstep (se 3 (by rfl) ⟨1044788, by rfl⟩ : syracuseStep 5572205 = 2089577) B2089577
theorem B3712625 : Blo 1649524 3712625 := bstep (se 2 (by rfl) ⟨1392234, by rfl⟩ : syracuseStep 3712625 = 2784469) B2784469
theorem B2475635 : Blo 1649524 2475635 := bstep (se 1 (by rfl) ⟨1856726, by rfl⟩ : syracuseStep 2475635 = 3713453) B3713453
theorem B3712643 : Blo 1649524 3712643 := bstep (se 1 (by rfl) ⟨2784482, by rfl⟩ : syracuseStep 3712643 = 5568965) B5568965
theorem B11298437 : Blo 1649524 11298437 := bstep (se 4 (by rfl) ⟨1059228, by rfl⟩ : syracuseStep 11298437 = 2118457) B2118457
theorem B2475665 : Blo 1649524 2475665 := bstep (se 2 (by rfl) ⟨928374, by rfl⟩ : syracuseStep 2475665 = 1856749) B1856749
theorem B2508451 : Blo 1649524 2508451 := bstep (se 1 (by rfl) ⟨1881338, by rfl⟩ : syracuseStep 2508451 = 3762677) B3762677
theorem B2475683 : Blo 1649524 2475683 := bstep (se 1 (by rfl) ⟨1856762, by rfl⟩ : syracuseStep 2475683 = 3713525) B3713525
theorem B5572259 : Blo 1649524 5572259 := bstep (se 1 (by rfl) ⟨4179194, by rfl⟩ : syracuseStep 5572259 = 8358389) B8358389
theorem B2475713 : Blo 1649524 2475713 := bstep (se 2 (by rfl) ⟨928392, by rfl⟩ : syracuseStep 2475713 = 1856785) B1856785
theorem B2475731 : Blo 1649524 2475731 := bstep (se 1 (by rfl) ⟨1856798, by rfl⟩ : syracuseStep 2475731 = 3713597) B3713597
theorem B2975459 : Blo 1649524 2975459 := bstep (se 1 (by rfl) ⟨2231594, by rfl⟩ : syracuseStep 2975459 = 4463189) B4463189
theorem B2475761 : Blo 1649524 2475761 := bstep (se 2 (by rfl) ⟨928410, by rfl⟩ : syracuseStep 2475761 = 1856821) B1856821
theorem B2475779 : Blo 1649524 2475779 := bstep (se 1 (by rfl) ⟨1856834, by rfl⟩ : syracuseStep 2475779 = 3713669) B3713669
theorem B2475809 : Blo 1649524 2475809 := bstep (se 2 (by rfl) ⟨928428, by rfl⟩ : syracuseStep 2475809 = 1856857) B1856857
theorem B2475827 : Blo 1649524 2475827 := bstep (se 1 (by rfl) ⟨1856870, by rfl⟩ : syracuseStep 2475827 = 3713741) B3713741
theorem B3524419 : Blo 1649524 3524419 := bstep (se 1 (by rfl) ⟨2643314, by rfl⟩ : syracuseStep 3524419 = 5286629) B5286629
theorem B2475857 : Blo 1649524 2475857 := bstep (se 2 (by rfl) ⟨928446, by rfl⟩ : syracuseStep 2475857 = 1856893) B1856893
theorem B2475875 : Blo 1649524 2475875 := bstep (se 1 (by rfl) ⟨1856906, by rfl⟩ : syracuseStep 2475875 = 3713813) B3713813
theorem B13387619 : Blo 1649524 13387619 := bstep (se 1 (by rfl) ⟨10040714, by rfl⟩ : syracuseStep 13387619 = 20081429) B20081429
theorem B2475905 : Blo 1649524 2475905 := bstep (se 2 (by rfl) ⟨928464, by rfl⟩ : syracuseStep 2475905 = 1856929) B1856929
theorem B7931789 : Blo 1649524 7931789 := bstep (se 3 (by rfl) ⟨1487210, by rfl⟩ : syracuseStep 7931789 = 2974421) B2974421
theorem B2508689 : Blo 1649524 2508689 := bstep (se 2 (by rfl) ⟨940758, by rfl⟩ : syracuseStep 2508689 = 1881517) B1881517
theorem B3712913 : Blo 1649524 3712913 := bstep (se 2 (by rfl) ⟨1392342, by rfl⟩ : syracuseStep 3712913 = 2784685) B2784685
theorem B2475923 : Blo 1649524 2475923 := bstep (se 1 (by rfl) ⟨1856942, by rfl⟩ : syracuseStep 2475923 = 3713885) B3713885
theorem B3712931 : Blo 1649524 3712931 := bstep (se 1 (by rfl) ⟨2784698, by rfl⟩ : syracuseStep 3712931 = 5569397) B5569397
theorem B2475953 : Blo 1649524 2475953 := bstep (se 2 (by rfl) ⟨928482, by rfl⟩ : syracuseStep 2475953 = 1856965) B1856965
theorem B5572529 : Blo 1649524 5572529 := bstep (se 2 (by rfl) ⟨2089698, by rfl⟩ : syracuseStep 5572529 = 4179397) B4179397
theorem B2475971 : Blo 1649524 2475971 := bstep (se 1 (by rfl) ⟨1856978, by rfl⟩ : syracuseStep 2475971 = 3713957) B3713957
theorem B2476001 : Blo 1649524 2476001 := bstep (se 2 (by rfl) ⟨928500, by rfl⟩ : syracuseStep 2476001 = 1857001) B1857001
theorem B1763299 : Blo 1649524 1763299 := bstep (se 1 (by rfl) ⟨1322474, by rfl⟩ : syracuseStep 1763299 = 2644949) B2644949
theorem B2476019 : Blo 1649524 2476019 := bstep (se 1 (by rfl) ⟨1857014, by rfl⟩ : syracuseStep 2476019 = 3714029) B3714029
theorem B2476049 : Blo 1649524 2476049 := bstep (se 2 (by rfl) ⟨928518, by rfl⟩ : syracuseStep 2476049 = 1857037) B1857037
theorem B2476067 : Blo 1649524 2476067 := bstep (se 1 (by rfl) ⟨1857050, by rfl⟩ : syracuseStep 2476067 = 3714101) B3714101
theorem B2009155 : Blo 1649524 2009155 := bstep (se 1 (by rfl) ⟨1506866, by rfl⟩ : syracuseStep 2009155 = 3013733) B3013733
theorem B2476097 : Blo 1649524 2476097 := bstep (se 2 (by rfl) ⟨928536, by rfl⟩ : syracuseStep 2476097 = 1857073) B1857073
theorem B2476115 : Blo 1649524 2476115 := bstep (se 1 (by rfl) ⟨1857086, by rfl⟩ : syracuseStep 2476115 = 3714173) B3714173
theorem B2476145 : Blo 1649524 2476145 := bstep (se 2 (by rfl) ⟨928554, by rfl⟩ : syracuseStep 2476145 = 1857109) B1857109
theorem B2476163 : Blo 1649524 2476163 := bstep (se 1 (by rfl) ⟨1857122, by rfl⟩ : syracuseStep 2476163 = 3714245) B3714245
theorem B2680963 : Blo 1649524 2680963 := bstep (se 1 (by rfl) ⟨2010722, by rfl⟩ : syracuseStep 2680963 = 4021445) B4021445
theorem B2476193 : Blo 1649524 2476193 := bstep (se 2 (by rfl) ⟨928572, by rfl⟩ : syracuseStep 2476193 = 1857145) B1857145
theorem B3713201 : Blo 1649524 3713201 := bstep (se 2 (by rfl) ⟨1392450, by rfl⟩ : syracuseStep 3713201 = 2784901) B2784901
theorem B8358065 : Blo 1649524 8358065 := bstep (se 2 (by rfl) ⟨3134274, by rfl⟩ : syracuseStep 8358065 = 6268549) B6268549
theorem B2476211 : Blo 1649524 2476211 := bstep (se 1 (by rfl) ⟨1857158, by rfl⟩ : syracuseStep 2476211 = 3714317) B3714317
theorem B3713219 : Blo 1649524 3713219 := bstep (se 1 (by rfl) ⟨2784914, by rfl⟩ : syracuseStep 3713219 = 5569829) B5569829
theorem B2230465 : Blo 1649524 2230465 := bstep (se 2 (by rfl) ⟨836424, by rfl⟩ : syracuseStep 2230465 = 1672849) B1672849
theorem B2476241 : Blo 1649524 2476241 := bstep (se 2 (by rfl) ⟨928590, by rfl⟩ : syracuseStep 2476241 = 1857181) B1857181
theorem B2476259 : Blo 1649524 2476259 := bstep (se 1 (by rfl) ⟨1857194, by rfl⟩ : syracuseStep 2476259 = 3714389) B3714389
theorem B2476289 : Blo 1649524 2476289 := bstep (se 2 (by rfl) ⟨928608, by rfl⟩ : syracuseStep 2476289 = 1857217) B1857217
theorem B2476307 : Blo 1649524 2476307 := bstep (se 1 (by rfl) ⟨1857230, by rfl⟩ : syracuseStep 2476307 = 3714461) B3714461
theorem B2476337 : Blo 1649524 2476337 := bstep (se 2 (by rfl) ⟨928626, by rfl⟩ : syracuseStep 2476337 = 1857253) B1857253
theorem B2476355 : Blo 1649524 2476355 := bstep (se 1 (by rfl) ⟨1857266, by rfl⟩ : syracuseStep 2476355 = 3714533) B3714533
theorem B2476385 : Blo 1649524 2476385 := bstep (se 2 (by rfl) ⟨928644, by rfl⟩ : syracuseStep 2476385 = 1857289) B1857289
theorem B2476403 : Blo 1649524 2476403 := bstep (se 1 (by rfl) ⟨1857302, by rfl⟩ : syracuseStep 2476403 = 3714605) B3714605
theorem B2476433 : Blo 1649524 2476433 := bstep (se 2 (by rfl) ⟨928662, by rfl⟩ : syracuseStep 2476433 = 1857325) B1857325
theorem B4180369 : Blo 1649524 4180369 := bstep (se 2 (by rfl) ⟨1567638, by rfl⟩ : syracuseStep 4180369 = 3135277) B3135277
theorem B2476451 : Blo 1649524 2476451 := bstep (se 1 (by rfl) ⟨1857338, by rfl⟩ : syracuseStep 2476451 = 3714677) B3714677
theorem B2476481 : Blo 1649524 2476481 := bstep (se 2 (by rfl) ⟨928680, by rfl⟩ : syracuseStep 2476481 = 1857361) B1857361
theorem B5573069 : Blo 1649524 5573069 := bstep (se 3 (by rfl) ⟨1044950, by rfl⟩ : syracuseStep 5573069 = 2089901) B2089901
theorem B3713489 : Blo 1649524 3713489 := bstep (se 2 (by rfl) ⟨1392558, by rfl⟩ : syracuseStep 3713489 = 2785117) B2785117
theorem B2476499 : Blo 1649524 2476499 := bstep (se 1 (by rfl) ⟨1857374, by rfl⟩ : syracuseStep 2476499 = 3714749) B3714749
theorem B3131875 : Blo 1649524 3131875 := bstep (se 1 (by rfl) ⟨2348906, by rfl⟩ : syracuseStep 3131875 = 4697813) B4697813
theorem B3713507 : Blo 1649524 3713507 := bstep (se 1 (by rfl) ⟨2785130, by rfl⟩ : syracuseStep 3713507 = 5570261) B5570261
theorem B2476529 : Blo 1649524 2476529 := bstep (se 2 (by rfl) ⟨928698, by rfl⟩ : syracuseStep 2476529 = 1857397) B1857397
theorem B2476547 : Blo 1649524 2476547 := bstep (se 1 (by rfl) ⟨1857410, by rfl⟩ : syracuseStep 2476547 = 3714821) B3714821
theorem B5573123 : Blo 1649524 5573123 := bstep (se 1 (by rfl) ⟨4179842, by rfl⟩ : syracuseStep 5573123 = 8359685) B8359685
theorem B10578437 : Blo 1649524 10578437 := bstep (se 4 (by rfl) ⟨991728, by rfl⟩ : syracuseStep 10578437 = 1983457) B1983457
theorem B3131921 : Blo 1649524 3131921 := bstep (se 2 (by rfl) ⟨1174470, by rfl⟩ : syracuseStep 3131921 = 2348941) B2348941
theorem B3525137 : Blo 1649524 3525137 := bstep (se 2 (by rfl) ⟨1321926, by rfl⟩ : syracuseStep 3525137 = 2643853) B2643853
theorem B2476577 : Blo 1649524 2476577 := bstep (se 2 (by rfl) ⟨928716, by rfl⟩ : syracuseStep 2476577 = 1857433) B1857433
theorem B2476595 : Blo 1649524 2476595 := bstep (se 1 (by rfl) ⟨1857446, by rfl⟩ : syracuseStep 2476595 = 3714893) B3714893
theorem B18795077 : Blo 1649524 18795077 := bstep (se 4 (by rfl) ⟨1762038, by rfl⟩ : syracuseStep 18795077 = 3524077) B3524077
theorem B9398861 : Blo 1649524 9398861 := bstep (se 3 (by rfl) ⟨1762286, by rfl⟩ : syracuseStep 9398861 = 3524573) B3524573
theorem B2476625 : Blo 1649524 2476625 := bstep (se 2 (by rfl) ⟨928734, by rfl⟩ : syracuseStep 2476625 = 1857469) B1857469
theorem B2476643 : Blo 1649524 2476643 := bstep (se 1 (by rfl) ⟨1857482, by rfl⟩ : syracuseStep 2476643 = 3714965) B3714965
theorem B2476673 : Blo 1649524 2476673 := bstep (se 2 (by rfl) ⟨928752, by rfl⟩ : syracuseStep 2476673 = 1857505) B1857505
theorem B2476691 : Blo 1649524 2476691 := bstep (se 1 (by rfl) ⟨1857518, by rfl⟩ : syracuseStep 2476691 = 3715037) B3715037
theorem B2476721 : Blo 1649524 2476721 := bstep (se 2 (by rfl) ⟨928770, by rfl⟩ : syracuseStep 2476721 = 1857541) B1857541
theorem B2476739 : Blo 1649524 2476739 := bstep (se 1 (by rfl) ⟨1857554, by rfl⟩ : syracuseStep 2476739 = 3715109) B3715109
theorem B2476769 : Blo 1649524 2476769 := bstep (se 2 (by rfl) ⟨928788, by rfl⟩ : syracuseStep 2476769 = 1857577) B1857577
theorem B20064995 : Blo 1649524 20064995 := bstep (se 1 (by rfl) ⟨15048746, by rfl⟩ : syracuseStep 20064995 = 30097493) B30097493
theorem B2231011 : Blo 1649524 2231011 := bstep (se 1 (by rfl) ⟨1673258, by rfl⟩ : syracuseStep 2231011 = 3346517) B3346517
theorem B3713777 : Blo 1649524 3713777 := bstep (se 2 (by rfl) ⟨1392666, by rfl⟩ : syracuseStep 3713777 = 2785333) B2785333
theorem B2476787 : Blo 1649524 2476787 := bstep (se 1 (by rfl) ⟨1857590, by rfl⟩ : syracuseStep 2476787 = 3715181) B3715181
theorem B3713795 : Blo 1649524 3713795 := bstep (se 1 (by rfl) ⟨2785346, by rfl⟩ : syracuseStep 3713795 = 5570693) B5570693
theorem B2476817 : Blo 1649524 2476817 := bstep (se 2 (by rfl) ⟨928806, by rfl⟩ : syracuseStep 2476817 = 1857613) B1857613
theorem B5573393 : Blo 1649524 5573393 := bstep (se 2 (by rfl) ⟨2090022, by rfl⟩ : syracuseStep 5573393 = 4180045) B4180045
theorem B2476835 : Blo 1649524 2476835 := bstep (se 1 (by rfl) ⟨1857626, by rfl⟩ : syracuseStep 2476835 = 3715253) B3715253
theorem B3132209 : Blo 1649524 3132209 := bstep (se 2 (by rfl) ⟨1174578, by rfl⟩ : syracuseStep 3132209 = 2349157) B2349157
theorem B28207925 : Blo 1649524 28207925 := bstep (se 5 (by rfl) ⟨1322246, by rfl⟩ : syracuseStep 28207925 = 2644493) B2644493
theorem B2476865 : Blo 1649524 2476865 := bstep (se 2 (by rfl) ⟨928824, by rfl⟩ : syracuseStep 2476865 = 1857649) B1857649
theorem B2476883 : Blo 1649524 2476883 := bstep (se 1 (by rfl) ⟨1857662, by rfl⟩ : syracuseStep 2476883 = 3715325) B3715325
theorem B6269795 : Blo 1649524 6269795 := bstep (se 1 (by rfl) ⟨4702346, by rfl⟩ : syracuseStep 6269795 = 9404693) B9404693
theorem B2476913 : Blo 1649524 2476913 := bstep (se 2 (by rfl) ⟨928842, by rfl⟩ : syracuseStep 2476913 = 1857685) B1857685
theorem B1649539 : Blo 1649524 1649539 := bstep (se 1 (by rfl) ⟨1237154, by rfl⟩ : syracuseStep 1649539 = 2474309) B2474309
theorem B2476931 : Blo 1649524 2476931 := bstep (se 1 (by rfl) ⟨1857698, by rfl⟩ : syracuseStep 2476931 = 3715397) B3715397
theorem B1649555 : Blo 1649524 1649555 := bstep (se 1 (by rfl) ⟨1237166, by rfl⟩ : syracuseStep 1649555 = 2474333) B2474333
theorem B2476961 : Blo 1649524 2476961 := bstep (se 2 (by rfl) ⟨928860, by rfl⟩ : syracuseStep 2476961 = 1857721) B1857721
theorem B1649571 : Blo 1649524 1649571 := bstep (se 1 (by rfl) ⟨1237178, by rfl⟩ : syracuseStep 1649571 = 2474357) B2474357
theorem B4459427 : Blo 1649524 4459427 := bstep (se 1 (by rfl) ⟨3344570, by rfl⟩ : syracuseStep 4459427 = 6689141) B6689141
theorem B1649587 : Blo 1649524 1649587 := bstep (se 1 (by rfl) ⟨1237190, by rfl⟩ : syracuseStep 1649587 = 2474381) B2474381
theorem B2476979 : Blo 1649524 2476979 := bstep (se 1 (by rfl) ⟨1857734, by rfl⟩ : syracuseStep 2476979 = 3715469) B3715469
theorem B1649603 : Blo 1649524 1649603 := bstep (se 1 (by rfl) ⟨1237202, by rfl⟩ : syracuseStep 1649603 = 2474405) B2474405
theorem B2477009 : Blo 1649524 2477009 := bstep (se 2 (by rfl) ⟨928878, by rfl⟩ : syracuseStep 2477009 = 1857757) B1857757
theorem B1649619 : Blo 1649524 1649619 := bstep (se 1 (by rfl) ⟨1237214, by rfl⟩ : syracuseStep 1649619 = 2474429) B2474429
theorem B1649635 : Blo 1649524 1649635 := bstep (se 1 (by rfl) ⟨1237226, by rfl⟩ : syracuseStep 1649635 = 2474453) B2474453
theorem B2477027 : Blo 1649524 2477027 := bstep (se 1 (by rfl) ⟨1857770, by rfl⟩ : syracuseStep 2477027 = 3715541) B3715541
theorem B1649651 : Blo 1649524 1649651 := bstep (se 1 (by rfl) ⟨1237238, by rfl⟩ : syracuseStep 1649651 = 2474477) B2474477
theorem B2477057 : Blo 1649524 2477057 := bstep (se 2 (by rfl) ⟨928896, by rfl⟩ : syracuseStep 2477057 = 1857793) B1857793
theorem B1649667 : Blo 1649524 1649667 := bstep (se 1 (by rfl) ⟨1237250, by rfl⟩ : syracuseStep 1649667 = 2474501) B2474501
theorem B3714065 : Blo 1649524 3714065 := bstep (se 2 (by rfl) ⟨1392774, by rfl⟩ : syracuseStep 3714065 = 2785549) B2785549
theorem B1649683 : Blo 1649524 1649683 := bstep (se 1 (by rfl) ⟨1237262, by rfl⟩ : syracuseStep 1649683 = 2474525) B2474525
theorem B2477075 : Blo 1649524 2477075 := bstep (se 1 (by rfl) ⟨1857806, by rfl⟩ : syracuseStep 2477075 = 3715613) B3715613
theorem B5016611 : Blo 1649524 5016611 := bstep (se 1 (by rfl) ⟨3762458, by rfl⟩ : syracuseStep 5016611 = 7524917) B7524917
theorem B1649699 : Blo 1649524 1649699 := bstep (se 1 (by rfl) ⟨1237274, by rfl⟩ : syracuseStep 1649699 = 2474549) B2474549
theorem B4459555 : Blo 1649524 4459555 := bstep (se 1 (by rfl) ⟨3344666, by rfl⟩ : syracuseStep 4459555 = 6689333) B6689333
theorem B3714083 : Blo 1649524 3714083 := bstep (se 1 (by rfl) ⟨2785562, by rfl⟩ : syracuseStep 3714083 = 5571125) B5571125
theorem B2477105 : Blo 1649524 2477105 := bstep (se 2 (by rfl) ⟨928914, by rfl⟩ : syracuseStep 2477105 = 1857829) B1857829
theorem B1649715 : Blo 1649524 1649715 := bstep (se 1 (by rfl) ⟨1237286, by rfl⟩ : syracuseStep 1649715 = 2474573) B2474573
theorem B18091061 : Blo 1649524 18091061 := bstep (se 5 (by rfl) ⟨848018, by rfl⟩ : syracuseStep 18091061 = 1696037) B1696037
theorem B1649731 : Blo 1649524 1649731 := bstep (se 1 (by rfl) ⟨1237298, by rfl⟩ : syracuseStep 1649731 = 2474597) B2474597
theorem B2477123 : Blo 1649524 2477123 := bstep (se 1 (by rfl) ⟨1857842, by rfl⟩ : syracuseStep 2477123 = 3715685) B3715685
theorem B15051845 : Blo 1649524 15051845 := bstep (se 4 (by rfl) ⟨1411110, by rfl⟩ : syracuseStep 15051845 = 2822221) B2822221
theorem B1649747 : Blo 1649524 1649747 := bstep (se 1 (by rfl) ⟨1237310, by rfl⟩ : syracuseStep 1649747 = 2474621) B2474621
theorem B2477153 : Blo 1649524 2477153 := bstep (se 2 (by rfl) ⟨928932, by rfl⟩ : syracuseStep 2477153 = 1857865) B1857865
theorem B1649763 : Blo 1649524 1649763 := bstep (se 1 (by rfl) ⟨1237322, by rfl⟩ : syracuseStep 1649763 = 2474645) B2474645
theorem B7048291 : Blo 1649524 7048291 := bstep (se 1 (by rfl) ⟨5286218, by rfl⟩ : syracuseStep 7048291 = 10572437) B10572437
theorem B18803825 : Blo 1649524 18803825 := bstep (se 2 (by rfl) ⟨7051434, by rfl⟩ : syracuseStep 18803825 = 14102869) B14102869
theorem B1649779 : Blo 1649524 1649779 := bstep (se 1 (by rfl) ⟨1237334, by rfl⟩ : syracuseStep 1649779 = 2474669) B2474669
theorem B2477171 : Blo 1649524 2477171 := bstep (se 1 (by rfl) ⟨1857878, by rfl⟩ : syracuseStep 2477171 = 3715757) B3715757
theorem B1649795 : Blo 1649524 1649795 := bstep (se 1 (by rfl) ⟨1237346, by rfl⟩ : syracuseStep 1649795 = 2474693) B2474693
theorem B2509955 : Blo 1649524 2509955 := bstep (se 1 (by rfl) ⟨1882466, by rfl⟩ : syracuseStep 2509955 = 3764933) B3764933
theorem B2477201 : Blo 1649524 2477201 := bstep (se 2 (by rfl) ⟨928950, by rfl⟩ : syracuseStep 2477201 = 1857901) B1857901
theorem B1649811 : Blo 1649524 1649811 := bstep (se 1 (by rfl) ⟨1237358, by rfl⟩ : syracuseStep 1649811 = 2474717) B2474717
theorem B1649827 : Blo 1649524 1649827 := bstep (se 1 (by rfl) ⟨1237370, by rfl⟩ : syracuseStep 1649827 = 2474741) B2474741
theorem B2477219 : Blo 1649524 2477219 := bstep (se 1 (by rfl) ⟨1857914, by rfl⟩ : syracuseStep 2477219 = 3715829) B3715829
theorem B1649843 : Blo 1649524 1649843 := bstep (se 1 (by rfl) ⟨1237382, by rfl⟩ : syracuseStep 1649843 = 2474765) B2474765
theorem B2477249 : Blo 1649524 2477249 := bstep (se 2 (by rfl) ⟨928968, by rfl⟩ : syracuseStep 2477249 = 1857937) B1857937
theorem B1649859 : Blo 1649524 1649859 := bstep (se 1 (by rfl) ⟨1237394, by rfl⟩ : syracuseStep 1649859 = 2474789) B2474789
theorem B13569221 : Blo 1649524 13569221 := bstep (se 4 (by rfl) ⟨1272114, by rfl⟩ : syracuseStep 13569221 = 2544229) B2544229
theorem B1649875 : Blo 1649524 1649875 := bstep (se 1 (by rfl) ⟨1237406, by rfl⟩ : syracuseStep 1649875 = 2474813) B2474813
theorem B2477267 : Blo 1649524 2477267 := bstep (se 1 (by rfl) ⟨1857950, by rfl⟩ : syracuseStep 2477267 = 3715901) B3715901
theorem B1649891 : Blo 1649524 1649891 := bstep (se 1 (by rfl) ⟨1237418, by rfl⟩ : syracuseStep 1649891 = 2474837) B2474837
theorem B1649907 : Blo 1649524 1649907 := bstep (se 1 (by rfl) ⟨1237430, by rfl⟩ : syracuseStep 1649907 = 2474861) B2474861
theorem B1649923 : Blo 1649524 1649923 := bstep (se 1 (by rfl) ⟨1237442, by rfl⟩ : syracuseStep 1649923 = 2474885) B2474885
theorem B1649939 : Blo 1649524 1649939 := bstep (se 1 (by rfl) ⟨1237454, by rfl⟩ : syracuseStep 1649939 = 2474909) B2474909
theorem B1649955 : Blo 1649524 1649955 := bstep (se 1 (by rfl) ⟨1237466, by rfl⟩ : syracuseStep 1649955 = 2474933) B2474933
theorem B3525923 : Blo 1649524 3525923 := bstep (se 1 (by rfl) ⟨2644442, by rfl⟩ : syracuseStep 3525923 = 5288885) B5288885
theorem B3714353 : Blo 1649524 3714353 := bstep (se 2 (by rfl) ⟨1392882, by rfl⟩ : syracuseStep 3714353 = 2785765) B2785765
theorem B1649971 : Blo 1649524 1649971 := bstep (se 1 (by rfl) ⟨1237478, by rfl⟩ : syracuseStep 1649971 = 2474957) B2474957
theorem B1649987 : Blo 1649524 1649987 := bstep (se 1 (by rfl) ⟨1237490, by rfl⟩ : syracuseStep 1649987 = 2474981) B2474981
theorem B3714371 : Blo 1649524 3714371 := bstep (se 1 (by rfl) ⟨2785778, by rfl⟩ : syracuseStep 3714371 = 5571557) B5571557
theorem B1650003 : Blo 1649524 1650003 := bstep (se 1 (by rfl) ⟨1237502, by rfl⟩ : syracuseStep 1650003 = 2475005) B2475005
theorem B1650019 : Blo 1649524 1650019 := bstep (se 1 (by rfl) ⟨1237514, by rfl⟩ : syracuseStep 1650019 = 2475029) B2475029
theorem B1650035 : Blo 1649524 1650035 := bstep (se 1 (by rfl) ⟨1237526, by rfl⟩ : syracuseStep 1650035 = 2475053) B2475053
theorem B1650051 : Blo 1649524 1650051 := bstep (se 1 (by rfl) ⟨1237538, by rfl⟩ : syracuseStep 1650051 = 2475077) B2475077
theorem B1650067 : Blo 1649524 1650067 := bstep (se 1 (by rfl) ⟨1237550, by rfl⟩ : syracuseStep 1650067 = 2475101) B2475101
theorem B1650083 : Blo 1649524 1650083 := bstep (se 1 (by rfl) ⟨1237562, by rfl⟩ : syracuseStep 1650083 = 2475125) B2475125
theorem B1650099 : Blo 1649524 1650099 := bstep (se 1 (by rfl) ⟨1237574, by rfl⟩ : syracuseStep 1650099 = 2475149) B2475149
theorem B1650115 : Blo 1649524 1650115 := bstep (se 1 (by rfl) ⟨1237586, by rfl⟩ : syracuseStep 1650115 = 2475173) B2475173
theorem B10038725 : Blo 1649524 10038725 := bstep (se 4 (by rfl) ⟨941130, by rfl⟩ : syracuseStep 10038725 = 1882261) B1882261
theorem B1650131 : Blo 1649524 1650131 := bstep (se 1 (by rfl) ⟨1237598, by rfl⟩ : syracuseStep 1650131 = 2475197) B2475197
theorem B1650147 : Blo 1649524 1650147 := bstep (se 1 (by rfl) ⟨1237610, by rfl⟩ : syracuseStep 1650147 = 2475221) B2475221
theorem B4697585 : Blo 1649524 4697585 := bstep (se 2 (by rfl) ⟨1761594, by rfl⟩ : syracuseStep 4697585 = 3523189) B3523189
theorem B5361137 : Blo 1649524 5361137 := bstep (se 2 (by rfl) ⟨2010426, by rfl⟩ : syracuseStep 5361137 = 4020853) B4020853
theorem B1650163 : Blo 1649524 1650163 := bstep (se 1 (by rfl) ⟨1237622, by rfl⟩ : syracuseStep 1650163 = 2475245) B2475245
theorem B1650179 : Blo 1649524 1650179 := bstep (se 1 (by rfl) ⟨1237634, by rfl⟩ : syracuseStep 1650179 = 2475269) B2475269
theorem B3132931 : Blo 1649524 3132931 := bstep (se 1 (by rfl) ⟨2349698, by rfl⟩ : syracuseStep 3132931 = 4699397) B4699397
theorem B1650195 : Blo 1649524 1650195 := bstep (se 1 (by rfl) ⟨1237646, by rfl⟩ : syracuseStep 1650195 = 2475293) B2475293
theorem B1650211 : Blo 1649524 1650211 := bstep (se 1 (by rfl) ⟨1237658, by rfl⟩ : syracuseStep 1650211 = 2475317) B2475317
theorem B1650227 : Blo 1649524 1650227 := bstep (se 1 (by rfl) ⟨1237670, by rfl⟩ : syracuseStep 1650227 = 2475341) B2475341
theorem B1650243 : Blo 1649524 1650243 := bstep (se 1 (by rfl) ⟨1237682, by rfl⟩ : syracuseStep 1650243 = 2475365) B2475365
theorem B3714641 : Blo 1649524 3714641 := bstep (se 2 (by rfl) ⟨1392990, by rfl⟩ : syracuseStep 3714641 = 2785981) B2785981
theorem B1650259 : Blo 1649524 1650259 := bstep (se 1 (by rfl) ⟨1237694, by rfl⟩ : syracuseStep 1650259 = 2475389) B2475389
theorem B1650275 : Blo 1649524 1650275 := bstep (se 1 (by rfl) ⟨1237706, by rfl⟩ : syracuseStep 1650275 = 2475413) B2475413
theorem B3714659 : Blo 1649524 3714659 := bstep (se 1 (by rfl) ⟨2785994, by rfl⟩ : syracuseStep 3714659 = 5571989) B5571989
theorem B8359523 : Blo 1649524 8359523 := bstep (se 1 (by rfl) ⟨6269642, by rfl⟩ : syracuseStep 8359523 = 12539285) B12539285
theorem B1650291 : Blo 1649524 1650291 := bstep (se 1 (by rfl) ⟨1237718, by rfl⟩ : syracuseStep 1650291 = 2475437) B2475437
theorem B1650307 : Blo 1649524 1650307 := bstep (se 1 (by rfl) ⟨1237730, by rfl⟩ : syracuseStep 1650307 = 2475461) B2475461
theorem B11292301 : Blo 1649524 11292301 := bstep (se 3 (by rfl) ⟨2117306, by rfl⟩ : syracuseStep 11292301 = 4234613) B4234613
theorem B1650323 : Blo 1649524 1650323 := bstep (se 1 (by rfl) ⟨1237742, by rfl⟩ : syracuseStep 1650323 = 2475485) B2475485
theorem B1650339 : Blo 1649524 1650339 := bstep (se 1 (by rfl) ⟨1237754, by rfl⟩ : syracuseStep 1650339 = 2475509) B2475509
theorem B1650355 : Blo 1649524 1650355 := bstep (se 1 (by rfl) ⟨1237766, by rfl⟩ : syracuseStep 1650355 = 2475533) B2475533
theorem B1650371 : Blo 1649524 1650371 := bstep (se 1 (by rfl) ⟨1237778, by rfl⟩ : syracuseStep 1650371 = 2475557) B2475557
theorem B1650387 : Blo 1649524 1650387 := bstep (se 1 (by rfl) ⟨1237790, by rfl⟩ : syracuseStep 1650387 = 2475581) B2475581
theorem B1650403 : Blo 1649524 1650403 := bstep (se 1 (by rfl) ⟨1237802, by rfl⟩ : syracuseStep 1650403 = 2475605) B2475605
theorem B1650419 : Blo 1649524 1650419 := bstep (se 1 (by rfl) ⟨1237814, by rfl⟩ : syracuseStep 1650419 = 2475629) B2475629
theorem B1650435 : Blo 1649524 1650435 := bstep (se 1 (by rfl) ⟨1237826, by rfl⟩ : syracuseStep 1650435 = 2475653) B2475653
theorem B1650451 : Blo 1649524 1650451 := bstep (se 1 (by rfl) ⟨1237838, by rfl⟩ : syracuseStep 1650451 = 2475677) B2475677
theorem B1650467 : Blo 1649524 1650467 := bstep (se 1 (by rfl) ⟨1237850, by rfl⟩ : syracuseStep 1650467 = 2475701) B2475701
theorem B1650483 : Blo 1649524 1650483 := bstep (se 1 (by rfl) ⟨1237862, by rfl⟩ : syracuseStep 1650483 = 2475725) B2475725
theorem B1650499 : Blo 1649524 1650499 := bstep (se 1 (by rfl) ⟨1237874, by rfl⟩ : syracuseStep 1650499 = 2475749) B2475749
theorem B1650515 : Blo 1649524 1650515 := bstep (se 1 (by rfl) ⟨1237886, by rfl⟩ : syracuseStep 1650515 = 2475773) B2475773
theorem B1650531 : Blo 1649524 1650531 := bstep (se 1 (by rfl) ⟨1237898, by rfl⟩ : syracuseStep 1650531 = 2475797) B2475797
theorem B3346289 : Blo 1649524 3346289 := bstep (se 2 (by rfl) ⟨1254858, by rfl⟩ : syracuseStep 3346289 = 2509717) B2509717
theorem B3714929 : Blo 1649524 3714929 := bstep (se 2 (by rfl) ⟨1393098, by rfl⟩ : syracuseStep 3714929 = 2786197) B2786197
theorem B1650547 : Blo 1649524 1650547 := bstep (se 1 (by rfl) ⟨1237910, by rfl⟩ : syracuseStep 1650547 = 2475821) B2475821
theorem B1650563 : Blo 1649524 1650563 := bstep (se 1 (by rfl) ⟨1237922, by rfl⟩ : syracuseStep 1650563 = 2475845) B2475845
theorem B3714947 : Blo 1649524 3714947 := bstep (se 1 (by rfl) ⟨2786210, by rfl⟩ : syracuseStep 3714947 = 5572421) B5572421
theorem B1650579 : Blo 1649524 1650579 := bstep (se 1 (by rfl) ⟨1237934, by rfl⟩ : syracuseStep 1650579 = 2475869) B2475869
theorem B1650595 : Blo 1649524 1650595 := bstep (se 1 (by rfl) ⟨1237946, by rfl⟩ : syracuseStep 1650595 = 2475893) B2475893
theorem B1650611 : Blo 1649524 1650611 := bstep (se 1 (by rfl) ⟨1237958, by rfl⟩ : syracuseStep 1650611 = 2475917) B2475917
theorem B3133379 : Blo 1649524 3133379 := bstep (se 1 (by rfl) ⟨2350034, by rfl⟩ : syracuseStep 3133379 = 4700069) B4700069
theorem B1650627 : Blo 1649524 1650627 := bstep (se 1 (by rfl) ⟨1237970, by rfl⟩ : syracuseStep 1650627 = 2475941) B2475941
theorem B1650643 : Blo 1649524 1650643 := bstep (se 1 (by rfl) ⟨1237982, by rfl⟩ : syracuseStep 1650643 = 2475965) B2475965
theorem B1650659 : Blo 1649524 1650659 := bstep (se 1 (by rfl) ⟨1237994, by rfl⟩ : syracuseStep 1650659 = 2475989) B2475989
theorem B12537827 : Blo 1649524 12537827 := bstep (se 1 (by rfl) ⟨9403370, by rfl⟩ : syracuseStep 12537827 = 18806741) B18806741
theorem B1650675 : Blo 1649524 1650675 := bstep (se 1 (by rfl) ⟨1238006, by rfl⟩ : syracuseStep 1650675 = 2476013) B2476013
theorem B1650691 : Blo 1649524 1650691 := bstep (se 1 (by rfl) ⟨1238018, by rfl⟩ : syracuseStep 1650691 = 2476037) B2476037
theorem B1650707 : Blo 1649524 1650707 := bstep (se 1 (by rfl) ⟨1238030, by rfl⟩ : syracuseStep 1650707 = 2476061) B2476061
theorem B1650723 : Blo 1649524 1650723 := bstep (se 1 (by rfl) ⟨1238042, by rfl⟩ : syracuseStep 1650723 = 2476085) B2476085
theorem B1650739 : Blo 1649524 1650739 := bstep (se 1 (by rfl) ⟨1238054, by rfl⟩ : syracuseStep 1650739 = 2476109) B2476109
theorem B26783797 : Blo 1649524 26783797 := bstep (se 5 (by rfl) ⟨1255490, by rfl⟩ : syracuseStep 26783797 = 2510981) B2510981
theorem B1650755 : Blo 1649524 1650755 := bstep (se 1 (by rfl) ⟨1238066, by rfl⟩ : syracuseStep 1650755 = 2476133) B2476133
theorem B1650771 : Blo 1649524 1650771 := bstep (se 1 (by rfl) ⟨1238078, by rfl⟩ : syracuseStep 1650771 = 2476157) B2476157
theorem B1650787 : Blo 1649524 1650787 := bstep (se 1 (by rfl) ⟨1238090, by rfl⟩ : syracuseStep 1650787 = 2476181) B2476181
theorem B1650803 : Blo 1649524 1650803 := bstep (se 1 (by rfl) ⟨1238102, by rfl⟩ : syracuseStep 1650803 = 2476205) B2476205
theorem B1650819 : Blo 1649524 1650819 := bstep (se 1 (by rfl) ⟨1238114, by rfl⟩ : syracuseStep 1650819 = 2476229) B2476229
theorem B3715217 : Blo 1649524 3715217 := bstep (se 2 (by rfl) ⟨1393206, by rfl⟩ : syracuseStep 3715217 = 2786413) B2786413
theorem B1650835 : Blo 1649524 1650835 := bstep (se 1 (by rfl) ⟨1238126, by rfl⟩ : syracuseStep 1650835 = 2476253) B2476253
theorem B1650851 : Blo 1649524 1650851 := bstep (se 1 (by rfl) ⟨1238138, by rfl⟩ : syracuseStep 1650851 = 2476277) B2476277
theorem B3715235 : Blo 1649524 3715235 := bstep (se 1 (by rfl) ⟨2786426, by rfl⟩ : syracuseStep 3715235 = 5572853) B5572853
theorem B1650867 : Blo 1649524 1650867 := bstep (se 1 (by rfl) ⟨1238150, by rfl⟩ : syracuseStep 1650867 = 2476301) B2476301
theorem B1650883 : Blo 1649524 1650883 := bstep (se 1 (by rfl) ⟨1238162, by rfl⟩ : syracuseStep 1650883 = 2476325) B2476325
theorem B1650899 : Blo 1649524 1650899 := bstep (se 1 (by rfl) ⟨1238174, by rfl⟩ : syracuseStep 1650899 = 2476349) B2476349
theorem B3133667 : Blo 1649524 3133667 := bstep (se 1 (by rfl) ⟨2350250, by rfl⟩ : syracuseStep 3133667 = 4700501) B4700501
theorem B1650915 : Blo 1649524 1650915 := bstep (se 1 (by rfl) ⟨1238186, by rfl⟩ : syracuseStep 1650915 = 2476373) B2476373
theorem B3526897 : Blo 1649524 3526897 := bstep (se 2 (by rfl) ⟨1322586, by rfl⟩ : syracuseStep 3526897 = 2645173) B2645173
theorem B1650931 : Blo 1649524 1650931 := bstep (se 1 (by rfl) ⟨1238198, by rfl⟩ : syracuseStep 1650931 = 2476397) B2476397
theorem B1650947 : Blo 1649524 1650947 := bstep (se 1 (by rfl) ⟨1238210, by rfl⟩ : syracuseStep 1650947 = 2476421) B2476421
theorem B1650963 : Blo 1649524 1650963 := bstep (se 1 (by rfl) ⟨1238222, by rfl⟩ : syracuseStep 1650963 = 2476445) B2476445
theorem B1650979 : Blo 1649524 1650979 := bstep (se 1 (by rfl) ⟨1238234, by rfl⟩ : syracuseStep 1650979 = 2476469) B2476469
theorem B7049521 : Blo 1649524 7049521 := bstep (se 2 (by rfl) ⟨2643570, by rfl⟩ : syracuseStep 7049521 = 5287141) B5287141
theorem B1855795 : Blo 1649524 1855795 := bstep (se 1 (by rfl) ⟨1391846, by rfl⟩ : syracuseStep 1855795 = 2783693) B2783693
theorem B1650995 : Blo 1649524 1650995 := bstep (se 1 (by rfl) ⟨1238246, by rfl⟩ : syracuseStep 1650995 = 2476493) B2476493
theorem B1651011 : Blo 1649524 1651011 := bstep (se 1 (by rfl) ⟨1238258, by rfl⟩ : syracuseStep 1651011 = 2476517) B2476517
theorem B16085317 : Blo 1649524 16085317 := bstep (se 4 (by rfl) ⟨1507998, by rfl⟩ : syracuseStep 16085317 = 3015997) B3015997
theorem B17854789 : Blo 1649524 17854789 := bstep (se 4 (by rfl) ⟨1673886, by rfl⟩ : syracuseStep 17854789 = 3347773) B3347773
theorem B5288269 : Blo 1649524 5288269 := bstep (se 3 (by rfl) ⟨991550, by rfl⟩ : syracuseStep 5288269 = 1983101) B1983101
theorem B1651027 : Blo 1649524 1651027 := bstep (se 1 (by rfl) ⟨1238270, by rfl⟩ : syracuseStep 1651027 = 2476541) B2476541
theorem B1651043 : Blo 1649524 1651043 := bstep (se 1 (by rfl) ⟨1238282, by rfl⟩ : syracuseStep 1651043 = 2476565) B2476565
theorem B1651059 : Blo 1649524 1651059 := bstep (se 1 (by rfl) ⟨1238294, by rfl⟩ : syracuseStep 1651059 = 2476589) B2476589
theorem B1651075 : Blo 1649524 1651075 := bstep (se 1 (by rfl) ⟨1238306, by rfl⟩ : syracuseStep 1651075 = 2476613) B2476613
theorem B8360333 : Blo 1649524 8360333 := bstep (se 3 (by rfl) ⟨1567562, by rfl⟩ : syracuseStep 8360333 = 3135125) B3135125
theorem B1651091 : Blo 1649524 1651091 := bstep (se 1 (by rfl) ⟨1238318, by rfl⟩ : syracuseStep 1651091 = 2476637) B2476637
theorem B6263203 : Blo 1649524 6263203 := bstep (se 1 (by rfl) ⟨4697402, by rfl⟩ : syracuseStep 6263203 = 9394805) B9394805
theorem B1651107 : Blo 1649524 1651107 := bstep (se 1 (by rfl) ⟨1238330, by rfl⟩ : syracuseStep 1651107 = 2476661) B2476661
theorem B3715505 : Blo 1649524 3715505 := bstep (se 2 (by rfl) ⟨1393314, by rfl⟩ : syracuseStep 3715505 = 2786629) B2786629
theorem B1651123 : Blo 1649524 1651123 := bstep (se 1 (by rfl) ⟨1238342, by rfl⟩ : syracuseStep 1651123 = 2476685) B2476685
theorem B1855939 : Blo 1649524 1855939 := bstep (se 1 (by rfl) ⟨1391954, by rfl⟩ : syracuseStep 1855939 = 2783909) B2783909
theorem B1651139 : Blo 1649524 1651139 := bstep (se 1 (by rfl) ⟨1238354, by rfl⟩ : syracuseStep 1651139 = 2476709) B2476709
theorem B3715523 : Blo 1649524 3715523 := bstep (se 1 (by rfl) ⟨2786642, by rfl⟩ : syracuseStep 3715523 = 5573285) B5573285
theorem B1651155 : Blo 1649524 1651155 := bstep (se 1 (by rfl) ⟨1238366, by rfl⟩ : syracuseStep 1651155 = 2476733) B2476733
theorem B1651171 : Blo 1649524 1651171 := bstep (se 1 (by rfl) ⟨1238378, by rfl⟩ : syracuseStep 1651171 = 2476757) B2476757
theorem B3527153 : Blo 1649524 3527153 := bstep (se 2 (by rfl) ⟨1322682, by rfl⟩ : syracuseStep 3527153 = 2645365) B2645365
theorem B1651187 : Blo 1649524 1651187 := bstep (se 1 (by rfl) ⟨1238390, by rfl⟩ : syracuseStep 1651187 = 2476781) B2476781
theorem B1651203 : Blo 1649524 1651203 := bstep (se 1 (by rfl) ⟨1238402, by rfl⟩ : syracuseStep 1651203 = 2476805) B2476805
theorem B1651219 : Blo 1649524 1651219 := bstep (se 1 (by rfl) ⟨1238414, by rfl⟩ : syracuseStep 1651219 = 2476829) B2476829
theorem B1651235 : Blo 1649524 1651235 := bstep (se 1 (by rfl) ⟨1238426, by rfl⟩ : syracuseStep 1651235 = 2476853) B2476853
theorem B8917553 : Blo 1649524 8917553 := bstep (se 2 (by rfl) ⟨3344082, by rfl⟩ : syracuseStep 8917553 = 6688165) B6688165
theorem B1651251 : Blo 1649524 1651251 := bstep (se 1 (by rfl) ⟨1238438, by rfl⟩ : syracuseStep 1651251 = 2476877) B2476877
theorem B30511669 : Blo 1649524 30511669 := bstep (se 5 (by rfl) ⟨1430234, by rfl⟩ : syracuseStep 30511669 = 2860469) B2860469
theorem B1651267 : Blo 1649524 1651267 := bstep (se 1 (by rfl) ⟨1238450, by rfl⟩ : syracuseStep 1651267 = 2476901) B2476901
theorem B1856083 : Blo 1649524 1856083 := bstep (se 1 (by rfl) ⟨1392062, by rfl⟩ : syracuseStep 1856083 = 2784125) B2784125
theorem B1651283 : Blo 1649524 1651283 := bstep (se 1 (by rfl) ⟨1238462, by rfl⟩ : syracuseStep 1651283 = 2476925) B2476925
theorem B1651299 : Blo 1649524 1651299 := bstep (se 1 (by rfl) ⟨1238474, by rfl⟩ : syracuseStep 1651299 = 2476949) B2476949
theorem B1651315 : Blo 1649524 1651315 := bstep (se 1 (by rfl) ⟨1238486, by rfl⟩ : syracuseStep 1651315 = 2476973) B2476973
theorem B1651331 : Blo 1649524 1651331 := bstep (se 1 (by rfl) ⟨1238498, by rfl⟩ : syracuseStep 1651331 = 2476997) B2476997
theorem B1651347 : Blo 1649524 1651347 := bstep (se 1 (by rfl) ⟨1238510, by rfl⟩ : syracuseStep 1651347 = 2477021) B2477021
theorem B1651363 : Blo 1649524 1651363 := bstep (se 1 (by rfl) ⟨1238522, by rfl⟩ : syracuseStep 1651363 = 2477045) B2477045
theorem B1651379 : Blo 1649524 1651379 := bstep (se 1 (by rfl) ⟨1238534, by rfl⟩ : syracuseStep 1651379 = 2477069) B2477069
theorem B1651395 : Blo 1649524 1651395 := bstep (se 1 (by rfl) ⟨1238546, by rfl⟩ : syracuseStep 1651395 = 2477093) B2477093
theorem B3715793 : Blo 1649524 3715793 := bstep (se 2 (by rfl) ⟨1393422, by rfl⟩ : syracuseStep 3715793 = 2786845) B2786845
theorem B1651411 : Blo 1649524 1651411 := bstep (se 1 (by rfl) ⟨1238558, by rfl⟩ : syracuseStep 1651411 = 2477117) B2477117
theorem B1856227 : Blo 1649524 1856227 := bstep (se 1 (by rfl) ⟨1392170, by rfl⟩ : syracuseStep 1856227 = 2784341) B2784341
theorem B1651427 : Blo 1649524 1651427 := bstep (se 1 (by rfl) ⟨1238570, by rfl⟩ : syracuseStep 1651427 = 2477141) B2477141
theorem B3715811 : Blo 1649524 3715811 := bstep (se 1 (by rfl) ⟨2786858, by rfl⟩ : syracuseStep 3715811 = 5573717) B5573717
theorem B1651443 : Blo 1649524 1651443 := bstep (se 1 (by rfl) ⟨1238582, by rfl⟩ : syracuseStep 1651443 = 2477165) B2477165
theorem B1651459 : Blo 1649524 1651459 := bstep (se 1 (by rfl) ⟨1238594, by rfl⟩ : syracuseStep 1651459 = 2477189) B2477189
theorem B9401093 : Blo 1649524 9401093 := bstep (se 4 (by rfl) ⟨881352, by rfl⟩ : syracuseStep 9401093 = 1762705) B1762705
theorem B1651475 : Blo 1649524 1651475 := bstep (se 1 (by rfl) ⟨1238606, by rfl⟩ : syracuseStep 1651475 = 2477213) B2477213
theorem B1651491 : Blo 1649524 1651491 := bstep (se 1 (by rfl) ⟨1238618, by rfl⟩ : syracuseStep 1651491 = 2477237) B2477237
theorem B1651507 : Blo 1649524 1651507 := bstep (se 1 (by rfl) ⟨1238630, by rfl⟩ : syracuseStep 1651507 = 2477261) B2477261
theorem B5362499 : Blo 1649524 5362499 := bstep (se 1 (by rfl) ⟨4021874, by rfl⟩ : syracuseStep 5362499 = 8043749) B8043749
theorem B1651523 : Blo 1649524 1651523 := bstep (se 1 (by rfl) ⟨1238642, by rfl⟩ : syracuseStep 1651523 = 2477285) B2477285
theorem B5567345 : Blo 1649524 5567345 := bstep (se 2 (by rfl) ⟨2087754, by rfl⟩ : syracuseStep 5567345 = 4175509) B4175509
theorem B22598513 : Blo 1649524 22598513 := bstep (se 2 (by rfl) ⟨8474442, by rfl⟩ : syracuseStep 22598513 = 16948885) B16948885
theorem B1856371 : Blo 1649524 1856371 := bstep (se 1 (by rfl) ⟨1392278, by rfl⟩ : syracuseStep 1856371 = 2784557) B2784557
theorem B4699043 : Blo 1649524 4699043 := bstep (se 1 (by rfl) ⟨3524282, by rfl⟩ : syracuseStep 4699043 = 7048565) B7048565
theorem B1856515 : Blo 1649524 1856515 := bstep (se 1 (by rfl) ⟨1392386, by rfl⟩ : syracuseStep 1856515 = 2784773) B2784773
theorem B13390861 : Blo 1649524 13390861 := bstep (se 3 (by rfl) ⟨2510786, by rfl⟩ : syracuseStep 13390861 = 5021573) B5021573
theorem B5018705 : Blo 1649524 5018705 := bstep (se 2 (by rfl) ⟨1882014, by rfl⟩ : syracuseStep 5018705 = 3764029) B3764029
theorem B8352881 : Blo 1649524 8352881 := bstep (se 2 (by rfl) ⟨3132330, by rfl⟩ : syracuseStep 8352881 = 6264661) B6264661
theorem B35689585 : Blo 1649524 35689585 := bstep (se 2 (by rfl) ⟨13383594, by rfl⟩ : syracuseStep 35689585 = 26767189) B26767189
theorem B3134609 : Blo 1649524 3134609 := bstep (se 2 (by rfl) ⟨1175478, by rfl⟩ : syracuseStep 3134609 = 2350957) B2350957
theorem B1856659 : Blo 1649524 1856659 := bstep (se 1 (by rfl) ⟨1392494, by rfl⟩ : syracuseStep 1856659 = 2784989) B2784989
theorem B2643187 : Blo 1649524 2643187 := bstep (se 1 (by rfl) ⟨1982390, by rfl⟩ : syracuseStep 2643187 = 3964781) B3964781
theorem B9532685 : Blo 1649524 9532685 := bstep (se 3 (by rfl) ⟨1787378, by rfl⟩ : syracuseStep 9532685 = 3574757) B3574757
theorem B1856803 : Blo 1649524 1856803 := bstep (se 1 (by rfl) ⟨1392602, by rfl⟩ : syracuseStep 1856803 = 2785205) B2785205
theorem B5567885 : Blo 1649524 5567885 := bstep (se 3 (by rfl) ⟨1043978, by rfl⟩ : syracuseStep 5567885 = 2087957) B2087957
theorem B9401777 : Blo 1649524 9401777 := bstep (se 2 (by rfl) ⟨3525666, by rfl⟩ : syracuseStep 9401777 = 7051333) B7051333
theorem B1856947 : Blo 1649524 1856947 := bstep (se 1 (by rfl) ⟨1392710, by rfl⟩ : syracuseStep 1856947 = 2785421) B2785421
theorem B5567939 : Blo 1649524 5567939 := bstep (se 1 (by rfl) ⟨4175954, by rfl⟩ : syracuseStep 5567939 = 8351909) B8351909
theorem B16512497 : Blo 1649524 16512497 := bstep (se 2 (by rfl) ⟨6192186, by rfl⟩ : syracuseStep 16512497 = 12384373) B12384373
theorem B2823665 : Blo 1649524 2823665 := bstep (se 2 (by rfl) ⟨1058874, by rfl⟩ : syracuseStep 2823665 = 2117749) B2117749
theorem B2643443 : Blo 1649524 2643443 := bstep (se 1 (by rfl) ⟨1982582, by rfl⟩ : syracuseStep 2643443 = 3965165) B3965165
theorem B10573361 : Blo 1649524 10573361 := bstep (se 2 (by rfl) ⟨3965010, by rfl⟩ : syracuseStep 10573361 = 7930021) B7930021
theorem B1857091 : Blo 1649524 1857091 := bstep (se 1 (by rfl) ⟨1392818, by rfl⟩ : syracuseStep 1857091 = 2785637) B2785637
theorem B4175459 : Blo 1649524 4175459 := bstep (se 1 (by rfl) ⟨3131594, by rfl⟩ : syracuseStep 4175459 = 6263189) B6263189
theorem B14104205 : Blo 1649524 14104205 := bstep (se 3 (by rfl) ⟨2644538, by rfl⟩ : syracuseStep 14104205 = 5289077) B5289077
theorem B2643635 : Blo 1649524 2643635 := bstep (se 1 (by rfl) ⟨1982726, by rfl⟩ : syracuseStep 2643635 = 3965453) B3965453
theorem B4699853 : Blo 1649524 4699853 := bstep (se 3 (by rfl) ⟨881222, by rfl⟩ : syracuseStep 4699853 = 1762445) B1762445
theorem B5568209 : Blo 1649524 5568209 := bstep (se 2 (by rfl) ⟨2088078, by rfl⟩ : syracuseStep 5568209 = 4176157) B4176157
theorem B1857235 : Blo 1649524 1857235 := bstep (se 1 (by rfl) ⟨1392926, by rfl⟩ : syracuseStep 1857235 = 2785853) B2785853
theorem B5289731 : Blo 1649524 5289731 := bstep (se 1 (by rfl) ⟨3967298, by rfl⟩ : syracuseStep 5289731 = 7934597) B7934597
theorem B2348833 : Blo 1649524 2348833 := bstep (se 2 (by rfl) ⟨880812, by rfl⟩ : syracuseStep 2348833 = 1761625) B1761625
theorem B4175651 : Blo 1649524 4175651 := bstep (se 1 (by rfl) ⟨3131738, by rfl⟩ : syracuseStep 4175651 = 6263477) B6263477
theorem B1857379 : Blo 1649524 1857379 := bstep (se 1 (by rfl) ⟨1393034, by rfl⟩ : syracuseStep 1857379 = 2786069) B2786069
theorem B2348929 : Blo 1649524 2348929 := bstep (se 2 (by rfl) ⟨880848, by rfl⟩ : syracuseStep 2348929 = 1761697) B1761697
theorem B16078733 : Blo 1649524 16078733 := bstep (se 3 (by rfl) ⟨3014762, by rfl⟩ : syracuseStep 16078733 = 6029525) B6029525
theorem B4700045 : Blo 1649524 4700045 := bstep (se 3 (by rfl) ⟨881258, by rfl⟩ : syracuseStep 4700045 = 1762517) B1762517
theorem B1857523 : Blo 1649524 1857523 := bstep (se 1 (by rfl) ⟨1393142, by rfl⟩ : syracuseStep 1857523 = 2786285) B2786285
theorem B2578529 : Blo 1649524 2578529 := bstep (se 2 (by rfl) ⟨966948, by rfl⟩ : syracuseStep 2578529 = 1933897) B1933897
theorem B1857667 : Blo 1649524 1857667 := bstep (se 1 (by rfl) ⟨1393250, by rfl⟩ : syracuseStep 1857667 = 2786501) B2786501
theorem B5568749 : Blo 1649524 5568749 := bstep (se 3 (by rfl) ⟨1044140, by rfl⟩ : syracuseStep 5568749 = 2088281) B2088281
theorem B1857811 : Blo 1649524 1857811 := bstep (se 1 (by rfl) ⟨1393358, by rfl⟩ : syracuseStep 1857811 = 2786717) B2786717
theorem B5568803 : Blo 1649524 5568803 := bstep (se 1 (by rfl) ⟨4176602, by rfl⟩ : syracuseStep 5568803 = 8353205) B8353205
theorem B2783585 : Blo 1649524 2783585 := bstep (se 2 (by rfl) ⟨1043844, by rfl⟩ : syracuseStep 2783585 = 2087689) B2087689
theorem B8927587 : Blo 1649524 8927587 := bstep (se 1 (by rfl) ⟨6695690, by rfl⟩ : syracuseStep 8927587 = 13391381) B13391381
theorem B9525617 : Blo 1649524 9525617 := bstep (se 2 (by rfl) ⟨3572106, by rfl⟩ : syracuseStep 9525617 = 7144213) B7144213
theorem B2349425 : Blo 1649524 2349425 := bstep (se 2 (by rfl) ⟨881034, by rfl⟩ : syracuseStep 2349425 = 1762069) B1762069
theorem B1857955 : Blo 1649524 1857955 := bstep (se 1 (by rfl) ⟨1393466, by rfl⟩ : syracuseStep 1857955 = 2786933) B2786933
theorem B2644417 : Blo 1649524 2644417 := bstep (se 2 (by rfl) ⟨991656, by rfl⟩ : syracuseStep 2644417 = 1983313) B1983313
theorem B2783713 : Blo 1649524 2783713 := bstep (se 2 (by rfl) ⟨1043892, by rfl⟩ : syracuseStep 2783713 = 2087785) B2087785
theorem B2783747 : Blo 1649524 2783747 := bstep (se 1 (by rfl) ⟨2087810, by rfl⟩ : syracuseStep 2783747 = 4175621) B4175621
theorem B8354339 : Blo 1649524 8354339 := bstep (se 1 (by rfl) ⟨6265754, by rfl⟩ : syracuseStep 8354339 = 12531509) B12531509
theorem B5569073 : Blo 1649524 5569073 := bstep (se 2 (by rfl) ⟨2088402, by rfl⟩ : syracuseStep 5569073 = 4176805) B4176805
theorem B77290037 : Blo 1649524 77290037 := bstep (se 5 (by rfl) ⟨3622970, by rfl⟩ : syracuseStep 77290037 = 7245941) B7245941
theorem B8919629 : Blo 1649524 8919629 := bstep (se 3 (by rfl) ⟨1672430, by rfl⟩ : syracuseStep 8919629 = 3344861) B3344861
theorem B6265421 : Blo 1649524 6265421 := bstep (se 3 (by rfl) ⟨1174766, by rfl⟩ : syracuseStep 6265421 = 2349533) B2349533
theorem B42318449 : Blo 1649524 42318449 := bstep (se 2 (by rfl) ⟨15869418, by rfl⟩ : syracuseStep 42318449 = 31738837) B31738837
theorem B2783875 : Blo 1649524 2783875 := bstep (se 1 (by rfl) ⟨2087906, by rfl⟩ : syracuseStep 2783875 = 4175813) B4175813
theorem B5946061 : Blo 1649524 5946061 := bstep (se 3 (by rfl) ⟨1114886, by rfl⟩ : syracuseStep 5946061 = 2229773) B2229773
theorem B4176593 : Blo 1649524 4176593 := bstep (se 2 (by rfl) ⟨1566222, by rfl⟩ : syracuseStep 4176593 = 3132445) B3132445
theorem B4176643 : Blo 1649524 4176643 := bstep (se 1 (by rfl) ⟨3132482, by rfl⟩ : syracuseStep 4176643 = 6264965) B6264965
theorem B4463363 : Blo 1649524 4463363 := bstep (se 1 (by rfl) ⟨3347522, by rfl⟩ : syracuseStep 4463363 = 6695045) B6695045
theorem B2784017 : Blo 1649524 2784017 := bstep (se 2 (by rfl) ⟨1044006, by rfl⟩ : syracuseStep 2784017 = 2088013) B2088013
theorem B9403235 : Blo 1649524 9403235 := bstep (se 1 (by rfl) ⟨7052426, by rfl⟩ : syracuseStep 9403235 = 14104853) B14104853
theorem B4701037 : Blo 1649524 4701037 := bstep (se 3 (by rfl) ⟨881444, by rfl⟩ : syracuseStep 4701037 = 1762889) B1762889
theorem B2087795 : Blo 1649524 2087795 := bstep (se 1 (by rfl) ⟨1565846, by rfl⟩ : syracuseStep 2087795 = 3131693) B3131693
theorem B2784145 : Blo 1649524 2784145 := bstep (se 2 (by rfl) ⟨1044054, by rfl⟩ : syracuseStep 2784145 = 2088109) B2088109
theorem B4176785 : Blo 1649524 4176785 := bstep (se 2 (by rfl) ⟨1566294, by rfl⟩ : syracuseStep 4176785 = 3132589) B3132589
theorem B2784179 : Blo 1649524 2784179 := bstep (se 1 (by rfl) ⟨2088134, by rfl⟩ : syracuseStep 2784179 = 4176269) B4176269
theorem B7928867 : Blo 1649524 7928867 := bstep (se 1 (by rfl) ⟨5946650, by rfl⟩ : syracuseStep 7928867 = 11893301) B11893301
theorem B2784307 : Blo 1649524 2784307 := bstep (se 1 (by rfl) ⟨2088230, by rfl⟩ : syracuseStep 2784307 = 4176461) B4176461
theorem B9657413 : Blo 1649524 9657413 := bstep (se 4 (by rfl) ⟨905382, by rfl⟩ : syracuseStep 9657413 = 1810765) B1810765
theorem B5569613 : Blo 1649524 5569613 := bstep (se 3 (by rfl) ⟨1044302, by rfl⟩ : syracuseStep 5569613 = 2088605) B2088605
theorem B5569667 : Blo 1649524 5569667 := bstep (se 1 (by rfl) ⟨4177250, by rfl⟩ : syracuseStep 5569667 = 8354501) B8354501
theorem B2784449 : Blo 1649524 2784449 := bstep (se 2 (by rfl) ⟨1044168, by rfl⟩ : syracuseStep 2784449 = 2088337) B2088337
theorem B2350291 : Blo 1649524 2350291 := bstep (se 1 (by rfl) ⟨1762718, by rfl⟩ : syracuseStep 2350291 = 3525437) B3525437
theorem B80321813 : Blo 1649524 80321813 := bstep (se 6 (by rfl) ⟨1882542, by rfl⟩ : syracuseStep 80321813 = 3765085) B3765085
theorem B3439921 : Blo 1649524 3439921 := bstep (se 2 (by rfl) ⟨1289970, by rfl⟩ : syracuseStep 3439921 = 2579941) B2579941
theorem B2350387 : Blo 1649524 2350387 := bstep (se 1 (by rfl) ⟨1762790, by rfl⟩ : syracuseStep 2350387 = 3525581) B3525581
theorem B2784577 : Blo 1649524 2784577 := bstep (se 2 (by rfl) ⟨1044216, by rfl⟩ : syracuseStep 2784577 = 2088433) B2088433
theorem B8355149 : Blo 1649524 8355149 := bstep (se 3 (by rfl) ⟨1566590, by rfl⟩ : syracuseStep 8355149 = 3133181) B3133181
theorem B2784611 : Blo 1649524 2784611 := bstep (se 1 (by rfl) ⟨2088458, by rfl⟩ : syracuseStep 2784611 = 4176917) B4176917
theorem B5569937 : Blo 1649524 5569937 := bstep (se 2 (by rfl) ⟨2088726, by rfl⟩ : syracuseStep 5569937 = 4177453) B4177453
theorem B57187781 : Blo 1649524 57187781 := bstep (se 4 (by rfl) ⟨5361354, by rfl⟩ : syracuseStep 57187781 = 10722709) B10722709
theorem B2784739 : Blo 1649524 2784739 := bstep (se 1 (by rfl) ⟨2088554, by rfl⟩ : syracuseStep 2784739 = 4177109) B4177109
theorem B2088499 : Blo 1649524 2088499 := bstep (se 1 (by rfl) ⟨1566374, by rfl⟩ : syracuseStep 2088499 = 3132749) B3132749
theorem B3014243 : Blo 1649524 3014243 := bstep (se 1 (by rfl) ⟨2260682, by rfl⟩ : syracuseStep 3014243 = 4521365) B4521365
theorem B2784881 : Blo 1649524 2784881 := bstep (se 2 (by rfl) ⟨1044330, by rfl⟩ : syracuseStep 2784881 = 2088661) B2088661
theorem B2260595 : Blo 1649524 2260595 := bstep (se 1 (by rfl) ⟨1695446, by rfl⟩ : syracuseStep 2260595 = 3390893) B3390893
theorem B1982083 : Blo 1649524 1982083 := bstep (se 1 (by rfl) ⟨1486562, by rfl⟩ : syracuseStep 1982083 = 2973125) B2973125
theorem B2088595 : Blo 1649524 2088595 := bstep (se 1 (by rfl) ⟨1566446, by rfl⟩ : syracuseStep 2088595 = 3132893) B3132893
theorem B2785009 : Blo 1649524 2785009 := bstep (se 2 (by rfl) ⟨1044378, by rfl⟩ : syracuseStep 2785009 = 2088757) B2088757
theorem B11902733 : Blo 1649524 11902733 := bstep (se 3 (by rfl) ⟨2231762, by rfl⟩ : syracuseStep 11902733 = 4463525) B4463525
theorem B1982227 : Blo 1649524 1982227 := bstep (se 1 (by rfl) ⟨1486670, by rfl⟩ : syracuseStep 1982227 = 2973341) B2973341
theorem B2785043 : Blo 1649524 2785043 := bstep (se 1 (by rfl) ⟨2088782, by rfl⟩ : syracuseStep 2785043 = 4177565) B4177565
theorem B2350883 : Blo 1649524 2350883 := bstep (se 1 (by rfl) ⟨1763162, by rfl⟩ : syracuseStep 2350883 = 3526325) B3526325
theorem B7929713 : Blo 1649524 7929713 := bstep (se 2 (by rfl) ⟨2973642, by rfl⟩ : syracuseStep 7929713 = 5947285) B5947285
theorem B4177777 : Blo 1649524 4177777 := bstep (se 2 (by rfl) ⟨1566666, by rfl⟩ : syracuseStep 4177777 = 3133333) B3133333
theorem B27500429 : Blo 1649524 27500429 := bstep (se 3 (by rfl) ⟨5156330, by rfl⟩ : syracuseStep 27500429 = 10312661) B10312661
theorem B2785171 : Blo 1649524 2785171 := bstep (se 1 (by rfl) ⟨2088878, by rfl⟩ : syracuseStep 2785171 = 4177757) B4177757
theorem B5570477 : Blo 1649524 5570477 := bstep (se 3 (by rfl) ⟨1044464, by rfl⟩ : syracuseStep 5570477 = 2088929) B2088929
theorem B5644237 : Blo 1649524 5644237 := bstep (se 3 (by rfl) ⟨1058294, by rfl⟩ : syracuseStep 5644237 = 2116589) B2116589
theorem B5570531 : Blo 1649524 5570531 := bstep (se 1 (by rfl) ⟨4177898, by rfl⟩ : syracuseStep 5570531 = 8355797) B8355797
theorem B2785367 : Blo 1649524 2785367 := bstep (se 1 (by rfl) ⟨2089025, by rfl⟩ : syracuseStep 2785367 = 4178051) B4178051
theorem B2678873 : Blo 1649524 2678873 := bstep (se 2 (by rfl) ⟨1004577, by rfl⟩ : syracuseStep 2678873 = 2009155) B2009155
theorem B13377629 : Blo 1649524 13377629 := bstep (se 3 (by rfl) ⟨2508305, by rfl⟩ : syracuseStep 13377629 = 5016611) B5016611
theorem B12533939 : Blo 1649524 12533939 := bstep (se 1 (by rfl) ⟨9400454, by rfl⟩ : syracuseStep 12533939 = 18800909) B18800909
theorem B2785495 : Blo 1649524 2785495 := bstep (se 1 (by rfl) ⟨2089121, by rfl⟩ : syracuseStep 2785495 = 4178243) B4178243
theorem B2973953 : Blo 1649524 2973953 := bstep (se 2 (by rfl) ⟨1115232, by rfl⟩ : syracuseStep 2973953 = 2230465) B2230465
theorem B4702529 : Blo 1649524 4702529 := bstep (se 2 (by rfl) ⟨1763448, by rfl⟩ : syracuseStep 4702529 = 3526897) B3526897
theorem B2474315 : Blo 1649524 2474315 := bstep (se 1 (by rfl) ⟨1855736, by rfl⟩ : syracuseStep 2474315 = 3711473) B3711473
theorem B2351435 : Blo 1649524 2351435 := bstep (se 1 (by rfl) ⟨1763576, by rfl⟩ : syracuseStep 2351435 = 3527153) B3527153
theorem B2474327 : Blo 1649524 2474327 := bstep (se 1 (by rfl) ⟨1855745, by rfl⟩ : syracuseStep 2474327 = 3711491) B3711491
theorem B5570909 : Blo 1649524 5570909 := bstep (se 3 (by rfl) ⟨1044545, by rfl⟩ : syracuseStep 5570909 = 2089091) B2089091
theorem B2474393 : Blo 1649524 2474393 := bstep (se 2 (by rfl) ⟨927897, by rfl⟩ : syracuseStep 2474393 = 1855795) B1855795
theorem B21447089 : Blo 1649524 21447089 := bstep (se 2 (by rfl) ⟨8042658, by rfl⟩ : syracuseStep 21447089 = 16085317) B16085317
theorem B23806385 : Blo 1649524 23806385 := bstep (se 2 (by rfl) ⟨8927394, by rfl⟩ : syracuseStep 23806385 = 17854789) B17854789
theorem B4702643 : Blo 1649524 4702643 := bstep (se 1 (by rfl) ⟨3526982, by rfl⟩ : syracuseStep 4702643 = 7053965) B7053965
theorem B6029761 : Blo 1649524 6029761 := bstep (se 2 (by rfl) ⟨2261160, by rfl⟩ : syracuseStep 6029761 = 4522321) B4522321
theorem B11903449 : Blo 1649524 11903449 := bstep (se 2 (by rfl) ⟨4463793, by rfl⟩ : syracuseStep 11903449 = 8927587) B8927587
theorem B6267395 : Blo 1649524 6267395 := bstep (se 1 (by rfl) ⟨4700546, by rfl⟩ : syracuseStep 6267395 = 9401093) B9401093
theorem B2474507 : Blo 1649524 2474507 := bstep (se 1 (by rfl) ⟨1855880, by rfl⟩ : syracuseStep 2474507 = 3711761) B3711761
theorem B36184589 : Blo 1649524 36184589 := bstep (se 3 (by rfl) ⟨6784610, by rfl⟩ : syracuseStep 36184589 = 13569221) B13569221
theorem B2474519 : Blo 1649524 2474519 := bstep (se 1 (by rfl) ⟨1855889, by rfl⟩ : syracuseStep 2474519 = 3711779) B3711779
theorem B3711563 : Blo 1649524 3711563 := bstep (se 1 (by rfl) ⟨2783672, by rfl⟩ : syracuseStep 3711563 = 5567345) B5567345
theorem B15065675 : Blo 1649524 15065675 := bstep (se 1 (by rfl) ⟨11299256, by rfl⟩ : syracuseStep 15065675 = 22598513) B22598513
theorem B2474585 : Blo 1649524 2474585 := bstep (se 2 (by rfl) ⟨927969, by rfl⟩ : syracuseStep 2474585 = 1855939) B1855939
theorem B8356445 : Blo 1649524 8356445 := bstep (se 3 (by rfl) ⟨1566833, by rfl⟩ : syracuseStep 8356445 = 3133667) B3133667
theorem B3711617 : Blo 1649524 3711617 := bstep (se 2 (by rfl) ⟨1391856, by rfl⟩ : syracuseStep 3711617 = 2783713) B2783713
theorem B3523223 : Blo 1649524 3523223 := bstep (se 1 (by rfl) ⟨2642417, by rfl⟩ : syracuseStep 3523223 = 5284835) B5284835
theorem B2474699 : Blo 1649524 2474699 := bstep (se 1 (by rfl) ⟨1856024, by rfl⟩ : syracuseStep 2474699 = 3712049) B3712049
theorem B25420493 : Blo 1649524 25420493 := bstep (se 3 (by rfl) ⟨4766342, by rfl⟩ : syracuseStep 25420493 = 9532685) B9532685
theorem B2474711 : Blo 1649524 2474711 := bstep (se 1 (by rfl) ⟨1856033, by rfl⟩ : syracuseStep 2474711 = 3712067) B3712067
theorem B40682225 : Blo 1649524 40682225 := bstep (se 2 (by rfl) ⟨15255834, by rfl⟩ : syracuseStep 40682225 = 30511669) B30511669
theorem B2089739 : Blo 1649524 2089739 := bstep (se 1 (by rfl) ⟨1567304, by rfl⟩ : syracuseStep 2089739 = 3134609) B3134609
theorem B2474777 : Blo 1649524 2474777 := bstep (se 2 (by rfl) ⟨928041, by rfl⟩ : syracuseStep 2474777 = 1856083) B1856083
theorem B7627565 : Blo 1649524 7627565 := bstep (se 3 (by rfl) ⟨1430168, by rfl⟩ : syracuseStep 7627565 = 2860337) B2860337
theorem B2786123 : Blo 1649524 2786123 := bstep (se 1 (by rfl) ⟨2089592, by rfl⟩ : syracuseStep 2786123 = 4179185) B4179185
theorem B3711833 : Blo 1649524 3711833 := bstep (se 2 (by rfl) ⟨1391937, by rfl⟩ : syracuseStep 3711833 = 2783875) B2783875
theorem B2474891 : Blo 1649524 2474891 := bstep (se 1 (by rfl) ⟨1856168, by rfl⟩ : syracuseStep 2474891 = 3712337) B3712337
theorem B2474903 : Blo 1649524 2474903 := bstep (se 1 (by rfl) ⟨1856177, by rfl⟩ : syracuseStep 2474903 = 3712355) B3712355
theorem B3711923 : Blo 1649524 3711923 := bstep (se 1 (by rfl) ⟨2783942, by rfl⟩ : syracuseStep 3711923 = 5567885) B5567885
theorem B6267851 : Blo 1649524 6267851 := bstep (se 1 (by rfl) ⟨4700888, by rfl⟩ : syracuseStep 6267851 = 9401777) B9401777
theorem B4178891 : Blo 1649524 4178891 := bstep (se 1 (by rfl) ⟨3134168, by rfl⟩ : syracuseStep 4178891 = 6268337) B6268337
theorem B2786251 : Blo 1649524 2786251 := bstep (se 1 (by rfl) ⟨2089688, by rfl⟩ : syracuseStep 2786251 = 4179377) B4179377
theorem B3711959 : Blo 1649524 3711959 := bstep (se 1 (by rfl) ⟨2783969, by rfl⟩ : syracuseStep 3711959 = 5567939) B5567939
theorem B2474969 : Blo 1649524 2474969 := bstep (se 2 (by rfl) ⟨928113, by rfl⟩ : syracuseStep 2474969 = 1856227) B1856227
theorem B2974681 : Blo 1649524 2974681 := bstep (se 2 (by rfl) ⟨1115505, by rfl⟩ : syracuseStep 2974681 = 2231011) B2231011
theorem B1762295 : Blo 1649524 1762295 := bstep (se 1 (by rfl) ⟨1321721, by rfl⟩ : syracuseStep 1762295 = 2643443) B2643443
theorem B2475083 : Blo 1649524 2475083 := bstep (se 1 (by rfl) ⟨1856312, by rfl⟩ : syracuseStep 2475083 = 3712625) B3712625
theorem B2475095 : Blo 1649524 2475095 := bstep (se 1 (by rfl) ⟨1856321, by rfl⟩ : syracuseStep 2475095 = 3712643) B3712643
theorem B2786393 : Blo 1649524 2786393 := bstep (se 2 (by rfl) ⟨1044897, by rfl⟩ : syracuseStep 2786393 = 2089795) B2089795
theorem B3712139 : Blo 1649524 3712139 := bstep (se 1 (by rfl) ⟨2784104, by rfl⟩ : syracuseStep 3712139 = 5568209) B5568209
theorem B6268049 : Blo 1649524 6268049 := bstep (se 2 (by rfl) ⟨2350518, by rfl⟩ : syracuseStep 6268049 = 4701037) B4701037
theorem B2475161 : Blo 1649524 2475161 := bstep (se 2 (by rfl) ⟨928185, by rfl⟩ : syracuseStep 2475161 = 1856371) B1856371
theorem B3712193 : Blo 1649524 3712193 := bstep (se 2 (by rfl) ⟨1392072, by rfl⟩ : syracuseStep 3712193 = 2784145) B2784145
theorem B2786521 : Blo 1649524 2786521 := bstep (se 2 (by rfl) ⟨1044945, by rfl⟩ : syracuseStep 2786521 = 2089891) B2089891
theorem B2475275 : Blo 1649524 2475275 := bstep (se 1 (by rfl) ⟨1856456, by rfl⟩ : syracuseStep 2475275 = 3712913) B3712913
theorem B2475287 : Blo 1649524 2475287 := bstep (se 1 (by rfl) ⟨1856465, by rfl⟩ : syracuseStep 2475287 = 3712931) B3712931
theorem B7529773 : Blo 1649524 7529773 := bstep (se 3 (by rfl) ⟨1411832, by rfl⟩ : syracuseStep 7529773 = 2823665) B2823665
theorem B2475353 : Blo 1649524 2475353 := bstep (se 2 (by rfl) ⟨928257, by rfl⟩ : syracuseStep 2475353 = 1856515) B1856515
theorem B3712409 : Blo 1649524 3712409 := bstep (se 2 (by rfl) ⟨1392153, by rfl⟩ : syracuseStep 3712409 = 2784307) B2784307
theorem B2475467 : Blo 1649524 2475467 := bstep (se 1 (by rfl) ⟨1856600, by rfl⟩ : syracuseStep 2475467 = 3713201) B3713201
theorem B5572043 : Blo 1649524 5572043 := bstep (se 1 (by rfl) ⟨4179032, by rfl⟩ : syracuseStep 5572043 = 8358065) B8358065
theorem B2475479 : Blo 1649524 2475479 := bstep (se 1 (by rfl) ⟨1856609, by rfl⟩ : syracuseStep 2475479 = 3713219) B3713219
theorem B9397721 : Blo 1649524 9397721 := bstep (se 2 (by rfl) ⟨3524145, by rfl⟩ : syracuseStep 9397721 = 7048291) B7048291
theorem B3712499 : Blo 1649524 3712499 := bstep (se 1 (by rfl) ⟨2784374, by rfl⟩ : syracuseStep 3712499 = 5568749) B5568749
theorem B3712535 : Blo 1649524 3712535 := bstep (se 1 (by rfl) ⟨2784401, by rfl⟩ : syracuseStep 3712535 = 5568803) B5568803
theorem B2475545 : Blo 1649524 2475545 := bstep (se 2 (by rfl) ⟨928329, by rfl⟩ : syracuseStep 2475545 = 1856659) B1856659
theorem B6350411 : Blo 1649524 6350411 := bstep (se 1 (by rfl) ⟨4762808, by rfl⟩ : syracuseStep 6350411 = 9525617) B9525617
theorem B12535397 : Blo 1649524 12535397 := bstep (se 4 (by rfl) ⟨1175193, by rfl⟩ : syracuseStep 12535397 = 2350387) B2350387
theorem B2475659 : Blo 1649524 2475659 := bstep (se 1 (by rfl) ⟨1856744, by rfl⟩ : syracuseStep 2475659 = 3713489) B3713489
theorem B2475671 : Blo 1649524 2475671 := bstep (se 1 (by rfl) ⟨1856753, by rfl⟩ : syracuseStep 2475671 = 3713507) B3713507
theorem B3524249 : Blo 1649524 3524249 := bstep (se 2 (by rfl) ⟨1321593, by rfl⟩ : syracuseStep 3524249 = 2643187) B2643187
theorem B3712715 : Blo 1649524 3712715 := bstep (se 1 (by rfl) ⟨2784536, by rfl⟩ : syracuseStep 3712715 = 5569073) B5569073
theorem B2475737 : Blo 1649524 2475737 := bstep (se 2 (by rfl) ⟨928401, by rfl⟩ : syracuseStep 2475737 = 1856803) B1856803
theorem B5572313 : Blo 1649524 5572313 := bstep (se 2 (by rfl) ⟨2089617, by rfl⟩ : syracuseStep 5572313 = 4179235) B4179235
theorem B3712769 : Blo 1649524 3712769 := bstep (se 2 (by rfl) ⟨1392288, by rfl⟩ : syracuseStep 3712769 = 2784577) B2784577
theorem B2475851 : Blo 1649524 2475851 := bstep (se 1 (by rfl) ⟨1856888, by rfl⟩ : syracuseStep 2475851 = 3713777) B3713777
theorem B2475863 : Blo 1649524 2475863 := bstep (se 1 (by rfl) ⟨1856897, by rfl⟩ : syracuseStep 2475863 = 3713795) B3713795
theorem B2975575 : Blo 1649524 2975575 := bstep (se 1 (by rfl) ⟨2231681, by rfl⟩ : syracuseStep 2975575 = 4463363) B4463363
theorem B6268823 : Blo 1649524 6268823 := bstep (se 1 (by rfl) ⟨4701617, by rfl⟩ : syracuseStep 6268823 = 9403235) B9403235
theorem B4179863 : Blo 1649524 4179863 := bstep (se 1 (by rfl) ⟨3134897, by rfl⟩ : syracuseStep 4179863 = 6269795) B6269795
theorem B2475929 : Blo 1649524 2475929 := bstep (se 2 (by rfl) ⟨928473, by rfl⟩ : syracuseStep 2475929 = 1856947) B1856947
theorem B3712985 : Blo 1649524 3712985 := bstep (se 2 (by rfl) ⟨1392369, by rfl⟩ : syracuseStep 3712985 = 2784739) B2784739
theorem B12527621 : Blo 1649524 12527621 := bstep (se 4 (by rfl) ⟨1174464, by rfl⟩ : syracuseStep 12527621 = 2348929) B2348929
theorem B2476043 : Blo 1649524 2476043 := bstep (se 1 (by rfl) ⟨1857032, by rfl⟩ : syracuseStep 2476043 = 3714065) B3714065
theorem B5285911 : Blo 1649524 5285911 := bstep (se 1 (by rfl) ⟨3964433, by rfl⟩ : syracuseStep 5285911 = 7928867) B7928867
theorem B2476055 : Blo 1649524 2476055 := bstep (se 1 (by rfl) ⟨1857041, by rfl⟩ : syracuseStep 2476055 = 3714083) B3714083
theorem B12060707 : Blo 1649524 12060707 := bstep (se 1 (by rfl) ⟨9045530, by rfl⟩ : syracuseStep 12060707 = 18091061) B18091061
theorem B3713075 : Blo 1649524 3713075 := bstep (se 1 (by rfl) ⟨2784806, by rfl⟩ : syracuseStep 3713075 = 5569613) B5569613
theorem B7047233 : Blo 1649524 7047233 := bstep (se 2 (by rfl) ⟨2642712, by rfl⟩ : syracuseStep 7047233 = 5285425) B5285425
theorem B12535883 : Blo 1649524 12535883 := bstep (se 1 (by rfl) ⟨9401912, by rfl⟩ : syracuseStep 12535883 = 18803825) B18803825
theorem B3713111 : Blo 1649524 3713111 := bstep (se 1 (by rfl) ⟨2784833, by rfl⟩ : syracuseStep 3713111 = 5569667) B5569667
theorem B1673303 : Blo 1649524 1673303 := bstep (se 1 (by rfl) ⟨1254977, by rfl⟩ : syracuseStep 1673303 = 2509955) B2509955
theorem B2476121 : Blo 1649524 2476121 := bstep (se 2 (by rfl) ⟨928545, by rfl⟩ : syracuseStep 2476121 = 1857091) B1857091
theorem B6269021 : Blo 1649524 6269021 := bstep (se 3 (by rfl) ⟨1175441, by rfl⟩ : syracuseStep 6269021 = 2350883) B2350883
theorem B2476235 : Blo 1649524 2476235 := bstep (se 1 (by rfl) ⟨1857176, by rfl⟩ : syracuseStep 2476235 = 3714353) B3714353
theorem B2476247 : Blo 1649524 2476247 := bstep (se 1 (by rfl) ⟨1857185, by rfl⟩ : syracuseStep 2476247 = 3714371) B3714371
theorem B3713291 : Blo 1649524 3713291 := bstep (se 1 (by rfl) ⟨2784968, by rfl⟩ : syracuseStep 3713291 = 5569937) B5569937
theorem B2476313 : Blo 1649524 2476313 := bstep (se 2 (by rfl) ⟨928617, by rfl⟩ : syracuseStep 2476313 = 1857235) B1857235
theorem B3713345 : Blo 1649524 3713345 := bstep (se 2 (by rfl) ⟨1392504, by rfl⟩ : syracuseStep 3713345 = 2785009) B2785009
theorem B3131723 : Blo 1649524 3131723 := bstep (se 1 (by rfl) ⟨2348792, by rfl⟩ : syracuseStep 3131723 = 4697585) B4697585
theorem B3574091 : Blo 1649524 3574091 := bstep (se 1 (by rfl) ⟨2680568, by rfl⟩ : syracuseStep 3574091 = 5361137) B5361137
theorem B3131777 : Blo 1649524 3131777 := bstep (se 2 (by rfl) ⟨1174416, by rfl⟩ : syracuseStep 3131777 = 2348833) B2348833
theorem B2476427 : Blo 1649524 2476427 := bstep (se 1 (by rfl) ⟨1857320, by rfl⟩ : syracuseStep 2476427 = 3714641) B3714641
theorem B2009495 : Blo 1649524 2009495 := bstep (se 1 (by rfl) ⟨1507121, by rfl⟩ : syracuseStep 2009495 = 3014243) B3014243
theorem B2476439 : Blo 1649524 2476439 := bstep (se 1 (by rfl) ⟨1857329, by rfl⟩ : syracuseStep 2476439 = 3714659) B3714659
theorem B5573015 : Blo 1649524 5573015 := bstep (se 1 (by rfl) ⟨4179761, by rfl⟩ : syracuseStep 5573015 = 8359523) B8359523
theorem B2476505 : Blo 1649524 2476505 := bstep (se 2 (by rfl) ⟨928689, by rfl⟩ : syracuseStep 2476505 = 1857379) B1857379
theorem B3713561 : Blo 1649524 3713561 := bstep (se 2 (by rfl) ⟨1392585, by rfl⟩ : syracuseStep 3713561 = 2785171) B2785171
theorem B5286475 : Blo 1649524 5286475 := bstep (se 1 (by rfl) ⟨3964856, by rfl⟩ : syracuseStep 5286475 = 7929713) B7929713
theorem B2230859 : Blo 1649524 2230859 := bstep (se 1 (by rfl) ⟨1673144, by rfl⟩ : syracuseStep 2230859 = 3346289) B3346289
theorem B2476619 : Blo 1649524 2476619 := bstep (se 1 (by rfl) ⟨1857464, by rfl⟩ : syracuseStep 2476619 = 3714929) B3714929
theorem B2476631 : Blo 1649524 2476631 := bstep (se 1 (by rfl) ⟨1857473, by rfl⟩ : syracuseStep 2476631 = 3714947) B3714947
theorem B3713651 : Blo 1649524 3713651 := bstep (se 1 (by rfl) ⟨2785238, by rfl⟩ : syracuseStep 3713651 = 5570477) B5570477
theorem B3713687 : Blo 1649524 3713687 := bstep (se 1 (by rfl) ⟨2785265, by rfl⟩ : syracuseStep 3713687 = 5570531) B5570531
theorem B8358551 : Blo 1649524 8358551 := bstep (se 1 (by rfl) ⟨6268913, by rfl⟩ : syracuseStep 8358551 = 12537827) B12537827
theorem B2476697 : Blo 1649524 2476697 := bstep (se 2 (by rfl) ⟨928761, by rfl⟩ : syracuseStep 2476697 = 1857523) B1857523
theorem B5286617 : Blo 1649524 5286617 := bstep (se 2 (by rfl) ⟨1982481, by rfl⟩ : syracuseStep 5286617 = 3964963) B3964963
theorem B35711729 : Blo 1649524 35711729 := bstep (se 2 (by rfl) ⟨13391898, by rfl⟩ : syracuseStep 35711729 = 26783797) B26783797
theorem B2476811 : Blo 1649524 2476811 := bstep (se 1 (by rfl) ⟨1857608, by rfl⟩ : syracuseStep 2476811 = 3715217) B3715217
theorem B2476823 : Blo 1649524 2476823 := bstep (se 1 (by rfl) ⟨1857617, by rfl⟩ : syracuseStep 2476823 = 3715235) B3715235
theorem B3713867 : Blo 1649524 3713867 := bstep (se 1 (by rfl) ⟨2785400, by rfl⟩ : syracuseStep 3713867 = 5570801) B5570801
theorem B2476889 : Blo 1649524 2476889 := bstep (se 2 (by rfl) ⟨928833, by rfl⟩ : syracuseStep 2476889 = 1857667) B1857667
theorem B23784293 : Blo 1649524 23784293 := bstep (se 4 (by rfl) ⟨2229777, by rfl⟩ : syracuseStep 23784293 = 4459555) B4459555
theorem B21162869 : Blo 1649524 21162869 := bstep (se 5 (by rfl) ⟨992009, by rfl⟩ : syracuseStep 21162869 = 1984019) B1984019
theorem B1649527 : Blo 1649524 1649527 := bstep (se 1 (by rfl) ⟨1237145, by rfl⟩ : syracuseStep 1649527 = 2474291) B2474291
theorem B3713921 : Blo 1649524 3713921 := bstep (se 2 (by rfl) ⟨1392720, by rfl⟩ : syracuseStep 3713921 = 2785441) B2785441
theorem B1649547 : Blo 1649524 1649547 := bstep (se 1 (by rfl) ⟨1237160, by rfl⟩ : syracuseStep 1649547 = 2474321) B2474321
theorem B1649559 : Blo 1649524 1649559 := bstep (se 1 (by rfl) ⟨1237169, by rfl⟩ : syracuseStep 1649559 = 2474339) B2474339
theorem B1649579 : Blo 1649524 1649579 := bstep (se 1 (by rfl) ⟨1237184, by rfl⟩ : syracuseStep 1649579 = 2474369) B2474369
theorem B5573555 : Blo 1649524 5573555 := bstep (se 1 (by rfl) ⟨4180166, by rfl⟩ : syracuseStep 5573555 = 8360333) B8360333
theorem B1649591 : Blo 1649524 1649591 := bstep (se 1 (by rfl) ⟨1237193, by rfl⟩ : syracuseStep 1649591 = 2474387) B2474387
theorem B1649611 : Blo 1649524 1649611 := bstep (se 1 (by rfl) ⟨1237208, by rfl⟩ : syracuseStep 1649611 = 2474417) B2474417
theorem B2477003 : Blo 1649524 2477003 := bstep (se 1 (by rfl) ⟨1857752, by rfl⟩ : syracuseStep 2477003 = 3715505) B3715505
theorem B1649623 : Blo 1649524 1649623 := bstep (se 1 (by rfl) ⟨1237217, by rfl⟩ : syracuseStep 1649623 = 2474435) B2474435
theorem B2477015 : Blo 1649524 2477015 := bstep (se 1 (by rfl) ⟨1857761, by rfl⟩ : syracuseStep 2477015 = 3715523) B3715523
theorem B1649643 : Blo 1649524 1649643 := bstep (se 1 (by rfl) ⟨1237232, by rfl⟩ : syracuseStep 1649643 = 2474465) B2474465
theorem B1649655 : Blo 1649524 1649655 := bstep (se 1 (by rfl) ⟨1237241, by rfl⟩ : syracuseStep 1649655 = 2474483) B2474483
theorem B1649675 : Blo 1649524 1649675 := bstep (se 1 (by rfl) ⟨1237256, by rfl⟩ : syracuseStep 1649675 = 2474513) B2474513
theorem B1649687 : Blo 1649524 1649687 := bstep (se 1 (by rfl) ⟨1237265, by rfl⟩ : syracuseStep 1649687 = 2474531) B2474531
theorem B2477081 : Blo 1649524 2477081 := bstep (se 2 (by rfl) ⟨928905, by rfl⟩ : syracuseStep 2477081 = 1857811) B1857811
theorem B1649707 : Blo 1649524 1649707 := bstep (se 1 (by rfl) ⟨1237280, by rfl⟩ : syracuseStep 1649707 = 2474561) B2474561
theorem B1649719 : Blo 1649524 1649719 := bstep (se 1 (by rfl) ⟨1237289, by rfl⟩ : syracuseStep 1649719 = 2474579) B2474579
theorem B9399361 : Blo 1649524 9399361 := bstep (se 2 (by rfl) ⟨3524760, by rfl⟩ : syracuseStep 9399361 = 7049521) B7049521
theorem B1649739 : Blo 1649524 1649739 := bstep (se 1 (by rfl) ⟨1237304, by rfl⟩ : syracuseStep 1649739 = 2474609) B2474609
theorem B1649751 : Blo 1649524 1649751 := bstep (se 1 (by rfl) ⟨1237313, by rfl⟩ : syracuseStep 1649751 = 2474627) B2474627
theorem B3714137 : Blo 1649524 3714137 := bstep (se 2 (by rfl) ⟨1392801, by rfl⟩ : syracuseStep 3714137 = 2785603) B2785603
theorem B1649771 : Blo 1649524 1649771 := bstep (se 1 (by rfl) ⟨1237328, by rfl⟩ : syracuseStep 1649771 = 2474657) B2474657
theorem B1649783 : Blo 1649524 1649783 := bstep (se 1 (by rfl) ⟨1237337, by rfl⟩ : syracuseStep 1649783 = 2474675) B2474675
theorem B1649803 : Blo 1649524 1649803 := bstep (se 1 (by rfl) ⟨1237352, by rfl⟩ : syracuseStep 1649803 = 2474705) B2474705
theorem B2477195 : Blo 1649524 2477195 := bstep (se 1 (by rfl) ⟨1857896, by rfl⟩ : syracuseStep 2477195 = 3715793) B3715793
theorem B1649815 : Blo 1649524 1649815 := bstep (se 1 (by rfl) ⟨1237361, by rfl⟩ : syracuseStep 1649815 = 2474723) B2474723
theorem B2477207 : Blo 1649524 2477207 := bstep (se 1 (by rfl) ⟨1857905, by rfl⟩ : syracuseStep 2477207 = 3715811) B3715811
theorem B1649835 : Blo 1649524 1649835 := bstep (se 1 (by rfl) ⟨1237376, by rfl⟩ : syracuseStep 1649835 = 2474753) B2474753
theorem B3714227 : Blo 1649524 3714227 := bstep (se 1 (by rfl) ⟨2785670, by rfl⟩ : syracuseStep 3714227 = 5571341) B5571341
theorem B1649847 : Blo 1649524 1649847 := bstep (se 1 (by rfl) ⟨1237385, by rfl⟩ : syracuseStep 1649847 = 2474771) B2474771
theorem B5573825 : Blo 1649524 5573825 := bstep (se 2 (by rfl) ⟨2090184, by rfl⟩ : syracuseStep 5573825 = 4180369) B4180369
theorem B1649867 : Blo 1649524 1649867 := bstep (se 1 (by rfl) ⟨1237400, by rfl⟩ : syracuseStep 1649867 = 2474801) B2474801
theorem B1649879 : Blo 1649524 1649879 := bstep (se 1 (by rfl) ⟨1237409, by rfl⟩ : syracuseStep 1649879 = 2474819) B2474819
theorem B8350937 : Blo 1649524 8350937 := bstep (se 2 (by rfl) ⟨3131601, by rfl⟩ : syracuseStep 8350937 = 6263203) B6263203
theorem B3714263 : Blo 1649524 3714263 := bstep (se 1 (by rfl) ⟨2785697, by rfl⟩ : syracuseStep 3714263 = 5571395) B5571395
theorem B2477273 : Blo 1649524 2477273 := bstep (se 2 (by rfl) ⟨928977, by rfl⟩ : syracuseStep 2477273 = 1857955) B1857955
theorem B1649899 : Blo 1649524 1649899 := bstep (se 1 (by rfl) ⟨1237424, by rfl⟩ : syracuseStep 1649899 = 2474849) B2474849
theorem B1649911 : Blo 1649524 1649911 := bstep (se 1 (by rfl) ⟨1237433, by rfl⟩ : syracuseStep 1649911 = 2474867) B2474867
theorem B3525889 : Blo 1649524 3525889 := bstep (se 2 (by rfl) ⟨1322208, by rfl⟩ : syracuseStep 3525889 = 2644417) B2644417
theorem B1649931 : Blo 1649524 1649931 := bstep (se 1 (by rfl) ⟨1237448, by rfl⟩ : syracuseStep 1649931 = 2474897) B2474897
theorem B1649943 : Blo 1649524 1649943 := bstep (se 1 (by rfl) ⟨1237457, by rfl⟩ : syracuseStep 1649943 = 2474915) B2474915
theorem B3132695 : Blo 1649524 3132695 := bstep (se 1 (by rfl) ⟨2349521, by rfl⟩ : syracuseStep 3132695 = 4699043) B4699043
theorem B1649963 : Blo 1649524 1649963 := bstep (se 1 (by rfl) ⟨1237472, by rfl⟩ : syracuseStep 1649963 = 2474945) B2474945
theorem B30125357 : Blo 1649524 30125357 := bstep (se 3 (by rfl) ⟨5648504, by rfl⟩ : syracuseStep 30125357 = 11297009) B11297009
theorem B1649975 : Blo 1649524 1649975 := bstep (se 1 (by rfl) ⟨1237481, by rfl⟩ : syracuseStep 1649975 = 2474963) B2474963
theorem B1649995 : Blo 1649524 1649995 := bstep (se 1 (by rfl) ⟨1237496, by rfl⟩ : syracuseStep 1649995 = 2474993) B2474993
theorem B1650007 : Blo 1649524 1650007 := bstep (se 1 (by rfl) ⟨1237505, by rfl⟩ : syracuseStep 1650007 = 2475011) B2475011
theorem B1650027 : Blo 1649524 1650027 := bstep (se 1 (by rfl) ⟨1237520, by rfl⟩ : syracuseStep 1650027 = 2475041) B2475041
theorem B19049845 : Blo 1649524 19049845 := bstep (se 5 (by rfl) ⟨892961, by rfl⟩ : syracuseStep 19049845 = 1785923) B1785923
theorem B1650039 : Blo 1649524 1650039 := bstep (se 1 (by rfl) ⟨1237529, by rfl⟩ : syracuseStep 1650039 = 2475059) B2475059
theorem B1650059 : Blo 1649524 1650059 := bstep (se 1 (by rfl) ⟨1237544, by rfl⟩ : syracuseStep 1650059 = 2475089) B2475089
theorem B3345803 : Blo 1649524 3345803 := bstep (se 1 (by rfl) ⟨2509352, by rfl⟩ : syracuseStep 3345803 = 5018705) B5018705
theorem B3714443 : Blo 1649524 3714443 := bstep (se 1 (by rfl) ⟨2785832, by rfl⟩ : syracuseStep 3714443 = 5571665) B5571665
theorem B53513621 : Blo 1649524 53513621 := bstep (se 6 (by rfl) ⟨1254225, by rfl⟩ : syracuseStep 53513621 = 2508451) B2508451
theorem B1650071 : Blo 1649524 1650071 := bstep (se 1 (by rfl) ⟨1237553, by rfl⟩ : syracuseStep 1650071 = 2475107) B2475107
theorem B1650091 : Blo 1649524 1650091 := bstep (se 1 (by rfl) ⟨1237568, by rfl⟩ : syracuseStep 1650091 = 2475137) B2475137
theorem B8465843 : Blo 1649524 8465843 := bstep (se 1 (by rfl) ⟨6349382, by rfl⟩ : syracuseStep 8465843 = 12698765) B12698765
theorem B1650103 : Blo 1649524 1650103 := bstep (se 1 (by rfl) ⟨1237577, by rfl⟩ : syracuseStep 1650103 = 2475155) B2475155
theorem B3714497 : Blo 1649524 3714497 := bstep (se 2 (by rfl) ⟨1392936, by rfl⟩ : syracuseStep 3714497 = 2785873) B2785873
theorem B1650123 : Blo 1649524 1650123 := bstep (se 1 (by rfl) ⟨1237592, by rfl⟩ : syracuseStep 1650123 = 2475185) B2475185
theorem B1650135 : Blo 1649524 1650135 := bstep (se 1 (by rfl) ⟨1237601, by rfl⟩ : syracuseStep 1650135 = 2475203) B2475203
theorem B1650155 : Blo 1649524 1650155 := bstep (se 1 (by rfl) ⟨1237616, by rfl⟩ : syracuseStep 1650155 = 2475233) B2475233
theorem B1650167 : Blo 1649524 1650167 := bstep (se 1 (by rfl) ⟨1237625, by rfl⟩ : syracuseStep 1650167 = 2475251) B2475251
theorem B1650187 : Blo 1649524 1650187 := bstep (se 1 (by rfl) ⟨1237640, by rfl⟩ : syracuseStep 1650187 = 2475281) B2475281
theorem B1650199 : Blo 1649524 1650199 := bstep (se 1 (by rfl) ⟨1237649, by rfl⟩ : syracuseStep 1650199 = 2475299) B2475299
theorem B1650219 : Blo 1649524 1650219 := bstep (se 1 (by rfl) ⟨1237664, by rfl⟩ : syracuseStep 1650219 = 2475329) B2475329
theorem B1650231 : Blo 1649524 1650231 := bstep (se 1 (by rfl) ⟨1237673, by rfl⟩ : syracuseStep 1650231 = 2475347) B2475347
theorem B1650251 : Blo 1649524 1650251 := bstep (se 1 (by rfl) ⟨1237688, by rfl⟩ : syracuseStep 1650251 = 2475377) B2475377
theorem B1650263 : Blo 1649524 1650263 := bstep (se 1 (by rfl) ⟨1237697, by rfl⟩ : syracuseStep 1650263 = 2475395) B2475395
theorem B1650283 : Blo 1649524 1650283 := bstep (se 1 (by rfl) ⟨1237712, by rfl⟩ : syracuseStep 1650283 = 2475425) B2475425
theorem B1650295 : Blo 1649524 1650295 := bstep (se 1 (by rfl) ⟨1237721, by rfl⟩ : syracuseStep 1650295 = 2475443) B2475443
theorem B1650315 : Blo 1649524 1650315 := bstep (se 1 (by rfl) ⟨1237736, by rfl⟩ : syracuseStep 1650315 = 2475473) B2475473
theorem B1650327 : Blo 1649524 1650327 := bstep (se 1 (by rfl) ⟨1237745, by rfl⟩ : syracuseStep 1650327 = 2475491) B2475491
theorem B3714713 : Blo 1649524 3714713 := bstep (se 2 (by rfl) ⟨1393017, by rfl⟩ : syracuseStep 3714713 = 2786035) B2786035
theorem B1650347 : Blo 1649524 1650347 := bstep (se 1 (by rfl) ⟨1237760, by rfl⟩ : syracuseStep 1650347 = 2475521) B2475521
theorem B1650359 : Blo 1649524 1650359 := bstep (se 1 (by rfl) ⟨1237769, by rfl⟩ : syracuseStep 1650359 = 2475539) B2475539
theorem B7048907 : Blo 1649524 7048907 := bstep (se 1 (by rfl) ⟨5286680, by rfl⟩ : syracuseStep 7048907 = 10573361) B10573361
theorem B1650379 : Blo 1649524 1650379 := bstep (se 1 (by rfl) ⟨1237784, by rfl⟩ : syracuseStep 1650379 = 2475569) B2475569
theorem B1650391 : Blo 1649524 1650391 := bstep (se 1 (by rfl) ⟨1237793, by rfl⟩ : syracuseStep 1650391 = 2475587) B2475587
theorem B1650411 : Blo 1649524 1650411 := bstep (se 1 (by rfl) ⟨1237808, by rfl⟩ : syracuseStep 1650411 = 2475617) B2475617
theorem B3714803 : Blo 1649524 3714803 := bstep (se 1 (by rfl) ⟨2786102, by rfl⟩ : syracuseStep 3714803 = 5572205) B5572205
theorem B1650423 : Blo 1649524 1650423 := bstep (se 1 (by rfl) ⟨1237817, by rfl⟩ : syracuseStep 1650423 = 2475635) B2475635
theorem B7532291 : Blo 1649524 7532291 := bstep (se 1 (by rfl) ⟨5649218, by rfl⟩ : syracuseStep 7532291 = 11298437) B11298437
theorem B1650443 : Blo 1649524 1650443 := bstep (se 1 (by rfl) ⟨1237832, by rfl⟩ : syracuseStep 1650443 = 2475665) B2475665
theorem B1650455 : Blo 1649524 1650455 := bstep (se 1 (by rfl) ⟨1237841, by rfl⟩ : syracuseStep 1650455 = 2475683) B2475683
theorem B3714839 : Blo 1649524 3714839 := bstep (se 1 (by rfl) ⟨2786129, by rfl⟩ : syracuseStep 3714839 = 5572259) B5572259
theorem B1650475 : Blo 1649524 1650475 := bstep (se 1 (by rfl) ⟨1237856, by rfl⟩ : syracuseStep 1650475 = 2475713) B2475713
theorem B3133235 : Blo 1649524 3133235 := bstep (se 1 (by rfl) ⟨2349926, by rfl⟩ : syracuseStep 3133235 = 4699853) B4699853
theorem B1650487 : Blo 1649524 1650487 := bstep (se 1 (by rfl) ⟨1237865, by rfl⟩ : syracuseStep 1650487 = 2475731) B2475731
theorem B1650507 : Blo 1649524 1650507 := bstep (se 1 (by rfl) ⟨1237880, by rfl⟩ : syracuseStep 1650507 = 2475761) B2475761
theorem B1650519 : Blo 1649524 1650519 := bstep (se 1 (by rfl) ⟨1237889, by rfl⟩ : syracuseStep 1650519 = 2475779) B2475779
theorem B3526487 : Blo 1649524 3526487 := bstep (se 1 (by rfl) ⟨2644865, by rfl⟩ : syracuseStep 3526487 = 5289731) B5289731
theorem B1650539 : Blo 1649524 1650539 := bstep (se 1 (by rfl) ⟨1237904, by rfl⟩ : syracuseStep 1650539 = 2475809) B2475809
theorem B1650551 : Blo 1649524 1650551 := bstep (se 1 (by rfl) ⟨1237913, by rfl⟩ : syracuseStep 1650551 = 2475827) B2475827
theorem B1650571 : Blo 1649524 1650571 := bstep (se 1 (by rfl) ⟨1237928, by rfl⟩ : syracuseStep 1650571 = 2475857) B2475857
theorem B1650583 : Blo 1649524 1650583 := bstep (se 1 (by rfl) ⟨1237937, by rfl⟩ : syracuseStep 1650583 = 2475875) B2475875
theorem B8925079 : Blo 1649524 8925079 := bstep (se 1 (by rfl) ⟨6693809, by rfl⟩ : syracuseStep 8925079 = 13387619) B13387619
theorem B1650603 : Blo 1649524 1650603 := bstep (se 1 (by rfl) ⟨1237952, by rfl⟩ : syracuseStep 1650603 = 2475905) B2475905
theorem B10719155 : Blo 1649524 10719155 := bstep (se 1 (by rfl) ⟨8039366, by rfl⟩ : syracuseStep 10719155 = 16078733) B16078733
theorem B5287859 : Blo 1649524 5287859 := bstep (se 1 (by rfl) ⟨3965894, by rfl⟩ : syracuseStep 5287859 = 7931789) B7931789
theorem B1650615 : Blo 1649524 1650615 := bstep (se 1 (by rfl) ⟨1237961, by rfl⟩ : syracuseStep 1650615 = 2475923) B2475923
theorem B1650635 : Blo 1649524 1650635 := bstep (se 1 (by rfl) ⟨1237976, by rfl⟩ : syracuseStep 1650635 = 2475953) B2475953
theorem B3715019 : Blo 1649524 3715019 := bstep (se 1 (by rfl) ⟨2786264, by rfl⟩ : syracuseStep 3715019 = 5572529) B5572529
theorem B1650647 : Blo 1649524 1650647 := bstep (se 1 (by rfl) ⟨1237985, by rfl⟩ : syracuseStep 1650647 = 2475971) B2475971
theorem B1650667 : Blo 1649524 1650667 := bstep (se 1 (by rfl) ⟨1238000, by rfl⟩ : syracuseStep 1650667 = 2476001) B2476001
theorem B1650679 : Blo 1649524 1650679 := bstep (se 1 (by rfl) ⟨1238009, by rfl⟩ : syracuseStep 1650679 = 2476019) B2476019
theorem B3715073 : Blo 1649524 3715073 := bstep (se 2 (by rfl) ⟨1393152, by rfl⟩ : syracuseStep 3715073 = 2786305) B2786305
theorem B1650699 : Blo 1649524 1650699 := bstep (se 1 (by rfl) ⟨1238024, by rfl⟩ : syracuseStep 1650699 = 2476049) B2476049
theorem B17854481 : Blo 1649524 17854481 := bstep (se 2 (by rfl) ⟨6695430, by rfl⟩ : syracuseStep 17854481 = 13390861) B13390861
theorem B1650711 : Blo 1649524 1650711 := bstep (se 1 (by rfl) ⟨1238033, by rfl⟩ : syracuseStep 1650711 = 2476067) B2476067
theorem B1650731 : Blo 1649524 1650731 := bstep (se 1 (by rfl) ⟨1238048, by rfl⟩ : syracuseStep 1650731 = 2476097) B2476097
theorem B1650743 : Blo 1649524 1650743 := bstep (se 1 (by rfl) ⟨1238057, by rfl⟩ : syracuseStep 1650743 = 2476115) B2476115
theorem B1650763 : Blo 1649524 1650763 := bstep (se 1 (by rfl) ⟨1238072, by rfl⟩ : syracuseStep 1650763 = 2476145) B2476145
theorem B1650775 : Blo 1649524 1650775 := bstep (se 1 (by rfl) ⟨1238081, by rfl⟩ : syracuseStep 1650775 = 2476163) B2476163
theorem B1650795 : Blo 1649524 1650795 := bstep (se 1 (by rfl) ⟨1238096, by rfl⟩ : syracuseStep 1650795 = 2476193) B2476193
theorem B1650807 : Blo 1649524 1650807 := bstep (se 1 (by rfl) ⟨1238105, by rfl⟩ : syracuseStep 1650807 = 2476211) B2476211
theorem B1650827 : Blo 1649524 1650827 := bstep (se 1 (by rfl) ⟨1238120, by rfl⟩ : syracuseStep 1650827 = 2476241) B2476241
theorem B1650839 : Blo 1649524 1650839 := bstep (se 1 (by rfl) ⟨1238129, by rfl⟩ : syracuseStep 1650839 = 2476259) B2476259
theorem B1650859 : Blo 1649524 1650859 := bstep (se 1 (by rfl) ⟨1238144, by rfl⟩ : syracuseStep 1650859 = 2476289) B2476289
theorem B1650871 : Blo 1649524 1650871 := bstep (se 1 (by rfl) ⟨1238153, by rfl⟩ : syracuseStep 1650871 = 2476307) B2476307
theorem B1650891 : Blo 1649524 1650891 := bstep (se 1 (by rfl) ⟨1238168, by rfl⟩ : syracuseStep 1650891 = 2476337) B2476337
theorem B1650903 : Blo 1649524 1650903 := bstep (se 1 (by rfl) ⟨1238177, by rfl⟩ : syracuseStep 1650903 = 2476355) B2476355
theorem B3715289 : Blo 1649524 3715289 := bstep (se 2 (by rfl) ⟨1393233, by rfl⟩ : syracuseStep 3715289 = 2786467) B2786467
theorem B1855723 : Blo 1649524 1855723 := bstep (se 1 (by rfl) ⟨1391792, by rfl⟩ : syracuseStep 1855723 = 2783585) B2783585
theorem B1650923 : Blo 1649524 1650923 := bstep (se 1 (by rfl) ⟨1238192, by rfl⟩ : syracuseStep 1650923 = 2476385) B2476385
theorem B1650935 : Blo 1649524 1650935 := bstep (se 1 (by rfl) ⟨1238201, by rfl⟩ : syracuseStep 1650935 = 2476403) B2476403
theorem B1650955 : Blo 1649524 1650955 := bstep (se 1 (by rfl) ⟨1238216, by rfl⟩ : syracuseStep 1650955 = 2476433) B2476433
theorem B1650967 : Blo 1649524 1650967 := bstep (se 1 (by rfl) ⟨1238225, by rfl⟩ : syracuseStep 1650967 = 2476451) B2476451
theorem B3133721 : Blo 1649524 3133721 := bstep (se 2 (by rfl) ⟨1175145, by rfl⟩ : syracuseStep 3133721 = 2350291) B2350291
theorem B1650987 : Blo 1649524 1650987 := bstep (se 1 (by rfl) ⟨1238240, by rfl⟩ : syracuseStep 1650987 = 2476481) B2476481
theorem B3715379 : Blo 1649524 3715379 := bstep (se 1 (by rfl) ⟨2786534, by rfl⟩ : syracuseStep 3715379 = 5573069) B5573069
theorem B1650999 : Blo 1649524 1650999 := bstep (se 1 (by rfl) ⟨1238249, by rfl⟩ : syracuseStep 1650999 = 2476499) B2476499
theorem B5288257 : Blo 1649524 5288257 := bstep (se 2 (by rfl) ⟨1983096, by rfl⟩ : syracuseStep 5288257 = 3966193) B3966193
theorem B1651019 : Blo 1649524 1651019 := bstep (se 1 (by rfl) ⟨1238264, by rfl⟩ : syracuseStep 1651019 = 2476529) B2476529
theorem B1855831 : Blo 1649524 1855831 := bstep (se 1 (by rfl) ⟨1391873, by rfl⟩ : syracuseStep 1855831 = 2783747) B2783747
theorem B1651031 : Blo 1649524 1651031 := bstep (se 1 (by rfl) ⟨1238273, by rfl⟩ : syracuseStep 1651031 = 2476547) B2476547
theorem B3715415 : Blo 1649524 3715415 := bstep (se 1 (by rfl) ⟨2786561, by rfl⟩ : syracuseStep 3715415 = 5573123) B5573123
theorem B1651051 : Blo 1649524 1651051 := bstep (se 1 (by rfl) ⟨1238288, by rfl⟩ : syracuseStep 1651051 = 2476577) B2476577
theorem B1651063 : Blo 1649524 1651063 := bstep (se 1 (by rfl) ⟨1238297, by rfl⟩ : syracuseStep 1651063 = 2476595) B2476595
theorem B12530051 : Blo 1649524 12530051 := bstep (se 1 (by rfl) ⟨9397538, by rfl⟩ : syracuseStep 12530051 = 18795077) B18795077
theorem B1651083 : Blo 1649524 1651083 := bstep (se 1 (by rfl) ⟨1238312, by rfl⟩ : syracuseStep 1651083 = 2476625) B2476625
theorem B1651095 : Blo 1649524 1651095 := bstep (se 1 (by rfl) ⟨1238321, by rfl⟩ : syracuseStep 1651095 = 2476643) B2476643
theorem B1651115 : Blo 1649524 1651115 := bstep (se 1 (by rfl) ⟨1238336, by rfl⟩ : syracuseStep 1651115 = 2476673) B2476673
theorem B1651127 : Blo 1649524 1651127 := bstep (se 1 (by rfl) ⟨1238345, by rfl⟩ : syracuseStep 1651127 = 2476691) B2476691
theorem B1651147 : Blo 1649524 1651147 := bstep (se 1 (by rfl) ⟨1238360, by rfl⟩ : syracuseStep 1651147 = 2476721) B2476721
theorem B1651159 : Blo 1649524 1651159 := bstep (se 1 (by rfl) ⟨1238369, by rfl⟩ : syracuseStep 1651159 = 2476739) B2476739
theorem B7049693 : Blo 1649524 7049693 := bstep (se 3 (by rfl) ⟨1321817, by rfl⟩ : syracuseStep 7049693 = 2643635) B2643635
theorem B1651179 : Blo 1649524 1651179 := bstep (se 1 (by rfl) ⟨1238384, by rfl⟩ : syracuseStep 1651179 = 2476769) B2476769
theorem B1651191 : Blo 1649524 1651191 := bstep (se 1 (by rfl) ⟨1238393, by rfl⟩ : syracuseStep 1651191 = 2476787) B2476787
theorem B1856011 : Blo 1649524 1856011 := bstep (se 1 (by rfl) ⟨1392008, by rfl⟩ : syracuseStep 1856011 = 2784017) B2784017
theorem B1651211 : Blo 1649524 1651211 := bstep (se 1 (by rfl) ⟨1238408, by rfl⟩ : syracuseStep 1651211 = 2476817) B2476817
theorem B3715595 : Blo 1649524 3715595 := bstep (se 1 (by rfl) ⟨2786696, by rfl⟩ : syracuseStep 3715595 = 5573393) B5573393
theorem B1651223 : Blo 1649524 1651223 := bstep (se 1 (by rfl) ⟨1238417, by rfl⟩ : syracuseStep 1651223 = 2476835) B2476835
theorem B18805283 : Blo 1649524 18805283 := bstep (se 1 (by rfl) ⟨14103962, by rfl⟩ : syracuseStep 18805283 = 28207925) B28207925
theorem B1651243 : Blo 1649524 1651243 := bstep (se 1 (by rfl) ⟨1238432, by rfl⟩ : syracuseStep 1651243 = 2476865) B2476865
theorem B1651255 : Blo 1649524 1651255 := bstep (se 1 (by rfl) ⟨1238441, by rfl⟩ : syracuseStep 1651255 = 2476883) B2476883
theorem B3715649 : Blo 1649524 3715649 := bstep (se 2 (by rfl) ⟨1393368, by rfl⟩ : syracuseStep 3715649 = 2786737) B2786737
theorem B1651275 : Blo 1649524 1651275 := bstep (se 1 (by rfl) ⟨1238456, by rfl⟩ : syracuseStep 1651275 = 2476913) B2476913
theorem B1651287 : Blo 1649524 1651287 := bstep (se 1 (by rfl) ⟨1238465, by rfl⟩ : syracuseStep 1651287 = 2476931) B2476931
theorem B7934557 : Blo 1649524 7934557 := bstep (se 3 (by rfl) ⟨1487729, by rfl⟩ : syracuseStep 7934557 = 2975459) B2975459
theorem B1651307 : Blo 1649524 1651307 := bstep (se 1 (by rfl) ⟨1238480, by rfl⟩ : syracuseStep 1651307 = 2476961) B2476961
theorem B1856119 : Blo 1649524 1856119 := bstep (se 1 (by rfl) ⟨1392089, by rfl⟩ : syracuseStep 1856119 = 2784179) B2784179
theorem B1651319 : Blo 1649524 1651319 := bstep (se 1 (by rfl) ⟨1238489, by rfl⟩ : syracuseStep 1651319 = 2476979) B2476979
theorem B1651339 : Blo 1649524 1651339 := bstep (se 1 (by rfl) ⟨1238504, by rfl⟩ : syracuseStep 1651339 = 2477009) B2477009
theorem B1651351 : Blo 1649524 1651351 := bstep (se 1 (by rfl) ⟨1238513, by rfl⟩ : syracuseStep 1651351 = 2477027) B2477027
theorem B1651371 : Blo 1649524 1651371 := bstep (se 1 (by rfl) ⟨1238528, by rfl⟩ : syracuseStep 1651371 = 2477057) B2477057
theorem B1651383 : Blo 1649524 1651383 := bstep (se 1 (by rfl) ⟨1238537, by rfl⟩ : syracuseStep 1651383 = 2477075) B2477075
theorem B1651403 : Blo 1649524 1651403 := bstep (se 1 (by rfl) ⟨1238552, by rfl⟩ : syracuseStep 1651403 = 2477105) B2477105
theorem B1651415 : Blo 1649524 1651415 := bstep (se 1 (by rfl) ⟨1238561, by rfl⟩ : syracuseStep 1651415 = 2477123) B2477123
theorem B1651435 : Blo 1649524 1651435 := bstep (se 1 (by rfl) ⟨1238576, by rfl⟩ : syracuseStep 1651435 = 2477153) B2477153
theorem B1651447 : Blo 1649524 1651447 := bstep (se 1 (by rfl) ⟨1238585, by rfl⟩ : syracuseStep 1651447 = 2477171) B2477171
theorem B1651467 : Blo 1649524 1651467 := bstep (se 1 (by rfl) ⟨1238600, by rfl⟩ : syracuseStep 1651467 = 2477201) B2477201
theorem B1651479 : Blo 1649524 1651479 := bstep (se 1 (by rfl) ⟨1238609, by rfl⟩ : syracuseStep 1651479 = 2477219) B2477219
theorem B3715865 : Blo 1649524 3715865 := bstep (se 2 (by rfl) ⟨1393449, by rfl⟩ : syracuseStep 3715865 = 2786899) B2786899
theorem B1856299 : Blo 1649524 1856299 := bstep (se 1 (by rfl) ⟨1392224, by rfl⟩ : syracuseStep 1856299 = 2784449) B2784449
theorem B1651499 : Blo 1649524 1651499 := bstep (se 1 (by rfl) ⟨1238624, by rfl⟩ : syracuseStep 1651499 = 2477249) B2477249
theorem B8352557 : Blo 1649524 8352557 := bstep (se 3 (by rfl) ⟨1566104, by rfl⟩ : syracuseStep 8352557 = 3132209) B3132209
theorem B1651511 : Blo 1649524 1651511 := bstep (se 1 (by rfl) ⟨1238633, by rfl⟩ : syracuseStep 1651511 = 2477267) B2477267
theorem B2642777 : Blo 1649524 2642777 := bstep (se 2 (by rfl) ⟨991041, by rfl⟩ : syracuseStep 2642777 = 1982083) B1982083
theorem B53547875 : Blo 1649524 53547875 := bstep (se 1 (by rfl) ⟨40160906, by rfl⟩ : syracuseStep 53547875 = 80321813) B80321813
theorem B1856407 : Blo 1649524 1856407 := bstep (se 1 (by rfl) ⟨1392305, by rfl⟩ : syracuseStep 1856407 = 2784611) B2784611
theorem B5567453 : Blo 1649524 5567453 := bstep (se 3 (by rfl) ⟨1043897, by rfl⟩ : syracuseStep 5567453 = 2087795) B2087795
theorem B2642969 : Blo 1649524 2642969 := bstep (se 2 (by rfl) ⟨991113, by rfl⟩ : syracuseStep 2642969 = 1982227) B1982227
theorem B6689837 : Blo 1649524 6689837 := bstep (se 3 (by rfl) ⟨1254344, by rfl⟩ : syracuseStep 6689837 = 2508689) B2508689
theorem B1856587 : Blo 1649524 1856587 := bstep (se 1 (by rfl) ⟨1392440, by rfl⟩ : syracuseStep 1856587 = 2784881) B2784881
theorem B4699225 : Blo 1649524 4699225 := bstep (se 2 (by rfl) ⟨1762209, by rfl⟩ : syracuseStep 4699225 = 3524419) B3524419
theorem B3574999 : Blo 1649524 3574999 := bstep (se 1 (by rfl) ⟨2681249, by rfl⟩ : syracuseStep 3574999 = 5362499) B5362499
theorem B7935155 : Blo 1649524 7935155 := bstep (se 1 (by rfl) ⟨5951366, by rfl⟩ : syracuseStep 7935155 = 11902733) B11902733
theorem B1856695 : Blo 1649524 1856695 := bstep (se 1 (by rfl) ⟨1392521, by rfl⟩ : syracuseStep 1856695 = 2785043) B2785043
theorem B7525649 : Blo 1649524 7525649 := bstep (se 2 (by rfl) ⟨2822118, by rfl⟩ : syracuseStep 7525649 = 5644237) B5644237
theorem B1856875 : Blo 1649524 1856875 := bstep (se 1 (by rfl) ⟨1392656, by rfl⟩ : syracuseStep 1856875 = 2785313) B2785313
theorem B57193877 : Blo 1649524 57193877 := bstep (se 6 (by rfl) ⟨1340481, by rfl⟩ : syracuseStep 57193877 = 2680963) B2680963
theorem B1856983 : Blo 1649524 1856983 := bstep (se 1 (by rfl) ⟨1392737, by rfl⟩ : syracuseStep 1856983 = 2785475) B2785475
theorem B4699613 : Blo 1649524 4699613 := bstep (se 3 (by rfl) ⟨881177, by rfl⟩ : syracuseStep 4699613 = 1762355) B1762355
theorem B40138253 : Blo 1649524 40138253 := bstep (se 3 (by rfl) ⟨7525922, by rfl⟩ : syracuseStep 40138253 = 15051845) B15051845
theorem B1857163 : Blo 1649524 1857163 := bstep (se 1 (by rfl) ⟨1392872, by rfl⟩ : syracuseStep 1857163 = 2785745) B2785745
theorem B3135179 : Blo 1649524 3135179 := bstep (se 1 (by rfl) ⟨2351384, by rfl⟩ : syracuseStep 3135179 = 4702769) B4702769
theorem B1857271 : Blo 1649524 1857271 := bstep (se 1 (by rfl) ⟨1392953, by rfl⟩ : syracuseStep 1857271 = 2785907) B2785907
theorem B7051025 : Blo 1649524 7051025 := bstep (se 2 (by rfl) ⟨2644134, by rfl⟩ : syracuseStep 7051025 = 5288269) B5288269
theorem B4462411 : Blo 1649524 4462411 := bstep (se 1 (by rfl) ⟨3346808, by rfl⟩ : syracuseStep 4462411 = 6693617) B6693617
theorem B1857451 : Blo 1649524 1857451 := bstep (se 1 (by rfl) ⟨1393088, by rfl⟩ : syracuseStep 1857451 = 2786177) B2786177
theorem B4175833 : Blo 1649524 4175833 := bstep (se 2 (by rfl) ⟨1565937, by rfl⟩ : syracuseStep 4175833 = 3131875) B3131875
theorem B1857559 : Blo 1649524 1857559 := bstep (se 1 (by rfl) ⟨1393169, by rfl⟩ : syracuseStep 1857559 = 2786339) B2786339
theorem B60225605 : Blo 1649524 60225605 := bstep (se 4 (by rfl) ⟨5646150, by rfl⟩ : syracuseStep 60225605 = 11292301) B11292301
theorem B5568587 : Blo 1649524 5568587 := bstep (se 1 (by rfl) ⟨4176440, by rfl⟩ : syracuseStep 5568587 = 8352881) B8352881
theorem B1857739 : Blo 1649524 1857739 := bstep (se 1 (by rfl) ⟨1393304, by rfl⟩ : syracuseStep 1857739 = 2786609) B2786609
theorem B2349271 : Blo 1649524 2349271 := bstep (se 1 (by rfl) ⟨1761953, by rfl⟩ : syracuseStep 2349271 = 3523907) B3523907
theorem B15866117 : Blo 1649524 15866117 := bstep (se 4 (by rfl) ⟨1487448, by rfl⟩ : syracuseStep 15866117 = 2974897) B2974897
theorem B7928081 : Blo 1649524 7928081 := bstep (se 2 (by rfl) ⟨2973030, by rfl⟩ : syracuseStep 7928081 = 5946061) B5946061
theorem B6265133 : Blo 1649524 6265133 := bstep (se 3 (by rfl) ⟨1174712, by rfl⟩ : syracuseStep 6265133 = 2349425) B2349425
theorem B1857847 : Blo 1649524 1857847 := bstep (se 1 (by rfl) ⟨1393385, by rfl⟩ : syracuseStep 1857847 = 2786771) B2786771
theorem B11008331 : Blo 1649524 11008331 := bstep (se 1 (by rfl) ⟨8256248, by rfl⟩ : syracuseStep 11008331 = 16512497) B16512497
theorem B5568857 : Blo 1649524 5568857 := bstep (se 2 (by rfl) ⟨2088321, by rfl⟩ : syracuseStep 5568857 = 4176643) B4176643
theorem B2783639 : Blo 1649524 2783639 := bstep (se 1 (by rfl) ⟨2087729, by rfl⟩ : syracuseStep 2783639 = 4175459) B4175459
theorem B9402803 : Blo 1649524 9402803 := bstep (se 1 (by rfl) ⟨7052102, by rfl⟩ : syracuseStep 9402803 = 14104205) B14104205
theorem B2783767 : Blo 1649524 2783767 := bstep (se 1 (by rfl) ⟨2087825, by rfl⟩ : syracuseStep 2783767 = 4175651) B4175651
theorem B1719019 : Blo 1649524 1719019 := bstep (se 1 (by rfl) ⟨1289264, by rfl⟩ : syracuseStep 1719019 = 2578529) B2578529
theorem B23780141 : Blo 1649524 23780141 := bstep (se 3 (by rfl) ⟨4458776, by rfl⟩ : syracuseStep 23780141 = 8917553) B8917553
theorem B47586113 : Blo 1649524 47586113 := bstep (se 2 (by rfl) ⟨17844792, by rfl⟩ : syracuseStep 47586113 = 35689585) B35689585
theorem B2349977 : Blo 1649524 2349977 := bstep (se 2 (by rfl) ⟨881241, by rfl⟩ : syracuseStep 2349977 = 1762483) B1762483
theorem B2972633 : Blo 1649524 2972633 := bstep (se 2 (by rfl) ⟨1114737, by rfl⟩ : syracuseStep 2972633 = 2229475) B2229475
theorem B6028253 : Blo 1649524 6028253 := bstep (se 3 (by rfl) ⟨1130297, by rfl⟩ : syracuseStep 6028253 = 2260595) B2260595
theorem B7052291 : Blo 1649524 7052291 := bstep (se 1 (by rfl) ⟨5289218, by rfl⟩ : syracuseStep 7052291 = 10578437) B10578437
theorem B2087947 : Blo 1649524 2087947 := bstep (se 1 (by rfl) ⟨1565960, by rfl⟩ : syracuseStep 2087947 = 3131921) B3131921
theorem B2350091 : Blo 1649524 2350091 := bstep (se 1 (by rfl) ⟨1762568, by rfl⟩ : syracuseStep 2350091 = 3525137) B3525137
theorem B5569559 : Blo 1649524 5569559 := bstep (se 1 (by rfl) ⟨4177169, by rfl⟩ : syracuseStep 5569559 = 8354339) B8354339
theorem B51526691 : Blo 1649524 51526691 := bstep (se 1 (by rfl) ⟨38645018, by rfl⟩ : syracuseStep 51526691 = 77290037) B77290037
theorem B6265907 : Blo 1649524 6265907 := bstep (se 1 (by rfl) ⟨4699430, by rfl⟩ : syracuseStep 6265907 = 9398861) B9398861
theorem B5946419 : Blo 1649524 5946419 := bstep (se 1 (by rfl) ⟨4459814, by rfl⟩ : syracuseStep 5946419 = 8919629) B8919629
theorem B4176947 : Blo 1649524 4176947 := bstep (se 1 (by rfl) ⟨3132710, by rfl⟩ : syracuseStep 4176947 = 6265421) B6265421
theorem B4586561 : Blo 1649524 4586561 := bstep (se 2 (by rfl) ⟨1719960, by rfl⟩ : syracuseStep 4586561 = 3439921) B3439921
theorem B28212299 : Blo 1649524 28212299 := bstep (se 1 (by rfl) ⟨21159224, by rfl⟩ : syracuseStep 28212299 = 42318449) B42318449
theorem B2784395 : Blo 1649524 2784395 := bstep (se 1 (by rfl) ⟨2088296, by rfl⟩ : syracuseStep 2784395 = 4176593) B4176593
theorem B13376663 : Blo 1649524 13376663 := bstep (se 1 (by rfl) ⟨10032497, by rfl⟩ : syracuseStep 13376663 = 20064995) B20064995
theorem B2784523 : Blo 1649524 2784523 := bstep (se 1 (by rfl) ⟨2088392, by rfl⟩ : syracuseStep 2784523 = 4176785) B4176785
theorem B2972951 : Blo 1649524 2972951 := bstep (se 1 (by rfl) ⟨2229713, by rfl⟩ : syracuseStep 2972951 = 4459427) B4459427
theorem B12541229 : Blo 1649524 12541229 := bstep (se 3 (by rfl) ⟨2351480, by rfl⟩ : syracuseStep 12541229 = 4702961) B4702961
theorem B4177241 : Blo 1649524 4177241 := bstep (se 2 (by rfl) ⟨1566465, by rfl⟩ : syracuseStep 4177241 = 3132931) B3132931
theorem B6438275 : Blo 1649524 6438275 := bstep (se 1 (by rfl) ⟨4828706, by rfl⟩ : syracuseStep 6438275 = 9657413) B9657413
theorem B2784665 : Blo 1649524 2784665 := bstep (se 2 (by rfl) ⟨1044249, by rfl⟩ : syracuseStep 2784665 = 2088499) B2088499
theorem B2350615 : Blo 1649524 2350615 := bstep (se 1 (by rfl) ⟨1762961, by rfl⟩ : syracuseStep 2350615 = 3525923) B3525923
theorem B2784793 : Blo 1649524 2784793 := bstep (se 2 (by rfl) ⟨1044297, by rfl⟩ : syracuseStep 2784793 = 2088595) B2088595
theorem B5570099 : Blo 1649524 5570099 := bstep (se 1 (by rfl) ⟨4177574, by rfl⟩ : syracuseStep 5570099 = 8355149) B8355149
theorem B6692483 : Blo 1649524 6692483 := bstep (se 1 (by rfl) ⟨5019362, by rfl⟩ : syracuseStep 6692483 = 10038725) B10038725
theorem B38125187 : Blo 1649524 38125187 := bstep (se 1 (by rfl) ⟨28593890, by rfl⟩ : syracuseStep 38125187 = 57187781) B57187781
theorem B73334477 : Blo 1649524 73334477 := bstep (se 3 (by rfl) ⟨13750214, by rfl⟩ : syracuseStep 73334477 = 27500429) B27500429
theorem B12533453 : Blo 1649524 12533453 := bstep (se 3 (by rfl) ⟨2350022, by rfl⟩ : syracuseStep 12533453 = 4700045) B4700045
theorem B5570369 : Blo 1649524 5570369 := bstep (se 2 (by rfl) ⟨2088888, by rfl⟩ : syracuseStep 5570369 = 4177777) B4177777
theorem B9404261 : Blo 1649524 9404261 := bstep (se 4 (by rfl) ⟨881649, by rfl⟩ : syracuseStep 9404261 = 1763299) B1763299
theorem B2088919 : Blo 1649524 2088919 := bstep (se 1 (by rfl) ⟨1566689, by rfl⟩ : syracuseStep 2088919 = 3133379) B3133379
theorem B11902987 : Blo 1649524 11902987 := bstep (se 1 (by rfl) ⟨8927240, by rfl⟩ : syracuseStep 11902987 = 17854481) B17854481
theorem B6266909 : Blo 1649524 6266909 := bstep (se 3 (by rfl) ⟨1175045, by rfl⟩ : syracuseStep 6266909 = 2350091) B2350091
theorem B8355959 : Blo 1649524 8355959 := bstep (se 1 (by rfl) ⟨6266969, by rfl⟩ : syracuseStep 8355959 = 12533939) B12533939
theorem B2089147 : Blo 1649524 2089147 := bstep (se 1 (by rfl) ⟨1566860, by rfl⟩ : syracuseStep 2089147 = 3133721) B3133721
theorem B7143661 : Blo 1649524 7143661 := bstep (se 3 (by rfl) ⟨1339436, by rfl⟩ : syracuseStep 7143661 = 2678873) B2678873
theorem B2474297 : Blo 1649524 2474297 := bstep (se 2 (by rfl) ⟨927861, by rfl⟩ : syracuseStep 2474297 = 1855723) B1855723
theorem B4178263 : Blo 1649524 4178263 := bstep (se 1 (by rfl) ⟨3133697, by rfl⟩ : syracuseStep 4178263 = 6267395) B6267395
theorem B128647541 : Blo 1649524 128647541 := bstep (se 5 (by rfl) ⟨6030353, by rfl⟩ : syracuseStep 128647541 = 12060707) B12060707
theorem B2474375 : Blo 1649524 2474375 := bstep (se 1 (by rfl) ⟨1855781, by rfl⟩ : syracuseStep 2474375 = 3711563) B3711563
theorem B10043783 : Blo 1649524 10043783 := bstep (se 1 (by rfl) ⟨7532837, by rfl⟩ : syracuseStep 10043783 = 15065675) B15065675
theorem B5570963 : Blo 1649524 5570963 := bstep (se 1 (by rfl) ⟨4178222, by rfl⟩ : syracuseStep 5570963 = 8356445) B8356445
theorem B2474411 : Blo 1649524 2474411 := bstep (se 1 (by rfl) ⟨1855808, by rfl⟩ : syracuseStep 2474411 = 3711617) B3711617
theorem B2474441 : Blo 1649524 2474441 := bstep (se 2 (by rfl) ⟨927915, by rfl⟩ : syracuseStep 2474441 = 1855831) B1855831
theorem B2474555 : Blo 1649524 2474555 := bstep (se 1 (by rfl) ⟨1855916, by rfl⟩ : syracuseStep 2474555 = 3711833) B3711833
theorem B1761851 : Blo 1649524 1761851 := bstep (se 1 (by rfl) ⟨1321388, by rfl⟩ : syracuseStep 1761851 = 2642777) B2642777
theorem B2474615 : Blo 1649524 2474615 := bstep (se 1 (by rfl) ⟨1855961, by rfl⟩ : syracuseStep 2474615 = 3711923) B3711923
theorem B4178567 : Blo 1649524 4178567 := bstep (se 1 (by rfl) ⟨3133925, by rfl⟩ : syracuseStep 4178567 = 6267851) B6267851
theorem B2785927 : Blo 1649524 2785927 := bstep (se 1 (by rfl) ⟨2089445, by rfl⟩ : syracuseStep 2785927 = 4178891) B4178891
theorem B2474639 : Blo 1649524 2474639 := bstep (se 1 (by rfl) ⟨1855979, by rfl⟩ : syracuseStep 2474639 = 3711959) B3711959
theorem B3711635 : Blo 1649524 3711635 := bstep (se 1 (by rfl) ⟨2783726, by rfl⟩ : syracuseStep 3711635 = 5567453) B5567453
theorem B7930541 : Blo 1649524 7930541 := bstep (se 3 (by rfl) ⟨1486976, by rfl⟩ : syracuseStep 7930541 = 2973953) B2973953
theorem B2474681 : Blo 1649524 2474681 := bstep (se 2 (by rfl) ⟨928005, by rfl⟩ : syracuseStep 2474681 = 1856011) B1856011
theorem B3711689 : Blo 1649524 3711689 := bstep (se 2 (by rfl) ⟨1391883, by rfl⟩ : syracuseStep 3711689 = 2783767) B2783767
theorem B2474759 : Blo 1649524 2474759 := bstep (se 1 (by rfl) ⟨1856069, by rfl⟩ : syracuseStep 2474759 = 3712139) B3712139
theorem B4178699 : Blo 1649524 4178699 := bstep (se 1 (by rfl) ⟨3134024, by rfl⟩ : syracuseStep 4178699 = 6268049) B6268049
theorem B2474795 : Blo 1649524 2474795 := bstep (se 1 (by rfl) ⟨1856096, by rfl⟩ : syracuseStep 2474795 = 3712193) B3712193
theorem B2474825 : Blo 1649524 2474825 := bstep (se 2 (by rfl) ⟨928059, by rfl⟩ : syracuseStep 2474825 = 1856119) B1856119
theorem B2474939 : Blo 1649524 2474939 := bstep (se 1 (by rfl) ⟨1856204, by rfl⟩ : syracuseStep 2474939 = 3712409) B3712409
theorem B2474999 : Blo 1649524 2474999 := bstep (se 1 (by rfl) ⟨1856249, by rfl⟩ : syracuseStep 2474999 = 3712499) B3712499
theorem B2475023 : Blo 1649524 2475023 := bstep (se 1 (by rfl) ⟨1856267, by rfl⟩ : syracuseStep 2475023 = 3712535) B3712535
theorem B2475065 : Blo 1649524 2475065 := bstep (se 2 (by rfl) ⟨928149, by rfl⟩ : syracuseStep 2475065 = 1856299) B1856299
theorem B5358653 : Blo 1649524 5358653 := bstep (se 3 (by rfl) ⟨1004747, by rfl⟩ : syracuseStep 5358653 = 2009495) B2009495
theorem B8356931 : Blo 1649524 8356931 := bstep (se 1 (by rfl) ⟨6267698, by rfl⟩ : syracuseStep 8356931 = 12535397) B12535397
theorem B2475143 : Blo 1649524 2475143 := bstep (se 1 (by rfl) ⟨1856357, by rfl⟩ : syracuseStep 2475143 = 3712715) B3712715
theorem B2090119 : Blo 1649524 2090119 := bstep (se 1 (by rfl) ⟨1567589, by rfl⟩ : syracuseStep 2090119 = 3135179) B3135179
theorem B2475179 : Blo 1649524 2475179 := bstep (se 1 (by rfl) ⟨1856384, by rfl⟩ : syracuseStep 2475179 = 3712769) B3712769
theorem B2475209 : Blo 1649524 2475209 := bstep (se 2 (by rfl) ⟨928203, by rfl⟩ : syracuseStep 2475209 = 1856407) B1856407
theorem B4179215 : Blo 1649524 4179215 := bstep (se 1 (by rfl) ⟨3134411, by rfl⟩ : syracuseStep 4179215 = 6268823) B6268823
theorem B2786575 : Blo 1649524 2786575 := bstep (se 1 (by rfl) ⟨2089931, by rfl⟩ : syracuseStep 2786575 = 4179863) B4179863
theorem B3966241 : Blo 1649524 3966241 := bstep (se 2 (by rfl) ⟨1487340, by rfl⟩ : syracuseStep 3966241 = 2974681) B2974681
theorem B2475323 : Blo 1649524 2475323 := bstep (se 1 (by rfl) ⟨1856492, by rfl⟩ : syracuseStep 2475323 = 3712985) B3712985
theorem B2475383 : Blo 1649524 2475383 := bstep (se 1 (by rfl) ⟨1856537, by rfl⟩ : syracuseStep 2475383 = 3713075) B3713075
theorem B40150403 : Blo 1649524 40150403 := bstep (se 1 (by rfl) ⟨30112802, by rfl⟩ : syracuseStep 40150403 = 60225605) B60225605
theorem B3712391 : Blo 1649524 3712391 := bstep (se 1 (by rfl) ⟨2784293, by rfl⟩ : syracuseStep 3712391 = 5568587) B5568587
theorem B8357255 : Blo 1649524 8357255 := bstep (se 1 (by rfl) ⟨6267941, by rfl⟩ : syracuseStep 8357255 = 12535883) B12535883
theorem B2475407 : Blo 1649524 2475407 := bstep (se 1 (by rfl) ⟨1856555, by rfl⟩ : syracuseStep 2475407 = 3713111) B3713111
theorem B4179347 : Blo 1649524 4179347 := bstep (se 1 (by rfl) ⟨3134510, by rfl⟩ : syracuseStep 4179347 = 6269021) B6269021
theorem B2475449 : Blo 1649524 2475449 := bstep (se 2 (by rfl) ⟨928293, by rfl⟩ : syracuseStep 2475449 = 1856587) B1856587
theorem B10577411 : Blo 1649524 10577411 := bstep (se 1 (by rfl) ⟨7933058, by rfl⟩ : syracuseStep 10577411 = 15866117) B15866117
theorem B2475527 : Blo 1649524 2475527 := bstep (se 1 (by rfl) ⟨1856645, by rfl⟩ : syracuseStep 2475527 = 3713291) B3713291
theorem B5285387 : Blo 1649524 5285387 := bstep (se 1 (by rfl) ⟨3964040, by rfl⟩ : syracuseStep 5285387 = 7928081) B7928081
theorem B16934429 : Blo 1649524 16934429 := bstep (se 3 (by rfl) ⟨3175205, by rfl⟩ : syracuseStep 16934429 = 6350411) B6350411
theorem B5948957 : Blo 1649524 5948957 := bstep (se 3 (by rfl) ⟨1115429, by rfl⟩ : syracuseStep 5948957 = 2230859) B2230859
theorem B2475563 : Blo 1649524 2475563 := bstep (se 1 (by rfl) ⟨1856672, by rfl⟩ : syracuseStep 2475563 = 3713345) B3713345
theorem B3712571 : Blo 1649524 3712571 := bstep (se 1 (by rfl) ⟨2784428, by rfl⟩ : syracuseStep 3712571 = 5568857) B5568857
theorem B2475593 : Blo 1649524 2475593 := bstep (se 2 (by rfl) ⟨928347, by rfl⟩ : syracuseStep 2475593 = 1856695) B1856695
theorem B6268535 : Blo 1649524 6268535 := bstep (se 1 (by rfl) ⟨4701401, by rfl⟩ : syracuseStep 6268535 = 9402803) B9402803
theorem B3712697 : Blo 1649524 3712697 := bstep (se 2 (by rfl) ⟨1392261, by rfl⟩ : syracuseStep 3712697 = 2784523) B2784523
theorem B2475707 : Blo 1649524 2475707 := bstep (se 1 (by rfl) ⟨1856780, by rfl⟩ : syracuseStep 2475707 = 3713561) B3713561
theorem B2475767 : Blo 1649524 2475767 := bstep (se 1 (by rfl) ⟨1856825, by rfl⟩ : syracuseStep 2475767 = 3713651) B3713651
theorem B2475791 : Blo 1649524 2475791 := bstep (se 1 (by rfl) ⟨1856843, by rfl⟩ : syracuseStep 2475791 = 3713687) B3713687
theorem B5572367 : Blo 1649524 5572367 := bstep (se 1 (by rfl) ⟨4179275, by rfl⟩ : syracuseStep 5572367 = 8358551) B8358551
theorem B2475833 : Blo 1649524 2475833 := bstep (se 2 (by rfl) ⟨928437, by rfl⟩ : syracuseStep 2475833 = 1856875) B1856875
theorem B3524411 : Blo 1649524 3524411 := bstep (se 1 (by rfl) ⟨2643308, by rfl⟩ : syracuseStep 3524411 = 5286617) B5286617
theorem B23807819 : Blo 1649524 23807819 := bstep (se 1 (by rfl) ⟨17855864, by rfl⟩ : syracuseStep 23807819 = 35711729) B35711729
theorem B15853427 : Blo 1649524 15853427 := bstep (se 1 (by rfl) ⟨11890070, by rfl⟩ : syracuseStep 15853427 = 23780141) B23780141
theorem B2475911 : Blo 1649524 2475911 := bstep (se 1 (by rfl) ⟨1856933, by rfl⟩ : syracuseStep 2475911 = 3713867) B3713867
theorem B14108579 : Blo 1649524 14108579 := bstep (se 1 (by rfl) ⟨10581434, by rfl⟩ : syracuseStep 14108579 = 21162869) B21162869
theorem B2475947 : Blo 1649524 2475947 := bstep (se 1 (by rfl) ⟨1856960, by rfl⟩ : syracuseStep 2475947 = 3713921) B3713921
theorem B2475977 : Blo 1649524 2475977 := bstep (se 2 (by rfl) ⟨928491, by rfl⟩ : syracuseStep 2475977 = 1856983) B1856983
theorem B3713039 : Blo 1649524 3713039 := bstep (se 1 (by rfl) ⟨2784779, by rfl⟩ : syracuseStep 3713039 = 5569559) B5569559
theorem B34351127 : Blo 1649524 34351127 := bstep (se 1 (by rfl) ⟨25763345, by rfl⟩ : syracuseStep 34351127 = 51526691) B51526691
theorem B5572637 : Blo 1649524 5572637 := bstep (se 3 (by rfl) ⟨1044869, by rfl⟩ : syracuseStep 5572637 = 2089739) B2089739
theorem B3713057 : Blo 1649524 3713057 := bstep (se 2 (by rfl) ⟨1392396, by rfl⟩ : syracuseStep 3713057 = 2784793) B2784793
theorem B3057707 : Blo 1649524 3057707 := bstep (se 1 (by rfl) ⟨2293280, by rfl⟩ : syracuseStep 3057707 = 4586561) B4586561
theorem B2476091 : Blo 1649524 2476091 := bstep (se 1 (by rfl) ⟨1857068, by rfl⟩ : syracuseStep 2476091 = 3714137) B3714137
theorem B2476151 : Blo 1649524 2476151 := bstep (se 1 (by rfl) ⟨1857113, by rfl⟩ : syracuseStep 2476151 = 3714227) B3714227
theorem B2476175 : Blo 1649524 2476175 := bstep (se 1 (by rfl) ⟨1857131, by rfl⟩ : syracuseStep 2476175 = 3714263) B3714263
theorem B2476217 : Blo 1649524 2476217 := bstep (se 2 (by rfl) ⟨928581, by rfl⟩ : syracuseStep 2476217 = 1857163) B1857163
theorem B2230535 : Blo 1649524 2230535 := bstep (se 1 (by rfl) ⟨1672901, by rfl⟩ : syracuseStep 2230535 = 3345803) B3345803
theorem B2476295 : Blo 1649524 2476295 := bstep (se 1 (by rfl) ⟨1857221, by rfl⟩ : syracuseStep 2476295 = 3714443) B3714443
theorem B2476331 : Blo 1649524 2476331 := bstep (se 1 (by rfl) ⟨1857248, by rfl⟩ : syracuseStep 2476331 = 3714497) B3714497
theorem B2476361 : Blo 1649524 2476361 := bstep (se 2 (by rfl) ⟨928635, by rfl⟩ : syracuseStep 2476361 = 1857271) B1857271
theorem B3713399 : Blo 1649524 3713399 := bstep (se 1 (by rfl) ⟨2785049, by rfl⟩ : syracuseStep 3713399 = 5570099) B5570099
theorem B5949881 : Blo 1649524 5949881 := bstep (se 2 (by rfl) ⟨2231205, by rfl⟩ : syracuseStep 5949881 = 4462411) B4462411
theorem B2476475 : Blo 1649524 2476475 := bstep (se 1 (by rfl) ⟨1857356, by rfl⟩ : syracuseStep 2476475 = 3714713) B3714713
theorem B3967433 : Blo 1649524 3967433 := bstep (se 2 (by rfl) ⟨1487787, by rfl⟩ : syracuseStep 3967433 = 2975575) B2975575
theorem B2476535 : Blo 1649524 2476535 := bstep (se 1 (by rfl) ⟨1857401, by rfl⟩ : syracuseStep 2476535 = 3714803) B3714803
theorem B2476559 : Blo 1649524 2476559 := bstep (se 1 (by rfl) ⟨1857419, by rfl⟩ : syracuseStep 2476559 = 3714839) B3714839
theorem B3713579 : Blo 1649524 3713579 := bstep (se 1 (by rfl) ⟨2785184, by rfl⟩ : syracuseStep 3713579 = 5570369) B5570369
theorem B2476601 : Blo 1649524 2476601 := bstep (se 2 (by rfl) ⟨928725, by rfl⟩ : syracuseStep 2476601 = 1857451) B1857451
theorem B6269507 : Blo 1649524 6269507 := bstep (se 1 (by rfl) ⟨4702130, by rfl⟩ : syracuseStep 6269507 = 9404261) B9404261
theorem B7146103 : Blo 1649524 7146103 := bstep (se 1 (by rfl) ⟨5359577, by rfl⟩ : syracuseStep 7146103 = 10719155) B10719155
theorem B3525239 : Blo 1649524 3525239 := bstep (se 1 (by rfl) ⟨2643929, by rfl⟩ : syracuseStep 3525239 = 5287859) B5287859
theorem B2476679 : Blo 1649524 2476679 := bstep (se 1 (by rfl) ⟨1857509, by rfl⟩ : syracuseStep 2476679 = 3715019) B3715019
theorem B2476715 : Blo 1649524 2476715 := bstep (se 1 (by rfl) ⟨1857536, by rfl⟩ : syracuseStep 2476715 = 3715073) B3715073
theorem B7047881 : Blo 1649524 7047881 := bstep (se 2 (by rfl) ⟨2642955, by rfl⟩ : syracuseStep 7047881 = 5285911) B5285911
theorem B2476745 : Blo 1649524 2476745 := bstep (se 2 (by rfl) ⟨928779, by rfl⟩ : syracuseStep 2476745 = 1857559) B1857559
theorem B7047917 : Blo 1649524 7047917 := bstep (se 3 (by rfl) ⟨1321484, by rfl⟩ : syracuseStep 7047917 = 2642969) B2642969
theorem B2476859 : Blo 1649524 2476859 := bstep (se 1 (by rfl) ⟨1857644, by rfl⟩ : syracuseStep 2476859 = 3715289) B3715289
theorem B2476919 : Blo 1649524 2476919 := bstep (se 1 (by rfl) ⟨1857689, by rfl⟩ : syracuseStep 2476919 = 3715379) B3715379
theorem B1649543 : Blo 1649524 1649543 := bstep (se 1 (by rfl) ⟨1237157, by rfl⟩ : syracuseStep 1649543 = 2474315) B2474315
theorem B1649551 : Blo 1649524 1649551 := bstep (se 1 (by rfl) ⟨1237163, by rfl⟩ : syracuseStep 1649551 = 2474327) B2474327
theorem B2476943 : Blo 1649524 2476943 := bstep (se 1 (by rfl) ⟨1857707, by rfl⟩ : syracuseStep 2476943 = 3715415) B3715415
theorem B3713939 : Blo 1649524 3713939 := bstep (se 1 (by rfl) ⟨2785454, by rfl⟩ : syracuseStep 3713939 = 5570909) B5570909
theorem B2476985 : Blo 1649524 2476985 := bstep (se 2 (by rfl) ⟨928869, by rfl⟩ : syracuseStep 2476985 = 1857739) B1857739
theorem B1649595 : Blo 1649524 1649595 := bstep (se 1 (by rfl) ⟨1237196, by rfl⟩ : syracuseStep 1649595 = 2474393) B2474393
theorem B3132361 : Blo 1649524 3132361 := bstep (se 2 (by rfl) ⟨1174635, by rfl⟩ : syracuseStep 3132361 = 2349271) B2349271
theorem B3713993 : Blo 1649524 3713993 := bstep (se 2 (by rfl) ⟨1392747, by rfl⟩ : syracuseStep 3713993 = 2785495) B2785495
theorem B14298059 : Blo 1649524 14298059 := bstep (se 1 (by rfl) ⟨10723544, by rfl⟩ : syracuseStep 14298059 = 21447089) B21447089
theorem B15870923 : Blo 1649524 15870923 := bstep (se 1 (by rfl) ⟨11903192, by rfl⟩ : syracuseStep 15870923 = 23806385) B23806385
theorem B1649671 : Blo 1649524 1649671 := bstep (se 1 (by rfl) ⟨1237253, by rfl⟩ : syracuseStep 1649671 = 2474507) B2474507
theorem B2477063 : Blo 1649524 2477063 := bstep (se 1 (by rfl) ⟨1857797, by rfl⟩ : syracuseStep 2477063 = 3715595) B3715595
theorem B1649679 : Blo 1649524 1649679 := bstep (se 1 (by rfl) ⟨1237259, by rfl⟩ : syracuseStep 1649679 = 2474519) B2474519
theorem B12536855 : Blo 1649524 12536855 := bstep (se 1 (by rfl) ⟨9402641, by rfl⟩ : syracuseStep 12536855 = 18805283) B18805283
theorem B2477099 : Blo 1649524 2477099 := bstep (se 1 (by rfl) ⟨1857824, by rfl⟩ : syracuseStep 2477099 = 3715649) B3715649
theorem B1649723 : Blo 1649524 1649723 := bstep (se 1 (by rfl) ⟨1237292, by rfl⟩ : syracuseStep 1649723 = 2474585) B2474585
theorem B2477129 : Blo 1649524 2477129 := bstep (se 2 (by rfl) ⟨928923, by rfl⟩ : syracuseStep 2477129 = 1857847) B1857847
theorem B1649799 : Blo 1649524 1649799 := bstep (se 1 (by rfl) ⟨1237349, by rfl⟩ : syracuseStep 1649799 = 2474699) B2474699
theorem B1649807 : Blo 1649524 1649807 := bstep (se 1 (by rfl) ⟨1237355, by rfl⟩ : syracuseStep 1649807 = 2474711) B2474711
theorem B1649851 : Blo 1649524 1649851 := bstep (se 1 (by rfl) ⟨1237388, by rfl⟩ : syracuseStep 1649851 = 2474777) B2474777
theorem B2477243 : Blo 1649524 2477243 := bstep (se 1 (by rfl) ⟨1857932, by rfl⟩ : syracuseStep 2477243 = 3715865) B3715865
theorem B8039681 : Blo 1649524 8039681 := bstep (se 2 (by rfl) ⟨3014880, by rfl⟩ : syracuseStep 8039681 = 6029761) B6029761
theorem B1649927 : Blo 1649524 1649927 := bstep (se 1 (by rfl) ⟨1237445, by rfl⟩ : syracuseStep 1649927 = 2474891) B2474891
theorem B1649935 : Blo 1649524 1649935 := bstep (se 1 (by rfl) ⟨1237451, by rfl⟩ : syracuseStep 1649935 = 2474903) B2474903
theorem B15871265 : Blo 1649524 15871265 := bstep (se 2 (by rfl) ⟨5951724, by rfl⟩ : syracuseStep 15871265 = 11903449) B11903449
theorem B1649979 : Blo 1649524 1649979 := bstep (se 1 (by rfl) ⟨1237484, by rfl⟩ : syracuseStep 1649979 = 2474969) B2474969
theorem B1650055 : Blo 1649524 1650055 := bstep (se 1 (by rfl) ⟨1237541, by rfl⟩ : syracuseStep 1650055 = 2475083) B2475083
theorem B1650063 : Blo 1649524 1650063 := bstep (se 1 (by rfl) ⟨1237547, by rfl⟩ : syracuseStep 1650063 = 2475095) B2475095
theorem B7048633 : Blo 1649524 7048633 := bstep (se 2 (by rfl) ⟨2643237, by rfl⟩ : syracuseStep 7048633 = 5286475) B5286475
theorem B1650107 : Blo 1649524 1650107 := bstep (se 1 (by rfl) ⟨1237580, by rfl⟩ : syracuseStep 1650107 = 2475161) B2475161
theorem B10579409 : Blo 1649524 10579409 := bstep (se 2 (by rfl) ⟨3967278, by rfl⟩ : syracuseStep 10579409 = 7934557) B7934557
theorem B1650183 : Blo 1649524 1650183 := bstep (se 1 (by rfl) ⟨1237637, by rfl⟩ : syracuseStep 1650183 = 2475275) B2475275
theorem B5017099 : Blo 1649524 5017099 := bstep (se 1 (by rfl) ⟨3762824, by rfl⟩ : syracuseStep 5017099 = 7525649) B7525649
theorem B1650191 : Blo 1649524 1650191 := bstep (se 1 (by rfl) ⟨1237643, by rfl⟩ : syracuseStep 1650191 = 2475287) B2475287
theorem B8351261 : Blo 1649524 8351261 := bstep (se 3 (by rfl) ⟨1565861, by rfl⟩ : syracuseStep 8351261 = 3131723) B3131723
theorem B6270493 : Blo 1649524 6270493 := bstep (se 3 (by rfl) ⟨1175717, by rfl⟩ : syracuseStep 6270493 = 2351435) B2351435
theorem B1650235 : Blo 1649524 1650235 := bstep (se 1 (by rfl) ⟨1237676, by rfl⟩ : syracuseStep 1650235 = 2475353) B2475353
theorem B1650311 : Blo 1649524 1650311 := bstep (se 1 (by rfl) ⟨1237733, by rfl⟩ : syracuseStep 1650311 = 2475467) B2475467
theorem B3714695 : Blo 1649524 3714695 := bstep (se 1 (by rfl) ⟨2786021, by rfl⟩ : syracuseStep 3714695 = 5572043) B5572043
theorem B1650319 : Blo 1649524 1650319 := bstep (se 1 (by rfl) ⟨1237739, by rfl⟩ : syracuseStep 1650319 = 2475479) B2475479
theorem B3133075 : Blo 1649524 3133075 := bstep (se 1 (by rfl) ⟨2349806, by rfl⟩ : syracuseStep 3133075 = 4699613) B4699613
theorem B26758835 : Blo 1649524 26758835 := bstep (se 1 (by rfl) ⟨20069126, by rfl⟩ : syracuseStep 26758835 = 40138253) B40138253
theorem B1650363 : Blo 1649524 1650363 := bstep (se 1 (by rfl) ⟨1237772, by rfl⟩ : syracuseStep 1650363 = 2475545) B2475545
theorem B1650439 : Blo 1649524 1650439 := bstep (se 1 (by rfl) ⟨1237829, by rfl⟩ : syracuseStep 1650439 = 2475659) B2475659
theorem B1650447 : Blo 1649524 1650447 := bstep (se 1 (by rfl) ⟨1237835, by rfl⟩ : syracuseStep 1650447 = 2475671) B2475671
theorem B19066661 : Blo 1649524 19066661 := bstep (se 4 (by rfl) ⟨1787499, by rfl⟩ : syracuseStep 19066661 = 3574999) B3574999
theorem B1650491 : Blo 1649524 1650491 := bstep (se 1 (by rfl) ⟨1237868, by rfl⟩ : syracuseStep 1650491 = 2475737) B2475737
theorem B3714875 : Blo 1649524 3714875 := bstep (se 1 (by rfl) ⟨2786156, by rfl⟩ : syracuseStep 3714875 = 5572313) B5572313
theorem B1650567 : Blo 1649524 1650567 := bstep (se 1 (by rfl) ⟨1237925, by rfl⟩ : syracuseStep 1650567 = 2475851) B2475851
theorem B1650575 : Blo 1649524 1650575 := bstep (se 1 (by rfl) ⟨1237931, by rfl⟩ : syracuseStep 1650575 = 2475863) B2475863
theorem B3715001 : Blo 1649524 3715001 := bstep (se 2 (by rfl) ⟨1393125, by rfl⟩ : syracuseStep 3715001 = 2786251) B2786251
theorem B1650619 : Blo 1649524 1650619 := bstep (se 1 (by rfl) ⟨1237964, by rfl⟩ : syracuseStep 1650619 = 2475929) B2475929
theorem B8351747 : Blo 1649524 8351747 := bstep (se 1 (by rfl) ⟨6263810, by rfl⟩ : syracuseStep 8351747 = 12527621) B12527621
theorem B1650695 : Blo 1649524 1650695 := bstep (se 1 (by rfl) ⟨1238021, by rfl⟩ : syracuseStep 1650695 = 2476043) B2476043
theorem B1650703 : Blo 1649524 1650703 := bstep (se 1 (by rfl) ⟨1238027, by rfl⟩ : syracuseStep 1650703 = 2476055) B2476055
theorem B4698155 : Blo 1649524 4698155 := bstep (se 1 (by rfl) ⟨3523616, by rfl⟩ : syracuseStep 4698155 = 7047233) B7047233
theorem B1650747 : Blo 1649524 1650747 := bstep (se 1 (by rfl) ⟨1238060, by rfl⟩ : syracuseStep 1650747 = 2476121) B2476121
theorem B1650823 : Blo 1649524 1650823 := bstep (se 1 (by rfl) ⟨1238117, by rfl⟩ : syracuseStep 1650823 = 2476235) B2476235
theorem B1650831 : Blo 1649524 1650831 := bstep (se 1 (by rfl) ⟨1238123, by rfl⟩ : syracuseStep 1650831 = 2476247) B2476247
theorem B1650875 : Blo 1649524 1650875 := bstep (se 1 (by rfl) ⟨1238156, by rfl⟩ : syracuseStep 1650875 = 2476313) B2476313
theorem B1650951 : Blo 1649524 1650951 := bstep (se 1 (by rfl) ⟨1238213, by rfl⟩ : syracuseStep 1650951 = 2476427) B2476427
theorem B1855759 : Blo 1649524 1855759 := bstep (se 1 (by rfl) ⟨1391819, by rfl⟩ : syracuseStep 1855759 = 2783639) B2783639
theorem B1650959 : Blo 1649524 1650959 := bstep (se 1 (by rfl) ⟨1238219, by rfl⟩ : syracuseStep 1650959 = 2476439) B2476439
theorem B3715343 : Blo 1649524 3715343 := bstep (se 1 (by rfl) ⟨2786507, by rfl⟩ : syracuseStep 3715343 = 5573015) B5573015
theorem B3715361 : Blo 1649524 3715361 := bstep (se 2 (by rfl) ⟨1393260, by rfl⟩ : syracuseStep 3715361 = 2786521) B2786521
theorem B1651003 : Blo 1649524 1651003 := bstep (se 1 (by rfl) ⟨1238252, by rfl⟩ : syracuseStep 1651003 = 2476505) B2476505
theorem B1651079 : Blo 1649524 1651079 := bstep (se 1 (by rfl) ⟨1238309, by rfl⟩ : syracuseStep 1651079 = 2476619) B2476619
theorem B1651087 : Blo 1649524 1651087 := bstep (se 1 (by rfl) ⟨1238315, by rfl⟩ : syracuseStep 1651087 = 2476631) B2476631
theorem B10039697 : Blo 1649524 10039697 := bstep (se 2 (by rfl) ⟨3764886, by rfl⟩ : syracuseStep 10039697 = 7529773) B7529773
theorem B1651131 : Blo 1649524 1651131 := bstep (se 1 (by rfl) ⟨1238348, by rfl⟩ : syracuseStep 1651131 = 2476697) B2476697
theorem B25399793 : Blo 1649524 25399793 := bstep (se 2 (by rfl) ⟨9524922, by rfl⟩ : syracuseStep 25399793 = 19049845) B19049845
theorem B1651207 : Blo 1649524 1651207 := bstep (se 1 (by rfl) ⟨1238405, by rfl⟩ : syracuseStep 1651207 = 2476811) B2476811
theorem B1651215 : Blo 1649524 1651215 := bstep (se 1 (by rfl) ⟨1238411, by rfl⟩ : syracuseStep 1651215 = 2476823) B2476823
theorem B31724075 : Blo 1649524 31724075 := bstep (se 1 (by rfl) ⟨23793056, by rfl⟩ : syracuseStep 31724075 = 47586113) B47586113
theorem B1651259 : Blo 1649524 1651259 := bstep (se 1 (by rfl) ⟨1238444, by rfl⟩ : syracuseStep 1651259 = 2476889) B2476889
theorem B15856195 : Blo 1649524 15856195 := bstep (se 1 (by rfl) ⟨11892146, by rfl⟩ : syracuseStep 15856195 = 23784293) B23784293
theorem B3715703 : Blo 1649524 3715703 := bstep (se 1 (by rfl) ⟨2786777, by rfl⟩ : syracuseStep 3715703 = 5573555) B5573555
theorem B1651335 : Blo 1649524 1651335 := bstep (se 1 (by rfl) ⟨1238501, by rfl⟩ : syracuseStep 1651335 = 2477003) B2477003
theorem B1651343 : Blo 1649524 1651343 := bstep (se 1 (by rfl) ⟨1238507, by rfl⟩ : syracuseStep 1651343 = 2477015) B2477015
theorem B4018835 : Blo 1649524 4018835 := bstep (se 1 (by rfl) ⟨3014126, by rfl⟩ : syracuseStep 4018835 = 6028253) B6028253
theorem B1651387 : Blo 1649524 1651387 := bstep (se 1 (by rfl) ⟨1238540, by rfl⟩ : syracuseStep 1651387 = 2477081) B2477081
theorem B3134153 : Blo 1649524 3134153 := bstep (se 2 (by rfl) ⟨1175307, by rfl⟩ : syracuseStep 3134153 = 2350615) B2350615
theorem B1856263 : Blo 1649524 1856263 := bstep (se 1 (by rfl) ⟨1392197, by rfl⟩ : syracuseStep 1856263 = 2784395) B2784395
theorem B1651463 : Blo 1649524 1651463 := bstep (se 1 (by rfl) ⟨1238597, by rfl⟩ : syracuseStep 1651463 = 2477195) B2477195
theorem B8917775 : Blo 1649524 8917775 := bstep (se 1 (by rfl) ⟨6688331, by rfl⟩ : syracuseStep 8917775 = 13376663) B13376663
theorem B1651471 : Blo 1649524 1651471 := bstep (se 1 (by rfl) ⟨1238603, by rfl⟩ : syracuseStep 1651471 = 2477207) B2477207
theorem B3715883 : Blo 1649524 3715883 := bstep (se 1 (by rfl) ⟨2786912, by rfl⟩ : syracuseStep 3715883 = 5573825) B5573825
theorem B5567291 : Blo 1649524 5567291 := bstep (se 1 (by rfl) ⟨4175468, by rfl⟩ : syracuseStep 5567291 = 8350937) B8350937
theorem B1651515 : Blo 1649524 1651515 := bstep (se 1 (by rfl) ⟨1238636, by rfl⟩ : syracuseStep 1651515 = 2477273) B2477273
theorem B20083571 : Blo 1649524 20083571 := bstep (se 1 (by rfl) ⟨15062678, by rfl⟩ : syracuseStep 20083571 = 30125357) B30125357
theorem B8360819 : Blo 1649524 8360819 := bstep (se 1 (by rfl) ⟨6270614, by rfl⟩ : syracuseStep 8360819 = 12541229) B12541229
theorem B1856443 : Blo 1649524 1856443 := bstep (se 1 (by rfl) ⟨1392332, by rfl⟩ : syracuseStep 1856443 = 2784665) B2784665
theorem B4461655 : Blo 1649524 4461655 := bstep (se 1 (by rfl) ⟨3346241, by rfl⟩ : syracuseStep 4461655 = 6692483) B6692483
theorem B25416791 : Blo 1649524 25416791 := bstep (se 1 (by rfl) ⟨19062593, by rfl⟩ : syracuseStep 25416791 = 38125187) B38125187
theorem B4699271 : Blo 1649524 4699271 := bstep (se 1 (by rfl) ⟨3524453, by rfl⟩ : syracuseStep 4699271 = 7048907) B7048907
theorem B11900105 : Blo 1649524 11900105 := bstep (se 2 (by rfl) ⟨4462539, by rfl⟩ : syracuseStep 11900105 = 8925079) B8925079
theorem B7927021 : Blo 1649524 7927021 := bstep (se 3 (by rfl) ⟨1486316, by rfl⟩ : syracuseStep 7927021 = 2972633) B2972633
theorem B5567777 : Blo 1649524 5567777 := bstep (se 2 (by rfl) ⟨2087916, by rfl⟩ : syracuseStep 5567777 = 4175833) B4175833
theorem B4699453 : Blo 1649524 4699453 := bstep (se 3 (by rfl) ⟨881147, by rfl⟩ : syracuseStep 4699453 = 1762295) B1762295
theorem B1856911 : Blo 1649524 1856911 := bstep (se 1 (by rfl) ⟨1392683, by rfl⟩ : syracuseStep 1856911 = 2785367) B2785367
theorem B8918419 : Blo 1649524 8918419 := bstep (se 1 (by rfl) ⟨6688814, by rfl⟩ : syracuseStep 8918419 = 13377629) B13377629
theorem B17839565 : Blo 1649524 17839565 := bstep (se 3 (by rfl) ⟨3344918, by rfl⟩ : syracuseStep 17839565 = 6689837) B6689837
theorem B15857117 : Blo 1649524 15857117 := bstep (se 3 (by rfl) ⟨2973209, by rfl⟩ : syracuseStep 15857117 = 5946419) B5946419
theorem B3135019 : Blo 1649524 3135019 := bstep (se 1 (by rfl) ⟨2351264, by rfl⟩ : syracuseStep 3135019 = 4702529) B4702529
theorem B4462141 : Blo 1649524 4462141 := bstep (se 3 (by rfl) ⟨836651, by rfl⟩ : syracuseStep 4462141 = 1673303) B1673303
theorem B8353367 : Blo 1649524 8353367 := bstep (se 1 (by rfl) ⟨6265025, by rfl⟩ : syracuseStep 8353367 = 12530051) B12530051
theorem B3135095 : Blo 1649524 3135095 := bstep (se 1 (by rfl) ⟨2351321, by rfl⟩ : syracuseStep 3135095 = 4702643) B4702643
theorem B4699795 : Blo 1649524 4699795 := bstep (se 1 (by rfl) ⟨3524846, by rfl⟩ : syracuseStep 4699795 = 7049693) B7049693
theorem B24123059 : Blo 1649524 24123059 := bstep (se 1 (by rfl) ⟨18092294, by rfl⟩ : syracuseStep 24123059 = 36184589) B36184589
theorem B7051009 : Blo 1649524 7051009 := bstep (se 2 (by rfl) ⟨2644128, by rfl⟩ : syracuseStep 7051009 = 5288257) B5288257
theorem B16946995 : Blo 1649524 16946995 := bstep (se 1 (by rfl) ⟨12710246, by rfl⟩ : syracuseStep 16946995 = 25420493) B25420493
theorem B27121483 : Blo 1649524 27121483 := bstep (se 1 (by rfl) ⟨20341112, by rfl⟩ : syracuseStep 27121483 = 40682225) B40682225
theorem B5568371 : Blo 1649524 5568371 := bstep (se 1 (by rfl) ⟨4176278, by rfl⟩ : syracuseStep 5568371 = 8352557) B8352557
theorem B1857415 : Blo 1649524 1857415 := bstep (se 1 (by rfl) ⟨1393061, by rfl⟩ : syracuseStep 1857415 = 2786123) B2786123
theorem B35698583 : Blo 1649524 35698583 := bstep (se 1 (by rfl) ⟨26773937, by rfl⟩ : syracuseStep 35698583 = 53547875) B53547875
theorem B1857595 : Blo 1649524 1857595 := bstep (se 1 (by rfl) ⟨1393196, by rfl⟩ : syracuseStep 1857595 = 2786393) B2786393
theorem B8353853 : Blo 1649524 8353853 := bstep (se 3 (by rfl) ⟨1566347, by rfl⟩ : syracuseStep 8353853 = 3132695) B3132695
theorem B5290103 : Blo 1649524 5290103 := bstep (se 1 (by rfl) ⟨3967577, by rfl⟩ : syracuseStep 5290103 = 7935155) B7935155
theorem B2292025 : Blo 1649524 2292025 := bstep (se 2 (by rfl) ⟨859509, by rfl⟩ : syracuseStep 2292025 = 1719019) B1719019
theorem B6265147 : Blo 1649524 6265147 := bstep (se 1 (by rfl) ⟨4698860, by rfl⟩ : syracuseStep 6265147 = 9397721) B9397721
theorem B152517005 : Blo 1649524 152517005 := bstep (se 3 (by rfl) ⟨28596938, by rfl⟩ : syracuseStep 152517005 = 57193877) B57193877
theorem B2349499 : Blo 1649524 2349499 := bstep (se 1 (by rfl) ⟨1762124, by rfl⟩ : syracuseStep 2349499 = 3524249) B3524249
theorem B22575581 : Blo 1649524 22575581 := bstep (se 3 (by rfl) ⟨4232921, by rfl⟩ : syracuseStep 22575581 = 8465843) B8465843
theorem B4700683 : Blo 1649524 4700683 := bstep (se 1 (by rfl) ⟨3525512, by rfl⟩ : syracuseStep 4700683 = 7051025) B7051025
theorem B2783929 : Blo 1649524 2783929 := bstep (se 2 (by rfl) ⟨1043973, by rfl⟩ : syracuseStep 2783929 = 2087947) B2087947
theorem B12532481 : Blo 1649524 12532481 := bstep (se 2 (by rfl) ⟨4699680, by rfl⟩ : syracuseStep 12532481 = 9399361) B9399361
theorem B6265633 : Blo 1649524 6265633 := bstep (se 2 (by rfl) ⟨2349612, by rfl⟩ : syracuseStep 6265633 = 4699225) B4699225
theorem B4176755 : Blo 1649524 4176755 := bstep (se 1 (by rfl) ⟨3132566, by rfl⟩ : syracuseStep 4176755 = 6265133) B6265133
theorem B7338887 : Blo 1649524 7338887 := bstep (se 1 (by rfl) ⟨5504165, by rfl⟩ : syracuseStep 7338887 = 11008331) B11008331
theorem B2382727 : Blo 1649524 2382727 := bstep (se 1 (by rfl) ⟨1787045, by rfl⟩ : syracuseStep 2382727 = 3574091) B3574091
theorem B2087851 : Blo 1649524 2087851 := bstep (se 1 (by rfl) ⟨1565888, by rfl⟩ : syracuseStep 2087851 = 3131777) B3131777
theorem B4701185 : Blo 1649524 4701185 := bstep (se 2 (by rfl) ⟨1762944, by rfl⟩ : syracuseStep 4701185 = 3525889) B3525889
theorem B9395261 : Blo 1649524 9395261 := bstep (se 3 (by rfl) ⟨1761611, by rfl⟩ : syracuseStep 9395261 = 3523223) B3523223
theorem B4701527 : Blo 1649524 4701527 := bstep (se 1 (by rfl) ⟨3526145, by rfl⟩ : syracuseStep 4701527 = 7052291) B7052291
theorem B4177271 : Blo 1649524 4177271 := bstep (se 1 (by rfl) ⟨3132953, by rfl⟩ : syracuseStep 4177271 = 6265907) B6265907
theorem B2784631 : Blo 1649524 2784631 := bstep (se 1 (by rfl) ⟨2088473, by rfl⟩ : syracuseStep 2784631 = 4176947) B4176947
theorem B18808199 : Blo 1649524 18808199 := bstep (se 1 (by rfl) ⟨14106149, by rfl⟩ : syracuseStep 18808199 = 28212299) B28212299
theorem B20340173 : Blo 1649524 20340173 := bstep (se 3 (by rfl) ⟨3813782, by rfl⟩ : syracuseStep 20340173 = 7627565) B7627565
theorem B1981967 : Blo 1649524 1981967 := bstep (se 1 (by rfl) ⟨1486475, by rfl⟩ : syracuseStep 1981967 = 2972951) B2972951
theorem B2784827 : Blo 1649524 2784827 := bstep (se 1 (by rfl) ⟨2088620, by rfl⟩ : syracuseStep 2784827 = 4177241) B4177241
theorem B4292183 : Blo 1649524 4292183 := bstep (se 1 (by rfl) ⟨3219137, by rfl⟩ : syracuseStep 4292183 = 6438275) B6438275
theorem B35675747 : Blo 1649524 35675747 := bstep (se 1 (by rfl) ⟨26756810, by rfl⟩ : syracuseStep 35675747 = 53513621) B53513621
theorem B6266605 : Blo 1649524 6266605 := bstep (se 3 (by rfl) ⟨1174988, by rfl⟩ : syracuseStep 6266605 = 2349977) B2349977
theorem B48889651 : Blo 1649524 48889651 := bstep (se 1 (by rfl) ⟨36667238, by rfl⟩ : syracuseStep 48889651 = 73334477) B73334477
theorem B8355635 : Blo 1649524 8355635 := bstep (se 1 (by rfl) ⟨6266726, by rfl⟩ : syracuseStep 8355635 = 12533453) B12533453
theorem B5021527 : Blo 1649524 5021527 := bstep (se 1 (by rfl) ⟨3766145, by rfl⟩ : syracuseStep 5021527 = 7532291) B7532291
theorem B2088823 : Blo 1649524 2088823 := bstep (se 1 (by rfl) ⟨1566617, by rfl⟩ : syracuseStep 2088823 = 3133235) B3133235
theorem B2350991 : Blo 1649524 2350991 := bstep (se 1 (by rfl) ⟨1763243, by rfl⟩ : syracuseStep 2350991 = 3526487) B3526487
theorem B2785225 : Blo 1649524 2785225 := bstep (se 2 (by rfl) ⟨1044459, by rfl⟩ : syracuseStep 2785225 = 2088919) B2088919
theorem B4177939 : Blo 1649524 4177939 := bstep (se 1 (by rfl) ⟨3133454, by rfl⟩ : syracuseStep 4177939 = 6266909) B6266909
theorem B5570639 : Blo 1649524 5570639 := bstep (se 1 (by rfl) ⟨4177979, by rfl⟩ : syracuseStep 5570639 = 8355959) B8355959
theorem B2785529 : Blo 1649524 2785529 := bstep (se 2 (by rfl) ⟨1044573, by rfl⟩ : syracuseStep 2785529 = 2089147) B2089147
theorem B6693131 : Blo 1649524 6693131 := bstep (se 1 (by rfl) ⟨5019848, by rfl⟩ : syracuseStep 6693131 = 10039697) B10039697
theorem B16933195 : Blo 1649524 16933195 := bstep (se 1 (by rfl) ⟨12699896, by rfl⟩ : syracuseStep 16933195 = 25399793) B25399793
theorem B2474345 : Blo 1649524 2474345 := bstep (se 2 (by rfl) ⟨927879, by rfl⟩ : syracuseStep 2474345 = 1855759) B1855759
theorem B3056033 : Blo 1649524 3056033 := bstep (se 2 (by rfl) ⟨1146012, by rfl⟩ : syracuseStep 3056033 = 2292025) B2292025
theorem B2785711 : Blo 1649524 2785711 := bstep (se 1 (by rfl) ⟨2089283, by rfl⟩ : syracuseStep 2785711 = 4178567) B4178567
theorem B2474423 : Blo 1649524 2474423 := bstep (se 1 (by rfl) ⟨1855817, by rfl⟩ : syracuseStep 2474423 = 3711635) B3711635
theorem B2679223 : Blo 1649524 2679223 := bstep (se 1 (by rfl) ⟨2009417, by rfl⟩ : syracuseStep 2679223 = 4018835) B4018835
theorem B5571017 : Blo 1649524 5571017 := bstep (se 2 (by rfl) ⟨2089131, by rfl⟩ : syracuseStep 5571017 = 4178263) B4178263
theorem B2474459 : Blo 1649524 2474459 := bstep (se 1 (by rfl) ⟨1855844, by rfl⟩ : syracuseStep 2474459 = 3711689) B3711689
theorem B2785799 : Blo 1649524 2785799 := bstep (se 1 (by rfl) ⟨2089349, by rfl⟩ : syracuseStep 2785799 = 4178699) B4178699
theorem B3711527 : Blo 1649524 3711527 := bstep (se 1 (by rfl) ⟨2783645, by rfl⟩ : syracuseStep 3711527 = 5567291) B5567291
theorem B6267577 : Blo 1649524 6267577 := bstep (se 2 (by rfl) ⟨2350341, by rfl⟩ : syracuseStep 6267577 = 4700683) B4700683
theorem B5948093 : Blo 1649524 5948093 := bstep (se 3 (by rfl) ⟨1115267, by rfl⟩ : syracuseStep 5948093 = 2230535) B2230535
theorem B3572435 : Blo 1649524 3572435 := bstep (se 1 (by rfl) ⟨2679326, by rfl⟩ : syracuseStep 3572435 = 5358653) B5358653
theorem B5571287 : Blo 1649524 5571287 := bstep (se 1 (by rfl) ⟨4178465, by rfl⟩ : syracuseStep 5571287 = 8356931) B8356931
theorem B9528137 : Blo 1649524 9528137 := bstep (se 2 (by rfl) ⟨3573051, by rfl⟩ : syracuseStep 9528137 = 7146103) B7146103
theorem B2786143 : Blo 1649524 2786143 := bstep (se 1 (by rfl) ⟨2089607, by rfl⟩ : syracuseStep 2786143 = 4179215) B4179215
theorem B3711851 : Blo 1649524 3711851 := bstep (se 1 (by rfl) ⟨2783888, by rfl⟩ : syracuseStep 3711851 = 5567777) B5567777
theorem B3711905 : Blo 1649524 3711905 := bstep (se 2 (by rfl) ⟨1391964, by rfl⟩ : syracuseStep 3711905 = 2783929) B2783929
theorem B2474927 : Blo 1649524 2474927 := bstep (se 1 (by rfl) ⟨1856195, by rfl⟩ : syracuseStep 2474927 = 3712391) B3712391
theorem B5571503 : Blo 1649524 5571503 := bstep (se 1 (by rfl) ⟨4178627, by rfl⟩ : syracuseStep 5571503 = 8357255) B8357255
theorem B2786231 : Blo 1649524 2786231 := bstep (se 1 (by rfl) ⟨2089673, by rfl⟩ : syracuseStep 2786231 = 4179347) B4179347
theorem B3523591 : Blo 1649524 3523591 := bstep (se 1 (by rfl) ⟨2642693, by rfl⟩ : syracuseStep 3523591 = 5285387) B5285387
theorem B2475017 : Blo 1649524 2475017 := bstep (se 2 (by rfl) ⟨928131, by rfl⟩ : syracuseStep 2475017 = 1856263) B1856263
theorem B11289619 : Blo 1649524 11289619 := bstep (se 1 (by rfl) ⟨8467214, by rfl⟩ : syracuseStep 11289619 = 16934429) B16934429
theorem B3965971 : Blo 1649524 3965971 := bstep (se 1 (by rfl) ⟨2974478, by rfl⟩ : syracuseStep 3965971 = 5948957) B5948957
theorem B2475047 : Blo 1649524 2475047 := bstep (se 1 (by rfl) ⟨1856285, by rfl⟩ : syracuseStep 2475047 = 3712571) B3712571
theorem B4179023 : Blo 1649524 4179023 := bstep (se 1 (by rfl) ⟨3134267, by rfl⟩ : syracuseStep 4179023 = 6268535) B6268535
theorem B2090063 : Blo 1649524 2090063 := bstep (se 1 (by rfl) ⟨1567547, by rfl⟩ : syracuseStep 2090063 = 3135095) B3135095
theorem B16082039 : Blo 1649524 16082039 := bstep (se 1 (by rfl) ⟨12061529, by rfl⟩ : syracuseStep 16082039 = 24123059) B24123059
theorem B2475131 : Blo 1649524 2475131 := bstep (se 1 (by rfl) ⟨1856348, by rfl⟩ : syracuseStep 2475131 = 3712697) B3712697
theorem B54240461 : Blo 1649524 54240461 := bstep (se 3 (by rfl) ⟨10170086, by rfl⟩ : syracuseStep 54240461 = 20340173) B20340173
theorem B10568951 : Blo 1649524 10568951 := bstep (se 1 (by rfl) ⟨7926713, by rfl⟩ : syracuseStep 10568951 = 15853427) B15853427
theorem B3712247 : Blo 1649524 3712247 := bstep (se 1 (by rfl) ⟨2784185, by rfl⟩ : syracuseStep 3712247 = 5568371) B5568371
theorem B2475257 : Blo 1649524 2475257 := bstep (se 2 (by rfl) ⟨928221, by rfl⟩ : syracuseStep 2475257 = 1856443) B1856443
theorem B23799055 : Blo 1649524 23799055 := bstep (se 1 (by rfl) ⟨17849291, by rfl⟩ : syracuseStep 23799055 = 35698583) B35698583
theorem B9405719 : Blo 1649524 9405719 := bstep (se 1 (by rfl) ⟨7054289, by rfl⟩ : syracuseStep 9405719 = 14108579) B14108579
theorem B2475359 : Blo 1649524 2475359 := bstep (se 1 (by rfl) ⟨1856519, by rfl⟩ : syracuseStep 2475359 = 3713039) B3713039
theorem B2475371 : Blo 1649524 2475371 := bstep (se 1 (by rfl) ⟨1856528, by rfl⟩ : syracuseStep 2475371 = 3713057) B3713057
theorem B5285245 : Blo 1649524 5285245 := bstep (se 3 (by rfl) ⟨990983, by rfl⟩ : syracuseStep 5285245 = 1981967) B1981967
theorem B5948873 : Blo 1649524 5948873 := bstep (se 2 (by rfl) ⟨2230827, by rfl⟩ : syracuseStep 5948873 = 4461655) B4461655
theorem B2786825 : Blo 1649524 2786825 := bstep (se 2 (by rfl) ⟨1045059, by rfl⟩ : syracuseStep 2786825 = 2090119) B2090119
theorem B2475599 : Blo 1649524 2475599 := bstep (se 1 (by rfl) ⟨1856699, by rfl⟩ : syracuseStep 2475599 = 3713399) B3713399
theorem B3966587 : Blo 1649524 3966587 := bstep (se 1 (by rfl) ⟨2974940, by rfl⟩ : syracuseStep 3966587 = 5949881) B5949881
theorem B10569361 : Blo 1649524 10569361 := bstep (se 2 (by rfl) ⟨3963510, by rfl⟩ : syracuseStep 10569361 = 7927021) B7927021
theorem B15050387 : Blo 1649524 15050387 := bstep (se 1 (by rfl) ⟨11287790, by rfl⟩ : syracuseStep 15050387 = 22575581) B22575581
theorem B2475719 : Blo 1649524 2475719 := bstep (se 1 (by rfl) ⟨1856789, by rfl⟩ : syracuseStep 2475719 = 3713579) B3713579
theorem B4179671 : Blo 1649524 4179671 := bstep (se 1 (by rfl) ⟨3134753, by rfl⟩ : syracuseStep 4179671 = 6269507) B6269507
theorem B3712841 : Blo 1649524 3712841 := bstep (se 2 (by rfl) ⟨1392315, by rfl⟩ : syracuseStep 3712841 = 2784631) B2784631
theorem B2475881 : Blo 1649524 2475881 := bstep (se 2 (by rfl) ⟨928455, by rfl⟩ : syracuseStep 2475881 = 1856911) B1856911
theorem B8357741 : Blo 1649524 8357741 := bstep (se 3 (by rfl) ⟨1567076, by rfl⟩ : syracuseStep 8357741 = 3134153) B3134153
theorem B9398177 : Blo 1649524 9398177 := bstep (se 2 (by rfl) ⟨3524316, by rfl⟩ : syracuseStep 9398177 = 7048633) B7048633
theorem B4892591 : Blo 1649524 4892591 := bstep (se 1 (by rfl) ⟨3669443, by rfl⟩ : syracuseStep 4892591 = 7338887) B7338887
theorem B2475959 : Blo 1649524 2475959 := bstep (se 1 (by rfl) ⟨1856969, by rfl⟩ : syracuseStep 2475959 = 3713939) B3713939
theorem B2475995 : Blo 1649524 2475995 := bstep (se 1 (by rfl) ⟨1856996, by rfl⟩ : syracuseStep 2475995 = 3713993) B3713993
theorem B8357903 : Blo 1649524 8357903 := bstep (se 1 (by rfl) ⟨6268427, by rfl⟩ : syracuseStep 8357903 = 12536855) B12536855
theorem B4180025 : Blo 1649524 4180025 := bstep (se 2 (by rfl) ⟨1567509, by rfl⟩ : syracuseStep 4180025 = 3135019) B3135019
theorem B5949521 : Blo 1649524 5949521 := bstep (se 2 (by rfl) ⟨2231070, by rfl⟩ : syracuseStep 5949521 = 4462141) B4462141
theorem B9398429 : Blo 1649524 9398429 := bstep (se 3 (by rfl) ⟨1762205, by rfl⟩ : syracuseStep 9398429 = 3524411) B3524411
theorem B5359787 : Blo 1649524 5359787 := bstep (se 1 (by rfl) ⟨4019840, by rfl⟩ : syracuseStep 5359787 = 8039681) B8039681
theorem B6269309 : Blo 1649524 6269309 := bstep (se 3 (by rfl) ⟨1175495, by rfl⟩ : syracuseStep 6269309 = 2350991) B2350991
theorem B2861455 : Blo 1649524 2861455 := bstep (se 1 (by rfl) ⟨2146091, by rfl⟩ : syracuseStep 2861455 = 4292183) B4292183
theorem B23783831 : Blo 1649524 23783831 := bstep (se 1 (by rfl) ⟨17837873, by rfl⟩ : syracuseStep 23783831 = 35675747) B35675747
theorem B65186201 : Blo 1649524 65186201 := bstep (se 2 (by rfl) ⟨24444825, by rfl⟩ : syracuseStep 65186201 = 48889651) B48889651
theorem B22595993 : Blo 1649524 22595993 := bstep (se 2 (by rfl) ⟨8473497, by rfl⟩ : syracuseStep 22595993 = 16946995) B16946995
theorem B2476463 : Blo 1649524 2476463 := bstep (se 1 (by rfl) ⟨1857347, by rfl⟩ : syracuseStep 2476463 = 3714695) B3714695
theorem B36161977 : Blo 1649524 36161977 := bstep (se 2 (by rfl) ⟨13560741, by rfl⟩ : syracuseStep 36161977 = 27121483) B27121483
theorem B6695369 : Blo 1649524 6695369 := bstep (se 2 (by rfl) ⟨2510763, by rfl⟩ : syracuseStep 6695369 = 5021527) B5021527
theorem B2476553 : Blo 1649524 2476553 := bstep (se 2 (by rfl) ⟨928707, by rfl⟩ : syracuseStep 2476553 = 1857415) B1857415
theorem B38128157 : Blo 1649524 38128157 := bstep (se 3 (by rfl) ⟨7149029, by rfl⟩ : syracuseStep 38128157 = 14298059) B14298059
theorem B2476583 : Blo 1649524 2476583 := bstep (se 1 (by rfl) ⟨1857437, by rfl⟩ : syracuseStep 2476583 = 3714875) B3714875
theorem B3713633 : Blo 1649524 3713633 := bstep (se 2 (by rfl) ⟨1392612, by rfl⟩ : syracuseStep 3713633 = 2785225) B2785225
theorem B2476667 : Blo 1649524 2476667 := bstep (se 1 (by rfl) ⟨1857500, by rfl⟩ : syracuseStep 2476667 = 3715001) B3715001
theorem B15870649 : Blo 1649524 15870649 := bstep (se 2 (by rfl) ⟨5951493, by rfl⟩ : syracuseStep 15870649 = 11902987) B11902987
theorem B3132103 : Blo 1649524 3132103 := bstep (se 1 (by rfl) ⟨2349077, by rfl⟩ : syracuseStep 3132103 = 4698155) B4698155
theorem B2476793 : Blo 1649524 2476793 := bstep (se 2 (by rfl) ⟨928797, by rfl⟩ : syracuseStep 2476793 = 1857595) B1857595
theorem B2476895 : Blo 1649524 2476895 := bstep (se 1 (by rfl) ⟨1857671, by rfl⟩ : syracuseStep 2476895 = 3715343) B3715343
theorem B2476907 : Blo 1649524 2476907 := bstep (se 1 (by rfl) ⟨1857680, by rfl⟩ : syracuseStep 2476907 = 3715361) B3715361
theorem B1649531 : Blo 1649524 1649531 := bstep (se 1 (by rfl) ⟨1237148, by rfl⟩ : syracuseStep 1649531 = 2474297) B2474297
theorem B85765027 : Blo 1649524 85765027 := bstep (se 1 (by rfl) ⟨64323770, by rfl⟩ : syracuseStep 85765027 = 128647541) B128647541
theorem B1649583 : Blo 1649524 1649583 := bstep (se 1 (by rfl) ⟨1237187, by rfl⟩ : syracuseStep 1649583 = 2474375) B2474375
theorem B6695855 : Blo 1649524 6695855 := bstep (se 1 (by rfl) ⟨5021891, by rfl⟩ : syracuseStep 6695855 = 10043783) B10043783
theorem B3713975 : Blo 1649524 3713975 := bstep (se 1 (by rfl) ⟨2785481, by rfl⟩ : syracuseStep 3713975 = 5570963) B5570963
theorem B1649607 : Blo 1649524 1649607 := bstep (se 1 (by rfl) ⟨1237205, by rfl⟩ : syracuseStep 1649607 = 2474411) B2474411
theorem B1649627 : Blo 1649524 1649627 := bstep (se 1 (by rfl) ⟨1237220, by rfl⟩ : syracuseStep 1649627 = 2474441) B2474441
theorem B1649703 : Blo 1649524 1649703 := bstep (se 1 (by rfl) ⟨1237277, by rfl⟩ : syracuseStep 1649703 = 2474555) B2474555
theorem B1649743 : Blo 1649524 1649743 := bstep (se 1 (by rfl) ⟨1237307, by rfl⟩ : syracuseStep 1649743 = 2474615) B2474615
theorem B2477135 : Blo 1649524 2477135 := bstep (se 1 (by rfl) ⟨1857851, by rfl⟩ : syracuseStep 2477135 = 3715703) B3715703
theorem B1649759 : Blo 1649524 1649759 := bstep (se 1 (by rfl) ⟨1237319, by rfl⟩ : syracuseStep 1649759 = 2474639) B2474639
theorem B5287027 : Blo 1649524 5287027 := bstep (se 1 (by rfl) ⟨3965270, by rfl⟩ : syracuseStep 5287027 = 7930541) B7930541
theorem B1649787 : Blo 1649524 1649787 := bstep (se 1 (by rfl) ⟨1237340, by rfl⟩ : syracuseStep 1649787 = 2474681) B2474681
theorem B1649839 : Blo 1649524 1649839 := bstep (se 1 (by rfl) ⟨1237379, by rfl⟩ : syracuseStep 1649839 = 2474759) B2474759
theorem B1649863 : Blo 1649524 1649863 := bstep (se 1 (by rfl) ⟨1237397, by rfl⟩ : syracuseStep 1649863 = 2474795) B2474795
theorem B2477255 : Blo 1649524 2477255 := bstep (se 1 (by rfl) ⟨1857941, by rfl⟩ : syracuseStep 2477255 = 3715883) B3715883
theorem B1649883 : Blo 1649524 1649883 := bstep (se 1 (by rfl) ⟨1237412, by rfl⟩ : syracuseStep 1649883 = 2474825) B2474825
theorem B13389047 : Blo 1649524 13389047 := bstep (se 1 (by rfl) ⟨10041785, by rfl⟩ : syracuseStep 13389047 = 20083571) B20083571
theorem B3132665 : Blo 1649524 3132665 := bstep (se 2 (by rfl) ⟨1174749, by rfl⟩ : syracuseStep 3132665 = 2349499) B2349499
theorem B5573879 : Blo 1649524 5573879 := bstep (se 1 (by rfl) ⟨4180409, by rfl⟩ : syracuseStep 5573879 = 8360819) B8360819
theorem B1649959 : Blo 1649524 1649959 := bstep (se 1 (by rfl) ⟨1237469, by rfl⟩ : syracuseStep 1649959 = 2474939) B2474939
theorem B1649999 : Blo 1649524 1649999 := bstep (se 1 (by rfl) ⟨1237499, by rfl⟩ : syracuseStep 1649999 = 2474999) B2474999
theorem B1650015 : Blo 1649524 1650015 := bstep (se 1 (by rfl) ⟨1237511, by rfl⟩ : syracuseStep 1650015 = 2475023) B2475023
theorem B1650043 : Blo 1649524 1650043 := bstep (se 1 (by rfl) ⟨1237532, by rfl⟩ : syracuseStep 1650043 = 2475065) B2475065
theorem B16944527 : Blo 1649524 16944527 := bstep (se 1 (by rfl) ⟨12708395, by rfl⟩ : syracuseStep 16944527 = 25416791) B25416791
theorem B1650095 : Blo 1649524 1650095 := bstep (se 1 (by rfl) ⟨1237571, by rfl⟩ : syracuseStep 1650095 = 2475143) B2475143
theorem B3132847 : Blo 1649524 3132847 := bstep (se 1 (by rfl) ⟨2349635, by rfl⟩ : syracuseStep 3132847 = 4699271) B4699271
theorem B1650119 : Blo 1649524 1650119 := bstep (se 1 (by rfl) ⟨1237589, by rfl⟩ : syracuseStep 1650119 = 2475179) B2475179
theorem B1650139 : Blo 1649524 1650139 := bstep (se 1 (by rfl) ⟨1237604, by rfl⟩ : syracuseStep 1650139 = 2475209) B2475209
theorem B7933403 : Blo 1649524 7933403 := bstep (se 1 (by rfl) ⟨5950052, by rfl⟩ : syracuseStep 7933403 = 11900105) B11900105
theorem B3714569 : Blo 1649524 3714569 := bstep (se 2 (by rfl) ⟨1392963, by rfl⟩ : syracuseStep 3714569 = 2785927) B2785927
theorem B1650215 : Blo 1649524 1650215 := bstep (se 1 (by rfl) ⟨1237661, by rfl⟩ : syracuseStep 1650215 = 2475323) B2475323
theorem B1650255 : Blo 1649524 1650255 := bstep (se 1 (by rfl) ⟨1237691, by rfl⟩ : syracuseStep 1650255 = 2475383) B2475383
theorem B26766935 : Blo 1649524 26766935 := bstep (se 1 (by rfl) ⟨20075201, by rfl⟩ : syracuseStep 26766935 = 40150403) B40150403
theorem B1650271 : Blo 1649524 1650271 := bstep (se 1 (by rfl) ⟨1237703, by rfl⟩ : syracuseStep 1650271 = 2475407) B2475407
theorem B1650299 : Blo 1649524 1650299 := bstep (se 1 (by rfl) ⟨1237724, by rfl⟩ : syracuseStep 1650299 = 2475449) B2475449
theorem B10571411 : Blo 1649524 10571411 := bstep (se 1 (by rfl) ⟨7928558, by rfl⟩ : syracuseStep 10571411 = 15857117) B15857117
theorem B1650351 : Blo 1649524 1650351 := bstep (se 1 (by rfl) ⟨1237763, by rfl⟩ : syracuseStep 1650351 = 2475527) B2475527
theorem B1650375 : Blo 1649524 1650375 := bstep (se 1 (by rfl) ⟨1237781, by rfl⟩ : syracuseStep 1650375 = 2475563) B2475563
theorem B1650395 : Blo 1649524 1650395 := bstep (se 1 (by rfl) ⟨1237796, by rfl⟩ : syracuseStep 1650395 = 2475593) B2475593
theorem B1650471 : Blo 1649524 1650471 := bstep (se 1 (by rfl) ⟨1237853, by rfl⟩ : syracuseStep 1650471 = 2475707) B2475707
theorem B1650511 : Blo 1649524 1650511 := bstep (se 1 (by rfl) ⟨1237883, by rfl⟩ : syracuseStep 1650511 = 2475767) B2475767
theorem B1650527 : Blo 1649524 1650527 := bstep (se 1 (by rfl) ⟨1237895, by rfl⟩ : syracuseStep 1650527 = 2475791) B2475791
theorem B3714911 : Blo 1649524 3714911 := bstep (se 1 (by rfl) ⟨2786183, by rfl⟩ : syracuseStep 3714911 = 5572367) B5572367
theorem B1650555 : Blo 1649524 1650555 := bstep (se 1 (by rfl) ⟨1237916, by rfl⟩ : syracuseStep 1650555 = 2475833) B2475833
theorem B15871879 : Blo 1649524 15871879 := bstep (se 1 (by rfl) ⟨11903909, by rfl⟩ : syracuseStep 15871879 = 23807819) B23807819
theorem B1650607 : Blo 1649524 1650607 := bstep (se 1 (by rfl) ⟨1237955, by rfl⟩ : syracuseStep 1650607 = 2475911) B2475911
theorem B1650631 : Blo 1649524 1650631 := bstep (se 1 (by rfl) ⟨1237973, by rfl⟩ : syracuseStep 1650631 = 2475947) B2475947
theorem B1650651 : Blo 1649524 1650651 := bstep (se 1 (by rfl) ⟨1237988, by rfl⟩ : syracuseStep 1650651 = 2475977) B2475977
theorem B22900751 : Blo 1649524 22900751 := bstep (se 1 (by rfl) ⟨17175563, by rfl⟩ : syracuseStep 22900751 = 34351127) B34351127
theorem B3715091 : Blo 1649524 3715091 := bstep (se 1 (by rfl) ⟨2786318, by rfl⟩ : syracuseStep 3715091 = 5572637) B5572637
theorem B1650727 : Blo 1649524 1650727 := bstep (se 1 (by rfl) ⟨1238045, by rfl⟩ : syracuseStep 1650727 = 2476091) B2476091
theorem B1650767 : Blo 1649524 1650767 := bstep (se 1 (by rfl) ⟨1238075, by rfl⟩ : syracuseStep 1650767 = 2476151) B2476151
theorem B3526735 : Blo 1649524 3526735 := bstep (se 1 (by rfl) ⟨2645051, by rfl⟩ : syracuseStep 3526735 = 5290103) B5290103
theorem B1650783 : Blo 1649524 1650783 := bstep (se 1 (by rfl) ⟨1238087, by rfl⟩ : syracuseStep 1650783 = 2476175) B2476175
theorem B1650811 : Blo 1649524 1650811 := bstep (se 1 (by rfl) ⟨1238108, by rfl⟩ : syracuseStep 1650811 = 2476217) B2476217
theorem B4698269 : Blo 1649524 4698269 := bstep (se 3 (by rfl) ⟨880925, by rfl⟩ : syracuseStep 4698269 = 1761851) B1761851
theorem B1650863 : Blo 1649524 1650863 := bstep (se 1 (by rfl) ⟨1238147, by rfl⟩ : syracuseStep 1650863 = 2476295) B2476295
theorem B1650887 : Blo 1649524 1650887 := bstep (se 1 (by rfl) ⟨1238165, by rfl⟩ : syracuseStep 1650887 = 2476331) B2476331
theorem B1650907 : Blo 1649524 1650907 := bstep (se 1 (by rfl) ⟨1238180, by rfl⟩ : syracuseStep 1650907 = 2476361) B2476361
theorem B1650983 : Blo 1649524 1650983 := bstep (se 1 (by rfl) ⟨1238237, by rfl⟩ : syracuseStep 1650983 = 2476475) B2476475
theorem B9400637 : Blo 1649524 9400637 := bstep (se 3 (by rfl) ⟨1762619, by rfl⟩ : syracuseStep 9400637 = 3525239) B3525239
theorem B1651023 : Blo 1649524 1651023 := bstep (se 1 (by rfl) ⟨1238267, by rfl⟩ : syracuseStep 1651023 = 2476535) B2476535
theorem B1651039 : Blo 1649524 1651039 := bstep (se 1 (by rfl) ⟨1238279, by rfl⟩ : syracuseStep 1651039 = 2476559) B2476559
theorem B3715433 : Blo 1649524 3715433 := bstep (se 2 (by rfl) ⟨1393287, by rfl⟩ : syracuseStep 3715433 = 2786575) B2786575
theorem B1651067 : Blo 1649524 1651067 := bstep (se 1 (by rfl) ⟨1238300, by rfl⟩ : syracuseStep 1651067 = 2476601) B2476601
theorem B5288321 : Blo 1649524 5288321 := bstep (se 2 (by rfl) ⟨1983120, by rfl⟩ : syracuseStep 5288321 = 3966241) B3966241
theorem B1651119 : Blo 1649524 1651119 := bstep (se 1 (by rfl) ⟨1238339, by rfl⟩ : syracuseStep 1651119 = 2476679) B2476679
theorem B1651143 : Blo 1649524 1651143 := bstep (se 1 (by rfl) ⟨1238357, by rfl⟩ : syracuseStep 1651143 = 2476715) B2476715
theorem B4698587 : Blo 1649524 4698587 := bstep (se 1 (by rfl) ⟨3523940, by rfl⟩ : syracuseStep 4698587 = 7047881) B7047881
theorem B1651163 : Blo 1649524 1651163 := bstep (se 1 (by rfl) ⟨1238372, by rfl⟩ : syracuseStep 1651163 = 2476745) B2476745
theorem B4698611 : Blo 1649524 4698611 := bstep (se 1 (by rfl) ⟨3523958, by rfl⟩ : syracuseStep 4698611 = 7047917) B7047917
theorem B11891225 : Blo 1649524 11891225 := bstep (se 2 (by rfl) ⟨4459209, by rfl⟩ : syracuseStep 11891225 = 8918419) B8918419
theorem B1651239 : Blo 1649524 1651239 := bstep (se 1 (by rfl) ⟨1238429, by rfl⟩ : syracuseStep 1651239 = 2476859) B2476859
theorem B1651279 : Blo 1649524 1651279 := bstep (se 1 (by rfl) ⟨1238459, by rfl⟩ : syracuseStep 1651279 = 2476919) B2476919
theorem B1651295 : Blo 1649524 1651295 := bstep (se 1 (by rfl) ⟨1238471, by rfl⟩ : syracuseStep 1651295 = 2476943) B2476943
theorem B1651323 : Blo 1649524 1651323 := bstep (se 1 (by rfl) ⟨1238492, by rfl⟩ : syracuseStep 1651323 = 2476985) B2476985
theorem B10580615 : Blo 1649524 10580615 := bstep (se 1 (by rfl) ⟨7935461, by rfl⟩ : syracuseStep 10580615 = 15870923) B15870923
theorem B3134123 : Blo 1649524 3134123 := bstep (se 1 (by rfl) ⟨2350592, by rfl⟩ : syracuseStep 3134123 = 4701185) B4701185
theorem B1651375 : Blo 1649524 1651375 := bstep (se 1 (by rfl) ⟨1238531, by rfl⟩ : syracuseStep 1651375 = 2477063) B2477063
theorem B6689465 : Blo 1649524 6689465 := bstep (se 2 (by rfl) ⟨2508549, by rfl⟩ : syracuseStep 6689465 = 5017099) B5017099
theorem B1651399 : Blo 1649524 1651399 := bstep (se 1 (by rfl) ⟨1238549, by rfl⟩ : syracuseStep 1651399 = 2477099) B2477099
theorem B6263507 : Blo 1649524 6263507 := bstep (se 1 (by rfl) ⟨4697630, by rfl⟩ : syracuseStep 6263507 = 9395261) B9395261
theorem B8360657 : Blo 1649524 8360657 := bstep (se 2 (by rfl) ⟨3135246, by rfl⟩ : syracuseStep 8360657 = 6270493) B6270493
theorem B1651419 : Blo 1649524 1651419 := bstep (se 1 (by rfl) ⟨1238564, by rfl⟩ : syracuseStep 1651419 = 2477129) B2477129
theorem B1651495 : Blo 1649524 1651495 := bstep (se 1 (by rfl) ⟨1238621, by rfl⟩ : syracuseStep 1651495 = 2477243) B2477243
theorem B10580843 : Blo 1649524 10580843 := bstep (se 1 (by rfl) ⟨7935632, by rfl⟩ : syracuseStep 10580843 = 15871265) B15871265
theorem B3134351 : Blo 1649524 3134351 := bstep (se 1 (by rfl) ⟨2350763, by rfl⟩ : syracuseStep 3134351 = 4701527) B4701527
theorem B12538799 : Blo 1649524 12538799 := bstep (se 1 (by rfl) ⟨9404099, by rfl⟩ : syracuseStep 12538799 = 18808199) B18808199
theorem B9401345 : Blo 1649524 9401345 := bstep (se 2 (by rfl) ⟨3525504, by rfl⟩ : syracuseStep 9401345 = 7051009) B7051009
theorem B5567507 : Blo 1649524 5567507 := bstep (se 1 (by rfl) ⟨4175630, by rfl⟩ : syracuseStep 5567507 = 8351261) B8351261
theorem B1856551 : Blo 1649524 1856551 := bstep (se 1 (by rfl) ⟨1392413, by rfl⟩ : syracuseStep 1856551 = 2784827) B2784827
theorem B17839223 : Blo 1649524 17839223 := bstep (se 1 (by rfl) ⟨13379417, by rfl⟩ : syracuseStep 17839223 = 26758835) B26758835
theorem B12711107 : Blo 1649524 12711107 := bstep (se 1 (by rfl) ⟨9533330, by rfl⟩ : syracuseStep 12711107 = 19066661) B19066661
theorem B5567831 : Blo 1649524 5567831 := bstep (se 1 (by rfl) ⟨4175873, by rfl⟩ : syracuseStep 5567831 = 8351747) B8351747
theorem B9524881 : Blo 1649524 9524881 := bstep (se 2 (by rfl) ⟨3571830, by rfl⟩ : syracuseStep 9524881 = 7143661) B7143661
theorem B21149383 : Blo 1649524 21149383 := bstep (se 1 (by rfl) ⟨15862037, by rfl⟩ : syracuseStep 21149383 = 31724075) B31724075
theorem B8353529 : Blo 1649524 8353529 := bstep (se 2 (by rfl) ⟨3132573, by rfl⟩ : syracuseStep 8353529 = 6265147) B6265147
theorem B5945183 : Blo 1649524 5945183 := bstep (se 1 (by rfl) ⟨4458887, by rfl⟩ : syracuseStep 5945183 = 8917775) B8917775
theorem B21141593 : Blo 1649524 21141593 := bstep (se 2 (by rfl) ⟨7928097, by rfl⟩ : syracuseStep 21141593 = 15856195) B15856195
theorem B11893043 : Blo 1649524 11893043 := bstep (se 1 (by rfl) ⟨8919782, by rfl⟩ : syracuseStep 11893043 = 17839565) B17839565
theorem B7051607 : Blo 1649524 7051607 := bstep (se 1 (by rfl) ⟨5288705, by rfl⟩ : syracuseStep 7051607 = 10577411) B10577411
theorem B8354177 : Blo 1649524 8354177 := bstep (se 2 (by rfl) ⟨3132816, by rfl⟩ : syracuseStep 8354177 = 6265633) B6265633
theorem B5568911 : Blo 1649524 5568911 := bstep (se 1 (by rfl) ⟨4176683, by rfl⟩ : syracuseStep 5568911 = 8353367) B8353367
theorem B3176969 : Blo 1649524 3176969 := bstep (se 2 (by rfl) ⟨1191363, by rfl⟩ : syracuseStep 3176969 = 2382727) B2382727
theorem B2783801 : Blo 1649524 2783801 := bstep (se 2 (by rfl) ⟨1043925, by rfl⟩ : syracuseStep 2783801 = 2087851) B2087851
theorem B4176481 : Blo 1649524 4176481 := bstep (se 2 (by rfl) ⟨1566180, by rfl⟩ : syracuseStep 4176481 = 3132361) B3132361
theorem B2038471 : Blo 1649524 2038471 := bstep (se 1 (by rfl) ⟨1528853, by rfl⟩ : syracuseStep 2038471 = 3057707) B3057707
theorem B5569235 : Blo 1649524 5569235 := bstep (se 1 (by rfl) ⟨4176926, by rfl⟩ : syracuseStep 5569235 = 8353853) B8353853
theorem B101678003 : Blo 1649524 101678003 := bstep (se 1 (by rfl) ⟨76258502, by rfl⟩ : syracuseStep 101678003 = 152517005) B152517005
theorem B2644955 : Blo 1649524 2644955 := bstep (se 1 (by rfl) ⟨1983716, by rfl⟩ : syracuseStep 2644955 = 3967433) B3967433
theorem B6265937 : Blo 1649524 6265937 := bstep (se 2 (by rfl) ⟨2349726, by rfl⟩ : syracuseStep 6265937 = 4699453) B4699453
theorem B8354987 : Blo 1649524 8354987 := bstep (se 1 (by rfl) ⟨6266240, by rfl⟩ : syracuseStep 8354987 = 12532481) B12532481
theorem B2784503 : Blo 1649524 2784503 := bstep (se 1 (by rfl) ⟨2088377, by rfl⟩ : syracuseStep 2784503 = 4176755) B4176755
theorem B4177433 : Blo 1649524 4177433 := bstep (se 2 (by rfl) ⟨1566537, by rfl⟩ : syracuseStep 4177433 = 3133075) B3133075
theorem B6266393 : Blo 1649524 6266393 := bstep (se 2 (by rfl) ⟨2349897, by rfl⟩ : syracuseStep 6266393 = 4699795) B4699795
theorem B2784847 : Blo 1649524 2784847 := bstep (se 1 (by rfl) ⟨2088635, by rfl⟩ : syracuseStep 2784847 = 4177271) B4177271
theorem B7052939 : Blo 1649524 7052939 := bstep (se 1 (by rfl) ⟨5289704, by rfl⟩ : syracuseStep 7052939 = 10579409) B10579409
theorem B8355473 : Blo 1649524 8355473 := bstep (se 2 (by rfl) ⟨3133302, by rfl⟩ : syracuseStep 8355473 = 6266605) B6266605
theorem B2785097 : Blo 1649524 2785097 := bstep (se 2 (by rfl) ⟨1044411, by rfl⟩ : syracuseStep 2785097 = 2088823) B2088823
theorem B5570423 : Blo 1649524 5570423 := bstep (se 1 (by rfl) ⟨4177817, by rfl⟩ : syracuseStep 5570423 = 8355635) B8355635
theorem B5570585 : Blo 1649524 5570585 := bstep (se 2 (by rfl) ⟨2088969, by rfl⟩ : syracuseStep 5570585 = 4177939) B4177939
theorem B4702313 : Blo 1649524 4702313 := bstep (se 2 (by rfl) ⟨1763367, by rfl⟩ : syracuseStep 4702313 = 3526735) B3526735
theorem B6267091 : Blo 1649524 6267091 := bstep (se 1 (by rfl) ⟨4700318, by rfl⟩ : syracuseStep 6267091 = 9400637) B9400637
theorem B2474351 : Blo 1649524 2474351 := bstep (se 1 (by rfl) ⟨1855763, by rfl⟩ : syracuseStep 2474351 = 3711527) B3711527
theorem B7053743 : Blo 1649524 7053743 := bstep (se 1 (by rfl) ⟨5290307, by rfl⟩ : syracuseStep 7053743 = 10580615) B10580615
theorem B2089415 : Blo 1649524 2089415 := bstep (se 1 (by rfl) ⟨1567061, by rfl⟩ : syracuseStep 2089415 = 3134123) B3134123
theorem B2474567 : Blo 1649524 2474567 := bstep (se 1 (by rfl) ⟨1855925, by rfl⟩ : syracuseStep 2474567 = 3711851) B3711851
theorem B7053895 : Blo 1649524 7053895 := bstep (se 1 (by rfl) ⟨5290421, by rfl⟩ : syracuseStep 7053895 = 10580843) B10580843
theorem B3572297 : Blo 1649524 3572297 := bstep (se 2 (by rfl) ⟨1339611, by rfl⟩ : syracuseStep 3572297 = 2679223) B2679223
theorem B2089567 : Blo 1649524 2089567 := bstep (se 1 (by rfl) ⟨1567175, by rfl⟩ : syracuseStep 2089567 = 3134351) B3134351
theorem B2474603 : Blo 1649524 2474603 := bstep (se 1 (by rfl) ⟨1855952, by rfl⟩ : syracuseStep 2474603 = 3711905) B3711905
theorem B6267563 : Blo 1649524 6267563 := bstep (se 1 (by rfl) ⟨4700672, by rfl⟩ : syracuseStep 6267563 = 9401345) B9401345
theorem B3711671 : Blo 1649524 3711671 := bstep (se 1 (by rfl) ⟨2783753, by rfl⟩ : syracuseStep 3711671 = 5567507) B5567507
theorem B2786015 : Blo 1649524 2786015 := bstep (se 1 (by rfl) ⟨2089511, by rfl⟩ : syracuseStep 2786015 = 4179023) B4179023
theorem B36160307 : Blo 1649524 36160307 := bstep (se 1 (by rfl) ⟨27120230, by rfl⟩ : syracuseStep 36160307 = 54240461) B54240461
theorem B7045967 : Blo 1649524 7045967 := bstep (se 1 (by rfl) ⟨5284475, by rfl⟩ : syracuseStep 7045967 = 10568951) B10568951
theorem B2474831 : Blo 1649524 2474831 := bstep (se 1 (by rfl) ⟨1856123, by rfl⟩ : syracuseStep 2474831 = 3712247) B3712247
theorem B3711887 : Blo 1649524 3711887 := bstep (se 1 (by rfl) ⟨2783915, by rfl⟩ : syracuseStep 3711887 = 5567831) B5567831
theorem B8356769 : Blo 1649524 8356769 := bstep (se 2 (by rfl) ⟨3133788, by rfl⟩ : syracuseStep 8356769 = 6267577) B6267577
theorem B21160865 : Blo 1649524 21160865 := bstep (se 2 (by rfl) ⟨7935324, by rfl⟩ : syracuseStep 21160865 = 15870649) B15870649
theorem B3965915 : Blo 1649524 3965915 := bstep (se 1 (by rfl) ⟨2974436, by rfl⟩ : syracuseStep 3965915 = 5948873) B5948873
theorem B2786447 : Blo 1649524 2786447 := bstep (se 1 (by rfl) ⟨2089835, by rfl⟩ : syracuseStep 2786447 = 4179671) B4179671
theorem B114353369 : Blo 1649524 114353369 := bstep (se 2 (by rfl) ⟨42882513, by rfl⟩ : syracuseStep 114353369 = 85765027) B85765027
theorem B2475227 : Blo 1649524 2475227 := bstep (se 1 (by rfl) ⟨1856420, by rfl⟩ : syracuseStep 2475227 = 3712841) B3712841
theorem B5571827 : Blo 1649524 5571827 := bstep (se 1 (by rfl) ⟨4178870, by rfl⟩ : syracuseStep 5571827 = 8357741) B8357741
theorem B3261727 : Blo 1649524 3261727 := bstep (se 1 (by rfl) ⟨2446295, by rfl⟩ : syracuseStep 3261727 = 4892591) B4892591
theorem B5571935 : Blo 1649524 5571935 := bstep (se 1 (by rfl) ⟨4178951, by rfl⟩ : syracuseStep 5571935 = 8357903) B8357903
theorem B8471917 : Blo 1649524 8471917 := bstep (se 3 (by rfl) ⟨1588484, by rfl⟩ : syracuseStep 8471917 = 3176969) B3176969
theorem B2786683 : Blo 1649524 2786683 := bstep (se 1 (by rfl) ⟨2090012, by rfl⟩ : syracuseStep 2786683 = 4180025) B4180025
theorem B2475401 : Blo 1649524 2475401 := bstep (se 2 (by rfl) ⟨928275, by rfl⟩ : syracuseStep 2475401 = 1856551) B1856551
theorem B3966347 : Blo 1649524 3966347 := bstep (se 1 (by rfl) ⟨2974760, by rfl⟩ : syracuseStep 3966347 = 5949521) B5949521
theorem B3573191 : Blo 1649524 3573191 := bstep (se 1 (by rfl) ⟨2679893, by rfl⟩ : syracuseStep 3573191 = 5359787) B5359787
theorem B4179539 : Blo 1649524 4179539 := bstep (se 1 (by rfl) ⟨3134654, by rfl⟩ : syracuseStep 4179539 = 6269309) B6269309
theorem B3712607 : Blo 1649524 3712607 := bstep (se 1 (by rfl) ⟨2784455, by rfl⟩ : syracuseStep 3712607 = 5568911) B5568911
theorem B28190429 : Blo 1649524 28190429 := bstep (se 3 (by rfl) ⟨5285705, by rfl⟩ : syracuseStep 28190429 = 10571411) B10571411
theorem B90310373 : Blo 1649524 90310373 := bstep (se 4 (by rfl) ⟨8466597, by rfl⟩ : syracuseStep 90310373 = 16933195) B16933195
theorem B2475755 : Blo 1649524 2475755 := bstep (se 1 (by rfl) ⟨1856816, by rfl⟩ : syracuseStep 2475755 = 3713633) B3713633
theorem B3712823 : Blo 1649524 3712823 := bstep (se 1 (by rfl) ⟨2784617, by rfl⟩ : syracuseStep 3712823 = 5569235) B5569235
theorem B15861581 : Blo 1649524 15861581 := bstep (se 3 (by rfl) ⟨2974046, by rfl⟩ : syracuseStep 15861581 = 5948093) B5948093
theorem B7046993 : Blo 1649524 7046993 := bstep (se 2 (by rfl) ⟨2642622, by rfl⟩ : syracuseStep 7046993 = 5285245) B5285245
theorem B2475983 : Blo 1649524 2475983 := bstep (se 1 (by rfl) ⟨1856987, by rfl⟩ : syracuseStep 2475983 = 3713975) B3713975
theorem B1763303 : Blo 1649524 1763303 := bstep (se 1 (by rfl) ⟨1322477, by rfl⟩ : syracuseStep 1763303 = 2644955) B2644955
theorem B3713129 : Blo 1649524 3713129 := bstep (se 2 (by rfl) ⟨1392423, by rfl⟩ : syracuseStep 3713129 = 2784847) B2784847
theorem B14092481 : Blo 1649524 14092481 := bstep (se 2 (by rfl) ⟨5284680, by rfl⟩ : syracuseStep 14092481 = 10569361) B10569361
theorem B12699841 : Blo 1649524 12699841 := bstep (se 2 (by rfl) ⟨4762440, by rfl⟩ : syracuseStep 12699841 = 9524881) B9524881
theorem B28199177 : Blo 1649524 28199177 := bstep (se 2 (by rfl) ⟨10574691, by rfl⟩ : syracuseStep 28199177 = 21149383) B21149383
theorem B2476379 : Blo 1649524 2476379 := bstep (se 1 (by rfl) ⟨1857284, by rfl⟩ : syracuseStep 2476379 = 3714569) B3714569
theorem B17844623 : Blo 1649524 17844623 := bstep (se 1 (by rfl) ⟨13383467, by rfl⟩ : syracuseStep 17844623 = 26766935) B26766935
theorem B21162505 : Blo 1649524 21162505 := bstep (se 2 (by rfl) ⟨7935939, by rfl⟩ : syracuseStep 21162505 = 15871879) B15871879
theorem B2476607 : Blo 1649524 2476607 := bstep (se 1 (by rfl) ⟨1857455, by rfl⟩ : syracuseStep 2476607 = 3714911) B3714911
theorem B3713615 : Blo 1649524 3713615 := bstep (se 1 (by rfl) ⟨2785211, by rfl⟩ : syracuseStep 3713615 = 5570423) B5570423
theorem B2476727 : Blo 1649524 2476727 := bstep (se 1 (by rfl) ⟨1857545, by rfl⟩ : syracuseStep 2476727 = 3715091) B3715091
theorem B3713759 : Blo 1649524 3713759 := bstep (se 1 (by rfl) ⟨2785319, by rfl⟩ : syracuseStep 3713759 = 5570639) B5570639
theorem B3132179 : Blo 1649524 3132179 := bstep (se 1 (by rfl) ⟨2349134, by rfl⟩ : syracuseStep 3132179 = 4698269) B4698269
theorem B5573501 : Blo 1649524 5573501 := bstep (se 3 (by rfl) ⟨1045031, by rfl⟩ : syracuseStep 5573501 = 2090063) B2090063
theorem B1649563 : Blo 1649524 1649563 := bstep (se 1 (by rfl) ⟨1237172, by rfl⟩ : syracuseStep 1649563 = 2474345) B2474345
theorem B2476955 : Blo 1649524 2476955 := bstep (se 1 (by rfl) ⟨1857716, by rfl⟩ : syracuseStep 2476955 = 3715433) B3715433
theorem B3525547 : Blo 1649524 3525547 := bstep (se 1 (by rfl) ⟨2644160, by rfl⟩ : syracuseStep 3525547 = 5288321) B5288321
theorem B1649615 : Blo 1649524 1649615 := bstep (se 1 (by rfl) ⟨1237211, by rfl⟩ : syracuseStep 1649615 = 2474423) B2474423
theorem B3714011 : Blo 1649524 3714011 := bstep (se 1 (by rfl) ⟨2785508, by rfl⟩ : syracuseStep 3714011 = 5571017) B5571017
theorem B1649639 : Blo 1649524 1649639 := bstep (se 1 (by rfl) ⟨1237229, by rfl⟩ : syracuseStep 1649639 = 2474459) B2474459
theorem B3132407 : Blo 1649524 3132407 := bstep (se 1 (by rfl) ⟨2349305, by rfl⟩ : syracuseStep 3132407 = 4698611) B4698611
theorem B4459643 : Blo 1649524 4459643 := bstep (se 1 (by rfl) ⟨3344732, by rfl⟩ : syracuseStep 4459643 = 6689465) B6689465
theorem B5573771 : Blo 1649524 5573771 := bstep (se 1 (by rfl) ⟨4180328, by rfl⟩ : syracuseStep 5573771 = 8360657) B8360657
theorem B3714191 : Blo 1649524 3714191 := bstep (se 1 (by rfl) ⟨2785643, by rfl⟩ : syracuseStep 3714191 = 5571287) B5571287
theorem B6352091 : Blo 1649524 6352091 := bstep (se 1 (by rfl) ⟨4764068, by rfl⟩ : syracuseStep 6352091 = 9528137) B9528137
theorem B3714281 : Blo 1649524 3714281 := bstep (se 2 (by rfl) ⟨1392855, by rfl⟩ : syracuseStep 3714281 = 2785711) B2785711
theorem B1649951 : Blo 1649524 1649951 := bstep (se 1 (by rfl) ⟨1237463, by rfl⟩ : syracuseStep 1649951 = 2474927) B2474927
theorem B3714335 : Blo 1649524 3714335 := bstep (se 1 (by rfl) ⟨2785751, by rfl⟩ : syracuseStep 3714335 = 5571503) B5571503
theorem B8359199 : Blo 1649524 8359199 := bstep (se 1 (by rfl) ⟨6269399, by rfl⟩ : syracuseStep 8359199 = 12538799) B12538799
theorem B1650011 : Blo 1649524 1650011 := bstep (se 1 (by rfl) ⟨1237508, by rfl⟩ : syracuseStep 1650011 = 2475017) B2475017
theorem B1650031 : Blo 1649524 1650031 := bstep (se 1 (by rfl) ⟨1237523, by rfl⟩ : syracuseStep 1650031 = 2475047) B2475047
theorem B1650087 : Blo 1649524 1650087 := bstep (se 1 (by rfl) ⟨1237565, by rfl⟩ : syracuseStep 1650087 = 2475131) B2475131
theorem B8474071 : Blo 1649524 8474071 := bstep (se 1 (by rfl) ⟨6355553, by rfl⟩ : syracuseStep 8474071 = 12711107) B12711107
theorem B1650171 : Blo 1649524 1650171 := bstep (se 1 (by rfl) ⟨1237628, by rfl⟩ : syracuseStep 1650171 = 2475257) B2475257
theorem B6270479 : Blo 1649524 6270479 := bstep (se 1 (by rfl) ⟨4702859, by rfl⟩ : syracuseStep 6270479 = 9405719) B9405719
theorem B1650239 : Blo 1649524 1650239 := bstep (se 1 (by rfl) ⟨1237679, by rfl⟩ : syracuseStep 1650239 = 2475359) B2475359
theorem B1650247 : Blo 1649524 1650247 := bstep (se 1 (by rfl) ⟨1237685, by rfl⟩ : syracuseStep 1650247 = 2475371) B2475371
theorem B1650399 : Blo 1649524 1650399 := bstep (se 1 (by rfl) ⟨1237799, by rfl⟩ : syracuseStep 1650399 = 2475599) B2475599
theorem B3714857 : Blo 1649524 3714857 := bstep (se 2 (by rfl) ⟨1393071, by rfl⟩ : syracuseStep 3714857 = 2786143) B2786143
theorem B1650479 : Blo 1649524 1650479 := bstep (se 1 (by rfl) ⟨1237859, by rfl⟩ : syracuseStep 1650479 = 2475719) B2475719
theorem B1650587 : Blo 1649524 1650587 := bstep (se 1 (by rfl) ⟨1237940, by rfl⟩ : syracuseStep 1650587 = 2475881) B2475881
theorem B12529565 : Blo 1649524 12529565 := bstep (se 3 (by rfl) ⟨2349293, by rfl⟩ : syracuseStep 12529565 = 4698587) B4698587
theorem B21155741 : Blo 1649524 21155741 := bstep (se 3 (by rfl) ⟨3966701, by rfl⟩ : syracuseStep 21155741 = 7933403) B7933403
theorem B1650639 : Blo 1649524 1650639 := bstep (se 1 (by rfl) ⟨1237979, by rfl⟩ : syracuseStep 1650639 = 2475959) B2475959
theorem B1650663 : Blo 1649524 1650663 := bstep (se 1 (by rfl) ⟨1237997, by rfl⟩ : syracuseStep 1650663 = 2475995) B2475995
theorem B4698121 : Blo 1649524 4698121 := bstep (se 2 (by rfl) ⟨1761795, by rfl⟩ : syracuseStep 4698121 = 3523591) B3523591
theorem B15052825 : Blo 1649524 15052825 := bstep (se 2 (by rfl) ⟨5644809, by rfl⟩ : syracuseStep 15052825 = 11289619) B11289619
theorem B5287961 : Blo 1649524 5287961 := bstep (se 2 (by rfl) ⟨1982985, by rfl⟩ : syracuseStep 5287961 = 3965971) B3965971
theorem B14094395 : Blo 1649524 14094395 := bstep (se 1 (by rfl) ⟨10570796, by rfl⟩ : syracuseStep 14094395 = 21141593) B21141593
theorem B43487381 : Blo 1649524 43487381 := bstep (se 6 (by rfl) ⟨1019235, by rfl⟩ : syracuseStep 43487381 = 2038471) B2038471
theorem B7049369 : Blo 1649524 7049369 := bstep (se 2 (by rfl) ⟨2643513, by rfl⟩ : syracuseStep 7049369 = 5287027) B5287027
theorem B15855887 : Blo 1649524 15855887 := bstep (se 1 (by rfl) ⟨11891915, by rfl⟩ : syracuseStep 15855887 = 23783831) B23783831
theorem B1650975 : Blo 1649524 1650975 := bstep (se 1 (by rfl) ⟨1238231, by rfl⟩ : syracuseStep 1650975 = 2476463) B2476463
theorem B1651035 : Blo 1649524 1651035 := bstep (se 1 (by rfl) ⟨1238276, by rfl⟩ : syracuseStep 1651035 = 2476553) B2476553
theorem B31732073 : Blo 1649524 31732073 := bstep (se 2 (by rfl) ⟨11899527, by rfl⟩ : syracuseStep 31732073 = 23799055) B23799055
theorem B1651055 : Blo 1649524 1651055 := bstep (se 1 (by rfl) ⟨1238291, by rfl⟩ : syracuseStep 1651055 = 2476583) B2476583
theorem B1855867 : Blo 1649524 1855867 := bstep (se 1 (by rfl) ⟨1391900, by rfl⟩ : syracuseStep 1855867 = 2783801) B2783801
theorem B1651111 : Blo 1649524 1651111 := bstep (se 1 (by rfl) ⟨1238333, by rfl⟩ : syracuseStep 1651111 = 2476667) B2476667
theorem B1651195 : Blo 1649524 1651195 := bstep (se 1 (by rfl) ⟨1238396, by rfl⟩ : syracuseStep 1651195 = 2476793) B2476793
theorem B1651263 : Blo 1649524 1651263 := bstep (se 1 (by rfl) ⟨1238447, by rfl⟩ : syracuseStep 1651263 = 2476895) B2476895
theorem B1651271 : Blo 1649524 1651271 := bstep (se 1 (by rfl) ⟨1238453, by rfl⟩ : syracuseStep 1651271 = 2476907) B2476907
theorem B67785335 : Blo 1649524 67785335 := bstep (se 1 (by rfl) ⟨50839001, by rfl⟩ : syracuseStep 67785335 = 101678003) B101678003
theorem B1651423 : Blo 1649524 1651423 := bstep (se 1 (by rfl) ⟨1238567, by rfl⟩ : syracuseStep 1651423 = 2477135) B2477135
theorem B1651503 : Blo 1649524 1651503 := bstep (se 1 (by rfl) ⟨1238627, by rfl⟩ : syracuseStep 1651503 = 2477255) B2477255
theorem B1856335 : Blo 1649524 1856335 := bstep (se 1 (by rfl) ⟨1392251, by rfl⟩ : syracuseStep 1856335 = 2784503) B2784503
theorem B8926031 : Blo 1649524 8926031 := bstep (se 1 (by rfl) ⟨6694523, by rfl⟩ : syracuseStep 8926031 = 13389047) B13389047
theorem B3715919 : Blo 1649524 3715919 := bstep (se 1 (by rfl) ⟨2786939, by rfl⟩ : syracuseStep 3715919 = 5573879) B5573879
theorem B1856731 : Blo 1649524 1856731 := bstep (se 1 (by rfl) ⟨1392548, by rfl⟩ : syracuseStep 1856731 = 2785097) B2785097
theorem B15267167 : Blo 1649524 15267167 := bstep (se 1 (by rfl) ⟨11450375, by rfl⟩ : syracuseStep 15267167 = 22900751) B22900751
theorem B1857019 : Blo 1649524 1857019 := bstep (se 1 (by rfl) ⟨1392764, by rfl⟩ : syracuseStep 1857019 = 2785529) B2785529
theorem B1857199 : Blo 1649524 1857199 := bstep (se 1 (by rfl) ⟨1392899, by rfl⟩ : syracuseStep 1857199 = 2785799) B2785799
theorem B7927483 : Blo 1649524 7927483 := bstep (se 1 (by rfl) ⟨5945612, by rfl⟩ : syracuseStep 7927483 = 11891225) B11891225
theorem B4175671 : Blo 1649524 4175671 := bstep (se 1 (by rfl) ⟨3131753, by rfl⟩ : syracuseStep 4175671 = 6263507) B6263507
theorem B3815273 : Blo 1649524 3815273 := bstep (se 2 (by rfl) ⟨1430727, by rfl⟩ : syracuseStep 3815273 = 2861455) B2861455
theorem B48215969 : Blo 1649524 48215969 := bstep (se 2 (by rfl) ⟨18080988, by rfl⟩ : syracuseStep 48215969 = 36161977) B36161977
theorem B1857487 : Blo 1649524 1857487 := bstep (se 1 (by rfl) ⟨1393115, by rfl⟩ : syracuseStep 1857487 = 2786231) B2786231
theorem B17848349 : Blo 1649524 17848349 := bstep (se 3 (by rfl) ⟨3346565, by rfl⟩ : syracuseStep 17848349 = 6693131) B6693131
theorem B11892815 : Blo 1649524 11892815 := bstep (se 1 (by rfl) ⟨8919611, by rfl⟩ : syracuseStep 11892815 = 17839223) B17839223
theorem B10721359 : Blo 1649524 10721359 := bstep (se 1 (by rfl) ⟨8041019, by rfl⟩ : syracuseStep 10721359 = 16082039) B16082039
theorem B5568641 : Blo 1649524 5568641 := bstep (se 2 (by rfl) ⟨2088240, by rfl⟩ : syracuseStep 5568641 = 4176481) B4176481
theorem B4176137 : Blo 1649524 4176137 := bstep (se 2 (by rfl) ⟨1566051, by rfl⟩ : syracuseStep 4176137 = 3132103) B3132103
theorem B1857883 : Blo 1649524 1857883 := bstep (se 1 (by rfl) ⟨1393412, by rfl⟩ : syracuseStep 1857883 = 2786825) B2786825
theorem B2644391 : Blo 1649524 2644391 := bstep (se 1 (by rfl) ⟨1983293, by rfl⟩ : syracuseStep 2644391 = 3966587) B3966587
theorem B8149421 : Blo 1649524 8149421 := bstep (se 3 (by rfl) ⟨1528016, by rfl⟩ : syracuseStep 8149421 = 3056033) B3056033
theorem B10033591 : Blo 1649524 10033591 := bstep (se 1 (by rfl) ⟨7525193, by rfl⟩ : syracuseStep 10033591 = 15050387) B15050387
theorem B5569019 : Blo 1649524 5569019 := bstep (se 1 (by rfl) ⟨4176764, by rfl⟩ : syracuseStep 5569019 = 8353529) B8353529
theorem B3963455 : Blo 1649524 3963455 := bstep (se 1 (by rfl) ⟨2972591, by rfl⟩ : syracuseStep 3963455 = 5945183) B5945183
theorem B6265451 : Blo 1649524 6265451 := bstep (se 1 (by rfl) ⟨4699088, by rfl⟩ : syracuseStep 6265451 = 9398177) B9398177
theorem B6265619 : Blo 1649524 6265619 := bstep (se 1 (by rfl) ⟨4699214, by rfl⟩ : syracuseStep 6265619 = 9398429) B9398429
theorem B7928695 : Blo 1649524 7928695 := bstep (se 1 (by rfl) ⟨5946521, by rfl⟩ : syracuseStep 7928695 = 11893043) B11893043
theorem B4701071 : Blo 1649524 4701071 := bstep (se 1 (by rfl) ⟨3525803, by rfl⟩ : syracuseStep 4701071 = 7051607) B7051607
theorem B5569451 : Blo 1649524 5569451 := bstep (se 1 (by rfl) ⟨4177088, by rfl⟩ : syracuseStep 5569451 = 8354177) B8354177
theorem B43457467 : Blo 1649524 43457467 := bstep (se 1 (by rfl) ⟨32593100, by rfl⟩ : syracuseStep 43457467 = 65186201) B65186201
theorem B15063995 : Blo 1649524 15063995 := bstep (se 1 (by rfl) ⟨11297996, by rfl⟩ : syracuseStep 15063995 = 22595993) B22595993
theorem B4463579 : Blo 1649524 4463579 := bstep (se 1 (by rfl) ⟨3347684, by rfl⟩ : syracuseStep 4463579 = 6695369) B6695369
theorem B25418771 : Blo 1649524 25418771 := bstep (se 1 (by rfl) ⟨19064078, by rfl⟩ : syracuseStep 25418771 = 38128157) B38128157
theorem B9526493 : Blo 1649524 9526493 := bstep (se 3 (by rfl) ⟨1786217, by rfl⟩ : syracuseStep 9526493 = 3572435) B3572435
theorem B4177129 : Blo 1649524 4177129 := bstep (se 2 (by rfl) ⟨1566423, by rfl⟩ : syracuseStep 4177129 = 3132847) B3132847
theorem B4463903 : Blo 1649524 4463903 := bstep (se 1 (by rfl) ⟨3347927, by rfl⟩ : syracuseStep 4463903 = 6695855) B6695855
theorem B4177291 : Blo 1649524 4177291 := bstep (se 1 (by rfl) ⟨3132968, by rfl⟩ : syracuseStep 4177291 = 6265937) B6265937
theorem B5569991 : Blo 1649524 5569991 := bstep (se 1 (by rfl) ⟨4177493, by rfl⟩ : syracuseStep 5569991 = 8354987) B8354987
theorem B2088443 : Blo 1649524 2088443 := bstep (se 1 (by rfl) ⟨1566332, by rfl⟩ : syracuseStep 2088443 = 3132665) B3132665
theorem B11296351 : Blo 1649524 11296351 := bstep (se 1 (by rfl) ⟨8472263, by rfl⟩ : syracuseStep 11296351 = 16944527) B16944527
theorem B2784955 : Blo 1649524 2784955 := bstep (se 1 (by rfl) ⟨2088716, by rfl⟩ : syracuseStep 2784955 = 4177433) B4177433
theorem B4177595 : Blo 1649524 4177595 := bstep (se 1 (by rfl) ⟨3133196, by rfl⟩ : syracuseStep 4177595 = 6266393) B6266393
theorem B4701959 : Blo 1649524 4701959 := bstep (se 1 (by rfl) ⟨3526469, by rfl⟩ : syracuseStep 4701959 = 7052939) B7052939
theorem B5570315 : Blo 1649524 5570315 := bstep (se 1 (by rfl) ⟨4177736, by rfl⟩ : syracuseStep 5570315 = 8355473) B8355473
theorem B20070433 : Blo 1649524 20070433 := bstep (se 2 (by rfl) ⟨7526412, by rfl⟩ : syracuseStep 20070433 = 15052825) B15052825
theorem B9396263 : Blo 1649524 9396263 := bstep (se 1 (by rfl) ⟨7047197, by rfl⟩ : syracuseStep 9396263 = 14094395) B14094395
theorem B28991587 : Blo 1649524 28991587 := bstep (se 1 (by rfl) ⟨21743690, by rfl⟩ : syracuseStep 28991587 = 43487381) B43487381
theorem B14295145 : Blo 1649524 14295145 := bstep (se 2 (by rfl) ⟨5360679, by rfl⟩ : syracuseStep 14295145 = 10721359) B10721359
theorem B16933121 : Blo 1649524 16933121 := bstep (se 2 (by rfl) ⟨6349920, by rfl⟩ : syracuseStep 16933121 = 12699841) B12699841
theorem B8356121 : Blo 1649524 8356121 := bstep (se 2 (by rfl) ⟨3133545, by rfl⟩ : syracuseStep 8356121 = 6267091) B6267091
theorem B4702495 : Blo 1649524 4702495 := bstep (se 1 (by rfl) ⟨3526871, by rfl⟩ : syracuseStep 4702495 = 7053743) B7053743
theorem B4178375 : Blo 1649524 4178375 := bstep (se 1 (by rfl) ⟨3133781, by rfl⟩ : syracuseStep 4178375 = 6267563) B6267563
theorem B2474447 : Blo 1649524 2474447 := bstep (se 1 (by rfl) ⟨1855835, by rfl⟩ : syracuseStep 2474447 = 3711671) B3711671
theorem B2474489 : Blo 1649524 2474489 := bstep (se 2 (by rfl) ⟨927933, by rfl⟩ : syracuseStep 2474489 = 1855867) B1855867
theorem B13378121 : Blo 1649524 13378121 := bstep (se 2 (by rfl) ⟨5016795, by rfl⟩ : syracuseStep 13378121 = 10033591) B10033591
theorem B2474591 : Blo 1649524 2474591 := bstep (se 1 (by rfl) ⟨1855943, by rfl⟩ : syracuseStep 2474591 = 3711887) B3711887
theorem B5571179 : Blo 1649524 5571179 := bstep (se 1 (by rfl) ⟨4178384, by rfl⟩ : syracuseStep 5571179 = 8356769) B8356769
theorem B14107243 : Blo 1649524 14107243 := bstep (se 1 (by rfl) ⟨10580432, by rfl⟩ : syracuseStep 14107243 = 21160865) B21160865
theorem B9405193 : Blo 1649524 9405193 := bstep (se 2 (by rfl) ⟨3526947, by rfl⟩ : syracuseStep 9405193 = 7053895) B7053895
theorem B2786089 : Blo 1649524 2786089 := bstep (se 2 (by rfl) ⟨1044783, by rfl⟩ : syracuseStep 2786089 = 2089567) B2089567
theorem B76235579 : Blo 1649524 76235579 := bstep (se 1 (by rfl) ⟨57176684, by rfl⟩ : syracuseStep 76235579 = 114353369) B114353369
theorem B10576925 : Blo 1649524 10576925 := bstep (se 3 (by rfl) ⟨1983173, by rfl⟩ : syracuseStep 10576925 = 3966347) B3966347
theorem B2786359 : Blo 1649524 2786359 := bstep (se 1 (by rfl) ⟨2089769, by rfl⟩ : syracuseStep 2786359 = 4179539) B4179539
theorem B2475071 : Blo 1649524 2475071 := bstep (se 1 (by rfl) ⟨1856303, by rfl⟩ : syracuseStep 2475071 = 3712607) B3712607
theorem B2475113 : Blo 1649524 2475113 := bstep (se 2 (by rfl) ⟨928167, by rfl⟩ : syracuseStep 2475113 = 1856335) B1856335
theorem B18793619 : Blo 1649524 18793619 := bstep (se 1 (by rfl) ⟨14095214, by rfl⟩ : syracuseStep 18793619 = 28190429) B28190429
theorem B9528509 : Blo 1649524 9528509 := bstep (se 3 (by rfl) ⟨1786595, by rfl⟩ : syracuseStep 9528509 = 3573191) B3573191
theorem B5571773 : Blo 1649524 5571773 := bstep (se 3 (by rfl) ⟨1044707, by rfl⟩ : syracuseStep 5571773 = 2089415) B2089415
theorem B2475215 : Blo 1649524 2475215 := bstep (se 1 (by rfl) ⟨1856411, by rfl⟩ : syracuseStep 2475215 = 3712823) B3712823
theorem B57943289 : Blo 1649524 57943289 := bstep (se 2 (by rfl) ⟨21728733, by rfl⟩ : syracuseStep 57943289 = 43457467) B43457467
theorem B2475419 : Blo 1649524 2475419 := bstep (se 1 (by rfl) ⟨1856564, by rfl⟩ : syracuseStep 2475419 = 3713129) B3713129
theorem B3712427 : Blo 1649524 3712427 := bstep (se 1 (by rfl) ⟨2784320, by rfl⟩ : syracuseStep 3712427 = 5568641) B5568641
theorem B11896415 : Blo 1649524 11896415 := bstep (se 1 (by rfl) ⟨8922311, by rfl⟩ : syracuseStep 11896415 = 17844623) B17844623
theorem B1762927 : Blo 1649524 1762927 := bstep (se 1 (by rfl) ⟨1322195, by rfl⟩ : syracuseStep 1762927 = 2644391) B2644391
theorem B2475641 : Blo 1649524 2475641 := bstep (se 2 (by rfl) ⟨928365, by rfl⟩ : syracuseStep 2475641 = 1856731) B1856731
theorem B3712679 : Blo 1649524 3712679 := bstep (se 1 (by rfl) ⟨2784509, by rfl⟩ : syracuseStep 3712679 = 5569019) B5569019
theorem B2475743 : Blo 1649524 2475743 := bstep (se 1 (by rfl) ⟨1856807, by rfl⟩ : syracuseStep 2475743 = 3713615) B3713615
theorem B2475839 : Blo 1649524 2475839 := bstep (se 1 (by rfl) ⟨1856879, by rfl⟩ : syracuseStep 2475839 = 3713759) B3713759
theorem B3712967 : Blo 1649524 3712967 := bstep (se 1 (by rfl) ⟨2784725, by rfl⟩ : syracuseStep 3712967 = 5569451) B5569451
theorem B11298761 : Blo 1649524 11298761 := bstep (se 2 (by rfl) ⟨4237035, by rfl⟩ : syracuseStep 11298761 = 8474071) B8474071
theorem B2476007 : Blo 1649524 2476007 := bstep (se 1 (by rfl) ⟨1857005, by rfl⟩ : syracuseStep 2476007 = 3714011) B3714011
theorem B2975719 : Blo 1649524 2975719 := bstep (se 1 (by rfl) ⟨2231789, by rfl⟩ : syracuseStep 2975719 = 4463579) B4463579
theorem B2476025 : Blo 1649524 2476025 := bstep (se 2 (by rfl) ⟨928509, by rfl⟩ : syracuseStep 2476025 = 1857019) B1857019
theorem B2476127 : Blo 1649524 2476127 := bstep (se 1 (by rfl) ⟨1857095, by rfl⟩ : syracuseStep 2476127 = 3714191) B3714191
theorem B6350995 : Blo 1649524 6350995 := bstep (se 1 (by rfl) ⟨4763246, by rfl⟩ : syracuseStep 6350995 = 9526493) B9526493
theorem B2476187 : Blo 1649524 2476187 := bstep (se 1 (by rfl) ⟨1857140, by rfl⟩ : syracuseStep 2476187 = 3714281) B3714281
theorem B2476223 : Blo 1649524 2476223 := bstep (se 1 (by rfl) ⟨1857167, by rfl⟩ : syracuseStep 2476223 = 3714335) B3714335
theorem B5572799 : Blo 1649524 5572799 := bstep (se 1 (by rfl) ⟨4179599, by rfl⟩ : syracuseStep 5572799 = 8359199) B8359199
theorem B2975935 : Blo 1649524 2975935 := bstep (se 1 (by rfl) ⟨2231951, by rfl⟩ : syracuseStep 2975935 = 4463903) B4463903
theorem B2476265 : Blo 1649524 2476265 := bstep (se 2 (by rfl) ⟨928599, by rfl⟩ : syracuseStep 2476265 = 1857199) B1857199
theorem B10569977 : Blo 1649524 10569977 := bstep (se 2 (by rfl) ⟨3963741, by rfl⟩ : syracuseStep 10569977 = 7927483) B7927483
theorem B3713273 : Blo 1649524 3713273 := bstep (se 2 (by rfl) ⟨1392477, by rfl⟩ : syracuseStep 3713273 = 2784955) B2784955
theorem B3713327 : Blo 1649524 3713327 := bstep (se 1 (by rfl) ⟨2784995, by rfl⟩ : syracuseStep 3713327 = 5569991) B5569991
theorem B4180319 : Blo 1649524 4180319 := bstep (se 1 (by rfl) ⟨3135239, by rfl⟩ : syracuseStep 4180319 = 6270479) B6270479
theorem B3713543 : Blo 1649524 3713543 := bstep (se 1 (by rfl) ⟨2785157, by rfl⟩ : syracuseStep 3713543 = 5570315) B5570315
theorem B2476571 : Blo 1649524 2476571 := bstep (se 1 (by rfl) ⟨1857428, by rfl⟩ : syracuseStep 2476571 = 3714857) B3714857
theorem B2476649 : Blo 1649524 2476649 := bstep (se 2 (by rfl) ⟨928743, by rfl⟩ : syracuseStep 2476649 = 1857487) B1857487
theorem B3713723 : Blo 1649524 3713723 := bstep (se 1 (by rfl) ⟨2785292, by rfl⟩ : syracuseStep 3713723 = 5570585) B5570585
theorem B14101229 : Blo 1649524 14101229 := bstep (se 3 (by rfl) ⟨2643980, by rfl⟩ : syracuseStep 14101229 = 5287961) B5287961
theorem B10570591 : Blo 1649524 10570591 := bstep (se 1 (by rfl) ⟨7927943, by rfl⟩ : syracuseStep 10570591 = 15855887) B15855887
theorem B21154715 : Blo 1649524 21154715 := bstep (se 1 (by rfl) ⟨15866036, by rfl⟩ : syracuseStep 21154715 = 31732073) B31732073
theorem B1649567 : Blo 1649524 1649567 := bstep (se 1 (by rfl) ⟨1237175, by rfl⟩ : syracuseStep 1649567 = 2474351) B2474351
theorem B1649711 : Blo 1649524 1649711 := bstep (se 1 (by rfl) ⟨1237283, by rfl⟩ : syracuseStep 1649711 = 2474567) B2474567
theorem B1649735 : Blo 1649524 1649735 := bstep (se 1 (by rfl) ⟨1237301, by rfl⟩ : syracuseStep 1649735 = 2474603) B2474603
theorem B45190223 : Blo 1649524 45190223 := bstep (se 1 (by rfl) ⟨33892667, by rfl⟩ : syracuseStep 45190223 = 67785335) B67785335
theorem B2477177 : Blo 1649524 2477177 := bstep (se 2 (by rfl) ⟨928941, by rfl⟩ : syracuseStep 2477177 = 1857883) B1857883
theorem B1649887 : Blo 1649524 1649887 := bstep (se 1 (by rfl) ⟨1237415, by rfl⟩ : syracuseStep 1649887 = 2474831) B2474831
theorem B5950687 : Blo 1649524 5950687 := bstep (se 1 (by rfl) ⟨4463015, by rfl⟩ : syracuseStep 5950687 = 8926031) B8926031
theorem B2477279 : Blo 1649524 2477279 := bstep (se 1 (by rfl) ⟨1857959, by rfl⟩ : syracuseStep 2477279 = 3715919) B3715919
theorem B28216673 : Blo 1649524 28216673 := bstep (se 2 (by rfl) ⟨10581252, by rfl⟩ : syracuseStep 28216673 = 21162505) B21162505
theorem B1650151 : Blo 1649524 1650151 := bstep (se 1 (by rfl) ⟨1237613, by rfl⟩ : syracuseStep 1650151 = 2475227) B2475227
theorem B3714551 : Blo 1649524 3714551 := bstep (se 1 (by rfl) ⟨2785913, by rfl⟩ : syracuseStep 3714551 = 5571827) B5571827
theorem B3714623 : Blo 1649524 3714623 := bstep (se 1 (by rfl) ⟨2785967, by rfl⟩ : syracuseStep 3714623 = 5571935) B5571935
theorem B10178111 : Blo 1649524 10178111 := bstep (se 1 (by rfl) ⟨7633583, by rfl⟩ : syracuseStep 10178111 = 15267167) B15267167
theorem B1650267 : Blo 1649524 1650267 := bstep (se 1 (by rfl) ⟨1237700, by rfl⟩ : syracuseStep 1650267 = 2475401) B2475401
theorem B60206915 : Blo 1649524 60206915 := bstep (se 1 (by rfl) ⟨45155186, by rfl⟩ : syracuseStep 60206915 = 90310373) B90310373
theorem B1650503 : Blo 1649524 1650503 := bstep (se 1 (by rfl) ⟨1237877, by rfl⟩ : syracuseStep 1650503 = 2475755) B2475755
theorem B10571593 : Blo 1649524 10571593 := bstep (se 2 (by rfl) ⟨3964347, by rfl⟩ : syracuseStep 10571593 = 7928695) B7928695
theorem B4697995 : Blo 1649524 4697995 := bstep (se 1 (by rfl) ⟨3523496, by rfl⟩ : syracuseStep 4697995 = 7046993) B7046993
theorem B1650655 : Blo 1649524 1650655 := bstep (se 1 (by rfl) ⟨1237991, by rfl⟩ : syracuseStep 1650655 = 2475983) B2475983
theorem B11898899 : Blo 1649524 11898899 := bstep (se 1 (by rfl) ⟨8924174, by rfl⟩ : syracuseStep 11898899 = 17848349) B17848349
theorem B17395877 : Blo 1649524 17395877 := bstep (se 4 (by rfl) ⟨1630863, by rfl⟩ : syracuseStep 17395877 = 3261727) B3261727
theorem B1650919 : Blo 1649524 1650919 := bstep (se 1 (by rfl) ⟨1238189, by rfl⟩ : syracuseStep 1650919 = 2476379) B2476379
theorem B2642303 : Blo 1649524 2642303 := bstep (se 1 (by rfl) ⟨1981727, by rfl⟩ : syracuseStep 2642303 = 3963455) B3963455
theorem B1651071 : Blo 1649524 1651071 := bstep (se 1 (by rfl) ⟨1238303, by rfl⟩ : syracuseStep 1651071 = 2476607) B2476607
theorem B1651151 : Blo 1649524 1651151 := bstep (se 1 (by rfl) ⟨1238363, by rfl⟩ : syracuseStep 1651151 = 2476727) B2476727
theorem B3715577 : Blo 1649524 3715577 := bstep (se 2 (by rfl) ⟨1393341, by rfl⟩ : syracuseStep 3715577 = 2786683) B2786683
theorem B45183557 : Blo 1649524 45183557 := bstep (se 4 (by rfl) ⟨4235958, by rfl⟩ : syracuseStep 45183557 = 8471917) B8471917
theorem B3715667 : Blo 1649524 3715667 := bstep (se 1 (by rfl) ⟨2786750, by rfl⟩ : syracuseStep 3715667 = 5573501) B5573501
theorem B3134047 : Blo 1649524 3134047 := bstep (se 1 (by rfl) ⟨2350535, by rfl⟩ : syracuseStep 3134047 = 4701071) B4701071
theorem B1651303 : Blo 1649524 1651303 := bstep (se 1 (by rfl) ⟨1238477, by rfl⟩ : syracuseStep 1651303 = 2476955) B2476955
theorem B16945847 : Blo 1649524 16945847 := bstep (se 1 (by rfl) ⟨12709385, by rfl⟩ : syracuseStep 16945847 = 25418771) B25418771
theorem B3715847 : Blo 1649524 3715847 := bstep (se 1 (by rfl) ⟨2786885, by rfl⟩ : syracuseStep 3715847 = 5573771) B5573771
theorem B15061801 : Blo 1649524 15061801 := bstep (se 2 (by rfl) ⟨5648175, by rfl⟩ : syracuseStep 15061801 = 11296351) B11296351
theorem B18789245 : Blo 1649524 18789245 := bstep (se 3 (by rfl) ⟨3522983, by rfl⟩ : syracuseStep 18789245 = 7045967) B7045967
theorem B5567561 : Blo 1649524 5567561 := bstep (se 2 (by rfl) ⟨2087835, by rfl⟩ : syracuseStep 5567561 = 4175671) B4175671
theorem B3134639 : Blo 1649524 3134639 := bstep (se 1 (by rfl) ⟨2350979, by rfl⟩ : syracuseStep 3134639 = 4701959) B4701959
theorem B8353043 : Blo 1649524 8353043 := bstep (se 1 (by rfl) ⟨6264782, by rfl⟩ : syracuseStep 8353043 = 12529565) B12529565
theorem B14103827 : Blo 1649524 14103827 := bstep (se 1 (by rfl) ⟨10577870, by rfl⟩ : syracuseStep 14103827 = 21155741) B21155741
theorem B6264161 : Blo 1649524 6264161 := bstep (se 2 (by rfl) ⟨2349060, by rfl⟩ : syracuseStep 6264161 = 4698121) B4698121
theorem B3134875 : Blo 1649524 3134875 := bstep (se 1 (by rfl) ⟨2351156, by rfl⟩ : syracuseStep 3134875 = 4702313) B4702313
theorem B4699579 : Blo 1649524 4699579 := bstep (se 1 (by rfl) ⟨3524684, by rfl⟩ : syracuseStep 4699579 = 7049369) B7049369
theorem B2381531 : Blo 1649524 2381531 := bstep (se 1 (by rfl) ⟨1786148, by rfl⟩ : syracuseStep 2381531 = 3572297) B3572297
theorem B1857343 : Blo 1649524 1857343 := bstep (se 1 (by rfl) ⟨1393007, by rfl⟩ : syracuseStep 1857343 = 2786015) B2786015
theorem B24106871 : Blo 1649524 24106871 := bstep (se 1 (by rfl) ⟨18080153, by rfl⟩ : syracuseStep 24106871 = 36160307) B36160307
theorem B2643943 : Blo 1649524 2643943 := bstep (se 1 (by rfl) ⟨1982957, by rfl⟩ : syracuseStep 2643943 = 3965915) B3965915
theorem B1857631 : Blo 1649524 1857631 := bstep (se 1 (by rfl) ⟨1393223, by rfl⟩ : syracuseStep 1857631 = 2786447) B2786447
theorem B21731789 : Blo 1649524 21731789 := bstep (se 3 (by rfl) ⟨4074710, by rfl⟩ : syracuseStep 21731789 = 8149421) B8149421
theorem B10574387 : Blo 1649524 10574387 := bstep (se 1 (by rfl) ⟨7930790, by rfl⟩ : syracuseStep 10574387 = 15861581) B15861581
theorem B4700729 : Blo 1649524 4700729 := bstep (se 2 (by rfl) ⟨1762773, by rfl⟩ : syracuseStep 4700729 = 3525547) B3525547
theorem B32143979 : Blo 1649524 32143979 := bstep (se 1 (by rfl) ⟨24107984, by rfl⟩ : syracuseStep 32143979 = 48215969) B48215969
theorem B5569181 : Blo 1649524 5569181 := bstep (se 3 (by rfl) ⟨1044221, by rfl⟩ : syracuseStep 5569181 = 2088443) B2088443
theorem B7928543 : Blo 1649524 7928543 := bstep (se 1 (by rfl) ⟨5946407, by rfl⟩ : syracuseStep 7928543 = 11892815) B11892815
theorem B9394987 : Blo 1649524 9394987 := bstep (se 1 (by rfl) ⟨7046240, by rfl⟩ : syracuseStep 9394987 = 14092481) B14092481
theorem B2784091 : Blo 1649524 2784091 := bstep (se 1 (by rfl) ⟨2088068, by rfl⟩ : syracuseStep 2784091 = 4176137) B4176137
theorem B18799451 : Blo 1649524 18799451 := bstep (se 1 (by rfl) ⟨14099588, by rfl⟩ : syracuseStep 18799451 = 28199177) B28199177
theorem B5569505 : Blo 1649524 5569505 := bstep (se 2 (by rfl) ⟨2088564, by rfl⟩ : syracuseStep 5569505 = 4177129) B4177129
theorem B4176967 : Blo 1649524 4176967 := bstep (se 1 (by rfl) ⟨3132725, by rfl⟩ : syracuseStep 4176967 = 6265451) B6265451
theorem B2088119 : Blo 1649524 2088119 := bstep (se 1 (by rfl) ⟨1566089, by rfl⟩ : syracuseStep 2088119 = 3132179) B3132179
theorem B4177079 : Blo 1649524 4177079 := bstep (se 1 (by rfl) ⟨3132809, by rfl⟩ : syracuseStep 4177079 = 6265619) B6265619
theorem B5569721 : Blo 1649524 5569721 := bstep (se 2 (by rfl) ⟨2088645, by rfl⟩ : syracuseStep 5569721 = 4177291) B4177291
theorem B10042663 : Blo 1649524 10042663 := bstep (se 1 (by rfl) ⟨7531997, by rfl⟩ : syracuseStep 10042663 = 15063995) B15063995
theorem B2088271 : Blo 1649524 2088271 := bstep (se 1 (by rfl) ⟨1566203, by rfl⟩ : syracuseStep 2088271 = 3132407) B3132407
theorem B2973095 : Blo 1649524 2973095 := bstep (se 1 (by rfl) ⟨2229821, by rfl⟩ : syracuseStep 2973095 = 4459643) B4459643
theorem B4234727 : Blo 1649524 4234727 := bstep (se 1 (by rfl) ⟨3176045, by rfl⟩ : syracuseStep 4234727 = 6352091) B6352091
theorem B10174061 : Blo 1649524 10174061 := bstep (se 3 (by rfl) ⟨1907636, by rfl⟩ : syracuseStep 10174061 = 3815273) B3815273
theorem B2785063 : Blo 1649524 2785063 := bstep (se 1 (by rfl) ⟨2088797, by rfl⟩ : syracuseStep 2785063 = 4177595) B4177595
theorem B4702141 : Blo 1649524 4702141 := bstep (se 3 (by rfl) ⟨881651, by rfl⟩ : syracuseStep 4702141 = 1763303) B1763303
theorem B11288747 : Blo 1649524 11288747 := bstep (se 1 (by rfl) ⟨8466560, by rfl⟩ : syracuseStep 11288747 = 16933121) B16933121
theorem B5570747 : Blo 1649524 5570747 := bstep (se 1 (by rfl) ⟨4178060, by rfl⟩ : syracuseStep 5570747 = 8356121) B8356121
theorem B1761535 : Blo 1649524 1761535 := bstep (se 1 (by rfl) ⟨1321151, by rfl⟩ : syracuseStep 1761535 = 2642303) B2642303
theorem B2785583 : Blo 1649524 2785583 := bstep (se 1 (by rfl) ⟨2089187, by rfl⟩ : syracuseStep 2785583 = 4178375) B4178375
theorem B30122371 : Blo 1649524 30122371 := bstep (se 1 (by rfl) ⟨22591778, by rfl⟩ : syracuseStep 30122371 = 45183557) B45183557
theorem B11297231 : Blo 1649524 11297231 := bstep (se 1 (by rfl) ⟨8472923, by rfl⟩ : syracuseStep 11297231 = 16945847) B16945847
theorem B50823719 : Blo 1649524 50823719 := bstep (se 1 (by rfl) ⟨38117789, by rfl⟩ : syracuseStep 50823719 = 76235579) B76235579
theorem B12526163 : Blo 1649524 12526163 := bstep (se 1 (by rfl) ⟨9394622, by rfl⟩ : syracuseStep 12526163 = 18789245) B18789245
theorem B3711707 : Blo 1649524 3711707 := bstep (se 1 (by rfl) ⟨2783780, by rfl⟩ : syracuseStep 3711707 = 5567561) B5567561
theorem B4178729 : Blo 1649524 4178729 := bstep (se 2 (by rfl) ⟨1567023, by rfl⟩ : syracuseStep 4178729 = 3134047) B3134047
theorem B18809657 : Blo 1649524 18809657 := bstep (se 2 (by rfl) ⟨7053621, by rfl⟩ : syracuseStep 18809657 = 14107243) B14107243
theorem B2474951 : Blo 1649524 2474951 := bstep (se 1 (by rfl) ⟨1856213, by rfl⟩ : syracuseStep 2474951 = 3712427) B3712427
theorem B12526649 : Blo 1649524 12526649 := bstep (se 2 (by rfl) ⟨4697493, by rfl⟩ : syracuseStep 12526649 = 9394987) B9394987
theorem B7930943 : Blo 1649524 7930943 := bstep (se 1 (by rfl) ⟨5948207, by rfl⟩ : syracuseStep 7930943 = 11896415) B11896415
theorem B2475119 : Blo 1649524 2475119 := bstep (se 1 (by rfl) ⟨1856339, by rfl⟩ : syracuseStep 2475119 = 3712679) B3712679
theorem B3712121 : Blo 1649524 3712121 := bstep (se 2 (by rfl) ⟨1392045, by rfl⟩ : syracuseStep 3712121 = 2784091) B2784091
theorem B2475311 : Blo 1649524 2475311 := bstep (se 1 (by rfl) ⟨1856483, by rfl⟩ : syracuseStep 2475311 = 3712967) B3712967
theorem B7046651 : Blo 1649524 7046651 := bstep (se 1 (by rfl) ⟨5284988, by rfl⟩ : syracuseStep 7046651 = 10569977) B10569977
theorem B2475515 : Blo 1649524 2475515 := bstep (se 1 (by rfl) ⟨1856636, by rfl⟩ : syracuseStep 2475515 = 3713273) B3713273
theorem B2475551 : Blo 1649524 2475551 := bstep (se 1 (by rfl) ⟨1856663, by rfl⟩ : syracuseStep 2475551 = 3713327) B3713327
theorem B2786879 : Blo 1649524 2786879 := bstep (se 1 (by rfl) ⟨2090159, by rfl⟩ : syracuseStep 2786879 = 4180319) B4180319
theorem B2475695 : Blo 1649524 2475695 := bstep (se 1 (by rfl) ⟨1856771, by rfl⟩ : syracuseStep 2475695 = 3713543) B3713543
theorem B3712787 : Blo 1649524 3712787 := bstep (se 1 (by rfl) ⟨2784590, by rfl⟩ : syracuseStep 3712787 = 5569181) B5569181
theorem B2475815 : Blo 1649524 2475815 := bstep (se 1 (by rfl) ⟨1856861, by rfl⟩ : syracuseStep 2475815 = 3713723) B3713723
theorem B5285695 : Blo 1649524 5285695 := bstep (se 1 (by rfl) ⟨3964271, by rfl⟩ : syracuseStep 5285695 = 7928543) B7928543
theorem B4179833 : Blo 1649524 4179833 := bstep (se 2 (by rfl) ⟨1567437, by rfl⟩ : syracuseStep 4179833 = 3134875) B3134875
theorem B3713003 : Blo 1649524 3713003 := bstep (se 1 (by rfl) ⟨2784752, by rfl⟩ : syracuseStep 3713003 = 5569505) B5569505
theorem B3713147 : Blo 1649524 3713147 := bstep (se 1 (by rfl) ⟨2784860, by rfl⟩ : syracuseStep 3713147 = 5569721) B5569721
theorem B18811115 : Blo 1649524 18811115 := bstep (se 1 (by rfl) ⟨14108336, by rfl⟩ : syracuseStep 18811115 = 28216673) B28216673
theorem B2476367 : Blo 1649524 2476367 := bstep (se 1 (by rfl) ⟨1857275, by rfl⟩ : syracuseStep 2476367 = 3714551) B3714551
theorem B2476415 : Blo 1649524 2476415 := bstep (se 1 (by rfl) ⟨1857311, by rfl⟩ : syracuseStep 2476415 = 3714623) B3714623
theorem B6785407 : Blo 1649524 6785407 := bstep (se 1 (by rfl) ⟨5089055, by rfl⟩ : syracuseStep 6785407 = 10178111) B10178111
theorem B3713417 : Blo 1649524 3713417 := bstep (se 2 (by rfl) ⟨1392531, by rfl⟩ : syracuseStep 3713417 = 2785063) B2785063
theorem B2476457 : Blo 1649524 2476457 := bstep (se 2 (by rfl) ⟨928671, by rfl⟩ : syracuseStep 2476457 = 1857343) B1857343
theorem B6269521 : Blo 1649524 6269521 := bstep (se 2 (by rfl) ⟨2351070, by rfl⟩ : syracuseStep 6269521 = 4702141) B4702141
theorem B3525257 : Blo 1649524 3525257 := bstep (se 2 (by rfl) ⟨1321971, by rfl⟩ : syracuseStep 3525257 = 2643943) B2643943
theorem B3967625 : Blo 1649524 3967625 := bstep (se 2 (by rfl) ⟨1487859, by rfl⟩ : syracuseStep 3967625 = 2975719) B2975719
theorem B7932599 : Blo 1649524 7932599 := bstep (se 1 (by rfl) ⟨5949449, by rfl⟩ : syracuseStep 7932599 = 11898899) B11898899
theorem B2476841 : Blo 1649524 2476841 := bstep (se 2 (by rfl) ⟨928815, by rfl⟩ : syracuseStep 2476841 = 1857631) B1857631
theorem B3967913 : Blo 1649524 3967913 := bstep (se 2 (by rfl) ⟨1487967, by rfl⟩ : syracuseStep 3967913 = 2975935) B2975935
theorem B1649631 : Blo 1649524 1649631 := bstep (se 1 (by rfl) ⟨1237223, by rfl⟩ : syracuseStep 1649631 = 2474447) B2474447
theorem B1649659 : Blo 1649524 1649659 := bstep (se 1 (by rfl) ⟨1237244, by rfl⟩ : syracuseStep 1649659 = 2474489) B2474489
theorem B2477051 : Blo 1649524 2477051 := bstep (se 1 (by rfl) ⟨1857788, by rfl⟩ : syracuseStep 2477051 = 3715577) B3715577
theorem B6269993 : Blo 1649524 6269993 := bstep (se 2 (by rfl) ⟨2351247, by rfl⟩ : syracuseStep 6269993 = 4702495) B4702495
theorem B2477111 : Blo 1649524 2477111 := bstep (se 1 (by rfl) ⟨1857833, by rfl⟩ : syracuseStep 2477111 = 3715667) B3715667
theorem B1649727 : Blo 1649524 1649727 := bstep (se 1 (by rfl) ⟨1237295, by rfl⟩ : syracuseStep 1649727 = 2474591) B2474591
theorem B3714119 : Blo 1649524 3714119 := bstep (se 1 (by rfl) ⟨2785589, by rfl⟩ : syracuseStep 3714119 = 5571179) B5571179
theorem B8359037 : Blo 1649524 8359037 := bstep (se 3 (by rfl) ⟨1567319, by rfl⟩ : syracuseStep 8359037 = 3134639) B3134639
theorem B2477231 : Blo 1649524 2477231 := bstep (se 1 (by rfl) ⟨1857923, by rfl⟩ : syracuseStep 2477231 = 3715847) B3715847
theorem B1650047 : Blo 1649524 1650047 := bstep (se 1 (by rfl) ⟨1237535, by rfl⟩ : syracuseStep 1650047 = 2475071) B2475071
theorem B1650075 : Blo 1649524 1650075 := bstep (se 1 (by rfl) ⟨1237556, by rfl⟩ : syracuseStep 1650075 = 2475113) B2475113
theorem B12529079 : Blo 1649524 12529079 := bstep (se 1 (by rfl) ⟨9396809, by rfl⟩ : syracuseStep 12529079 = 18793619) B18793619
theorem B6352339 : Blo 1649524 6352339 := bstep (se 1 (by rfl) ⟨4764254, by rfl⟩ : syracuseStep 6352339 = 9528509) B9528509
theorem B3714515 : Blo 1649524 3714515 := bstep (se 1 (by rfl) ⟨2785886, by rfl⟩ : syracuseStep 3714515 = 5571773) B5571773
theorem B1650143 : Blo 1649524 1650143 := bstep (se 1 (by rfl) ⟨1237607, by rfl⟩ : syracuseStep 1650143 = 2475215) B2475215
theorem B1650279 : Blo 1649524 1650279 := bstep (se 1 (by rfl) ⟨1237709, by rfl⟩ : syracuseStep 1650279 = 2475419) B2475419
theorem B20082401 : Blo 1649524 20082401 := bstep (se 2 (by rfl) ⟨7530900, by rfl⟩ : syracuseStep 20082401 = 15061801) B15061801
theorem B3714785 : Blo 1649524 3714785 := bstep (se 2 (by rfl) ⟨1393044, by rfl⟩ : syracuseStep 3714785 = 2786089) B2786089
theorem B1650427 : Blo 1649524 1650427 := bstep (se 1 (by rfl) ⟨1237820, by rfl⟩ : syracuseStep 1650427 = 2475641) B2475641
theorem B14094121 : Blo 1649524 14094121 := bstep (se 2 (by rfl) ⟨5285295, by rfl⟩ : syracuseStep 14094121 = 10570591) B10570591
theorem B1650495 : Blo 1649524 1650495 := bstep (se 1 (by rfl) ⟨1237871, by rfl⟩ : syracuseStep 1650495 = 2475743) B2475743
theorem B1650559 : Blo 1649524 1650559 := bstep (se 1 (by rfl) ⟨1237919, by rfl⟩ : syracuseStep 1650559 = 2475839) B2475839
theorem B11292605 : Blo 1649524 11292605 := bstep (se 3 (by rfl) ⟨2117363, by rfl⟩ : syracuseStep 11292605 = 4234727) B4234727
theorem B7532507 : Blo 1649524 7532507 := bstep (se 1 (by rfl) ⟨5649380, by rfl⟩ : syracuseStep 7532507 = 11298761) B11298761
theorem B1650671 : Blo 1649524 1650671 := bstep (se 1 (by rfl) ⟨1238003, by rfl⟩ : syracuseStep 1650671 = 2476007) B2476007
theorem B1650683 : Blo 1649524 1650683 := bstep (se 1 (by rfl) ⟨1238012, by rfl⟩ : syracuseStep 1650683 = 2476025) B2476025
theorem B1650751 : Blo 1649524 1650751 := bstep (se 1 (by rfl) ⟨1238063, by rfl⟩ : syracuseStep 1650751 = 2476127) B2476127
theorem B3715145 : Blo 1649524 3715145 := bstep (se 2 (by rfl) ⟨1393179, by rfl⟩ : syracuseStep 3715145 = 2786359) B2786359
theorem B1650791 : Blo 1649524 1650791 := bstep (se 1 (by rfl) ⟨1238093, by rfl⟩ : syracuseStep 1650791 = 2476187) B2476187
theorem B1650815 : Blo 1649524 1650815 := bstep (se 1 (by rfl) ⟨1238111, by rfl⟩ : syracuseStep 1650815 = 2476223) B2476223
theorem B3715199 : Blo 1649524 3715199 := bstep (se 1 (by rfl) ⟨2786399, by rfl⟩ : syracuseStep 3715199 = 5572799) B5572799
theorem B1650843 : Blo 1649524 1650843 := bstep (se 1 (by rfl) ⟨1238132, by rfl⟩ : syracuseStep 1650843 = 2476265) B2476265
theorem B7934249 : Blo 1649524 7934249 := bstep (se 2 (by rfl) ⟨2975343, by rfl⟩ : syracuseStep 7934249 = 5950687) B5950687
theorem B14487859 : Blo 1649524 14487859 := bstep (se 1 (by rfl) ⟨10865894, by rfl⟩ : syracuseStep 14487859 = 21731789) B21731789
theorem B1651047 : Blo 1649524 1651047 := bstep (se 1 (by rfl) ⟨1238285, by rfl⟩ : syracuseStep 1651047 = 2476571) B2476571
theorem B7049591 : Blo 1649524 7049591 := bstep (se 1 (by rfl) ⟨5287193, by rfl⟩ : syracuseStep 7049591 = 10574387) B10574387
theorem B3133819 : Blo 1649524 3133819 := bstep (se 1 (by rfl) ⟨2350364, by rfl⟩ : syracuseStep 3133819 = 4700729) B4700729
theorem B13390217 : Blo 1649524 13390217 := bstep (se 2 (by rfl) ⟨5021331, by rfl⟩ : syracuseStep 13390217 = 10042663) B10042663
theorem B1651099 : Blo 1649524 1651099 := bstep (se 1 (by rfl) ⟨1238324, by rfl⟩ : syracuseStep 1651099 = 2476649) B2476649
theorem B9400819 : Blo 1649524 9400819 := bstep (se 1 (by rfl) ⟨7050614, by rfl⟩ : syracuseStep 9400819 = 14101229) B14101229
theorem B14103143 : Blo 1649524 14103143 := bstep (se 1 (by rfl) ⟨10577357, by rfl⟩ : syracuseStep 14103143 = 21154715) B21154715
theorem B30126815 : Blo 1649524 30126815 := bstep (se 1 (by rfl) ⟨22595111, by rfl⟩ : syracuseStep 30126815 = 45190223) B45190223
theorem B1651451 : Blo 1649524 1651451 := bstep (se 1 (by rfl) ⟨1238588, by rfl⟩ : syracuseStep 1651451 = 2477177) B2477177
theorem B1651519 : Blo 1649524 1651519 := bstep (se 1 (by rfl) ⟨1238639, by rfl⟩ : syracuseStep 1651519 = 2477279) B2477279
theorem B14095457 : Blo 1649524 14095457 := bstep (se 2 (by rfl) ⟨5285796, by rfl⟩ : syracuseStep 14095457 = 10571593) B10571593
theorem B6263993 : Blo 1649524 6263993 := bstep (se 2 (by rfl) ⟨2348997, by rfl⟩ : syracuseStep 6263993 = 4697995) B4697995
theorem B40137943 : Blo 1649524 40137943 := bstep (se 1 (by rfl) ⟨30103457, by rfl⟩ : syracuseStep 40137943 = 60206915) B60206915
theorem B6264175 : Blo 1649524 6264175 := bstep (se 1 (by rfl) ⟨4698131, by rfl⟩ : syracuseStep 6264175 = 9396263) B9396263
theorem B26760577 : Blo 1649524 26760577 := bstep (se 2 (by rfl) ⟨10035216, by rfl⟩ : syracuseStep 26760577 = 20070433) B20070433
theorem B11597251 : Blo 1649524 11597251 := bstep (se 1 (by rfl) ⟨8697938, by rfl⟩ : syracuseStep 11597251 = 17395877) B17395877
theorem B38655449 : Blo 1649524 38655449 := bstep (se 2 (by rfl) ⟨14495793, by rfl⟩ : syracuseStep 38655449 = 28991587) B28991587
theorem B19060193 : Blo 1649524 19060193 := bstep (se 2 (by rfl) ⟨7147572, by rfl⟩ : syracuseStep 19060193 = 14295145) B14295145
theorem B8467993 : Blo 1649524 8467993 := bstep (se 2 (by rfl) ⟨3175497, by rfl⟩ : syracuseStep 8467993 = 6350995) B6350995
theorem B8918747 : Blo 1649524 8918747 := bstep (se 1 (by rfl) ⟨6689060, by rfl⟩ : syracuseStep 8918747 = 13378121) B13378121
theorem B5568317 : Blo 1649524 5568317 := bstep (se 3 (by rfl) ⟨1044059, by rfl⟩ : syracuseStep 5568317 = 2088119) B2088119
theorem B9402277 : Blo 1649524 9402277 := bstep (se 4 (by rfl) ⟨881463, by rfl⟩ : syracuseStep 9402277 = 1762927) B1762927
theorem B154515437 : Blo 1649524 154515437 := bstep (se 3 (by rfl) ⟨28971644, by rfl⟩ : syracuseStep 154515437 = 57943289) B57943289
theorem B7051283 : Blo 1649524 7051283 := bstep (se 1 (by rfl) ⟨5288462, by rfl⟩ : syracuseStep 7051283 = 10576925) B10576925
theorem B5568695 : Blo 1649524 5568695 := bstep (se 1 (by rfl) ⟨4176521, by rfl⟩ : syracuseStep 5568695 = 8353043) B8353043
theorem B9402551 : Blo 1649524 9402551 := bstep (se 1 (by rfl) ⟨7051913, by rfl⟩ : syracuseStep 9402551 = 14103827) B14103827
theorem B4176107 : Blo 1649524 4176107 := bstep (se 1 (by rfl) ⟨3132080, by rfl⟩ : syracuseStep 4176107 = 6264161) B6264161
theorem B12540257 : Blo 1649524 12540257 := bstep (se 2 (by rfl) ⟨4702596, by rfl⟩ : syracuseStep 12540257 = 9405193) B9405193
theorem B16071247 : Blo 1649524 16071247 := bstep (se 1 (by rfl) ⟨12053435, by rfl⟩ : syracuseStep 16071247 = 24106871) B24106871
theorem B5569289 : Blo 1649524 5569289 := bstep (se 2 (by rfl) ⟨2088483, by rfl⟩ : syracuseStep 5569289 = 4176967) B4176967
theorem B21429319 : Blo 1649524 21429319 := bstep (se 1 (by rfl) ⟨16071989, by rfl⟩ : syracuseStep 21429319 = 32143979) B32143979
theorem B2784361 : Blo 1649524 2784361 := bstep (se 2 (by rfl) ⟨1044135, by rfl⟩ : syracuseStep 2784361 = 2088271) B2088271
theorem B12532967 : Blo 1649524 12532967 := bstep (se 1 (by rfl) ⟨9399725, by rfl⟩ : syracuseStep 12532967 = 18799451) B18799451
theorem B6266105 : Blo 1649524 6266105 := bstep (se 2 (by rfl) ⟨2349789, by rfl⟩ : syracuseStep 6266105 = 4699579) B4699579
theorem B2784719 : Blo 1649524 2784719 := bstep (se 1 (by rfl) ⟨2088539, by rfl⟩ : syracuseStep 2784719 = 4177079) B4177079
theorem B1982063 : Blo 1649524 1982063 := bstep (se 1 (by rfl) ⟨1486547, by rfl⟩ : syracuseStep 1982063 = 2973095) B2973095
theorem B25402997 : Blo 1649524 25402997 := bstep (se 5 (by rfl) ⟨1190765, by rfl⟩ : syracuseStep 25402997 = 2381531) B2381531
theorem B6782707 : Blo 1649524 6782707 := bstep (se 1 (by rfl) ⟨5087030, by rfl⟩ : syracuseStep 6782707 = 10174061) B10174061
theorem B45162629 : Blo 1649524 45162629 := bstep (se 4 (by rfl) ⟨4233996, by rfl⟩ : syracuseStep 45162629 = 8467993) B8467993
theorem B33882479 : Blo 1649524 33882479 := bstep (se 1 (by rfl) ⟨25411859, by rfl⟩ : syracuseStep 33882479 = 50823719) B50823719
theorem B19317145 : Blo 1649524 19317145 := bstep (se 2 (by rfl) ⟨7243929, by rfl⟩ : syracuseStep 19317145 = 14487859) B14487859
theorem B2474471 : Blo 1649524 2474471 := bstep (se 1 (by rfl) ⟨1855853, by rfl⟩ : syracuseStep 2474471 = 3711707) B3711707
theorem B4178425 : Blo 1649524 4178425 := bstep (se 2 (by rfl) ⟨1566909, by rfl⟩ : syracuseStep 4178425 = 3133819) B3133819
theorem B2785819 : Blo 1649524 2785819 := bstep (se 1 (by rfl) ⟨2089364, by rfl⟩ : syracuseStep 2785819 = 4178729) B4178729
theorem B12534425 : Blo 1649524 12534425 := bstep (se 2 (by rfl) ⟨4700409, by rfl⟩ : syracuseStep 12534425 = 9400819) B9400819
theorem B9396971 : Blo 1649524 9396971 := bstep (se 1 (by rfl) ⟨7047728, by rfl⟩ : syracuseStep 9396971 = 14095457) B14095457
theorem B2474747 : Blo 1649524 2474747 := bstep (se 1 (by rfl) ⟨1856060, by rfl⟩ : syracuseStep 2474747 = 3712121) B3712121
theorem B12706795 : Blo 1649524 12706795 := bstep (se 1 (by rfl) ⟨9530096, by rfl⟩ : syracuseStep 12706795 = 19060193) B19060193
theorem B2475191 : Blo 1649524 2475191 := bstep (se 1 (by rfl) ⟨1856393, by rfl⟩ : syracuseStep 2475191 = 3712787) B3712787
theorem B3712211 : Blo 1649524 3712211 := bstep (se 1 (by rfl) ⟨2784158, by rfl⟩ : syracuseStep 3712211 = 5568317) B5568317
theorem B2786555 : Blo 1649524 2786555 := bstep (se 1 (by rfl) ⟨2089916, by rfl⟩ : syracuseStep 2786555 = 4179833) B4179833
theorem B2475335 : Blo 1649524 2475335 := bstep (se 1 (by rfl) ⟨1856501, by rfl⟩ : syracuseStep 2475335 = 3713003) B3713003
theorem B2475431 : Blo 1649524 2475431 := bstep (se 1 (by rfl) ⟨1856573, by rfl⟩ : syracuseStep 2475431 = 3713147) B3713147
theorem B3712463 : Blo 1649524 3712463 := bstep (se 1 (by rfl) ⟨2784347, by rfl⟩ : syracuseStep 3712463 = 5568695) B5568695
theorem B6268367 : Blo 1649524 6268367 := bstep (se 1 (by rfl) ⟨4701275, by rfl⟩ : syracuseStep 6268367 = 9402551) B9402551
theorem B3712481 : Blo 1649524 3712481 := bstep (se 2 (by rfl) ⟨1392180, by rfl⟩ : syracuseStep 3712481 = 2784361) B2784361
theorem B2475611 : Blo 1649524 2475611 := bstep (se 1 (by rfl) ⟨1856708, by rfl⟩ : syracuseStep 2475611 = 3713417) B3713417
theorem B5285501 : Blo 1649524 5285501 := bstep (se 3 (by rfl) ⟨991031, by rfl⟩ : syracuseStep 5285501 = 1982063) B1982063
theorem B3712859 : Blo 1649524 3712859 := bstep (se 1 (by rfl) ⟨2784644, by rfl⟩ : syracuseStep 3712859 = 5569289) B5569289
theorem B4179995 : Blo 1649524 4179995 := bstep (se 1 (by rfl) ⟨3134996, by rfl⟩ : syracuseStep 4179995 = 6269993) B6269993
theorem B2476079 : Blo 1649524 2476079 := bstep (se 1 (by rfl) ⟨1857059, by rfl⟩ : syracuseStep 2476079 = 3714119) B3714119
theorem B5572691 : Blo 1649524 5572691 := bstep (se 1 (by rfl) ⟨4179518, by rfl⟩ : syracuseStep 5572691 = 8359037) B8359037
theorem B2476343 : Blo 1649524 2476343 := bstep (se 1 (by rfl) ⟨1857257, by rfl⟩ : syracuseStep 2476343 = 3714515) B3714515
theorem B16935331 : Blo 1649524 16935331 := bstep (se 1 (by rfl) ⟨12701498, by rfl⟩ : syracuseStep 16935331 = 25402997) B25402997
theorem B7047593 : Blo 1649524 7047593 := bstep (se 2 (by rfl) ⟨2642847, by rfl⟩ : syracuseStep 7047593 = 5285695) B5285695
theorem B13388267 : Blo 1649524 13388267 := bstep (se 1 (by rfl) ⟨10041200, by rfl⟩ : syracuseStep 13388267 = 20082401) B20082401
theorem B2476523 : Blo 1649524 2476523 := bstep (se 1 (by rfl) ⟨1857392, by rfl⟩ : syracuseStep 2476523 = 3714785) B3714785
theorem B12536369 : Blo 1649524 12536369 := bstep (se 2 (by rfl) ⟨4701138, by rfl⟩ : syracuseStep 12536369 = 9402277) B9402277
theorem B2476763 : Blo 1649524 2476763 := bstep (se 1 (by rfl) ⟨1857572, by rfl⟩ : syracuseStep 2476763 = 3715145) B3715145
theorem B2476799 : Blo 1649524 2476799 := bstep (se 1 (by rfl) ⟨1857599, by rfl⟩ : syracuseStep 2476799 = 3715199) B3715199
theorem B3713831 : Blo 1649524 3713831 := bstep (se 1 (by rfl) ⟨2785373, by rfl⟩ : syracuseStep 3713831 = 5570747) B5570747
theorem B7531487 : Blo 1649524 7531487 := bstep (se 1 (by rfl) ⟨5648615, by rfl⟩ : syracuseStep 7531487 = 11297231) B11297231
theorem B8350775 : Blo 1649524 8350775 := bstep (se 1 (by rfl) ⟨6263081, by rfl⟩ : syracuseStep 8350775 = 12526163) B12526163
theorem B9047209 : Blo 1649524 9047209 := bstep (se 2 (by rfl) ⟨3392703, by rfl⟩ : syracuseStep 9047209 = 6785407) B6785407
theorem B1649967 : Blo 1649524 1649967 := bstep (se 1 (by rfl) ⟨1237475, by rfl⟩ : syracuseStep 1649967 = 2474951) B2474951
theorem B8351099 : Blo 1649524 8351099 := bstep (se 1 (by rfl) ⟨6263324, by rfl⟩ : syracuseStep 8351099 = 12526649) B12526649
theorem B5287295 : Blo 1649524 5287295 := bstep (se 1 (by rfl) ⟨3965471, by rfl⟩ : syracuseStep 5287295 = 7930943) B7930943
theorem B1650079 : Blo 1649524 1650079 := bstep (se 1 (by rfl) ⟨1237559, by rfl⟩ : syracuseStep 1650079 = 2475119) B2475119
theorem B8359361 : Blo 1649524 8359361 := bstep (se 2 (by rfl) ⟨3134760, by rfl⟩ : syracuseStep 8359361 = 6269521) B6269521
theorem B1650207 : Blo 1649524 1650207 := bstep (se 1 (by rfl) ⟨1237655, by rfl⟩ : syracuseStep 1650207 = 2475311) B2475311
theorem B4697767 : Blo 1649524 4697767 := bstep (se 1 (by rfl) ⟨3523325, by rfl⟩ : syracuseStep 4697767 = 7046651) B7046651
theorem B1650343 : Blo 1649524 1650343 := bstep (se 1 (by rfl) ⟨1237757, by rfl⟩ : syracuseStep 1650343 = 2475515) B2475515
theorem B1650367 : Blo 1649524 1650367 := bstep (se 1 (by rfl) ⟨1237775, by rfl⟩ : syracuseStep 1650367 = 2475551) B2475551
theorem B1650463 : Blo 1649524 1650463 := bstep (se 1 (by rfl) ⟨1237847, by rfl⟩ : syracuseStep 1650463 = 2475695) B2475695
theorem B1650543 : Blo 1649524 1650543 := bstep (se 1 (by rfl) ⟨1237907, by rfl⟩ : syracuseStep 1650543 = 2475815) B2475815
theorem B103010291 : Blo 1649524 103010291 := bstep (se 1 (by rfl) ⟨77257718, by rfl⟩ : syracuseStep 103010291 = 154515437) B154515437
theorem B1650911 : Blo 1649524 1650911 := bstep (se 1 (by rfl) ⟨1238183, by rfl⟩ : syracuseStep 1650911 = 2476367) B2476367
theorem B8360171 : Blo 1649524 8360171 := bstep (se 1 (by rfl) ⟨6270128, by rfl⟩ : syracuseStep 8360171 = 12540257) B12540257
theorem B1650943 : Blo 1649524 1650943 := bstep (se 1 (by rfl) ⟨1238207, by rfl⟩ : syracuseStep 1650943 = 2476415) B2476415
theorem B1650971 : Blo 1649524 1650971 := bstep (se 1 (by rfl) ⟨1238228, by rfl⟩ : syracuseStep 1650971 = 2476457) B2476457
theorem B5288399 : Blo 1649524 5288399 := bstep (se 1 (by rfl) ⟨3966299, by rfl⟩ : syracuseStep 5288399 = 7932599) B7932599
theorem B8352233 : Blo 1649524 8352233 := bstep (se 2 (by rfl) ⟨3132087, by rfl⟩ : syracuseStep 8352233 = 6264175) B6264175
theorem B35680769 : Blo 1649524 35680769 := bstep (se 2 (by rfl) ⟨13380288, by rfl⟩ : syracuseStep 35680769 = 26760577) B26760577
theorem B1651227 : Blo 1649524 1651227 := bstep (se 1 (by rfl) ⟨1238420, by rfl⟩ : syracuseStep 1651227 = 2476841) B2476841
theorem B15463001 : Blo 1649524 15463001 := bstep (se 2 (by rfl) ⟨5798625, by rfl⟩ : syracuseStep 15463001 = 11597251) B11597251
theorem B1651367 : Blo 1649524 1651367 := bstep (se 1 (by rfl) ⟨1238525, by rfl⟩ : syracuseStep 1651367 = 2477051) B2477051
theorem B1651407 : Blo 1649524 1651407 := bstep (se 1 (by rfl) ⟨1238555, by rfl⟩ : syracuseStep 1651407 = 2477111) B2477111
theorem B1651487 : Blo 1649524 1651487 := bstep (se 1 (by rfl) ⟨1238615, by rfl⟩ : syracuseStep 1651487 = 2477231) B2477231
theorem B8352719 : Blo 1649524 8352719 := bstep (se 1 (by rfl) ⟨6264539, by rfl⟩ : syracuseStep 8352719 = 12529079) B12529079
theorem B1856479 : Blo 1649524 1856479 := bstep (se 1 (by rfl) ⟨1392359, by rfl⟩ : syracuseStep 1856479 = 2784719) B2784719
theorem B10581101 : Blo 1649524 10581101 := bstep (se 3 (by rfl) ⟨1983956, by rfl⟩ : syracuseStep 10581101 = 3967913) B3967913
theorem B5289499 : Blo 1649524 5289499 := bstep (se 1 (by rfl) ⟨3967124, by rfl⟩ : syracuseStep 5289499 = 7934249) B7934249
theorem B1857055 : Blo 1649524 1857055 := bstep (se 1 (by rfl) ⟨1392791, by rfl⟩ : syracuseStep 1857055 = 2785583) B2785583
theorem B4699727 : Blo 1649524 4699727 := bstep (se 1 (by rfl) ⟨3524795, by rfl⟩ : syracuseStep 4699727 = 7049591) B7049591
theorem B8926811 : Blo 1649524 8926811 := bstep (se 1 (by rfl) ⟨6695108, by rfl⟩ : syracuseStep 8926811 = 13390217) B13390217
theorem B2348713 : Blo 1649524 2348713 := bstep (se 2 (by rfl) ⟨880767, by rfl⟩ : syracuseStep 2348713 = 1761535) B1761535
theorem B9402095 : Blo 1649524 9402095 := bstep (se 1 (by rfl) ⟨7051571, by rfl⟩ : syracuseStep 9402095 = 14103143) B14103143
theorem B30103325 : Blo 1649524 30103325 := bstep (se 3 (by rfl) ⟨5644373, by rfl⟩ : syracuseStep 30103325 = 11288747) B11288747
theorem B20084543 : Blo 1649524 20084543 := bstep (se 1 (by rfl) ⟨15063407, by rfl⟩ : syracuseStep 20084543 = 30126815) B30126815
theorem B40163161 : Blo 1649524 40163161 := bstep (se 2 (by rfl) ⟨15061185, by rfl⟩ : syracuseStep 40163161 = 30122371) B30122371
theorem B12539771 : Blo 1649524 12539771 := bstep (se 1 (by rfl) ⟨9404828, by rfl⟩ : syracuseStep 12539771 = 18809657) B18809657
theorem B21428329 : Blo 1649524 21428329 := bstep (se 2 (by rfl) ⟨8035623, by rfl⟩ : syracuseStep 21428329 = 16071247) B16071247
theorem B4175995 : Blo 1649524 4175995 := bstep (se 1 (by rfl) ⟨3131996, by rfl⟩ : syracuseStep 4175995 = 6263993) B6263993
theorem B25770299 : Blo 1649524 25770299 := bstep (se 1 (by rfl) ⟨19327724, by rfl⟩ : syracuseStep 25770299 = 38655449) B38655449
theorem B1857919 : Blo 1649524 1857919 := bstep (se 1 (by rfl) ⟨1393439, by rfl⟩ : syracuseStep 1857919 = 2786879) B2786879
theorem B5945831 : Blo 1649524 5945831 := bstep (se 1 (by rfl) ⟨4459373, by rfl⟩ : syracuseStep 5945831 = 8918747) B8918747
theorem B36174437 : Blo 1649524 36174437 := bstep (se 4 (by rfl) ⟨3391353, by rfl⟩ : syracuseStep 36174437 = 6782707) B6782707
theorem B4700855 : Blo 1649524 4700855 := bstep (se 1 (by rfl) ⟨3525641, by rfl⟩ : syracuseStep 4700855 = 7051283) B7051283
theorem B28572425 : Blo 1649524 28572425 := bstep (se 2 (by rfl) ⟨10714659, by rfl⟩ : syracuseStep 28572425 = 21429319) B21429319
theorem B2784071 : Blo 1649524 2784071 := bstep (se 1 (by rfl) ⟨2088053, by rfl⟩ : syracuseStep 2784071 = 4176107) B4176107
theorem B12540743 : Blo 1649524 12540743 := bstep (se 1 (by rfl) ⟨9405557, by rfl⟩ : syracuseStep 12540743 = 18811115) B18811115
theorem B53517257 : Blo 1649524 53517257 := bstep (se 2 (by rfl) ⟨20068971, by rfl⟩ : syracuseStep 53517257 = 40137943) B40137943
theorem B2350171 : Blo 1649524 2350171 := bstep (se 1 (by rfl) ⟨1762628, by rfl⟩ : syracuseStep 2350171 = 3525257) B3525257
theorem B2645083 : Blo 1649524 2645083 := bstep (se 1 (by rfl) ⟨1983812, by rfl⟩ : syracuseStep 2645083 = 3967625) B3967625
theorem B8469785 : Blo 1649524 8469785 := bstep (se 2 (by rfl) ⟨3176169, by rfl⟩ : syracuseStep 8469785 = 6352339) B6352339
theorem B8355311 : Blo 1649524 8355311 := bstep (se 1 (by rfl) ⟨6266483, by rfl⟩ : syracuseStep 8355311 = 12532967) B12532967
theorem B4177403 : Blo 1649524 4177403 := bstep (se 1 (by rfl) ⟨3133052, by rfl⟩ : syracuseStep 4177403 = 6266105) B6266105
theorem B18792161 : Blo 1649524 18792161 := bstep (se 2 (by rfl) ⟨7047060, by rfl⟩ : syracuseStep 18792161 = 14094121) B14094121
theorem B7528403 : Blo 1649524 7528403 := bstep (se 1 (by rfl) ⟨5646302, by rfl⟩ : syracuseStep 7528403 = 11292605) B11292605
theorem B5021671 : Blo 1649524 5021671 := bstep (se 1 (by rfl) ⟨3766253, by rfl⟩ : syracuseStep 5021671 = 7532507) B7532507
theorem B8356283 : Blo 1649524 8356283 := bstep (se 1 (by rfl) ⟨6267212, by rfl⟩ : syracuseStep 8356283 = 12534425) B12534425
theorem B25756193 : Blo 1649524 25756193 := bstep (se 2 (by rfl) ⟨9658572, by rfl⟩ : syracuseStep 25756193 = 19317145) B19317145
theorem B5571233 : Blo 1649524 5571233 := bstep (se 2 (by rfl) ⟨2089212, by rfl⟩ : syracuseStep 5571233 = 4178425) B4178425
theorem B7054067 : Blo 1649524 7054067 := bstep (se 1 (by rfl) ⟨5290550, by rfl⟩ : syracuseStep 7054067 = 10581101) B10581101
theorem B2474807 : Blo 1649524 2474807 := bstep (se 1 (by rfl) ⟨1856105, by rfl⟩ : syracuseStep 2474807 = 3712211) B3712211
theorem B2474975 : Blo 1649524 2474975 := bstep (se 1 (by rfl) ⟨1856231, by rfl⟩ : syracuseStep 2474975 = 3712463) B3712463
theorem B4178911 : Blo 1649524 4178911 := bstep (se 1 (by rfl) ⟨3134183, by rfl⟩ : syracuseStep 4178911 = 6268367) B6268367
theorem B2474987 : Blo 1649524 2474987 := bstep (se 1 (by rfl) ⟨1856240, by rfl⟩ : syracuseStep 2474987 = 3712481) B3712481
theorem B14099453 : Blo 1649524 14099453 := bstep (se 3 (by rfl) ⟨2643647, by rfl⟩ : syracuseStep 14099453 = 5287295) B5287295
theorem B3523667 : Blo 1649524 3523667 := bstep (se 1 (by rfl) ⟨2642750, by rfl⟩ : syracuseStep 3523667 = 5285501) B5285501
theorem B6268063 : Blo 1649524 6268063 := bstep (se 1 (by rfl) ⟨4701047, by rfl⟩ : syracuseStep 6268063 = 9402095) B9402095
theorem B2475239 : Blo 1649524 2475239 := bstep (se 1 (by rfl) ⟨1856429, by rfl⟩ : syracuseStep 2475239 = 3712859) B3712859
theorem B35702045 : Blo 1649524 35702045 := bstep (se 3 (by rfl) ⟨6694133, by rfl⟩ : syracuseStep 35702045 = 13388267) B13388267
theorem B2475305 : Blo 1649524 2475305 := bstep (se 2 (by rfl) ⟨928239, by rfl⟩ : syracuseStep 2475305 = 1856479) B1856479
theorem B16942393 : Blo 1649524 16942393 := bstep (se 2 (by rfl) ⟨6353397, by rfl⟩ : syracuseStep 16942393 = 12706795) B12706795
theorem B2786663 : Blo 1649524 2786663 := bstep (se 1 (by rfl) ⟨2089997, by rfl⟩ : syracuseStep 2786663 = 4179995) B4179995
theorem B8357579 : Blo 1649524 8357579 := bstep (se 1 (by rfl) ⟨6268184, by rfl⟩ : syracuseStep 8357579 = 12536369) B12536369
theorem B19048283 : Blo 1649524 19048283 := bstep (se 1 (by rfl) ⟨14286212, by rfl⟩ : syracuseStep 19048283 = 28572425) B28572425
theorem B2475887 : Blo 1649524 2475887 := bstep (se 1 (by rfl) ⟨1856915, by rfl⟩ : syracuseStep 2475887 = 3713831) B3713831
theorem B35678171 : Blo 1649524 35678171 := bstep (se 1 (by rfl) ⟨26758628, by rfl⟩ : syracuseStep 35678171 = 53517257) B53517257
theorem B2476073 : Blo 1649524 2476073 := bstep (se 2 (by rfl) ⟨928527, by rfl⟩ : syracuseStep 2476073 = 1857055) B1857055
theorem B5646523 : Blo 1649524 5646523 := bstep (se 1 (by rfl) ⟨4234892, by rfl⟩ : syracuseStep 5646523 = 8469785) B8469785
theorem B3131617 : Blo 1649524 3131617 := bstep (se 2 (by rfl) ⟨1174356, by rfl⟩ : syracuseStep 3131617 = 2348713) B2348713
theorem B5572907 : Blo 1649524 5572907 := bstep (se 1 (by rfl) ⟨4179680, by rfl⟩ : syracuseStep 5572907 = 8359361) B8359361
theorem B12528107 : Blo 1649524 12528107 := bstep (se 1 (by rfl) ⟨9396080, by rfl⟩ : syracuseStep 12528107 = 18792161) B18792161
theorem B6695561 : Blo 1649524 6695561 := bstep (se 2 (by rfl) ⟨2510835, by rfl⟩ : syracuseStep 6695561 = 5021671) B5021671
theorem B30108419 : Blo 1649524 30108419 := bstep (se 1 (by rfl) ⟨22581314, by rfl⟩ : syracuseStep 30108419 = 45162629) B45162629
theorem B5573447 : Blo 1649524 5573447 := bstep (se 1 (by rfl) ⟨4180085, by rfl⟩ : syracuseStep 5573447 = 8360171) B8360171
theorem B22588319 : Blo 1649524 22588319 := bstep (se 1 (by rfl) ⟨16941239, by rfl⟩ : syracuseStep 22588319 = 33882479) B33882479
theorem B3525599 : Blo 1649524 3525599 := bstep (se 1 (by rfl) ⟨2644199, by rfl⟩ : syracuseStep 3525599 = 5288399) B5288399
theorem B1649647 : Blo 1649524 1649647 := bstep (se 1 (by rfl) ⟨1237235, by rfl⟩ : syracuseStep 1649647 = 2474471) B2474471
theorem B1649831 : Blo 1649524 1649831 := bstep (se 1 (by rfl) ⟨1237373, by rfl⟩ : syracuseStep 1649831 = 2474747) B2474747
theorem B2477225 : Blo 1649524 2477225 := bstep (se 2 (by rfl) ⟨928959, by rfl⟩ : syracuseStep 2477225 = 1857919) B1857919
theorem B22580441 : Blo 1649524 22580441 := bstep (se 2 (by rfl) ⟨8467665, by rfl⟩ : syracuseStep 22580441 = 16935331) B16935331
theorem B3714425 : Blo 1649524 3714425 := bstep (se 2 (by rfl) ⟨1392909, by rfl⟩ : syracuseStep 3714425 = 2785819) B2785819
theorem B1650127 : Blo 1649524 1650127 := bstep (se 1 (by rfl) ⟨1237595, by rfl⟩ : syracuseStep 1650127 = 2475191) B2475191
theorem B1650223 : Blo 1649524 1650223 := bstep (se 1 (by rfl) ⟨1237667, by rfl⟩ : syracuseStep 1650223 = 2475335) B2475335
theorem B1650287 : Blo 1649524 1650287 := bstep (se 1 (by rfl) ⟨1237715, by rfl⟩ : syracuseStep 1650287 = 2475431) B2475431
theorem B3133151 : Blo 1649524 3133151 := bstep (se 1 (by rfl) ⟨2349863, by rfl⟩ : syracuseStep 3133151 = 4699727) B4699727
theorem B1650407 : Blo 1649524 1650407 := bstep (se 1 (by rfl) ⟨1237805, by rfl⟩ : syracuseStep 1650407 = 2475611) B2475611
theorem B5951207 : Blo 1649524 5951207 := bstep (se 1 (by rfl) ⟨4463405, by rfl⟩ : syracuseStep 5951207 = 8926811) B8926811
theorem B13389695 : Blo 1649524 13389695 := bstep (se 1 (by rfl) ⟨10042271, by rfl⟩ : syracuseStep 13389695 = 20084543) B20084543
theorem B8359847 : Blo 1649524 8359847 := bstep (se 1 (by rfl) ⟨6269885, by rfl⟩ : syracuseStep 8359847 = 12539771) B12539771
theorem B1650719 : Blo 1649524 1650719 := bstep (se 1 (by rfl) ⟨1238039, by rfl⟩ : syracuseStep 1650719 = 2476079) B2476079
theorem B3715127 : Blo 1649524 3715127 := bstep (se 1 (by rfl) ⟨2786345, by rfl⟩ : syracuseStep 3715127 = 5572691) B5572691
theorem B3133561 : Blo 1649524 3133561 := bstep (se 2 (by rfl) ⟨1175085, by rfl⟩ : syracuseStep 3133561 = 2350171) B2350171
theorem B3526777 : Blo 1649524 3526777 := bstep (se 2 (by rfl) ⟨1322541, by rfl⟩ : syracuseStep 3526777 = 2645083) B2645083
theorem B1650895 : Blo 1649524 1650895 := bstep (se 1 (by rfl) ⟨1238171, by rfl⟩ : syracuseStep 1650895 = 2476343) B2476343
theorem B12062945 : Blo 1649524 12062945 := bstep (se 2 (by rfl) ⟨4523604, by rfl⟩ : syracuseStep 12062945 = 9047209) B9047209
theorem B41234669 : Blo 1649524 41234669 := bstep (se 3 (by rfl) ⟨7731500, by rfl⟩ : syracuseStep 41234669 = 15463001) B15463001
theorem B4698395 : Blo 1649524 4698395 := bstep (se 1 (by rfl) ⟨3523796, by rfl⟩ : syracuseStep 4698395 = 7047593) B7047593
theorem B1651015 : Blo 1649524 1651015 := bstep (se 1 (by rfl) ⟨1238261, by rfl⟩ : syracuseStep 1651015 = 2476523) B2476523
theorem B3133903 : Blo 1649524 3133903 := bstep (se 1 (by rfl) ⟨2350427, by rfl⟩ : syracuseStep 3133903 = 4700855) B4700855
theorem B1651175 : Blo 1649524 1651175 := bstep (se 1 (by rfl) ⟨1238381, by rfl⟩ : syracuseStep 1651175 = 2476763) B2476763
theorem B1651199 : Blo 1649524 1651199 := bstep (se 1 (by rfl) ⟨1238399, by rfl⟩ : syracuseStep 1651199 = 2476799) B2476799
theorem B1856047 : Blo 1649524 1856047 := bstep (se 1 (by rfl) ⟨1392035, by rfl⟩ : syracuseStep 1856047 = 2784071) B2784071
theorem B8360495 : Blo 1649524 8360495 := bstep (se 1 (by rfl) ⟨6270371, by rfl⟩ : syracuseStep 8360495 = 12540743) B12540743
theorem B5567183 : Blo 1649524 5567183 := bstep (se 1 (by rfl) ⟨4175387, by rfl⟩ : syracuseStep 5567183 = 8350775) B8350775
theorem B6263689 : Blo 1649524 6263689 := bstep (se 2 (by rfl) ⟨2348883, by rfl⟩ : syracuseStep 6263689 = 4697767) B4697767
theorem B5567399 : Blo 1649524 5567399 := bstep (se 1 (by rfl) ⟨4175549, by rfl⟩ : syracuseStep 5567399 = 8351099) B8351099
theorem B5018935 : Blo 1649524 5018935 := bstep (se 1 (by rfl) ⟨3764201, by rfl⟩ : syracuseStep 5018935 = 7528403) B7528403
theorem B28571105 : Blo 1649524 28571105 := bstep (se 2 (by rfl) ⟨10714164, by rfl⟩ : syracuseStep 28571105 = 21428329) B21428329
theorem B5567993 : Blo 1649524 5567993 := bstep (se 2 (by rfl) ⟨2087997, by rfl⟩ : syracuseStep 5567993 = 4175995) B4175995
theorem B5568155 : Blo 1649524 5568155 := bstep (se 1 (by rfl) ⟨4176116, by rfl⟩ : syracuseStep 5568155 = 8352233) B8352233
theorem B23787179 : Blo 1649524 23787179 := bstep (se 1 (by rfl) ⟨17840384, by rfl⟩ : syracuseStep 23787179 = 35680769) B35680769
theorem B6264647 : Blo 1649524 6264647 := bstep (se 1 (by rfl) ⟨4698485, by rfl⟩ : syracuseStep 6264647 = 9396971) B9396971
theorem B5568479 : Blo 1649524 5568479 := bstep (se 1 (by rfl) ⟨4176359, by rfl⟩ : syracuseStep 5568479 = 8352719) B8352719
theorem B68720797 : Blo 1649524 68720797 := bstep (se 3 (by rfl) ⟨12885149, by rfl⟩ : syracuseStep 68720797 = 25770299) B25770299
theorem B1857703 : Blo 1649524 1857703 := bstep (se 1 (by rfl) ⟨1393277, by rfl⟩ : syracuseStep 1857703 = 2786555) B2786555
theorem B20068883 : Blo 1649524 20068883 := bstep (se 1 (by rfl) ⟨15051662, by rfl⟩ : syracuseStep 20068883 = 30103325) B30103325
theorem B3963887 : Blo 1649524 3963887 := bstep (se 1 (by rfl) ⟨2972915, by rfl⟩ : syracuseStep 3963887 = 5945831) B5945831
theorem B24116291 : Blo 1649524 24116291 := bstep (se 1 (by rfl) ⟨18087218, by rfl⟩ : syracuseStep 24116291 = 36174437) B36174437
theorem B5020991 : Blo 1649524 5020991 := bstep (se 1 (by rfl) ⟨3765743, by rfl⟩ : syracuseStep 5020991 = 7531487) B7531487
theorem B7052665 : Blo 1649524 7052665 := bstep (se 2 (by rfl) ⟨2644749, by rfl⟩ : syracuseStep 7052665 = 5289499) B5289499
theorem B5570207 : Blo 1649524 5570207 := bstep (se 1 (by rfl) ⟨4177655, by rfl⟩ : syracuseStep 5570207 = 8355311) B8355311
theorem B2784935 : Blo 1649524 2784935 := bstep (se 1 (by rfl) ⟨2088701, by rfl⟩ : syracuseStep 2784935 = 4177403) B4177403
theorem B53550881 : Blo 1649524 53550881 := bstep (se 2 (by rfl) ⟨20081580, by rfl⟩ : syracuseStep 53550881 = 40163161) B40163161
theorem B68673527 : Blo 1649524 68673527 := bstep (se 1 (by rfl) ⟨51505145, by rfl⟩ : syracuseStep 68673527 = 103010291) B103010291
theorem B4178081 : Blo 1649524 4178081 := bstep (se 2 (by rfl) ⟨1566780, by rfl⟩ : syracuseStep 4178081 = 3133561) B3133561
theorem B4702369 : Blo 1649524 4702369 := bstep (se 2 (by rfl) ⟨1763388, by rfl⟩ : syracuseStep 4702369 = 3526777) B3526777
theorem B91627729 : Blo 1649524 91627729 := bstep (se 2 (by rfl) ⟨34360398, by rfl⟩ : syracuseStep 91627729 = 68720797) B68720797
theorem B9396445 : Blo 1649524 9396445 := bstep (se 3 (by rfl) ⟨1761833, by rfl⟩ : syracuseStep 9396445 = 3523667) B3523667
theorem B7528697 : Blo 1649524 7528697 := bstep (se 2 (by rfl) ⟨2823261, by rfl⟩ : syracuseStep 7528697 = 5646523) B5646523
theorem B5570855 : Blo 1649524 5570855 := bstep (se 1 (by rfl) ⟨4178141, by rfl⟩ : syracuseStep 5570855 = 8356283) B8356283
theorem B17170795 : Blo 1649524 17170795 := bstep (se 1 (by rfl) ⟨12878096, by rfl⟩ : syracuseStep 17170795 = 25756193) B25756193
theorem B3711455 : Blo 1649524 3711455 := bstep (se 1 (by rfl) ⟨2783591, by rfl⟩ : syracuseStep 3711455 = 5567183) B5567183
theorem B4702711 : Blo 1649524 4702711 := bstep (se 1 (by rfl) ⟨3527033, by rfl⟩ : syracuseStep 4702711 = 7054067) B7054067
theorem B4178537 : Blo 1649524 4178537 := bstep (se 2 (by rfl) ⟨1566951, by rfl⟩ : syracuseStep 4178537 = 3133903) B3133903
theorem B3711599 : Blo 1649524 3711599 := bstep (se 1 (by rfl) ⟨2783699, by rfl⟩ : syracuseStep 3711599 = 5567399) B5567399
theorem B2474729 : Blo 1649524 2474729 := bstep (se 2 (by rfl) ⟨928023, by rfl⟩ : syracuseStep 2474729 = 1856047) B1856047
theorem B19047403 : Blo 1649524 19047403 := bstep (se 1 (by rfl) ⟨14285552, by rfl⟩ : syracuseStep 19047403 = 28571105) B28571105
theorem B3711995 : Blo 1649524 3711995 := bstep (se 1 (by rfl) ⟨2783996, by rfl⟩ : syracuseStep 3711995 = 5567993) B5567993
theorem B3712103 : Blo 1649524 3712103 := bstep (se 1 (by rfl) ⟨2784077, by rfl⟩ : syracuseStep 3712103 = 5568155) B5568155
theorem B5571719 : Blo 1649524 5571719 := bstep (se 1 (by rfl) ⟨4178789, by rfl⟩ : syracuseStep 5571719 = 8357579) B8357579
theorem B12698855 : Blo 1649524 12698855 := bstep (se 1 (by rfl) ⟨9524141, by rfl⟩ : syracuseStep 12698855 = 19048283) B19048283
theorem B5571881 : Blo 1649524 5571881 := bstep (se 2 (by rfl) ⟨2089455, by rfl⟩ : syracuseStep 5571881 = 4178911) B4178911
theorem B3712319 : Blo 1649524 3712319 := bstep (se 1 (by rfl) ⟨2784239, by rfl⟩ : syracuseStep 3712319 = 5568479) B5568479
theorem B8357417 : Blo 1649524 8357417 := bstep (se 2 (by rfl) ⟨3134031, by rfl⟩ : syracuseStep 8357417 = 6268063) B6268063
theorem B13379255 : Blo 1649524 13379255 := bstep (se 1 (by rfl) ⟨10034441, by rfl⟩ : syracuseStep 13379255 = 20068883) B20068883
theorem B20072279 : Blo 1649524 20072279 := bstep (se 1 (by rfl) ⟨15054209, by rfl⟩ : syracuseStep 20072279 = 30108419) B30108419
theorem B15058879 : Blo 1649524 15058879 := bstep (se 1 (by rfl) ⟨11294159, by rfl⟩ : syracuseStep 15058879 = 22588319) B22588319
theorem B2476283 : Blo 1649524 2476283 := bstep (se 1 (by rfl) ⟨1857212, by rfl⟩ : syracuseStep 2476283 = 3714425) B3714425
theorem B3713471 : Blo 1649524 3713471 := bstep (se 1 (by rfl) ⟨2785103, by rfl⟩ : syracuseStep 3713471 = 5570207) B5570207
theorem B3967471 : Blo 1649524 3967471 := bstep (se 1 (by rfl) ⟨2975603, by rfl⟩ : syracuseStep 3967471 = 5951207) B5951207
theorem B5573231 : Blo 1649524 5573231 := bstep (se 1 (by rfl) ⟨4179923, by rfl⟩ : syracuseStep 5573231 = 8359847) B8359847
theorem B2476751 : Blo 1649524 2476751 := bstep (se 1 (by rfl) ⟨1857563, by rfl⟩ : syracuseStep 2476751 = 3715127) B3715127
theorem B3132263 : Blo 1649524 3132263 := bstep (se 1 (by rfl) ⟨2349197, by rfl⟩ : syracuseStep 3132263 = 4698395) B4698395
theorem B2476937 : Blo 1649524 2476937 := bstep (se 2 (by rfl) ⟨928851, by rfl⟩ : syracuseStep 2476937 = 1857703) B1857703
theorem B5573663 : Blo 1649524 5573663 := bstep (se 1 (by rfl) ⟨4180247, by rfl⟩ : syracuseStep 5573663 = 8360495) B8360495
theorem B3714155 : Blo 1649524 3714155 := bstep (se 1 (by rfl) ⟨2785616, by rfl⟩ : syracuseStep 3714155 = 5571233) B5571233
theorem B1649871 : Blo 1649524 1649871 := bstep (se 1 (by rfl) ⟨1237403, by rfl⟩ : syracuseStep 1649871 = 2474807) B2474807
theorem B1649983 : Blo 1649524 1649983 := bstep (se 1 (by rfl) ⟨1237487, by rfl⟩ : syracuseStep 1649983 = 2474975) B2474975
theorem B1649991 : Blo 1649524 1649991 := bstep (se 1 (by rfl) ⟨1237493, by rfl⟩ : syracuseStep 1649991 = 2474987) B2474987
theorem B9399635 : Blo 1649524 9399635 := bstep (se 1 (by rfl) ⟨7049726, by rfl⟩ : syracuseStep 9399635 = 14099453) B14099453
theorem B1650159 : Blo 1649524 1650159 := bstep (se 1 (by rfl) ⟨1237619, by rfl⟩ : syracuseStep 1650159 = 2475239) B2475239
theorem B23801363 : Blo 1649524 23801363 := bstep (se 1 (by rfl) ⟨17851022, by rfl⟩ : syracuseStep 23801363 = 35702045) B35702045
theorem B1650203 : Blo 1649524 1650203 := bstep (se 1 (by rfl) ⟨1237652, by rfl⟩ : syracuseStep 1650203 = 2475305) B2475305
theorem B8351585 : Blo 1649524 8351585 := bstep (se 2 (by rfl) ⟨3131844, by rfl⟩ : syracuseStep 8351585 = 6263689) B6263689
theorem B1650591 : Blo 1649524 1650591 := bstep (se 1 (by rfl) ⟨1237943, by rfl⟩ : syracuseStep 1650591 = 2475887) B2475887
theorem B23785447 : Blo 1649524 23785447 := bstep (se 1 (by rfl) ⟨17839085, by rfl⟩ : syracuseStep 23785447 = 35678171) B35678171
theorem B1650715 : Blo 1649524 1650715 := bstep (se 1 (by rfl) ⟨1238036, by rfl⟩ : syracuseStep 1650715 = 2476073) B2476073
theorem B3715271 : Blo 1649524 3715271 := bstep (se 1 (by rfl) ⟨2786453, by rfl⟩ : syracuseStep 3715271 = 5572907) B5572907
theorem B8352071 : Blo 1649524 8352071 := bstep (se 1 (by rfl) ⟨6264053, by rfl⟩ : syracuseStep 8352071 = 12528107) B12528107
theorem B17854829 : Blo 1649524 17854829 := bstep (se 3 (by rfl) ⟨3347780, by rfl⟩ : syracuseStep 17854829 = 6695561) B6695561
theorem B22589857 : Blo 1649524 22589857 := bstep (se 2 (by rfl) ⟨8471196, by rfl⟩ : syracuseStep 22589857 = 16942393) B16942393
theorem B3715631 : Blo 1649524 3715631 := bstep (se 1 (by rfl) ⟨2786723, by rfl⟩ : syracuseStep 3715631 = 5573447) B5573447
theorem B2642591 : Blo 1649524 2642591 := bstep (se 1 (by rfl) ⟨1981943, by rfl⟩ : syracuseStep 2642591 = 3963887) B3963887
theorem B16077527 : Blo 1649524 16077527 := bstep (se 1 (by rfl) ⟨12058145, by rfl⟩ : syracuseStep 16077527 = 24116291) B24116291
theorem B1651483 : Blo 1649524 1651483 := bstep (se 1 (by rfl) ⟨1238612, by rfl⟩ : syracuseStep 1651483 = 2477225) B2477225
theorem B15053627 : Blo 1649524 15053627 := bstep (se 1 (by rfl) ⟨11290220, by rfl⟩ : syracuseStep 15053627 = 22580441) B22580441
theorem B3347327 : Blo 1649524 3347327 := bstep (se 1 (by rfl) ⟨2510495, by rfl⟩ : syracuseStep 3347327 = 5020991) B5020991
theorem B1856623 : Blo 1649524 1856623 := bstep (se 1 (by rfl) ⟨1392467, by rfl⟩ : syracuseStep 1856623 = 2784935) B2784935
theorem B8926463 : Blo 1649524 8926463 := bstep (se 1 (by rfl) ⟨6694847, by rfl⟩ : syracuseStep 8926463 = 13389695) B13389695
theorem B45782351 : Blo 1649524 45782351 := bstep (se 1 (by rfl) ⟨34336763, by rfl⟩ : syracuseStep 45782351 = 68673527) B68673527
theorem B8041963 : Blo 1649524 8041963 := bstep (se 1 (by rfl) ⟨6031472, by rfl⟩ : syracuseStep 8041963 = 12062945) B12062945
theorem B27489779 : Blo 1649524 27489779 := bstep (se 1 (by rfl) ⟨20617334, by rfl⟩ : syracuseStep 27489779 = 41234669) B41234669
theorem B4175489 : Blo 1649524 4175489 := bstep (se 2 (by rfl) ⟨1565808, by rfl⟩ : syracuseStep 4175489 = 3131617) B3131617
theorem B1857775 : Blo 1649524 1857775 := bstep (se 1 (by rfl) ⟨1393331, by rfl⟩ : syracuseStep 1857775 = 2786663) B2786663
theorem B15858119 : Blo 1649524 15858119 := bstep (se 1 (by rfl) ⟨11893589, by rfl⟩ : syracuseStep 15858119 = 23787179) B23787179
theorem B4176431 : Blo 1649524 4176431 := bstep (se 1 (by rfl) ⟨3132323, by rfl⟩ : syracuseStep 4176431 = 6264647) B6264647
theorem B6691913 : Blo 1649524 6691913 := bstep (se 2 (by rfl) ⟨2509467, by rfl⟩ : syracuseStep 6691913 = 5018935) B5018935
theorem B9403553 : Blo 1649524 9403553 := bstep (se 2 (by rfl) ⟨3526332, by rfl⟩ : syracuseStep 9403553 = 7052665) B7052665
theorem B2350399 : Blo 1649524 2350399 := bstep (se 1 (by rfl) ⟨1762799, by rfl⟩ : syracuseStep 2350399 = 3525599) B3525599
theorem B2088767 : Blo 1649524 2088767 := bstep (se 1 (by rfl) ⟨1566575, by rfl⟩ : syracuseStep 2088767 = 3133151) B3133151
theorem B35700587 : Blo 1649524 35700587 := bstep (se 1 (by rfl) ⟨26775440, by rfl⟩ : syracuseStep 35700587 = 53550881) B53550881
theorem B2785387 : Blo 1649524 2785387 := bstep (se 1 (by rfl) ⟨2089040, by rfl⟩ : syracuseStep 2785387 = 4178081) B4178081
theorem B11903219 : Blo 1649524 11903219 := bstep (se 1 (by rfl) ⟨8927414, by rfl⟩ : syracuseStep 11903219 = 17854829) B17854829
theorem B2474303 : Blo 1649524 2474303 := bstep (se 1 (by rfl) ⟨1855727, by rfl⟩ : syracuseStep 2474303 = 3711455) B3711455
theorem B2785691 : Blo 1649524 2785691 := bstep (se 1 (by rfl) ⟨2089268, by rfl⟩ : syracuseStep 2785691 = 4178537) B4178537
theorem B2474399 : Blo 1649524 2474399 := bstep (se 1 (by rfl) ⟨1855799, by rfl⟩ : syracuseStep 2474399 = 3711599) B3711599
theorem B10035751 : Blo 1649524 10035751 := bstep (se 1 (by rfl) ⟨7526813, by rfl⟩ : syracuseStep 10035751 = 15053627) B15053627
theorem B2474663 : Blo 1649524 2474663 := bstep (se 1 (by rfl) ⟨1855997, by rfl⟩ : syracuseStep 2474663 = 3711995) B3711995
theorem B2474735 : Blo 1649524 2474735 := bstep (se 1 (by rfl) ⟨1856051, by rfl⟩ : syracuseStep 2474735 = 3712103) B3712103
theorem B2474879 : Blo 1649524 2474879 := bstep (se 1 (by rfl) ⟨1856159, by rfl⟩ : syracuseStep 2474879 = 3712319) B3712319
theorem B18326519 : Blo 1649524 18326519 := bstep (se 1 (by rfl) ⟨13744889, by rfl⟩ : syracuseStep 18326519 = 27489779) B27489779
theorem B5571611 : Blo 1649524 5571611 := bstep (se 1 (by rfl) ⟨4178708, by rfl⟩ : syracuseStep 5571611 = 8357417) B8357417
theorem B2475497 : Blo 1649524 2475497 := bstep (se 2 (by rfl) ⟨928311, by rfl⟩ : syracuseStep 2475497 = 1856623) B1856623
theorem B2475647 : Blo 1649524 2475647 := bstep (se 1 (by rfl) ⟨1856735, by rfl⟩ : syracuseStep 2475647 = 3713471) B3713471
theorem B7046909 : Blo 1649524 7046909 := bstep (se 3 (by rfl) ⟨1321295, by rfl⟩ : syracuseStep 7046909 = 2642591) B2642591
theorem B2476103 : Blo 1649524 2476103 := bstep (se 1 (by rfl) ⟨1857077, by rfl⟩ : syracuseStep 2476103 = 3714155) B3714155
theorem B6269035 : Blo 1649524 6269035 := bstep (se 1 (by rfl) ⟨4701776, by rfl⟩ : syracuseStep 6269035 = 9403553) B9403553
theorem B23800391 : Blo 1649524 23800391 := bstep (se 1 (by rfl) ⟨17850293, by rfl⟩ : syracuseStep 23800391 = 35700587) B35700587
theorem B31713929 : Blo 1649524 31713929 := bstep (se 2 (by rfl) ⟨11892723, by rfl⟩ : syracuseStep 31713929 = 23785447) B23785447
theorem B2476847 : Blo 1649524 2476847 := bstep (se 1 (by rfl) ⟨1857635, by rfl⟩ : syracuseStep 2476847 = 3715271) B3715271
theorem B3713903 : Blo 1649524 3713903 := bstep (se 1 (by rfl) ⟨2785427, by rfl⟩ : syracuseStep 3713903 = 5570855) B5570855
theorem B6269825 : Blo 1649524 6269825 := bstep (se 2 (by rfl) ⟨2351184, by rfl⟩ : syracuseStep 6269825 = 4702369) B4702369
theorem B12528593 : Blo 1649524 12528593 := bstep (se 2 (by rfl) ⟨4698222, by rfl⟩ : syracuseStep 12528593 = 9396445) B9396445
theorem B2477033 : Blo 1649524 2477033 := bstep (se 2 (by rfl) ⟨928887, by rfl⟩ : syracuseStep 2477033 = 1857775) B1857775
theorem B2477087 : Blo 1649524 2477087 := bstep (se 1 (by rfl) ⟨1857815, by rfl⟩ : syracuseStep 2477087 = 3715631) B3715631
theorem B10718351 : Blo 1649524 10718351 := bstep (se 1 (by rfl) ⟨8038763, by rfl⟩ : syracuseStep 10718351 = 16077527) B16077527
theorem B1649819 : Blo 1649524 1649819 := bstep (se 1 (by rfl) ⟨1237364, by rfl⟩ : syracuseStep 1649819 = 2474729) B2474729
theorem B2231551 : Blo 1649524 2231551 := bstep (se 1 (by rfl) ⟨1673663, by rfl⟩ : syracuseStep 2231551 = 3347327) B3347327
theorem B6270281 : Blo 1649524 6270281 := bstep (se 2 (by rfl) ⟨2351355, by rfl⟩ : syracuseStep 6270281 = 4702711) B4702711
theorem B3714479 : Blo 1649524 3714479 := bstep (se 1 (by rfl) ⟨2785859, by rfl⟩ : syracuseStep 3714479 = 5571719) B5571719
theorem B8465903 : Blo 1649524 8465903 := bstep (se 1 (by rfl) ⟨6349427, by rfl⟩ : syracuseStep 8465903 = 12698855) B12698855
theorem B3714587 : Blo 1649524 3714587 := bstep (se 1 (by rfl) ⟨2785940, by rfl⟩ : syracuseStep 3714587 = 5571881) B5571881
theorem B488681221 : Blo 1649524 488681221 := bstep (se 4 (by rfl) ⟨45813864, by rfl⟩ : syracuseStep 488681221 = 91627729) B91627729
theorem B13381519 : Blo 1649524 13381519 := bstep (se 1 (by rfl) ⟨10036139, by rfl⟩ : syracuseStep 13381519 = 20072279) B20072279
theorem B1650855 : Blo 1649524 1650855 := bstep (se 1 (by rfl) ⟨1238141, by rfl⟩ : syracuseStep 1650855 = 2476283) B2476283
theorem B10572079 : Blo 1649524 10572079 := bstep (se 1 (by rfl) ⟨7929059, by rfl⟩ : syracuseStep 10572079 = 15858119) B15858119
theorem B3715487 : Blo 1649524 3715487 := bstep (se 1 (by rfl) ⟨2786615, by rfl⟩ : syracuseStep 3715487 = 5573231) B5573231
theorem B3133865 : Blo 1649524 3133865 := bstep (se 2 (by rfl) ⟨1175199, by rfl⟩ : syracuseStep 3133865 = 2350399) B2350399
theorem B1651167 : Blo 1649524 1651167 := bstep (se 1 (by rfl) ⟨1238375, by rfl⟩ : syracuseStep 1651167 = 2476751) B2476751
theorem B1651291 : Blo 1649524 1651291 := bstep (se 1 (by rfl) ⟨1238468, by rfl⟩ : syracuseStep 1651291 = 2476937) B2476937
theorem B3715775 : Blo 1649524 3715775 := bstep (se 1 (by rfl) ⟨2786831, by rfl⟩ : syracuseStep 3715775 = 5573663) B5573663
theorem B4461275 : Blo 1649524 4461275 := bstep (se 1 (by rfl) ⟨3345956, by rfl⟩ : syracuseStep 4461275 = 6691913) B6691913
theorem B101586149 : Blo 1649524 101586149 := bstep (se 4 (by rfl) ⟨9523701, by rfl⟩ : syracuseStep 101586149 = 19047403) B19047403
theorem B5567723 : Blo 1649524 5567723 := bstep (se 1 (by rfl) ⟨4175792, by rfl⟩ : syracuseStep 5567723 = 8351585) B8351585
theorem B5019131 : Blo 1649524 5019131 := bstep (se 1 (by rfl) ⟨3764348, by rfl⟩ : syracuseStep 5019131 = 7528697) B7528697
theorem B5568047 : Blo 1649524 5568047 := bstep (se 1 (by rfl) ⟨4176035, by rfl⟩ : syracuseStep 5568047 = 8352071) B8352071
theorem B22894393 : Blo 1649524 22894393 := bstep (se 2 (by rfl) ⟨8585397, by rfl⟩ : syracuseStep 22894393 = 17170795) B17170795
theorem B30119809 : Blo 1649524 30119809 := bstep (se 2 (by rfl) ⟨11294928, by rfl⟩ : syracuseStep 30119809 = 22589857) B22589857
theorem B5289961 : Blo 1649524 5289961 := bstep (se 2 (by rfl) ⟨1983735, by rfl⟩ : syracuseStep 5289961 = 3967471) B3967471
theorem B23803901 : Blo 1649524 23803901 := bstep (se 3 (by rfl) ⟨4463231, by rfl⟩ : syracuseStep 23803901 = 8926463) B8926463
theorem B30521567 : Blo 1649524 30521567 := bstep (se 1 (by rfl) ⟨22891175, by rfl⟩ : syracuseStep 30521567 = 45782351) B45782351
theorem B2783659 : Blo 1649524 2783659 := bstep (se 1 (by rfl) ⟨2087744, by rfl⟩ : syracuseStep 2783659 = 4175489) B4175489
theorem B8919503 : Blo 1649524 8919503 := bstep (se 1 (by rfl) ⟨6689627, by rfl⟩ : syracuseStep 8919503 = 13379255) B13379255
theorem B2784287 : Blo 1649524 2784287 := bstep (se 1 (by rfl) ⟨2088215, by rfl⟩ : syracuseStep 2784287 = 4176431) B4176431
theorem B2088175 : Blo 1649524 2088175 := bstep (se 1 (by rfl) ⟨1566131, by rfl⟩ : syracuseStep 2088175 = 3132263) B3132263
theorem B10722617 : Blo 1649524 10722617 := bstep (se 2 (by rfl) ⟨4020981, by rfl⟩ : syracuseStep 10722617 = 8041963) B8041963
theorem B5570045 : Blo 1649524 5570045 := bstep (se 3 (by rfl) ⟨1044383, by rfl⟩ : syracuseStep 5570045 = 2088767) B2088767
theorem B6266423 : Blo 1649524 6266423 := bstep (se 1 (by rfl) ⟨4699817, by rfl⟩ : syracuseStep 6266423 = 9399635) B9399635
theorem B80314021 : Blo 1649524 80314021 := bstep (se 4 (by rfl) ⟨7529439, by rfl⟩ : syracuseStep 80314021 = 15058879) B15058879
theorem B15867575 : Blo 1649524 15867575 := bstep (se 1 (by rfl) ⟨11900681, by rfl⟩ : syracuseStep 15867575 = 23801363) B23801363
theorem B2089243 : Blo 1649524 2089243 := bstep (se 1 (by rfl) ⟨1566932, by rfl⟩ : syracuseStep 2089243 = 3133865) B3133865
theorem B3711545 : Blo 1649524 3711545 := bstep (se 2 (by rfl) ⟨1391829, by rfl⟩ : syracuseStep 3711545 = 2783659) B2783659
theorem B67724099 : Blo 1649524 67724099 := bstep (se 1 (by rfl) ⟨50793074, by rfl⟩ : syracuseStep 67724099 = 101586149) B101586149
theorem B3711815 : Blo 1649524 3711815 := bstep (se 1 (by rfl) ⟨2783861, by rfl⟩ : syracuseStep 3711815 = 5567723) B5567723
theorem B3712031 : Blo 1649524 3712031 := bstep (se 1 (by rfl) ⟨2784023, by rfl⟩ : syracuseStep 3712031 = 5568047) B5568047
theorem B15869267 : Blo 1649524 15869267 := bstep (se 1 (by rfl) ⟨11901950, by rfl⟩ : syracuseStep 15869267 = 23803901) B23803901
theorem B2975401 : Blo 1649524 2975401 := bstep (se 2 (by rfl) ⟨1115775, by rfl⟩ : syracuseStep 2975401 = 2231551) B2231551
theorem B11896733 : Blo 1649524 11896733 := bstep (se 3 (by rfl) ⟨2230637, by rfl⟩ : syracuseStep 11896733 = 4461275) B4461275
theorem B2475935 : Blo 1649524 2475935 := bstep (se 1 (by rfl) ⟨1856951, by rfl⟩ : syracuseStep 2475935 = 3713903) B3713903
theorem B4179883 : Blo 1649524 4179883 := bstep (se 1 (by rfl) ⟨3134912, by rfl⟩ : syracuseStep 4179883 = 6269825) B6269825
theorem B7145567 : Blo 1649524 7145567 := bstep (se 1 (by rfl) ⟨5359175, by rfl⟩ : syracuseStep 7145567 = 10718351) B10718351
theorem B4180187 : Blo 1649524 4180187 := bstep (se 1 (by rfl) ⟨3135140, by rfl⟩ : syracuseStep 4180187 = 6270281) B6270281
theorem B2476319 : Blo 1649524 2476319 := bstep (se 1 (by rfl) ⟨1857239, by rfl⟩ : syracuseStep 2476319 = 3714479) B3714479
theorem B3713363 : Blo 1649524 3713363 := bstep (se 1 (by rfl) ⟨2785022, by rfl⟩ : syracuseStep 3713363 = 5570045) B5570045
theorem B2476391 : Blo 1649524 2476391 := bstep (se 1 (by rfl) ⟨1857293, by rfl⟩ : syracuseStep 2476391 = 3714587) B3714587
theorem B30525857 : Blo 1649524 30525857 := bstep (se 2 (by rfl) ⟨11447196, by rfl⟩ : syracuseStep 30525857 = 22894393) B22894393
theorem B10578383 : Blo 1649524 10578383 := bstep (se 1 (by rfl) ⟨7933787, by rfl⟩ : syracuseStep 10578383 = 15867575) B15867575
theorem B40159745 : Blo 1649524 40159745 := bstep (se 2 (by rfl) ⟨15059904, by rfl⟩ : syracuseStep 40159745 = 30119809) B30119809
theorem B3713849 : Blo 1649524 3713849 := bstep (se 2 (by rfl) ⟨1392693, by rfl⟩ : syracuseStep 3713849 = 2785387) B2785387
theorem B8358713 : Blo 1649524 8358713 := bstep (se 2 (by rfl) ⟨3134517, by rfl⟩ : syracuseStep 8358713 = 6269035) B6269035
theorem B1649535 : Blo 1649524 1649535 := bstep (se 1 (by rfl) ⟨1237151, by rfl⟩ : syracuseStep 1649535 = 2474303) B2474303
theorem B1649599 : Blo 1649524 1649599 := bstep (se 1 (by rfl) ⟨1237199, by rfl⟩ : syracuseStep 1649599 = 2474399) B2474399
theorem B2476991 : Blo 1649524 2476991 := bstep (se 1 (by rfl) ⟨1857743, by rfl⟩ : syracuseStep 2476991 = 3715487) B3715487
theorem B1649775 : Blo 1649524 1649775 := bstep (se 1 (by rfl) ⟨1237331, by rfl⟩ : syracuseStep 1649775 = 2474663) B2474663
theorem B2477183 : Blo 1649524 2477183 := bstep (se 1 (by rfl) ⟨1857887, by rfl⟩ : syracuseStep 2477183 = 3715775) B3715775
theorem B1649823 : Blo 1649524 1649823 := bstep (se 1 (by rfl) ⟨1237367, by rfl⟩ : syracuseStep 1649823 = 2474735) B2474735
theorem B81390845 : Blo 1649524 81390845 := bstep (se 3 (by rfl) ⟨15260783, by rfl⟩ : syracuseStep 81390845 = 30521567) B30521567
theorem B1649919 : Blo 1649524 1649919 := bstep (se 1 (by rfl) ⟨1237439, by rfl⟩ : syracuseStep 1649919 = 2474879) B2474879
theorem B12217679 : Blo 1649524 12217679 := bstep (se 1 (by rfl) ⟨9163259, by rfl⟩ : syracuseStep 12217679 = 18326519) B18326519
theorem B3714407 : Blo 1649524 3714407 := bstep (se 1 (by rfl) ⟨2785805, by rfl⟩ : syracuseStep 3714407 = 5571611) B5571611
theorem B13381001 : Blo 1649524 13381001 := bstep (se 2 (by rfl) ⟨5017875, by rfl⟩ : syracuseStep 13381001 = 10035751) B10035751
theorem B1650331 : Blo 1649524 1650331 := bstep (se 1 (by rfl) ⟨1237748, by rfl⟩ : syracuseStep 1650331 = 2475497) B2475497
theorem B1650431 : Blo 1649524 1650431 := bstep (se 1 (by rfl) ⟨1237823, by rfl⟩ : syracuseStep 1650431 = 2475647) B2475647
theorem B4697939 : Blo 1649524 4697939 := bstep (se 1 (by rfl) ⟨3523454, by rfl⟩ : syracuseStep 4697939 = 7046909) B7046909
theorem B1650735 : Blo 1649524 1650735 := bstep (se 1 (by rfl) ⟨1238051, by rfl⟩ : syracuseStep 1650735 = 2476103) B2476103
theorem B1651231 : Blo 1649524 1651231 := bstep (se 1 (by rfl) ⟨1238423, by rfl⟩ : syracuseStep 1651231 = 2476847) B2476847
theorem B8352395 : Blo 1649524 8352395 := bstep (se 1 (by rfl) ⟨6264296, by rfl⟩ : syracuseStep 8352395 = 12528593) B12528593
theorem B1651355 : Blo 1649524 1651355 := bstep (se 1 (by rfl) ⟨1238516, by rfl⟩ : syracuseStep 1651355 = 2477033) B2477033
theorem B1856191 : Blo 1649524 1856191 := bstep (se 1 (by rfl) ⟨1392143, by rfl⟩ : syracuseStep 1856191 = 2784287) B2784287
theorem B1651391 : Blo 1649524 1651391 := bstep (se 1 (by rfl) ⟨1238543, by rfl⟩ : syracuseStep 1651391 = 2477087) B2477087
theorem B7148411 : Blo 1649524 7148411 := bstep (se 1 (by rfl) ⟨5361308, by rfl⟩ : syracuseStep 7148411 = 10722617) B10722617
theorem B7935479 : Blo 1649524 7935479 := bstep (se 1 (by rfl) ⟨5951609, by rfl⟩ : syracuseStep 7935479 = 11903219) B11903219
theorem B1857127 : Blo 1649524 1857127 := bstep (se 1 (by rfl) ⟨1392845, by rfl⟩ : syracuseStep 1857127 = 2785691) B2785691
theorem B14096105 : Blo 1649524 14096105 := bstep (se 2 (by rfl) ⟨5286039, by rfl⟩ : syracuseStep 14096105 = 10572079) B10572079
theorem B13384349 : Blo 1649524 13384349 := bstep (se 3 (by rfl) ⟨2509565, by rfl⟩ : syracuseStep 13384349 = 5019131) B5019131
theorem B5946335 : Blo 1649524 5946335 := bstep (se 1 (by rfl) ⟨4459751, by rfl⟩ : syracuseStep 5946335 = 8919503) B8919503
theorem B2784233 : Blo 1649524 2784233 := bstep (se 2 (by rfl) ⟨1044087, by rfl⟩ : syracuseStep 2784233 = 2088175) B2088175
theorem B15866927 : Blo 1649524 15866927 := bstep (se 1 (by rfl) ⟨11900195, by rfl⟩ : syracuseStep 15866927 = 23800391) B23800391
theorem B21142619 : Blo 1649524 21142619 := bstep (se 1 (by rfl) ⟨15856964, by rfl⟩ : syracuseStep 21142619 = 31713929) B31713929
theorem B107085361 : Blo 1649524 107085361 := bstep (se 2 (by rfl) ⟨40157010, by rfl⟩ : syracuseStep 107085361 = 80314021) B80314021
theorem B5643935 : Blo 1649524 5643935 := bstep (se 1 (by rfl) ⟨4232951, by rfl⟩ : syracuseStep 5643935 = 8465903) B8465903
theorem B651574961 : Blo 1649524 651574961 := bstep (se 2 (by rfl) ⟨244340610, by rfl⟩ : syracuseStep 651574961 = 488681221) B488681221
theorem B4177615 : Blo 1649524 4177615 := bstep (se 1 (by rfl) ⟨3133211, by rfl⟩ : syracuseStep 4177615 = 6266423) B6266423
theorem B17842025 : Blo 1649524 17842025 := bstep (se 2 (by rfl) ⟨6690759, by rfl⟩ : syracuseStep 17842025 = 13381519) B13381519
theorem B7053281 : Blo 1649524 7053281 := bstep (se 2 (by rfl) ⟨2644980, by rfl⟩ : syracuseStep 7053281 = 5289961) B5289961
theorem B2785657 : Blo 1649524 2785657 := bstep (se 2 (by rfl) ⟨1044621, by rfl⟩ : syracuseStep 2785657 = 2089243) B2089243
theorem B2474363 : Blo 1649524 2474363 := bstep (se 1 (by rfl) ⟨1855772, by rfl⟩ : syracuseStep 2474363 = 3711545) B3711545
theorem B2474543 : Blo 1649524 2474543 := bstep (se 1 (by rfl) ⟨1855907, by rfl⟩ : syracuseStep 2474543 = 3711815) B3711815
theorem B2474687 : Blo 1649524 2474687 := bstep (se 1 (by rfl) ⟨1856015, by rfl⟩ : syracuseStep 2474687 = 3712031) B3712031
theorem B2474921 : Blo 1649524 2474921 := bstep (se 2 (by rfl) ⟨928095, by rfl⟩ : syracuseStep 2474921 = 1856191) B1856191
theorem B9397403 : Blo 1649524 9397403 := bstep (se 1 (by rfl) ⟨7048052, by rfl⟩ : syracuseStep 9397403 = 14096105) B14096105
theorem B2786791 : Blo 1649524 2786791 := bstep (se 1 (by rfl) ⟨2090093, by rfl⟩ : syracuseStep 2786791 = 4180187) B4180187
theorem B2475575 : Blo 1649524 2475575 := bstep (se 1 (by rfl) ⟨1856681, by rfl⟩ : syracuseStep 2475575 = 3713363) B3713363
theorem B26773163 : Blo 1649524 26773163 := bstep (se 1 (by rfl) ⟨20079872, by rfl⟩ : syracuseStep 26773163 = 40159745) B40159745
theorem B325609141 : Blo 1649524 325609141 := bstep (se 5 (by rfl) ⟨15262928, by rfl⟩ : syracuseStep 325609141 = 30525857) B30525857
theorem B8922899 : Blo 1649524 8922899 := bstep (se 1 (by rfl) ⟨6692174, by rfl⟩ : syracuseStep 8922899 = 13384349) B13384349
theorem B2475899 : Blo 1649524 2475899 := bstep (se 1 (by rfl) ⟨1856924, by rfl⟩ : syracuseStep 2475899 = 3713849) B3713849
theorem B5572475 : Blo 1649524 5572475 := bstep (se 1 (by rfl) ⟨4179356, by rfl⟩ : syracuseStep 5572475 = 8358713) B8358713
theorem B10577951 : Blo 1649524 10577951 := bstep (se 1 (by rfl) ⟨7933463, by rfl⟩ : syracuseStep 10577951 = 15866927) B15866927
theorem B142780481 : Blo 1649524 142780481 := bstep (se 2 (by rfl) ⟨53542680, by rfl⟩ : syracuseStep 142780481 = 107085361) B107085361
theorem B2476169 : Blo 1649524 2476169 := bstep (se 2 (by rfl) ⟨928563, by rfl⟩ : syracuseStep 2476169 = 1857127) B1857127
theorem B8145119 : Blo 1649524 8145119 := bstep (se 1 (by rfl) ⟨6108839, by rfl⟩ : syracuseStep 8145119 = 12217679) B12217679
theorem B3967201 : Blo 1649524 3967201 := bstep (se 2 (by rfl) ⟨1487700, by rfl⟩ : syracuseStep 3967201 = 2975401) B2975401
theorem B2476271 : Blo 1649524 2476271 := bstep (se 1 (by rfl) ⟨1857203, by rfl⟩ : syracuseStep 2476271 = 3714407) B3714407
theorem B3762623 : Blo 1649524 3762623 := bstep (se 1 (by rfl) ⟨2821967, by rfl⟩ : syracuseStep 3762623 = 5643935) B5643935
theorem B434383307 : Blo 1649524 434383307 := bstep (se 1 (by rfl) ⟨325787480, by rfl⟩ : syracuseStep 434383307 = 651574961) B651574961
theorem B3131959 : Blo 1649524 3131959 := bstep (se 1 (by rfl) ⟨2348969, by rfl⟩ : syracuseStep 3131959 = 4697939) B4697939
theorem B5573177 : Blo 1649524 5573177 := bstep (se 2 (by rfl) ⟨2089941, by rfl⟩ : syracuseStep 5573177 = 4179883) B4179883
theorem B45149399 : Blo 1649524 45149399 := bstep (se 1 (by rfl) ⟨33862049, by rfl⟩ : syracuseStep 45149399 = 67724099) B67724099
theorem B10579511 : Blo 1649524 10579511 := bstep (se 1 (by rfl) ⟨7934633, by rfl⟩ : syracuseStep 10579511 = 15869267) B15869267
theorem B1650623 : Blo 1649524 1650623 := bstep (se 1 (by rfl) ⟨1237967, by rfl⟩ : syracuseStep 1650623 = 2475935) B2475935
theorem B4763711 : Blo 1649524 4763711 := bstep (se 1 (by rfl) ⟨3572783, by rfl⟩ : syracuseStep 4763711 = 7145567) B7145567
theorem B1650879 : Blo 1649524 1650879 := bstep (se 1 (by rfl) ⟨1238159, by rfl⟩ : syracuseStep 1650879 = 2476319) B2476319
theorem B1650927 : Blo 1649524 1650927 := bstep (se 1 (by rfl) ⟨1238195, by rfl⟩ : syracuseStep 1650927 = 2476391) B2476391
theorem B1651327 : Blo 1649524 1651327 := bstep (se 1 (by rfl) ⟨1238495, by rfl⟩ : syracuseStep 1651327 = 2476991) B2476991
theorem B1856155 : Blo 1649524 1856155 := bstep (se 1 (by rfl) ⟨1392116, by rfl⟩ : syracuseStep 1856155 = 2784233) B2784233
theorem B14095079 : Blo 1649524 14095079 := bstep (se 1 (by rfl) ⟨10571309, by rfl⟩ : syracuseStep 14095079 = 21142619) B21142619
theorem B1651455 : Blo 1649524 1651455 := bstep (se 1 (by rfl) ⟨1238591, by rfl⟩ : syracuseStep 1651455 = 2477183) B2477183
theorem B54260563 : Blo 1649524 54260563 := bstep (se 1 (by rfl) ⟨40695422, by rfl⟩ : syracuseStep 54260563 = 81390845) B81390845
theorem B31724621 : Blo 1649524 31724621 := bstep (se 3 (by rfl) ⟨5948366, by rfl⟩ : syracuseStep 31724621 = 11896733) B11896733
theorem B5568263 : Blo 1649524 5568263 := bstep (se 1 (by rfl) ⟨4176197, by rfl⟩ : syracuseStep 5568263 = 8352395) B8352395
theorem B4765607 : Blo 1649524 4765607 := bstep (se 1 (by rfl) ⟨3574205, by rfl⟩ : syracuseStep 4765607 = 7148411) B7148411
theorem B5290319 : Blo 1649524 5290319 := bstep (se 1 (by rfl) ⟨3967739, by rfl⟩ : syracuseStep 5290319 = 7935479) B7935479
theorem B7052255 : Blo 1649524 7052255 := bstep (se 1 (by rfl) ⟨5289191, by rfl⟩ : syracuseStep 7052255 = 10578383) B10578383
theorem B3964223 : Blo 1649524 3964223 := bstep (se 1 (by rfl) ⟨2973167, by rfl⟩ : syracuseStep 3964223 = 5946335) B5946335
theorem B8920667 : Blo 1649524 8920667 := bstep (se 1 (by rfl) ⟨6690500, by rfl⟩ : syracuseStep 8920667 = 13381001) B13381001
theorem B5570153 : Blo 1649524 5570153 := bstep (se 2 (by rfl) ⟨2088807, by rfl⟩ : syracuseStep 5570153 = 4177615) B4177615
theorem B11894683 : Blo 1649524 11894683 := bstep (se 1 (by rfl) ⟨8921012, by rfl⟩ : syracuseStep 11894683 = 17842025) B17842025
theorem B4702187 : Blo 1649524 4702187 := bstep (se 1 (by rfl) ⟨3526640, by rfl⟩ : syracuseStep 4702187 = 7053281) B7053281
theorem B9396719 : Blo 1649524 9396719 := bstep (se 1 (by rfl) ⟨7047539, by rfl⟩ : syracuseStep 9396719 = 14095079) B14095079
theorem B2474873 : Blo 1649524 2474873 := bstep (se 2 (by rfl) ⟨928077, by rfl⟩ : syracuseStep 2474873 = 1856155) B1856155
theorem B14107517 : Blo 1649524 14107517 := bstep (se 3 (by rfl) ⟨2645159, by rfl⟩ : syracuseStep 14107517 = 5290319) B5290319
theorem B3712175 : Blo 1649524 3712175 := bstep (se 1 (by rfl) ⟨2784131, by rfl⟩ : syracuseStep 3712175 = 5568263) B5568263
theorem B5948599 : Blo 1649524 5948599 := bstep (se 1 (by rfl) ⟨4461449, by rfl⟩ : syracuseStep 5948599 = 8922899) B8922899
theorem B2508415 : Blo 1649524 2508415 := bstep (se 1 (by rfl) ⟨1881311, by rfl⟩ : syracuseStep 2508415 = 3762623) B3762623
theorem B289588871 : Blo 1649524 289588871 := bstep (se 1 (by rfl) ⟨217191653, by rfl⟩ : syracuseStep 289588871 = 434383307) B434383307
theorem B30099599 : Blo 1649524 30099599 := bstep (se 1 (by rfl) ⟨22574699, by rfl⟩ : syracuseStep 30099599 = 45149399) B45149399
theorem B434145521 : Blo 1649524 434145521 := bstep (se 2 (by rfl) ⟨162804570, by rfl⟩ : syracuseStep 434145521 = 325609141) B325609141
theorem B3713435 : Blo 1649524 3713435 := bstep (se 1 (by rfl) ⟨2785076, by rfl⟩ : syracuseStep 3713435 = 5570153) B5570153
theorem B1649575 : Blo 1649524 1649575 := bstep (se 1 (by rfl) ⟨1237181, by rfl⟩ : syracuseStep 1649575 = 2474363) B2474363
theorem B1649695 : Blo 1649524 1649695 := bstep (se 1 (by rfl) ⟨1237271, by rfl⟩ : syracuseStep 1649695 = 2474543) B2474543
theorem B1649791 : Blo 1649524 1649791 := bstep (se 1 (by rfl) ⟨1237343, by rfl⟩ : syracuseStep 1649791 = 2474687) B2474687
theorem B3714209 : Blo 1649524 3714209 := bstep (se 2 (by rfl) ⟨1392828, by rfl⟩ : syracuseStep 3714209 = 2785657) B2785657
theorem B1649947 : Blo 1649524 1649947 := bstep (se 1 (by rfl) ⟨1237460, by rfl⟩ : syracuseStep 1649947 = 2474921) B2474921
theorem B1650383 : Blo 1649524 1650383 := bstep (se 1 (by rfl) ⟨1237787, by rfl⟩ : syracuseStep 1650383 = 2475575) B2475575
theorem B72347417 : Blo 1649524 72347417 := bstep (se 2 (by rfl) ⟨27130281, by rfl⟩ : syracuseStep 72347417 = 54260563) B54260563
theorem B1650599 : Blo 1649524 1650599 := bstep (se 1 (by rfl) ⟨1237949, by rfl⟩ : syracuseStep 1650599 = 2475899) B2475899
theorem B3714983 : Blo 1649524 3714983 := bstep (se 1 (by rfl) ⟨2786237, by rfl⟩ : syracuseStep 3714983 = 5572475) B5572475
theorem B95186987 : Blo 1649524 95186987 := bstep (se 1 (by rfl) ⟨71390240, by rfl⟩ : syracuseStep 95186987 = 142780481) B142780481
theorem B1650779 : Blo 1649524 1650779 := bstep (se 1 (by rfl) ⟨1238084, by rfl⟩ : syracuseStep 1650779 = 2476169) B2476169
theorem B1650847 : Blo 1649524 1650847 := bstep (se 1 (by rfl) ⟨1238135, by rfl⟩ : syracuseStep 1650847 = 2476271) B2476271
theorem B3715451 : Blo 1649524 3715451 := bstep (se 1 (by rfl) ⟨2786588, by rfl⟩ : syracuseStep 3715451 = 5573177) B5573177
theorem B3715721 : Blo 1649524 3715721 := bstep (se 2 (by rfl) ⟨1393395, by rfl⟩ : syracuseStep 3715721 = 2786791) B2786791
theorem B2642815 : Blo 1649524 2642815 := bstep (se 1 (by rfl) ⟨1982111, by rfl⟩ : syracuseStep 2642815 = 3964223) B3964223
theorem B3134791 : Blo 1649524 3134791 := bstep (se 1 (by rfl) ⟨2351093, by rfl⟩ : syracuseStep 3134791 = 4702187) B4702187
theorem B3175807 : Blo 1649524 3175807 := bstep (se 1 (by rfl) ⟨2381855, by rfl⟩ : syracuseStep 3175807 = 4763711) B4763711
theorem B21149747 : Blo 1649524 21149747 := bstep (se 1 (by rfl) ⟨15862310, by rfl⟩ : syracuseStep 21149747 = 31724621) B31724621
theorem B4175945 : Blo 1649524 4175945 := bstep (se 2 (by rfl) ⟨1565979, by rfl⟩ : syracuseStep 4175945 = 3131959) B3131959
theorem B6264935 : Blo 1649524 6264935 := bstep (se 1 (by rfl) ⟨4698701, by rfl⟩ : syracuseStep 6264935 = 9397403) B9397403
theorem B17848775 : Blo 1649524 17848775 := bstep (se 1 (by rfl) ⟨13386581, by rfl⟩ : syracuseStep 17848775 = 26773163) B26773163
theorem B21158405 : Blo 1649524 21158405 := bstep (se 4 (by rfl) ⟨1983600, by rfl⟩ : syracuseStep 21158405 = 3967201) B3967201
theorem B3177071 : Blo 1649524 3177071 := bstep (se 1 (by rfl) ⟨2382803, by rfl⟩ : syracuseStep 3177071 = 4765607) B4765607
theorem B7051967 : Blo 1649524 7051967 := bstep (se 1 (by rfl) ⟨5288975, by rfl⟩ : syracuseStep 7051967 = 10577951) B10577951
theorem B5430079 : Blo 1649524 5430079 := bstep (se 1 (by rfl) ⟨4072559, by rfl⟩ : syracuseStep 5430079 = 8145119) B8145119
theorem B4701503 : Blo 1649524 4701503 := bstep (se 1 (by rfl) ⟨3526127, by rfl⟩ : syracuseStep 4701503 = 7052255) B7052255
theorem B7053007 : Blo 1649524 7053007 := bstep (se 1 (by rfl) ⟨5289755, by rfl⟩ : syracuseStep 7053007 = 10579511) B10579511
theorem B5947111 : Blo 1649524 5947111 := bstep (se 1 (by rfl) ⟨4460333, by rfl⟩ : syracuseStep 5947111 = 8920667) B8920667
theorem B15859577 : Blo 1649524 15859577 := bstep (se 2 (by rfl) ⟨5947341, by rfl⟩ : syracuseStep 15859577 = 11894683) B11894683
theorem B9405011 : Blo 1649524 9405011 := bstep (se 1 (by rfl) ⟨7053758, by rfl⟩ : syracuseStep 9405011 = 14107517) B14107517
theorem B13378213 : Blo 1649524 13378213 := bstep (se 4 (by rfl) ⟨1254207, by rfl⟩ : syracuseStep 13378213 = 2508415) B2508415
theorem B2474783 : Blo 1649524 2474783 := bstep (se 1 (by rfl) ⟨1856087, by rfl⟩ : syracuseStep 2474783 = 3712175) B3712175
theorem B3523753 : Blo 1649524 3523753 := bstep (se 2 (by rfl) ⟨1321407, by rfl⟩ : syracuseStep 3523753 = 2642815) B2642815
theorem B14099831 : Blo 1649524 14099831 := bstep (se 1 (by rfl) ⟨10574873, by rfl⟩ : syracuseStep 14099831 = 21149747) B21149747
theorem B7931465 : Blo 1649524 7931465 := bstep (se 2 (by rfl) ⟨2974299, by rfl⟩ : syracuseStep 7931465 = 5948599) B5948599
theorem B2475623 : Blo 1649524 2475623 := bstep (se 1 (by rfl) ⟨1856717, by rfl⟩ : syracuseStep 2475623 = 3713435) B3713435
theorem B28960421 : Blo 1649524 28960421 := bstep (se 4 (by rfl) ⟨2715039, by rfl⟩ : syracuseStep 28960421 = 5430079) B5430079
theorem B4179721 : Blo 1649524 4179721 := bstep (se 2 (by rfl) ⟨1567395, by rfl⟩ : syracuseStep 4179721 = 3134791) B3134791
theorem B2476139 : Blo 1649524 2476139 := bstep (se 1 (by rfl) ⟨1857104, by rfl⟩ : syracuseStep 2476139 = 3714209) B3714209
theorem B2476655 : Blo 1649524 2476655 := bstep (se 1 (by rfl) ⟨1857491, by rfl⟩ : syracuseStep 2476655 = 3714983) B3714983
theorem B63457991 : Blo 1649524 63457991 := bstep (se 1 (by rfl) ⟨47593493, by rfl⟩ : syracuseStep 63457991 = 95186987) B95186987
theorem B2476967 : Blo 1649524 2476967 := bstep (se 1 (by rfl) ⟨1857725, by rfl⟩ : syracuseStep 2476967 = 3715451) B3715451
theorem B2477147 : Blo 1649524 2477147 := bstep (se 1 (by rfl) ⟨1857860, by rfl⟩ : syracuseStep 2477147 = 3715721) B3715721
theorem B1649915 : Blo 1649524 1649915 := bstep (se 1 (by rfl) ⟨1237436, by rfl⟩ : syracuseStep 1649915 = 2474873) B2474873
theorem B12537341 : Blo 1649524 12537341 := bstep (se 3 (by rfl) ⟨2350751, by rfl⟩ : syracuseStep 12537341 = 4701503) B4701503
theorem B20066399 : Blo 1649524 20066399 := bstep (se 1 (by rfl) ⟨15049799, by rfl⟩ : syracuseStep 20066399 = 30099599) B30099599
theorem B11899183 : Blo 1649524 11899183 := bstep (se 1 (by rfl) ⟨8924387, by rfl⟩ : syracuseStep 11899183 = 17848775) B17848775
theorem B2118047 : Blo 1649524 2118047 := bstep (se 1 (by rfl) ⟨1588535, by rfl⟩ : syracuseStep 2118047 = 3177071) B3177071
theorem B42292205 : Blo 1649524 42292205 := bstep (se 3 (by rfl) ⟨7929788, by rfl⟩ : syracuseStep 42292205 = 15859577) B15859577
theorem B48231611 : Blo 1649524 48231611 := bstep (se 1 (by rfl) ⟨36173708, by rfl⟩ : syracuseStep 48231611 = 72347417) B72347417
theorem B6264479 : Blo 1649524 6264479 := bstep (se 1 (by rfl) ⟨4698359, by rfl⟩ : syracuseStep 6264479 = 9396719) B9396719
theorem B193059247 : Blo 1649524 193059247 := bstep (se 1 (by rfl) ⟨144794435, by rfl⟩ : syracuseStep 193059247 = 289588871) B289588871
theorem B31717925 : Blo 1649524 31717925 := bstep (se 4 (by rfl) ⟨2973555, by rfl⟩ : syracuseStep 31717925 = 5947111) B5947111
theorem B2783963 : Blo 1649524 2783963 := bstep (se 1 (by rfl) ⟨2087972, by rfl⟩ : syracuseStep 2783963 = 4175945) B4175945
theorem B4176623 : Blo 1649524 4176623 := bstep (se 1 (by rfl) ⟨3132467, by rfl⟩ : syracuseStep 4176623 = 6264935) B6264935
theorem B289430347 : Blo 1649524 289430347 := bstep (se 1 (by rfl) ⟨217072760, by rfl⟩ : syracuseStep 289430347 = 434145521) B434145521
theorem B14105603 : Blo 1649524 14105603 := bstep (se 1 (by rfl) ⟨10579202, by rfl⟩ : syracuseStep 14105603 = 21158405) B21158405
theorem B4701311 : Blo 1649524 4701311 := bstep (se 1 (by rfl) ⟨3525983, by rfl⟩ : syracuseStep 4701311 = 7051967) B7051967
theorem B4234409 : Blo 1649524 4234409 := bstep (se 2 (by rfl) ⟨1587903, by rfl⟩ : syracuseStep 4234409 = 3175807) B3175807
theorem B9404009 : Blo 1649524 9404009 := bstep (se 2 (by rfl) ⟨3526503, by rfl⟩ : syracuseStep 9404009 = 7053007) B7053007
theorem B13377599 : Blo 1649524 13377599 := bstep (se 1 (by rfl) ⟨10033199, by rfl⟩ : syracuseStep 13377599 = 20066399) B20066399
theorem B32154407 : Blo 1649524 32154407 := bstep (se 1 (by rfl) ⟨24115805, by rfl⟩ : syracuseStep 32154407 = 48231611) B48231611
theorem B21145283 : Blo 1649524 21145283 := bstep (se 1 (by rfl) ⟨15858962, by rfl⟩ : syracuseStep 21145283 = 31717925) B31717925
theorem B77227789 : Blo 1649524 77227789 := bstep (se 3 (by rfl) ⟨14480210, by rfl⟩ : syracuseStep 77227789 = 28960421) B28960421
theorem B42305327 : Blo 1649524 42305327 := bstep (se 1 (by rfl) ⟨31728995, by rfl⟩ : syracuseStep 42305327 = 63457991) B63457991
theorem B8358227 : Blo 1649524 8358227 := bstep (se 1 (by rfl) ⟨6268670, by rfl⟩ : syracuseStep 8358227 = 12537341) B12537341
theorem B5572961 : Blo 1649524 5572961 := bstep (se 2 (by rfl) ⟨2089860, by rfl⟩ : syracuseStep 5572961 = 4179721) B4179721
theorem B6269339 : Blo 1649524 6269339 := bstep (se 1 (by rfl) ⟨4702004, by rfl⟩ : syracuseStep 6269339 = 9404009) B9404009
theorem B6270007 : Blo 1649524 6270007 := bstep (se 1 (by rfl) ⟨4702505, by rfl⟩ : syracuseStep 6270007 = 9405011) B9405011
theorem B1649855 : Blo 1649524 1649855 := bstep (se 1 (by rfl) ⟨1237391, by rfl⟩ : syracuseStep 1649855 = 2474783) B2474783
theorem B257412329 : Blo 1649524 257412329 := bstep (se 2 (by rfl) ⟨96529623, by rfl⟩ : syracuseStep 257412329 = 193059247) B193059247
theorem B17837617 : Blo 1649524 17837617 := bstep (se 2 (by rfl) ⟨6689106, by rfl⟩ : syracuseStep 17837617 = 13378213) B13378213
theorem B9399887 : Blo 1649524 9399887 := bstep (se 1 (by rfl) ⟨7049915, by rfl⟩ : syracuseStep 9399887 = 14099831) B14099831
theorem B5287643 : Blo 1649524 5287643 := bstep (se 1 (by rfl) ⟨3965732, by rfl⟩ : syracuseStep 5287643 = 7931465) B7931465
theorem B1650415 : Blo 1649524 1650415 := bstep (se 1 (by rfl) ⟨1237811, by rfl⟩ : syracuseStep 1650415 = 2475623) B2475623
theorem B5648125 : Blo 1649524 5648125 := bstep (se 3 (by rfl) ⟨1059023, by rfl⟩ : syracuseStep 5648125 = 2118047) B2118047
theorem B1650759 : Blo 1649524 1650759 := bstep (se 1 (by rfl) ⟨1238069, by rfl⟩ : syracuseStep 1650759 = 2476139) B2476139
theorem B4698337 : Blo 1649524 4698337 := bstep (se 2 (by rfl) ⟨1761876, by rfl⟩ : syracuseStep 4698337 = 3523753) B3523753
theorem B1651103 : Blo 1649524 1651103 := bstep (se 1 (by rfl) ⟨1238327, by rfl⟩ : syracuseStep 1651103 = 2476655) B2476655
theorem B1855975 : Blo 1649524 1855975 := bstep (se 1 (by rfl) ⟨1391981, by rfl⟩ : syracuseStep 1855975 = 2783963) B2783963
theorem B1651311 : Blo 1649524 1651311 := bstep (se 1 (by rfl) ⟨1238483, by rfl⟩ : syracuseStep 1651311 = 2476967) B2476967
theorem B1651431 : Blo 1649524 1651431 := bstep (se 1 (by rfl) ⟨1238573, by rfl⟩ : syracuseStep 1651431 = 2477147) B2477147
theorem B3134207 : Blo 1649524 3134207 := bstep (se 1 (by rfl) ⟨2350655, by rfl⟩ : syracuseStep 3134207 = 4701311) B4701311
theorem B2822939 : Blo 1649524 2822939 := bstep (se 1 (by rfl) ⟨2117204, by rfl⟩ : syracuseStep 2822939 = 4234409) B4234409
theorem B15865577 : Blo 1649524 15865577 := bstep (se 2 (by rfl) ⟨5949591, by rfl⟩ : syracuseStep 15865577 = 11899183) B11899183
theorem B28194803 : Blo 1649524 28194803 := bstep (se 1 (by rfl) ⟨21146102, by rfl⟩ : syracuseStep 28194803 = 42292205) B42292205
theorem B385907129 : Blo 1649524 385907129 := bstep (se 2 (by rfl) ⟨144715173, by rfl⟩ : syracuseStep 385907129 = 289430347) B289430347
theorem B4176319 : Blo 1649524 4176319 := bstep (se 1 (by rfl) ⟨3132239, by rfl⟩ : syracuseStep 4176319 = 6264479) B6264479
theorem B2784415 : Blo 1649524 2784415 := bstep (se 1 (by rfl) ⟨2088311, by rfl⟩ : syracuseStep 2784415 = 4176623) B4176623
theorem B9403735 : Blo 1649524 9403735 := bstep (se 1 (by rfl) ⟨7052801, by rfl⟩ : syracuseStep 9403735 = 14105603) B14105603
theorem B2089471 : Blo 1649524 2089471 := bstep (se 1 (by rfl) ⟨1567103, by rfl⟩ : syracuseStep 2089471 = 3134207) B3134207
theorem B2474633 : Blo 1649524 2474633 := bstep (se 2 (by rfl) ⟨927987, by rfl⟩ : syracuseStep 2474633 = 1855975) B1855975
theorem B10577051 : Blo 1649524 10577051 := bstep (se 1 (by rfl) ⟨7932788, by rfl⟩ : syracuseStep 10577051 = 15865577) B15865577
theorem B3712553 : Blo 1649524 3712553 := bstep (se 2 (by rfl) ⟨1392207, by rfl⟩ : syracuseStep 3712553 = 2784415) B2784415
theorem B5572151 : Blo 1649524 5572151 := bstep (se 1 (by rfl) ⟨4179113, by rfl⟩ : syracuseStep 5572151 = 8358227) B8358227
theorem B4179559 : Blo 1649524 4179559 := bstep (se 1 (by rfl) ⟨3134669, by rfl⟩ : syracuseStep 4179559 = 6269339) B6269339
theorem B257271419 : Blo 1649524 257271419 := bstep (se 1 (by rfl) ⟨192953564, by rfl⟩ : syracuseStep 257271419 = 385907129) B385907129
theorem B23783489 : Blo 1649524 23783489 := bstep (se 2 (by rfl) ⟨8918808, by rfl⟩ : syracuseStep 23783489 = 17837617) B17837617
theorem B171608219 : Blo 1649524 171608219 := bstep (se 1 (by rfl) ⟨128706164, by rfl⟩ : syracuseStep 171608219 = 257412329) B257412329
theorem B7530833 : Blo 1649524 7530833 := bstep (se 2 (by rfl) ⟨2824062, by rfl⟩ : syracuseStep 7530833 = 5648125) B5648125
theorem B3525095 : Blo 1649524 3525095 := bstep (se 1 (by rfl) ⟨2643821, by rfl⟩ : syracuseStep 3525095 = 5287643) B5287643
theorem B18796535 : Blo 1649524 18796535 := bstep (se 1 (by rfl) ⟨14097401, by rfl⟩ : syracuseStep 18796535 = 28194803) B28194803
theorem B8360009 : Blo 1649524 8360009 := bstep (se 2 (by rfl) ⟨3135003, by rfl⟩ : syracuseStep 8360009 = 6270007) B6270007
theorem B3715307 : Blo 1649524 3715307 := bstep (se 1 (by rfl) ⟨2786480, by rfl⟩ : syracuseStep 3715307 = 5572961) B5572961
theorem B12538313 : Blo 1649524 12538313 := bstep (se 2 (by rfl) ⟨4701867, by rfl⟩ : syracuseStep 12538313 = 9403735) B9403735
theorem B102970385 : Blo 1649524 102970385 := bstep (se 2 (by rfl) ⟨38613894, by rfl⟩ : syracuseStep 102970385 = 77227789) B77227789
theorem B8918399 : Blo 1649524 8918399 := bstep (se 1 (by rfl) ⟨6688799, by rfl⟩ : syracuseStep 8918399 = 13377599) B13377599
theorem B6264449 : Blo 1649524 6264449 := bstep (se 2 (by rfl) ⟨2349168, by rfl⟩ : syracuseStep 6264449 = 4698337) B4698337
theorem B1881959 : Blo 1649524 1881959 := bstep (se 1 (by rfl) ⟨1411469, by rfl⟩ : syracuseStep 1881959 = 2822939) B2822939
theorem B21436271 : Blo 1649524 21436271 := bstep (se 1 (by rfl) ⟨16077203, by rfl⟩ : syracuseStep 21436271 = 32154407) B32154407
theorem B5568425 : Blo 1649524 5568425 := bstep (se 2 (by rfl) ⟨2088159, by rfl⟩ : syracuseStep 5568425 = 4176319) B4176319
theorem B14096855 : Blo 1649524 14096855 := bstep (se 1 (by rfl) ⟨10572641, by rfl⟩ : syracuseStep 14096855 = 21145283) B21145283
theorem B28203551 : Blo 1649524 28203551 := bstep (se 1 (by rfl) ⟨21152663, by rfl⟩ : syracuseStep 28203551 = 42305327) B42305327
theorem B6266591 : Blo 1649524 6266591 := bstep (se 1 (by rfl) ⟨4699943, by rfl⟩ : syracuseStep 6266591 = 9399887) B9399887
theorem B2785961 : Blo 1649524 2785961 := bstep (se 2 (by rfl) ⟨1044735, by rfl⟩ : syracuseStep 2785961 = 2089471) B2089471
theorem B2475035 : Blo 1649524 2475035 := bstep (se 1 (by rfl) ⟨1856276, by rfl⟩ : syracuseStep 2475035 = 3712553) B3712553
theorem B3712283 : Blo 1649524 3712283 := bstep (se 1 (by rfl) ⟨2784212, by rfl⟩ : syracuseStep 3712283 = 5568425) B5568425
theorem B9397903 : Blo 1649524 9397903 := bstep (se 1 (by rfl) ⟨7048427, by rfl⟩ : syracuseStep 9397903 = 14096855) B14096855
theorem B18802367 : Blo 1649524 18802367 := bstep (se 1 (by rfl) ⟨14101775, by rfl⟩ : syracuseStep 18802367 = 28203551) B28203551
theorem B5572745 : Blo 1649524 5572745 := bstep (se 2 (by rfl) ⟨2089779, by rfl⟩ : syracuseStep 5572745 = 4179559) B4179559
theorem B5573339 : Blo 1649524 5573339 := bstep (se 1 (by rfl) ⟨4180004, by rfl⟩ : syracuseStep 5573339 = 8360009) B8360009
theorem B2476871 : Blo 1649524 2476871 := bstep (se 1 (by rfl) ⟨1857653, by rfl⟩ : syracuseStep 2476871 = 3715307) B3715307
theorem B8358875 : Blo 1649524 8358875 := bstep (se 1 (by rfl) ⟨6269156, by rfl⟩ : syracuseStep 8358875 = 12538313) B12538313
theorem B1649755 : Blo 1649524 1649755 := bstep (se 1 (by rfl) ⟨1237316, by rfl⟩ : syracuseStep 1649755 = 2474633) B2474633
theorem B3714767 : Blo 1649524 3714767 := bstep (se 1 (by rfl) ⟨2786075, by rfl⟩ : syracuseStep 3714767 = 5572151) B5572151
theorem B20074229 : Blo 1649524 20074229 := bstep (se 5 (by rfl) ⟨940979, by rfl⟩ : syracuseStep 20074229 = 1881959) B1881959
theorem B14290847 : Blo 1649524 14290847 := bstep (se 1 (by rfl) ⟨10718135, by rfl⟩ : syracuseStep 14290847 = 21436271) B21436271
theorem B15855659 : Blo 1649524 15855659 := bstep (se 1 (by rfl) ⟨11891744, by rfl⟩ : syracuseStep 15855659 = 23783489) B23783489
theorem B114405479 : Blo 1649524 114405479 := bstep (se 1 (by rfl) ⟨85804109, by rfl⟩ : syracuseStep 114405479 = 171608219) B171608219
theorem B12531023 : Blo 1649524 12531023 := bstep (se 1 (by rfl) ⟨9398267, by rfl⟩ : syracuseStep 12531023 = 18796535) B18796535
theorem B68646923 : Blo 1649524 68646923 := bstep (se 1 (by rfl) ⟨51485192, by rfl⟩ : syracuseStep 68646923 = 102970385) B102970385
theorem B7051367 : Blo 1649524 7051367 := bstep (se 1 (by rfl) ⟨5288525, by rfl⟩ : syracuseStep 7051367 = 10577051) B10577051
theorem B5945599 : Blo 1649524 5945599 := bstep (se 1 (by rfl) ⟨4459199, by rfl⟩ : syracuseStep 5945599 = 8918399) B8918399
theorem B171514279 : Blo 1649524 171514279 := bstep (se 1 (by rfl) ⟨128635709, by rfl⟩ : syracuseStep 171514279 = 257271419) B257271419
theorem B4176299 : Blo 1649524 4176299 := bstep (se 1 (by rfl) ⟨3132224, by rfl⟩ : syracuseStep 4176299 = 6264449) B6264449
theorem B5020555 : Blo 1649524 5020555 := bstep (se 1 (by rfl) ⟨3765416, by rfl⟩ : syracuseStep 5020555 = 7530833) B7530833
theorem B2350063 : Blo 1649524 2350063 := bstep (se 1 (by rfl) ⟨1762547, by rfl⟩ : syracuseStep 2350063 = 3525095) B3525095
theorem B4177727 : Blo 1649524 4177727 := bstep (se 1 (by rfl) ⟨3133295, by rfl⟩ : syracuseStep 4177727 = 6266591) B6266591
theorem B2474855 : Blo 1649524 2474855 := bstep (se 1 (by rfl) ⟨1856141, by rfl⟩ : syracuseStep 2474855 = 3712283) B3712283
theorem B12534911 : Blo 1649524 12534911 := bstep (se 1 (by rfl) ⟨9401183, by rfl⟩ : syracuseStep 12534911 = 18802367) B18802367
theorem B6694073 : Blo 1649524 6694073 := bstep (se 2 (by rfl) ⟨2510277, by rfl⟩ : syracuseStep 6694073 = 5020555) B5020555
theorem B5572583 : Blo 1649524 5572583 := bstep (se 1 (by rfl) ⟨4179437, by rfl⟩ : syracuseStep 5572583 = 8358875) B8358875
theorem B2476511 : Blo 1649524 2476511 := bstep (se 1 (by rfl) ⟨1857383, by rfl⟩ : syracuseStep 2476511 = 3714767) B3714767
theorem B10570439 : Blo 1649524 10570439 := bstep (se 1 (by rfl) ⟨7927829, by rfl⟩ : syracuseStep 10570439 = 15855659) B15855659
theorem B76270319 : Blo 1649524 76270319 := bstep (se 1 (by rfl) ⟨57202739, by rfl⟩ : syracuseStep 76270319 = 114405479) B114405479
theorem B1650023 : Blo 1649524 1650023 := bstep (se 1 (by rfl) ⟨1237517, by rfl⟩ : syracuseStep 1650023 = 2475035) B2475035
theorem B3133417 : Blo 1649524 3133417 := bstep (se 2 (by rfl) ⟨1175031, by rfl⟩ : syracuseStep 3133417 = 2350063) B2350063
theorem B45764615 : Blo 1649524 45764615 := bstep (se 1 (by rfl) ⟨34323461, by rfl⟩ : syracuseStep 45764615 = 68646923) B68646923
theorem B3715163 : Blo 1649524 3715163 := bstep (se 1 (by rfl) ⟨2786372, by rfl⟩ : syracuseStep 3715163 = 5572745) B5572745
theorem B3715559 : Blo 1649524 3715559 := bstep (se 1 (by rfl) ⟨2786669, by rfl⟩ : syracuseStep 3715559 = 5573339) B5573339
theorem B1651247 : Blo 1649524 1651247 := bstep (se 1 (by rfl) ⟨1238435, by rfl⟩ : syracuseStep 1651247 = 2476871) B2476871
theorem B12530537 : Blo 1649524 12530537 := bstep (se 2 (by rfl) ⟨4698951, by rfl⟩ : syracuseStep 12530537 = 9397903) B9397903
theorem B13382819 : Blo 1649524 13382819 := bstep (se 1 (by rfl) ⟨10037114, by rfl⟩ : syracuseStep 13382819 = 20074229) B20074229
theorem B7927465 : Blo 1649524 7927465 := bstep (se 2 (by rfl) ⟨2972799, by rfl⟩ : syracuseStep 7927465 = 5945599) B5945599
theorem B1857307 : Blo 1649524 1857307 := bstep (se 1 (by rfl) ⟨1392980, by rfl⟩ : syracuseStep 1857307 = 2785961) B2785961
theorem B8354015 : Blo 1649524 8354015 := bstep (se 1 (by rfl) ⟨6265511, by rfl⟩ : syracuseStep 8354015 = 12531023) B12531023
theorem B4700911 : Blo 1649524 4700911 := bstep (se 1 (by rfl) ⟨3525683, by rfl⟩ : syracuseStep 4700911 = 7051367) B7051367
theorem B2784199 : Blo 1649524 2784199 := bstep (se 1 (by rfl) ⟨2088149, by rfl⟩ : syracuseStep 2784199 = 4176299) B4176299
theorem B914742821 : Blo 1649524 914742821 := bstep (se 4 (by rfl) ⟨85757139, by rfl⟩ : syracuseStep 914742821 = 171514279) B171514279
theorem B2785151 : Blo 1649524 2785151 := bstep (se 1 (by rfl) ⟨2088863, by rfl⟩ : syracuseStep 2785151 = 4177727) B4177727
theorem B9527231 : Blo 1649524 9527231 := bstep (se 1 (by rfl) ⟨7145423, by rfl⟩ : syracuseStep 9527231 = 14290847) B14290847
theorem B8356607 : Blo 1649524 8356607 := bstep (se 1 (by rfl) ⟨6267455, by rfl⟩ : syracuseStep 8356607 = 12534911) B12534911
theorem B8921879 : Blo 1649524 8921879 := bstep (se 1 (by rfl) ⟨6691409, by rfl⟩ : syracuseStep 8921879 = 13382819) B13382819
theorem B6267881 : Blo 1649524 6267881 := bstep (se 2 (by rfl) ⟨2350455, by rfl⟩ : syracuseStep 6267881 = 4700911) B4700911
theorem B3712265 : Blo 1649524 3712265 := bstep (se 2 (by rfl) ⟨1392099, by rfl⟩ : syracuseStep 3712265 = 2784199) B2784199
theorem B7046959 : Blo 1649524 7046959 := bstep (se 1 (by rfl) ⟨5285219, by rfl⟩ : syracuseStep 7046959 = 10570439) B10570439
theorem B10569953 : Blo 1649524 10569953 := bstep (se 2 (by rfl) ⟨3963732, by rfl⟩ : syracuseStep 10569953 = 7927465) B7927465
theorem B2476409 : Blo 1649524 2476409 := bstep (se 2 (by rfl) ⟨928653, by rfl⟩ : syracuseStep 2476409 = 1857307) B1857307
theorem B25405949 : Blo 1649524 25405949 := bstep (se 3 (by rfl) ⟨4763615, by rfl⟩ : syracuseStep 25405949 = 9527231) B9527231
theorem B30509743 : Blo 1649524 30509743 := bstep (se 1 (by rfl) ⟨22882307, by rfl⟩ : syracuseStep 30509743 = 45764615) B45764615
theorem B2476775 : Blo 1649524 2476775 := bstep (se 1 (by rfl) ⟨1857581, by rfl⟩ : syracuseStep 2476775 = 3715163) B3715163
theorem B2477039 : Blo 1649524 2477039 := bstep (se 1 (by rfl) ⟨1857779, by rfl⟩ : syracuseStep 2477039 = 3715559) B3715559
theorem B1649903 : Blo 1649524 1649903 := bstep (se 1 (by rfl) ⟨1237427, by rfl⟩ : syracuseStep 1649903 = 2474855) B2474855
theorem B3715055 : Blo 1649524 3715055 := bstep (se 1 (by rfl) ⟨2786291, by rfl⟩ : syracuseStep 3715055 = 5572583) B5572583
theorem B1651007 : Blo 1649524 1651007 := bstep (se 1 (by rfl) ⟨1238255, by rfl⟩ : syracuseStep 1651007 = 2476511) B2476511
theorem B1856767 : Blo 1649524 1856767 := bstep (se 1 (by rfl) ⟨1392575, by rfl⟩ : syracuseStep 1856767 = 2785151) B2785151
theorem B8353691 : Blo 1649524 8353691 := bstep (se 1 (by rfl) ⟨6265268, by rfl⟩ : syracuseStep 8353691 = 12530537) B12530537
theorem B4462715 : Blo 1649524 4462715 := bstep (se 1 (by rfl) ⟨3347036, by rfl⟩ : syracuseStep 4462715 = 6694073) B6694073
theorem B5569343 : Blo 1649524 5569343 := bstep (se 1 (by rfl) ⟨4177007, by rfl⟩ : syracuseStep 5569343 = 8354015) B8354015
theorem B50846879 : Blo 1649524 50846879 := bstep (se 1 (by rfl) ⟨38135159, by rfl⟩ : syracuseStep 50846879 = 76270319) B76270319
theorem B609828547 : Blo 1649524 609828547 := bstep (se 1 (by rfl) ⟨457371410, by rfl⟩ : syracuseStep 609828547 = 914742821) B914742821
theorem B4177889 : Blo 1649524 4177889 := bstep (se 2 (by rfl) ⟨1566708, by rfl⟩ : syracuseStep 4177889 = 3133417) B3133417
theorem B5571071 : Blo 1649524 5571071 := bstep (se 1 (by rfl) ⟨4178303, by rfl⟩ : syracuseStep 5571071 = 8356607) B8356607
theorem B5947919 : Blo 1649524 5947919 := bstep (se 1 (by rfl) ⟨4460939, by rfl⟩ : syracuseStep 5947919 = 8921879) B8921879
theorem B4178587 : Blo 1649524 4178587 := bstep (se 1 (by rfl) ⟨3133940, by rfl⟩ : syracuseStep 4178587 = 6267881) B6267881
theorem B2474843 : Blo 1649524 2474843 := bstep (se 1 (by rfl) ⟨1856132, by rfl⟩ : syracuseStep 2474843 = 3712265) B3712265
theorem B2975143 : Blo 1649524 2975143 := bstep (se 1 (by rfl) ⟨2231357, by rfl⟩ : syracuseStep 2975143 = 4462715) B4462715
theorem B7046635 : Blo 1649524 7046635 := bstep (se 1 (by rfl) ⟨5284976, by rfl⟩ : syracuseStep 7046635 = 10569953) B10569953
theorem B2475689 : Blo 1649524 2475689 := bstep (se 2 (by rfl) ⟨928383, by rfl⟩ : syracuseStep 2475689 = 1856767) B1856767
theorem B3712895 : Blo 1649524 3712895 := bstep (se 1 (by rfl) ⟨2784671, by rfl⟩ : syracuseStep 3712895 = 5569343) B5569343
theorem B2476703 : Blo 1649524 2476703 := bstep (se 1 (by rfl) ⟨1857527, by rfl⟩ : syracuseStep 2476703 = 3715055) B3715055
theorem B1650939 : Blo 1649524 1650939 := bstep (se 1 (by rfl) ⟨1238204, by rfl⟩ : syracuseStep 1650939 = 2476409) B2476409
theorem B16937299 : Blo 1649524 16937299 := bstep (se 1 (by rfl) ⟨12702974, by rfl⟩ : syracuseStep 16937299 = 25405949) B25405949
theorem B1651183 : Blo 1649524 1651183 := bstep (se 1 (by rfl) ⟨1238387, by rfl⟩ : syracuseStep 1651183 = 2476775) B2476775
theorem B1651359 : Blo 1649524 1651359 := bstep (se 1 (by rfl) ⟨1238519, by rfl⟩ : syracuseStep 1651359 = 2477039) B2477039
theorem B135591677 : Blo 1649524 135591677 := bstep (se 3 (by rfl) ⟨25423439, by rfl⟩ : syracuseStep 135591677 = 50846879) B50846879
theorem B40679657 : Blo 1649524 40679657 := bstep (se 2 (by rfl) ⟨15254871, by rfl⟩ : syracuseStep 40679657 = 30509743) B30509743
theorem B5569127 : Blo 1649524 5569127 := bstep (se 1 (by rfl) ⟨4176845, by rfl⟩ : syracuseStep 5569127 = 8353691) B8353691
theorem B813104729 : Blo 1649524 813104729 := bstep (se 2 (by rfl) ⟨304914273, by rfl⟩ : syracuseStep 813104729 = 609828547) B609828547
theorem B9395945 : Blo 1649524 9395945 := bstep (se 2 (by rfl) ⟨3523479, by rfl⟩ : syracuseStep 9395945 = 7046959) B7046959
theorem B2785259 : Blo 1649524 2785259 := bstep (se 1 (by rfl) ⟨2088944, by rfl⟩ : syracuseStep 2785259 = 4177889) B4177889
theorem B3965279 : Blo 1649524 3965279 := bstep (se 1 (by rfl) ⟨2973959, by rfl⟩ : syracuseStep 3965279 = 5947919) B5947919
theorem B5571449 : Blo 1649524 5571449 := bstep (se 2 (by rfl) ⟨2089293, by rfl⟩ : syracuseStep 5571449 = 4178587) B4178587
theorem B2475263 : Blo 1649524 2475263 := bstep (se 1 (by rfl) ⟨1856447, by rfl⟩ : syracuseStep 2475263 = 3712895) B3712895
theorem B3712751 : Blo 1649524 3712751 := bstep (se 1 (by rfl) ⟨2784563, by rfl⟩ : syracuseStep 3712751 = 5569127) B5569127
theorem B3966857 : Blo 1649524 3966857 := bstep (se 2 (by rfl) ⟨1487571, by rfl⟩ : syracuseStep 3966857 = 2975143) B2975143
theorem B3714047 : Blo 1649524 3714047 := bstep (se 1 (by rfl) ⟨2785535, by rfl⟩ : syracuseStep 3714047 = 5571071) B5571071
theorem B1649895 : Blo 1649524 1649895 := bstep (se 1 (by rfl) ⟨1237421, by rfl⟩ : syracuseStep 1649895 = 2474843) B2474843
theorem B1650459 : Blo 1649524 1650459 := bstep (se 1 (by rfl) ⟨1237844, by rfl⟩ : syracuseStep 1650459 = 2475689) B2475689
theorem B90394451 : Blo 1649524 90394451 := bstep (se 1 (by rfl) ⟨67795838, by rfl⟩ : syracuseStep 90394451 = 135591677) B135591677
theorem B27119771 : Blo 1649524 27119771 := bstep (se 1 (by rfl) ⟨20339828, by rfl⟩ : syracuseStep 27119771 = 40679657) B40679657
theorem B1651135 : Blo 1649524 1651135 := bstep (se 1 (by rfl) ⟨1238351, by rfl⟩ : syracuseStep 1651135 = 2476703) B2476703
theorem B542069819 : Blo 1649524 542069819 := bstep (se 1 (by rfl) ⟨406552364, by rfl⟩ : syracuseStep 542069819 = 813104729) B813104729
theorem B6263963 : Blo 1649524 6263963 := bstep (se 1 (by rfl) ⟨4697972, by rfl⟩ : syracuseStep 6263963 = 9395945) B9395945
theorem B1856839 : Blo 1649524 1856839 := bstep (se 1 (by rfl) ⟨1392629, by rfl⟩ : syracuseStep 1856839 = 2785259) B2785259
theorem B22583065 : Blo 1649524 22583065 := bstep (se 2 (by rfl) ⟨8468649, by rfl⟩ : syracuseStep 22583065 = 16937299) B16937299
theorem B9395513 : Blo 1649524 9395513 := bstep (se 2 (by rfl) ⟨3523317, by rfl⟩ : syracuseStep 9395513 = 7046635) B7046635
theorem B18079847 : Blo 1649524 18079847 := bstep (se 1 (by rfl) ⟨13559885, by rfl⟩ : syracuseStep 18079847 = 27119771) B27119771
theorem B2475167 : Blo 1649524 2475167 := bstep (se 1 (by rfl) ⟨1856375, by rfl⟩ : syracuseStep 2475167 = 3712751) B3712751
theorem B2475785 : Blo 1649524 2475785 := bstep (se 2 (by rfl) ⟨928419, by rfl⟩ : syracuseStep 2475785 = 1856839) B1856839
theorem B2476031 : Blo 1649524 2476031 := bstep (se 1 (by rfl) ⟨1857023, by rfl⟩ : syracuseStep 2476031 = 3714047) B3714047
theorem B60262967 : Blo 1649524 60262967 := bstep (se 1 (by rfl) ⟨45197225, by rfl⟩ : syracuseStep 60262967 = 90394451) B90394451
theorem B3714299 : Blo 1649524 3714299 := bstep (se 1 (by rfl) ⟨2785724, by rfl⟩ : syracuseStep 3714299 = 5571449) B5571449
theorem B1650175 : Blo 1649524 1650175 := bstep (se 1 (by rfl) ⟨1237631, by rfl⟩ : syracuseStep 1650175 = 2475263) B2475263
theorem B6263675 : Blo 1649524 6263675 := bstep (se 1 (by rfl) ⟨4697756, by rfl⟩ : syracuseStep 6263675 = 9395513) B9395513
theorem B30110753 : Blo 1649524 30110753 := bstep (se 2 (by rfl) ⟨11291532, by rfl⟩ : syracuseStep 30110753 = 22583065) B22583065
theorem B361379879 : Blo 1649524 361379879 := bstep (se 1 (by rfl) ⟨271034909, by rfl⟩ : syracuseStep 361379879 = 542069819) B542069819
theorem B4175975 : Blo 1649524 4175975 := bstep (se 1 (by rfl) ⟨3131981, by rfl⟩ : syracuseStep 4175975 = 6263963) B6263963
theorem B10574077 : Blo 1649524 10574077 := bstep (se 3 (by rfl) ⟨1982639, by rfl⟩ : syracuseStep 10574077 = 3965279) B3965279
theorem B2644571 : Blo 1649524 2644571 := bstep (se 1 (by rfl) ⟨1983428, by rfl⟩ : syracuseStep 2644571 = 3966857) B3966857
theorem B14098769 : Blo 1649524 14098769 := bstep (se 2 (by rfl) ⟨5287038, by rfl⟩ : syracuseStep 14098769 = 10574077) B10574077
theorem B240919919 : Blo 1649524 240919919 := bstep (se 1 (by rfl) ⟨180689939, by rfl⟩ : syracuseStep 240919919 = 361379879) B361379879
theorem B40175311 : Blo 1649524 40175311 := bstep (se 1 (by rfl) ⟨30131483, by rfl⟩ : syracuseStep 40175311 = 60262967) B60262967
theorem B1763047 : Blo 1649524 1763047 := bstep (se 1 (by rfl) ⟨1322285, by rfl⟩ : syracuseStep 1763047 = 2644571) B2644571
theorem B2476199 : Blo 1649524 2476199 := bstep (se 1 (by rfl) ⟨1857149, by rfl⟩ : syracuseStep 2476199 = 3714299) B3714299
theorem B12053231 : Blo 1649524 12053231 := bstep (se 1 (by rfl) ⟨9039923, by rfl⟩ : syracuseStep 12053231 = 18079847) B18079847
theorem B20073835 : Blo 1649524 20073835 := bstep (se 1 (by rfl) ⟨15055376, by rfl⟩ : syracuseStep 20073835 = 30110753) B30110753
theorem B1650111 : Blo 1649524 1650111 := bstep (se 1 (by rfl) ⟨1237583, by rfl⟩ : syracuseStep 1650111 = 2475167) B2475167
theorem B1650523 : Blo 1649524 1650523 := bstep (se 1 (by rfl) ⟨1237892, by rfl⟩ : syracuseStep 1650523 = 2475785) B2475785
theorem B1650687 : Blo 1649524 1650687 := bstep (se 1 (by rfl) ⟨1238015, by rfl⟩ : syracuseStep 1650687 = 2476031) B2476031
theorem B4175783 : Blo 1649524 4175783 := bstep (se 1 (by rfl) ⟨3131837, by rfl⟩ : syracuseStep 4175783 = 6263675) B6263675
theorem B2783983 : Blo 1649524 2783983 := bstep (se 1 (by rfl) ⟨2087987, by rfl⟩ : syracuseStep 2783983 = 4175975) B4175975
theorem B160613279 : Blo 1649524 160613279 := bstep (se 1 (by rfl) ⟨120459959, by rfl⟩ : syracuseStep 160613279 = 240919919) B240919919
theorem B3711977 : Blo 1649524 3711977 := bstep (se 2 (by rfl) ⟨1391991, by rfl⟩ : syracuseStep 3711977 = 2783983) B2783983
theorem B9399179 : Blo 1649524 9399179 := bstep (se 1 (by rfl) ⟨7049384, by rfl⟩ : syracuseStep 9399179 = 14098769) B14098769
theorem B1650799 : Blo 1649524 1650799 := bstep (se 1 (by rfl) ⟨1238099, by rfl⟩ : syracuseStep 1650799 = 2476199) B2476199
theorem B2783855 : Blo 1649524 2783855 := bstep (se 1 (by rfl) ⟨2087891, by rfl⟩ : syracuseStep 2783855 = 4175783) B4175783
theorem B8035487 : Blo 1649524 8035487 := bstep (se 1 (by rfl) ⟨6026615, by rfl⟩ : syracuseStep 8035487 = 12053231) B12053231
theorem B107060453 : Blo 1649524 107060453 := bstep (se 4 (by rfl) ⟨10036917, by rfl⟩ : syracuseStep 107060453 = 20073835) B20073835
theorem B53567081 : Blo 1649524 53567081 := bstep (se 2 (by rfl) ⟨20087655, by rfl⟩ : syracuseStep 53567081 = 40175311) B40175311
theorem B2350729 : Blo 1649524 2350729 := bstep (se 2 (by rfl) ⟨881523, by rfl⟩ : syracuseStep 2350729 = 1763047) B1763047
theorem B2474651 : Blo 1649524 2474651 := bstep (se 1 (by rfl) ⟨1855988, by rfl⟩ : syracuseStep 2474651 = 3711977) B3711977
theorem B35711387 : Blo 1649524 35711387 := bstep (se 1 (by rfl) ⟨26783540, by rfl⟩ : syracuseStep 35711387 = 53567081) B53567081
theorem B1855903 : Blo 1649524 1855903 := bstep (se 1 (by rfl) ⟨1391927, by rfl⟩ : syracuseStep 1855903 = 2783855) B2783855
theorem B71373635 : Blo 1649524 71373635 := bstep (se 1 (by rfl) ⟨53530226, by rfl⟩ : syracuseStep 71373635 = 107060453) B107060453
theorem B3134305 : Blo 1649524 3134305 := bstep (se 2 (by rfl) ⟨1175364, by rfl⟩ : syracuseStep 3134305 = 2350729) B2350729
theorem B107075519 : Blo 1649524 107075519 := bstep (se 1 (by rfl) ⟨80306639, by rfl⟩ : syracuseStep 107075519 = 160613279) B160613279
theorem B6266119 : Blo 1649524 6266119 := bstep (se 1 (by rfl) ⟨4699589, by rfl⟩ : syracuseStep 6266119 = 9399179) B9399179
theorem B5356991 : Blo 1649524 5356991 := bstep (se 1 (by rfl) ⟨4017743, by rfl⟩ : syracuseStep 5356991 = 8035487) B8035487
theorem B2474537 : Blo 1649524 2474537 := bstep (se 2 (by rfl) ⟨927951, by rfl⟩ : syracuseStep 2474537 = 1855903) B1855903
theorem B4179073 : Blo 1649524 4179073 := bstep (se 2 (by rfl) ⟨1567152, by rfl⟩ : syracuseStep 4179073 = 3134305) B3134305
theorem B23807591 : Blo 1649524 23807591 := bstep (se 1 (by rfl) ⟨17855693, by rfl⟩ : syracuseStep 23807591 = 35711387) B35711387
theorem B1649767 : Blo 1649524 1649767 := bstep (se 1 (by rfl) ⟨1237325, by rfl⟩ : syracuseStep 1649767 = 2474651) B2474651
theorem B47582423 : Blo 1649524 47582423 := bstep (se 1 (by rfl) ⟨35686817, by rfl⟩ : syracuseStep 47582423 = 71373635) B71373635
theorem B71383679 : Blo 1649524 71383679 := bstep (se 1 (by rfl) ⟨53537759, by rfl⟩ : syracuseStep 71383679 = 107075519) B107075519
theorem B8354825 : Blo 1649524 8354825 := bstep (se 2 (by rfl) ⟨3133059, by rfl⟩ : syracuseStep 8354825 = 6266119) B6266119
theorem B3571327 : Blo 1649524 3571327 := bstep (se 1 (by rfl) ⟨2678495, by rfl⟩ : syracuseStep 3571327 = 5356991) B5356991
theorem B5572097 : Blo 1649524 5572097 := bstep (se 2 (by rfl) ⟨2089536, by rfl⟩ : syracuseStep 5572097 = 4179073) B4179073
theorem B47589119 : Blo 1649524 47589119 := bstep (se 1 (by rfl) ⟨35691839, by rfl⟩ : syracuseStep 47589119 = 71383679) B71383679
theorem B31721615 : Blo 1649524 31721615 := bstep (se 1 (by rfl) ⟨23791211, by rfl⟩ : syracuseStep 31721615 = 47582423) B47582423
theorem B4761769 : Blo 1649524 4761769 := bstep (se 2 (by rfl) ⟨1785663, by rfl⟩ : syracuseStep 4761769 = 3571327) B3571327
theorem B1649691 : Blo 1649524 1649691 := bstep (se 1 (by rfl) ⟨1237268, by rfl⟩ : syracuseStep 1649691 = 2474537) B2474537
theorem B15871727 : Blo 1649524 15871727 := bstep (se 1 (by rfl) ⟨11903795, by rfl⟩ : syracuseStep 15871727 = 23807591) B23807591
theorem B5569883 : Blo 1649524 5569883 := bstep (se 1 (by rfl) ⟨4177412, by rfl⟩ : syracuseStep 5569883 = 8354825) B8354825
theorem B6349025 : Blo 1649524 6349025 := bstep (se 2 (by rfl) ⟨2380884, by rfl⟩ : syracuseStep 6349025 = 4761769) B4761769
theorem B3713255 : Blo 1649524 3713255 := bstep (se 1 (by rfl) ⟨2784941, by rfl⟩ : syracuseStep 3713255 = 5569883) B5569883
theorem B3714731 : Blo 1649524 3714731 := bstep (se 1 (by rfl) ⟨2786048, by rfl⟩ : syracuseStep 3714731 = 5572097) B5572097
theorem B21147743 : Blo 1649524 21147743 := bstep (se 1 (by rfl) ⟨15860807, by rfl⟩ : syracuseStep 21147743 = 31721615) B31721615
theorem B10581151 : Blo 1649524 10581151 := bstep (se 1 (by rfl) ⟨7935863, by rfl⟩ : syracuseStep 10581151 = 15871727) B15871727
theorem B31726079 : Blo 1649524 31726079 := bstep (se 1 (by rfl) ⟨23794559, by rfl⟩ : syracuseStep 31726079 = 47589119) B47589119
theorem B14098495 : Blo 1649524 14098495 := bstep (se 1 (by rfl) ⟨10573871, by rfl⟩ : syracuseStep 14098495 = 21147743) B21147743
theorem B2475503 : Blo 1649524 2475503 := bstep (se 1 (by rfl) ⟨1856627, by rfl⟩ : syracuseStep 2475503 = 3713255) B3713255
theorem B14108201 : Blo 1649524 14108201 := bstep (se 2 (by rfl) ⟨5290575, by rfl⟩ : syracuseStep 14108201 = 10581151) B10581151
theorem B2476487 : Blo 1649524 2476487 := bstep (se 1 (by rfl) ⟨1857365, by rfl⟩ : syracuseStep 2476487 = 3714731) B3714731
theorem B4232683 : Blo 1649524 4232683 := bstep (se 1 (by rfl) ⟨3174512, by rfl⟩ : syracuseStep 4232683 = 6349025) B6349025
theorem B21150719 : Blo 1649524 21150719 := bstep (se 1 (by rfl) ⟨15863039, by rfl⟩ : syracuseStep 21150719 = 31726079) B31726079
theorem B9405467 : Blo 1649524 9405467 := bstep (se 1 (by rfl) ⟨7054100, by rfl⟩ : syracuseStep 9405467 = 14108201) B14108201
theorem B14100479 : Blo 1649524 14100479 := bstep (se 1 (by rfl) ⟨10575359, by rfl⟩ : syracuseStep 14100479 = 21150719) B21150719
theorem B1650335 : Blo 1649524 1650335 := bstep (se 1 (by rfl) ⟨1237751, by rfl⟩ : syracuseStep 1650335 = 2475503) B2475503
theorem B1650991 : Blo 1649524 1650991 := bstep (se 1 (by rfl) ⟨1238243, by rfl⟩ : syracuseStep 1650991 = 2476487) B2476487
theorem B18797993 : Blo 1649524 18797993 := bstep (se 2 (by rfl) ⟨7049247, by rfl⟩ : syracuseStep 18797993 = 14098495) B14098495
theorem B5643577 : Blo 1649524 5643577 := bstep (se 2 (by rfl) ⟨2116341, by rfl⟩ : syracuseStep 5643577 = 4232683) B4232683
theorem B6270311 : Blo 1649524 6270311 := bstep (se 1 (by rfl) ⟨4702733, by rfl⟩ : syracuseStep 6270311 = 9405467) B9405467
theorem B9400319 : Blo 1649524 9400319 := bstep (se 1 (by rfl) ⟨7050239, by rfl⟩ : syracuseStep 9400319 = 14100479) B14100479
theorem B7524769 : Blo 1649524 7524769 := bstep (se 2 (by rfl) ⟨2821788, by rfl⟩ : syracuseStep 7524769 = 5643577) B5643577
theorem B12531995 : Blo 1649524 12531995 := bstep (se 1 (by rfl) ⟨9398996, by rfl⟩ : syracuseStep 12531995 = 18797993) B18797993
theorem B4180207 : Blo 1649524 4180207 := bstep (se 1 (by rfl) ⟨3135155, by rfl⟩ : syracuseStep 4180207 = 6270311) B6270311
theorem B10033025 : Blo 1649524 10033025 := bstep (se 2 (by rfl) ⟨3762384, by rfl⟩ : syracuseStep 10033025 = 7524769) B7524769
theorem B8354663 : Blo 1649524 8354663 := bstep (se 1 (by rfl) ⟨6265997, by rfl⟩ : syracuseStep 8354663 = 12531995) B12531995
theorem B6266879 : Blo 1649524 6266879 := bstep (se 1 (by rfl) ⟨4700159, by rfl⟩ : syracuseStep 6266879 = 9400319) B9400319
theorem B5573609 : Blo 1649524 5573609 := bstep (se 2 (by rfl) ⟨2090103, by rfl⟩ : syracuseStep 5573609 = 4180207) B4180207
theorem B5569775 : Blo 1649524 5569775 := bstep (se 1 (by rfl) ⟨4177331, by rfl⟩ : syracuseStep 5569775 = 8354663) B8354663
theorem B4177919 : Blo 1649524 4177919 := bstep (se 1 (by rfl) ⟨3133439, by rfl⟩ : syracuseStep 4177919 = 6266879) B6266879
theorem B26754733 : Blo 1649524 26754733 := bstep (se 3 (by rfl) ⟨5016512, by rfl⟩ : syracuseStep 26754733 = 10033025) B10033025
theorem B3713183 : Blo 1649524 3713183 := bstep (se 1 (by rfl) ⟨2784887, by rfl⟩ : syracuseStep 3713183 = 5569775) B5569775
theorem B3715739 : Blo 1649524 3715739 := bstep (se 1 (by rfl) ⟨2786804, by rfl⟩ : syracuseStep 3715739 = 5573609) B5573609
theorem B35672977 : Blo 1649524 35672977 := bstep (se 2 (by rfl) ⟨13377366, by rfl⟩ : syracuseStep 35672977 = 26754733) B26754733
theorem B2785279 : Blo 1649524 2785279 := bstep (se 1 (by rfl) ⟨2088959, by rfl⟩ : syracuseStep 2785279 = 4177919) B4177919
theorem B47563969 : Blo 1649524 47563969 := bstep (se 2 (by rfl) ⟨17836488, by rfl⟩ : syracuseStep 47563969 = 35672977) B35672977
theorem B2475455 : Blo 1649524 2475455 := bstep (se 1 (by rfl) ⟨1856591, by rfl⟩ : syracuseStep 2475455 = 3713183) B3713183
theorem B3713705 : Blo 1649524 3713705 := bstep (se 2 (by rfl) ⟨1392639, by rfl⟩ : syracuseStep 3713705 = 2785279) B2785279
theorem B2477159 : Blo 1649524 2477159 := bstep (se 1 (by rfl) ⟨1857869, by rfl⟩ : syracuseStep 2477159 = 3715739) B3715739
theorem B2475803 : Blo 1649524 2475803 := bstep (se 1 (by rfl) ⟨1856852, by rfl⟩ : syracuseStep 2475803 = 3713705) B3713705
theorem B1650303 : Blo 1649524 1650303 := bstep (se 1 (by rfl) ⟨1237727, by rfl⟩ : syracuseStep 1650303 = 2475455) B2475455
theorem B63418625 : Blo 1649524 63418625 := bstep (se 2 (by rfl) ⟨23781984, by rfl⟩ : syracuseStep 63418625 = 47563969) B47563969
theorem B1651439 : Blo 1649524 1651439 := bstep (se 1 (by rfl) ⟨1238579, by rfl⟩ : syracuseStep 1651439 = 2477159) B2477159
theorem B42279083 : Blo 1649524 42279083 := bstep (se 1 (by rfl) ⟨31709312, by rfl⟩ : syracuseStep 42279083 = 63418625) B63418625
theorem B1650535 : Blo 1649524 1650535 := bstep (se 1 (by rfl) ⟨1237901, by rfl⟩ : syracuseStep 1650535 = 2475803) B2475803
theorem B28186055 : Blo 1649524 28186055 := bstep (se 1 (by rfl) ⟨21139541, by rfl⟩ : syracuseStep 28186055 = 42279083) B42279083
theorem B18790703 : Blo 1649524 18790703 := bstep (se 1 (by rfl) ⟨14093027, by rfl⟩ : syracuseStep 18790703 = 28186055) B28186055
theorem B12527135 : Blo 1649524 12527135 := bstep (se 1 (by rfl) ⟨9395351, by rfl⟩ : syracuseStep 12527135 = 18790703) B18790703
theorem B8351423 : Blo 1649524 8351423 := bstep (se 1 (by rfl) ⟨6263567, by rfl⟩ : syracuseStep 8351423 = 12527135) B12527135
theorem B5567615 : Blo 1649524 5567615 := bstep (se 1 (by rfl) ⟨4175711, by rfl⟩ : syracuseStep 5567615 = 8351423) B8351423
theorem B3711743 : Blo 1649524 3711743 := bstep (se 1 (by rfl) ⟨2783807, by rfl⟩ : syracuseStep 3711743 = 5567615) B5567615
theorem B2474495 : Blo 1649524 2474495 := bstep (se 1 (by rfl) ⟨1855871, by rfl⟩ : syracuseStep 2474495 = 3711743) B3711743
theorem B1649663 : Blo 1649524 1649663 := bstep (se 1 (by rfl) ⟨1237247, by rfl⟩ : syracuseStep 1649663 = 2474495) B2474495

theorem C0 (j : ℕ) (h1 : 412381 ≤ j) (h2 : j ≤ 412880) : Blo 1649524 (4 * j + 3) := by
  interval_cases j
  · exact B1649527
  · exact B1649531
  · exact B1649535
  · exact B1649539
  · exact B1649543
  · exact B1649547
  · exact B1649551
  · exact B1649555
  · exact B1649559
  · exact B1649563
  · exact B1649567
  · exact B1649571
  · exact B1649575
  · exact B1649579
  · exact B1649583
  · exact B1649587
  · exact B1649591
  · exact B1649595
  · exact B1649599
  · exact B1649603
  · exact B1649607
  · exact B1649611
  · exact B1649615
  · exact B1649619
  · exact B1649623
  · exact B1649627
  · exact B1649631
  · exact B1649635
  · exact B1649639
  · exact B1649643
  · exact B1649647
  · exact B1649651
  · exact B1649655
  · exact B1649659
  · exact B1649663
  · exact B1649667
  · exact B1649671
  · exact B1649675
  · exact B1649679
  · exact B1649683
  · exact B1649687
  · exact B1649691
  · exact B1649695
  · exact B1649699
  · exact B1649703
  · exact B1649707
  · exact B1649711
  · exact B1649715
  · exact B1649719
  · exact B1649723
  · exact B1649727
  · exact B1649731
  · exact B1649735
  · exact B1649739
  · exact B1649743
  · exact B1649747
  · exact B1649751
  · exact B1649755
  · exact B1649759
  · exact B1649763
  · exact B1649767
  · exact B1649771
  · exact B1649775
  · exact B1649779
  · exact B1649783
  · exact B1649787
  · exact B1649791
  · exact B1649795
  · exact B1649799
  · exact B1649803
  · exact B1649807
  · exact B1649811
  · exact B1649815
  · exact B1649819
  · exact B1649823
  · exact B1649827
  · exact B1649831
  · exact B1649835
  · exact B1649839
  · exact B1649843
  · exact B1649847
  · exact B1649851
  · exact B1649855
  · exact B1649859
  · exact B1649863
  · exact B1649867
  · exact B1649871
  · exact B1649875
  · exact B1649879
  · exact B1649883
  · exact B1649887
  · exact B1649891
  · exact B1649895
  · exact B1649899
  · exact B1649903
  · exact B1649907
  · exact B1649911
  · exact B1649915
  · exact B1649919
  · exact B1649923
  · exact B1649927
  · exact B1649931
  · exact B1649935
  · exact B1649939
  · exact B1649943
  · exact B1649947
  · exact B1649951
  · exact B1649955
  · exact B1649959
  · exact B1649963
  · exact B1649967
  · exact B1649971
  · exact B1649975
  · exact B1649979
  · exact B1649983
  · exact B1649987
  · exact B1649991
  · exact B1649995
  · exact B1649999
  · exact B1650003
  · exact B1650007
  · exact B1650011
  · exact B1650015
  · exact B1650019
  · exact B1650023
  · exact B1650027
  · exact B1650031
  · exact B1650035
  · exact B1650039
  · exact B1650043
  · exact B1650047
  · exact B1650051
  · exact B1650055
  · exact B1650059
  · exact B1650063
  · exact B1650067
  · exact B1650071
  · exact B1650075
  · exact B1650079
  · exact B1650083
  · exact B1650087
  · exact B1650091
  · exact B1650095
  · exact B1650099
  · exact B1650103
  · exact B1650107
  · exact B1650111
  · exact B1650115
  · exact B1650119
  · exact B1650123
  · exact B1650127
  · exact B1650131
  · exact B1650135
  · exact B1650139
  · exact B1650143
  · exact B1650147
  · exact B1650151
  · exact B1650155
  · exact B1650159
  · exact B1650163
  · exact B1650167
  · exact B1650171
  · exact B1650175
  · exact B1650179
  · exact B1650183
  · exact B1650187
  · exact B1650191
  · exact B1650195
  · exact B1650199
  · exact B1650203
  · exact B1650207
  · exact B1650211
  · exact B1650215
  · exact B1650219
  · exact B1650223
  · exact B1650227
  · exact B1650231
  · exact B1650235
  · exact B1650239
  · exact B1650243
  · exact B1650247
  · exact B1650251
  · exact B1650255
  · exact B1650259
  · exact B1650263
  · exact B1650267
  · exact B1650271
  · exact B1650275
  · exact B1650279
  · exact B1650283
  · exact B1650287
  · exact B1650291
  · exact B1650295
  · exact B1650299
  · exact B1650303
  · exact B1650307
  · exact B1650311
  · exact B1650315
  · exact B1650319
  · exact B1650323
  · exact B1650327
  · exact B1650331
  · exact B1650335
  · exact B1650339
  · exact B1650343
  · exact B1650347
  · exact B1650351
  · exact B1650355
  · exact B1650359
  · exact B1650363
  · exact B1650367
  · exact B1650371
  · exact B1650375
  · exact B1650379
  · exact B1650383
  · exact B1650387
  · exact B1650391
  · exact B1650395
  · exact B1650399
  · exact B1650403
  · exact B1650407
  · exact B1650411
  · exact B1650415
  · exact B1650419
  · exact B1650423
  · exact B1650427
  · exact B1650431
  · exact B1650435
  · exact B1650439
  · exact B1650443
  · exact B1650447
  · exact B1650451
  · exact B1650455
  · exact B1650459
  · exact B1650463
  · exact B1650467
  · exact B1650471
  · exact B1650475
  · exact B1650479
  · exact B1650483
  · exact B1650487
  · exact B1650491
  · exact B1650495
  · exact B1650499
  · exact B1650503
  · exact B1650507
  · exact B1650511
  · exact B1650515
  · exact B1650519
  · exact B1650523
  · exact B1650527
  · exact B1650531
  · exact B1650535
  · exact B1650539
  · exact B1650543
  · exact B1650547
  · exact B1650551
  · exact B1650555
  · exact B1650559
  · exact B1650563
  · exact B1650567
  · exact B1650571
  · exact B1650575
  · exact B1650579
  · exact B1650583
  · exact B1650587
  · exact B1650591
  · exact B1650595
  · exact B1650599
  · exact B1650603
  · exact B1650607
  · exact B1650611
  · exact B1650615
  · exact B1650619
  · exact B1650623
  · exact B1650627
  · exact B1650631
  · exact B1650635
  · exact B1650639
  · exact B1650643
  · exact B1650647
  · exact B1650651
  · exact B1650655
  · exact B1650659
  · exact B1650663
  · exact B1650667
  · exact B1650671
  · exact B1650675
  · exact B1650679
  · exact B1650683
  · exact B1650687
  · exact B1650691
  · exact B1650695
  · exact B1650699
  · exact B1650703
  · exact B1650707
  · exact B1650711
  · exact B1650715
  · exact B1650719
  · exact B1650723
  · exact B1650727
  · exact B1650731
  · exact B1650735
  · exact B1650739
  · exact B1650743
  · exact B1650747
  · exact B1650751
  · exact B1650755
  · exact B1650759
  · exact B1650763
  · exact B1650767
  · exact B1650771
  · exact B1650775
  · exact B1650779
  · exact B1650783
  · exact B1650787
  · exact B1650791
  · exact B1650795
  · exact B1650799
  · exact B1650803
  · exact B1650807
  · exact B1650811
  · exact B1650815
  · exact B1650819
  · exact B1650823
  · exact B1650827
  · exact B1650831
  · exact B1650835
  · exact B1650839
  · exact B1650843
  · exact B1650847
  · exact B1650851
  · exact B1650855
  · exact B1650859
  · exact B1650863
  · exact B1650867
  · exact B1650871
  · exact B1650875
  · exact B1650879
  · exact B1650883
  · exact B1650887
  · exact B1650891
  · exact B1650895
  · exact B1650899
  · exact B1650903
  · exact B1650907
  · exact B1650911
  · exact B1650915
  · exact B1650919
  · exact B1650923
  · exact B1650927
  · exact B1650931
  · exact B1650935
  · exact B1650939
  · exact B1650943
  · exact B1650947
  · exact B1650951
  · exact B1650955
  · exact B1650959
  · exact B1650963
  · exact B1650967
  · exact B1650971
  · exact B1650975
  · exact B1650979
  · exact B1650983
  · exact B1650987
  · exact B1650991
  · exact B1650995
  · exact B1650999
  · exact B1651003
  · exact B1651007
  · exact B1651011
  · exact B1651015
  · exact B1651019
  · exact B1651023
  · exact B1651027
  · exact B1651031
  · exact B1651035
  · exact B1651039
  · exact B1651043
  · exact B1651047
  · exact B1651051
  · exact B1651055
  · exact B1651059
  · exact B1651063
  · exact B1651067
  · exact B1651071
  · exact B1651075
  · exact B1651079
  · exact B1651083
  · exact B1651087
  · exact B1651091
  · exact B1651095
  · exact B1651099
  · exact B1651103
  · exact B1651107
  · exact B1651111
  · exact B1651115
  · exact B1651119
  · exact B1651123
  · exact B1651127
  · exact B1651131
  · exact B1651135
  · exact B1651139
  · exact B1651143
  · exact B1651147
  · exact B1651151
  · exact B1651155
  · exact B1651159
  · exact B1651163
  · exact B1651167
  · exact B1651171
  · exact B1651175
  · exact B1651179
  · exact B1651183
  · exact B1651187
  · exact B1651191
  · exact B1651195
  · exact B1651199
  · exact B1651203
  · exact B1651207
  · exact B1651211
  · exact B1651215
  · exact B1651219
  · exact B1651223
  · exact B1651227
  · exact B1651231
  · exact B1651235
  · exact B1651239
  · exact B1651243
  · exact B1651247
  · exact B1651251
  · exact B1651255
  · exact B1651259
  · exact B1651263
  · exact B1651267
  · exact B1651271
  · exact B1651275
  · exact B1651279
  · exact B1651283
  · exact B1651287
  · exact B1651291
  · exact B1651295
  · exact B1651299
  · exact B1651303
  · exact B1651307
  · exact B1651311
  · exact B1651315
  · exact B1651319
  · exact B1651323
  · exact B1651327
  · exact B1651331
  · exact B1651335
  · exact B1651339
  · exact B1651343
  · exact B1651347
  · exact B1651351
  · exact B1651355
  · exact B1651359
  · exact B1651363
  · exact B1651367
  · exact B1651371
  · exact B1651375
  · exact B1651379
  · exact B1651383
  · exact B1651387
  · exact B1651391
  · exact B1651395
  · exact B1651399
  · exact B1651403
  · exact B1651407
  · exact B1651411
  · exact B1651415
  · exact B1651419
  · exact B1651423
  · exact B1651427
  · exact B1651431
  · exact B1651435
  · exact B1651439
  · exact B1651443
  · exact B1651447
  · exact B1651451
  · exact B1651455
  · exact B1651459
  · exact B1651463
  · exact B1651467
  · exact B1651471
  · exact B1651475
  · exact B1651479
  · exact B1651483
  · exact B1651487
  · exact B1651491
  · exact B1651495
  · exact B1651499
  · exact B1651503
  · exact B1651507
  · exact B1651511
  · exact B1651515
  · exact B1651519
  · exact B1651523

theorem solution (m : ℕ) (hlo : 1649524 ≤ m) (hhi : m ≤ 1651524) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 412381 ≤ j := by omega
    have hj2 : j ≤ 412880 := by omega
    have hb : Blo 1649524 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
