-- Prove2me | solution 1 for syracuse_descends_range_1100624_1104624
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:22:38.097123+00:00
-- url     : https://prove2.me/submissions/bde71088-978a-426a-8617-a1a06d0e3661

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


theorem B10584533 : Blo 1100624 10584533 := bbase (se 7 (by rfl) ⟨124037, by rfl⟩ : syracuseStep 10584533 = 248075) (by norm_num)
theorem B2982437 : Blo 1100624 2982437 := bbase (se 4 (by rfl) ⟨279603, by rfl⟩ : syracuseStep 2982437 = 559207) (by norm_num)
theorem B10060469 : Blo 1100624 10060469 := bbase (se 5 (by rfl) ⟨471584, by rfl⟩ : syracuseStep 10060469 = 943169) (by norm_num)
theorem B2786197 : Blo 1100624 2786197 := bbase (se 6 (by rfl) ⟨65301, by rfl⟩ : syracuseStep 2786197 = 130603) (by norm_num)
theorem B2786309 : Blo 1100624 2786309 := bbase (se 4 (by rfl) ⟨261216, by rfl⟩ : syracuseStep 2786309 = 522433) (by norm_num)
theorem B2786501 : Blo 1100624 2786501 := bbase (se 4 (by rfl) ⟨261234, by rfl⟩ : syracuseStep 2786501 = 522469) (by norm_num)
theorem B5571989 : Blo 1100624 5571989 := bbase (se 6 (by rfl) ⟨130593, by rfl⟩ : syracuseStep 5571989 = 261187) (by norm_num)
theorem B2786845 : Blo 1100624 2786845 := bbase (se 3 (by rfl) ⟨522533, by rfl⟩ : syracuseStep 2786845 = 1045067) (by norm_num)
theorem B1508933 : Blo 1100624 1508933 := bbase (se 4 (by rfl) ⟨141462, by rfl⟩ : syracuseStep 1508933 = 282925) (by norm_num)
theorem B40175189 : Blo 1100624 40175189 := bbase (se 8 (by rfl) ⟨235401, by rfl⟩ : syracuseStep 40175189 = 470803) (by norm_num)
theorem B3180149 : Blo 1100624 3180149 := bbase (se 5 (by rfl) ⟨149069, by rfl⟩ : syracuseStep 3180149 = 298139) (by norm_num)
theorem B2786957 : Blo 1100624 2786957 := bbase (se 3 (by rfl) ⟨522554, by rfl⟩ : syracuseStep 2786957 = 1045109) (by norm_num)
theorem B2787149 : Blo 1100624 2787149 := bbase (se 3 (by rfl) ⟨522590, by rfl⟩ : syracuseStep 2787149 = 1045181) (by norm_num)
theorem B2295749 : Blo 1100624 2295749 := bbase (se 4 (by rfl) ⟨215226, by rfl⟩ : syracuseStep 2295749 = 430453) (by norm_num)
theorem B14125013 : Blo 1100624 14125013 := bbase (se 7 (by rfl) ⟨165527, by rfl⟩ : syracuseStep 14125013 = 331055) (by norm_num)
theorem B2787493 : Blo 1100624 2787493 := bbase (se 4 (by rfl) ⟨261327, by rfl⟩ : syracuseStep 2787493 = 522655) (by norm_num)
theorem B2787605 : Blo 1100624 2787605 := bbase (se 6 (by rfl) ⟨65334, by rfl⟩ : syracuseStep 2787605 = 130669) (by norm_num)
theorem B1116509 : Blo 1100624 1116509 := bbase (se 3 (by rfl) ⟨209345, by rfl⟩ : syracuseStep 1116509 = 418691) (by norm_num)
theorem B1673597 : Blo 1100624 1673597 := bbase (se 3 (by rfl) ⟨313799, by rfl⟩ : syracuseStep 1673597 = 627599) (by norm_num)
theorem B2787797 : Blo 1100624 2787797 := bbase (se 7 (by rfl) ⟨32669, by rfl⟩ : syracuseStep 2787797 = 65339) (by norm_num)
theorem B5573285 : Blo 1100624 5573285 := bbase (se 4 (by rfl) ⟨522495, by rfl⟩ : syracuseStep 5573285 = 1044991) (by norm_num)
theorem B15895253 : Blo 1100624 15895253 := bbase (se 7 (by rfl) ⟨186272, by rfl⟩ : syracuseStep 15895253 = 372545) (by norm_num)
theorem B2788141 : Blo 1100624 2788141 := bbase (se 3 (by rfl) ⟨522776, by rfl⟩ : syracuseStep 2788141 = 1045553) (by norm_num)
theorem B13405013 : Blo 1100624 13405013 := bbase (se 9 (by rfl) ⟨39272, by rfl⟩ : syracuseStep 13405013 = 78545) (by norm_num)
theorem B1149841 : Blo 1100624 1149841 := bbase (se 2 (by rfl) ⟨431190, by rfl⟩ : syracuseStep 1149841 = 862381) (by norm_num)
theorem B2788253 : Blo 1100624 2788253 := bbase (se 3 (by rfl) ⟨522797, by rfl⟩ : syracuseStep 2788253 = 1045595) (by norm_num)
theorem B3574757 : Blo 1100624 3574757 := bbase (se 4 (by rfl) ⟨335133, by rfl⟩ : syracuseStep 3574757 = 670267) (by norm_num)
theorem B3771461 : Blo 1100624 3771461 := bbase (se 4 (by rfl) ⟨353574, by rfl⟩ : syracuseStep 3771461 = 707149) (by norm_num)
theorem B2788445 : Blo 1100624 2788445 := bbase (se 3 (by rfl) ⟨522833, by rfl⟩ : syracuseStep 2788445 = 1045667) (by norm_num)
theorem B1412245 : Blo 1100624 1412245 := bbase (se 6 (by rfl) ⟨33099, by rfl⟩ : syracuseStep 1412245 = 66199) (by norm_num)
theorem B1117405 : Blo 1100624 1117405 := bbase (se 3 (by rfl) ⟨209513, by rfl⟩ : syracuseStep 1117405 = 419027) (by norm_num)
theorem B2788789 : Blo 1100624 2788789 := bbase (se 5 (by rfl) ⟨130724, by rfl⟩ : syracuseStep 2788789 = 261449) (by norm_num)
theorem B3968453 : Blo 1100624 3968453 := bbase (se 4 (by rfl) ⟨372042, by rfl⟩ : syracuseStep 3968453 = 744085) (by norm_num)
theorem B2788901 : Blo 1100624 2788901 := bbase (se 4 (by rfl) ⟨261459, by rfl⟩ : syracuseStep 2788901 = 522919) (by norm_num)
theorem B1117741 : Blo 1100624 1117741 := bbase (se 3 (by rfl) ⟨209576, by rfl⟩ : syracuseStep 1117741 = 419153) (by norm_num)
theorem B1379885 : Blo 1100624 1379885 := bbase (se 3 (by rfl) ⟨258728, by rfl⟩ : syracuseStep 1379885 = 517457) (by norm_num)
theorem B1117765 : Blo 1100624 1117765 := bbase (se 4 (by rfl) ⟨104790, by rfl⟩ : syracuseStep 1117765 = 209581) (by norm_num)
theorem B2789093 : Blo 1100624 2789093 := bbase (se 4 (by rfl) ⟨261477, by rfl⟩ : syracuseStep 2789093 = 522955) (by norm_num)
theorem B1675037 : Blo 1100624 1675037 := bbase (se 3 (by rfl) ⟨314069, by rfl⟩ : syracuseStep 1675037 = 628139) (by norm_num)
theorem B1118009 : Blo 1100624 1118009 := bbase (se 2 (by rfl) ⟨419253, by rfl⟩ : syracuseStep 1118009 = 838507) (by norm_num)
theorem B15109973 : Blo 1100624 15109973 := bbase (se 9 (by rfl) ⟨44267, by rfl⟩ : syracuseStep 15109973 = 88535) (by norm_num)
theorem B1118057 : Blo 1100624 1118057 := bbase (se 2 (by rfl) ⟨419271, by rfl⟩ : syracuseStep 1118057 = 838543) (by norm_num)
theorem B5574581 : Blo 1100624 5574581 := bbase (se 5 (by rfl) ⟨261308, by rfl⟩ : syracuseStep 5574581 = 522617) (by norm_num)
theorem B2789437 : Blo 1100624 2789437 := bbase (se 3 (by rfl) ⟨523019, by rfl⟩ : syracuseStep 2789437 = 1046039) (by norm_num)
theorem B5967989 : Blo 1100624 5967989 := bbase (se 5 (by rfl) ⟨279749, by rfl⟩ : syracuseStep 5967989 = 559499) (by norm_num)
theorem B2789549 : Blo 1100624 2789549 := bbase (se 3 (by rfl) ⟨523040, by rfl⟩ : syracuseStep 2789549 = 1046081) (by norm_num)
theorem B1937677 : Blo 1100624 1937677 := bbase (se 3 (by rfl) ⟨363314, by rfl⟩ : syracuseStep 1937677 = 726629) (by norm_num)
theorem B3969317 : Blo 1100624 3969317 := bbase (se 4 (by rfl) ⟨372123, by rfl⟩ : syracuseStep 3969317 = 744247) (by norm_num)
theorem B2789741 : Blo 1100624 2789741 := bbase (se 3 (by rfl) ⟨523076, by rfl⟩ : syracuseStep 2789741 = 1046153) (by norm_num)
theorem B12751253 : Blo 1100624 12751253 := bbase (se 6 (by rfl) ⟨298857, by rfl⟩ : syracuseStep 12751253 = 597715) (by norm_num)
theorem B12554837 : Blo 1100624 12554837 := bbase (se 8 (by rfl) ⟨73563, by rfl⟩ : syracuseStep 12554837 = 147127) (by norm_num)
theorem B2790085 : Blo 1100624 2790085 := bbase (se 4 (by rfl) ⟨261570, by rfl⟩ : syracuseStep 2790085 = 523141) (by norm_num)
theorem B2790197 : Blo 1100624 2790197 := bbase (se 5 (by rfl) ⟨130790, by rfl⟩ : syracuseStep 2790197 = 261581) (by norm_num)
theorem B4723525 : Blo 1100624 4723525 := bbase (se 4 (by rfl) ⟨442830, by rfl⟩ : syracuseStep 4723525 = 885661) (by norm_num)
theorem B3969893 : Blo 1100624 3969893 := bbase (se 4 (by rfl) ⟨372177, by rfl⟩ : syracuseStep 3969893 = 744355) (by norm_num)
theorem B3773333 : Blo 1100624 3773333 := bbase (se 6 (by rfl) ⟨88437, by rfl⟩ : syracuseStep 3773333 = 176875) (by norm_num)
theorem B2233261 : Blo 1100624 2233261 := bbase (se 3 (by rfl) ⟨418736, by rfl⟩ : syracuseStep 2233261 = 837473) (by norm_num)
theorem B2790389 : Blo 1100624 2790389 := bbase (se 5 (by rfl) ⟨130799, by rfl⟩ : syracuseStep 2790389 = 261599) (by norm_num)
theorem B1676381 : Blo 1100624 1676381 := bbase (se 3 (by rfl) ⟨314321, by rfl⟩ : syracuseStep 1676381 = 628643) (by norm_num)
theorem B1676429 : Blo 1100624 1676429 := bbase (se 3 (by rfl) ⟨314330, by rfl⟩ : syracuseStep 1676429 = 628661) (by norm_num)
theorem B5575877 : Blo 1100624 5575877 := bbase (se 4 (by rfl) ⟨522738, by rfl⟩ : syracuseStep 5575877 = 1045477) (by norm_num)
theorem B2790733 : Blo 1100624 2790733 := bbase (se 3 (by rfl) ⟨523262, by rfl⟩ : syracuseStep 2790733 = 1046525) (by norm_num)
theorem B2790845 : Blo 1100624 2790845 := bbase (se 3 (by rfl) ⟨523283, by rfl⟩ : syracuseStep 2790845 = 1046567) (by norm_num)
theorem B2791037 : Blo 1100624 2791037 := bbase (se 3 (by rfl) ⟨523319, by rfl⟩ : syracuseStep 2791037 = 1046639) (by norm_num)
theorem B2791381 : Blo 1100624 2791381 := bbase (se 7 (by rfl) ⟨32711, by rfl⟩ : syracuseStep 2791381 = 65423) (by norm_num)
theorem B3774485 : Blo 1100624 3774485 := bbase (se 6 (by rfl) ⟨88464, by rfl⟩ : syracuseStep 3774485 = 176929) (by norm_num)
theorem B2791493 : Blo 1100624 2791493 := bbase (se 4 (by rfl) ⟨261702, by rfl⟩ : syracuseStep 2791493 = 523405) (by norm_num)
theorem B2234557 : Blo 1100624 2234557 := bbase (se 3 (by rfl) ⟨418979, by rfl⟩ : syracuseStep 2234557 = 837959) (by norm_num)
theorem B2791685 : Blo 1100624 2791685 := bbase (se 4 (by rfl) ⟨261720, by rfl⟩ : syracuseStep 2791685 = 523441) (by norm_num)
theorem B5577173 : Blo 1100624 5577173 := bbase (se 7 (by rfl) ⟨65357, by rfl⟩ : syracuseStep 5577173 = 130715) (by norm_num)
theorem B2824685 : Blo 1100624 2824685 := bbase (se 3 (by rfl) ⟨529628, by rfl⟩ : syracuseStep 2824685 = 1059257) (by norm_num)
theorem B5380613 : Blo 1100624 5380613 := bbase (se 4 (by rfl) ⟨504432, by rfl⟩ : syracuseStep 5380613 = 1008865) (by norm_num)
theorem B2792029 : Blo 1100624 2792029 := bbase (se 3 (by rfl) ⟨523505, by rfl⟩ : syracuseStep 2792029 = 1047011) (by norm_num)
theorem B3676837 : Blo 1100624 3676837 := bbase (se 4 (by rfl) ⟨344703, by rfl⟩ : syracuseStep 3676837 = 689407) (by norm_num)
theorem B2792141 : Blo 1100624 2792141 := bbase (se 3 (by rfl) ⟨523526, by rfl⟩ : syracuseStep 2792141 = 1047053) (by norm_num)
theorem B1678205 : Blo 1100624 1678205 := bbase (se 3 (by rfl) ⟨314663, by rfl⟩ : syracuseStep 1678205 = 629327) (by norm_num)
theorem B2792333 : Blo 1100624 2792333 := bbase (se 3 (by rfl) ⟨523562, by rfl⟩ : syracuseStep 2792333 = 1047125) (by norm_num)
theorem B2792677 : Blo 1100624 2792677 := bbase (se 4 (by rfl) ⟨261813, by rfl⟩ : syracuseStep 2792677 = 523627) (by norm_num)
theorem B2268397 : Blo 1100624 2268397 := bbase (se 3 (by rfl) ⟨425324, by rfl⟩ : syracuseStep 2268397 = 850649) (by norm_num)
theorem B2792789 : Blo 1100624 2792789 := bbase (se 11 (by rfl) ⟨2045, by rfl⟩ : syracuseStep 2792789 = 4091) (by norm_num)
theorem B10722709 : Blo 1100624 10722709 := bbase (se 6 (by rfl) ⟨251313, by rfl⟩ : syracuseStep 10722709 = 502627) (by norm_num)
theorem B2792981 : Blo 1100624 2792981 := bbase (se 6 (by rfl) ⟨65460, by rfl⟩ : syracuseStep 2792981 = 130921) (by norm_num)
theorem B8363573 : Blo 1100624 8363573 := bbase (se 5 (by rfl) ⟨392042, by rfl⟩ : syracuseStep 8363573 = 784085) (by norm_num)
theorem B5578469 : Blo 1100624 5578469 := bbase (se 4 (by rfl) ⟨522981, by rfl⟩ : syracuseStep 5578469 = 1045963) (by norm_num)
theorem B2236261 : Blo 1100624 2236261 := bbase (se 4 (by rfl) ⟨209649, by rfl⟩ : syracuseStep 2236261 = 419299) (by norm_num)
theorem B2793325 : Blo 1100624 2793325 := bbase (se 3 (by rfl) ⟨523748, by rfl⟩ : syracuseStep 2793325 = 1047497) (by norm_num)
theorem B16981973 : Blo 1100624 16981973 := bbase (se 7 (by rfl) ⟨199007, by rfl⟩ : syracuseStep 16981973 = 398015) (by norm_num)
theorem B2793437 : Blo 1100624 2793437 := bbase (se 3 (by rfl) ⟨523769, by rfl⟩ : syracuseStep 2793437 = 1047539) (by norm_num)
theorem B2793629 : Blo 1100624 2793629 := bbase (se 3 (by rfl) ⟨523805, by rfl⟩ : syracuseStep 2793629 = 1047611) (by norm_num)
theorem B2826677 : Blo 1100624 2826677 := bbase (se 5 (by rfl) ⟨132500, by rfl⟩ : syracuseStep 2826677 = 265001) (by norm_num)
theorem B2793973 : Blo 1100624 2793973 := bbase (se 5 (by rfl) ⟨130967, by rfl⟩ : syracuseStep 2793973 = 261935) (by norm_num)
theorem B31760981 : Blo 1100624 31760981 := bbase (se 8 (by rfl) ⟨186099, by rfl⟩ : syracuseStep 31760981 = 372199) (by norm_num)
theorem B2794085 : Blo 1100624 2794085 := bbase (se 4 (by rfl) ⟨261945, by rfl⟩ : syracuseStep 2794085 = 523891) (by norm_num)
theorem B2794277 : Blo 1100624 2794277 := bbase (se 4 (by rfl) ⟨261963, by rfl⟩ : syracuseStep 2794277 = 523927) (by norm_num)
theorem B5579765 : Blo 1100624 5579765 := bbase (se 5 (by rfl) ⟨261551, by rfl⟩ : syracuseStep 5579765 = 523103) (by norm_num)
theorem B2794621 : Blo 1100624 2794621 := bbase (se 3 (by rfl) ⟨523991, by rfl⟩ : syracuseStep 2794621 = 1047983) (by norm_num)
theorem B2794733 : Blo 1100624 2794733 := bbase (se 3 (by rfl) ⟨524012, by rfl⟩ : syracuseStep 2794733 = 1048025) (by norm_num)
theorem B9413941 : Blo 1100624 9413941 := bbase (se 5 (by rfl) ⟨441278, by rfl⟩ : syracuseStep 9413941 = 882557) (by norm_num)
theorem B2794925 : Blo 1100624 2794925 := bbase (se 3 (by rfl) ⟨524048, by rfl⟩ : syracuseStep 2794925 = 1048097) (by norm_num)
theorem B6039157 : Blo 1100624 6039157 := bbase (se 5 (by rfl) ⟨283085, by rfl⟩ : syracuseStep 6039157 = 566171) (by norm_num)
theorem B2238077 : Blo 1100624 2238077 := bbase (se 3 (by rfl) ⟨419639, by rfl⟩ : syracuseStep 2238077 = 839279) (by norm_num)
theorem B11904661 : Blo 1100624 11904661 := bbase (se 6 (by rfl) ⟨279015, by rfl⟩ : syracuseStep 11904661 = 558031) (by norm_num)
theorem B1255133 : Blo 1100624 1255133 := bbase (se 3 (by rfl) ⟨235337, by rfl⟩ : syracuseStep 1255133 = 470675) (by norm_num)
theorem B2795269 : Blo 1100624 2795269 := bbase (se 4 (by rfl) ⟨262056, by rfl⟩ : syracuseStep 2795269 = 524113) (by norm_num)
theorem B2795381 : Blo 1100624 2795381 := bbase (se 5 (by rfl) ⟨131033, by rfl⟩ : syracuseStep 2795381 = 262067) (by norm_num)
theorem B6268853 : Blo 1100624 6268853 := bbase (se 5 (by rfl) ⟨293852, by rfl⟩ : syracuseStep 6268853 = 587705) (by norm_num)
theorem B2828317 : Blo 1100624 2828317 := bbase (se 3 (by rfl) ⟨530309, by rfl⟩ : syracuseStep 2828317 = 1060619) (by norm_num)
theorem B2795573 : Blo 1100624 2795573 := bbase (se 5 (by rfl) ⟨131042, by rfl⟩ : syracuseStep 2795573 = 262085) (by norm_num)
theorem B5581061 : Blo 1100624 5581061 := bbase (se 4 (by rfl) ⟨523224, by rfl⟩ : syracuseStep 5581061 = 1046449) (by norm_num)
theorem B2795917 : Blo 1100624 2795917 := bbase (se 3 (by rfl) ⟨524234, by rfl⟩ : syracuseStep 2795917 = 1048469) (by norm_num)
theorem B2796029 : Blo 1100624 2796029 := bbase (se 3 (by rfl) ⟨524255, by rfl⟩ : syracuseStep 2796029 = 1048511) (by norm_num)
theorem B9415925 : Blo 1100624 9415925 := bbase (se 5 (by rfl) ⟨441371, by rfl⟩ : syracuseStep 9415925 = 882743) (by norm_num)
theorem B10595605 : Blo 1100624 10595605 := bbase (se 6 (by rfl) ⟨248334, by rfl⟩ : syracuseStep 10595605 = 496669) (by norm_num)
theorem B2043389 : Blo 1100624 2043389 := bbase (se 3 (by rfl) ⟨383135, by rfl⟩ : syracuseStep 2043389 = 766271) (by norm_num)
theorem B6696469 : Blo 1100624 6696469 := bbase (se 6 (by rfl) ⟨156948, by rfl⟩ : syracuseStep 6696469 = 313897) (by norm_num)
theorem B5582357 : Blo 1100624 5582357 := bbase (se 6 (by rfl) ⟨130836, by rfl⟩ : syracuseStep 5582357 = 261673) (by norm_num)
theorem B3714821 : Blo 1100624 3714821 := bbase (se 4 (by rfl) ⟨348264, by rfl⟩ : syracuseStep 3714821 = 696529) (by norm_num)
theorem B2862917 : Blo 1100624 2862917 := bbase (se 4 (by rfl) ⟨268398, by rfl⟩ : syracuseStep 2862917 = 536797) (by norm_num)
theorem B1257377 : Blo 1100624 1257377 := bbase (se 2 (by rfl) ⟨471516, by rfl⟩ : syracuseStep 1257377 = 943033) (by norm_num)
theorem B4599749 : Blo 1100624 4599749 := bbase (se 4 (by rfl) ⟨431226, by rfl⟩ : syracuseStep 4599749 = 862453) (by norm_num)
theorem B4239397 : Blo 1100624 4239397 := bbase (se 4 (by rfl) ⟨397443, by rfl⟩ : syracuseStep 4239397 = 794887) (by norm_num)
theorem B1323101 : Blo 1100624 1323101 := bbase (se 3 (by rfl) ⟨248081, by rfl⟩ : syracuseStep 1323101 = 496163) (by norm_num)
theorem B3977333 : Blo 1100624 3977333 := bbase (se 5 (by rfl) ⟨186437, by rfl⟩ : syracuseStep 3977333 = 372875) (by norm_num)
theorem B3715253 : Blo 1100624 3715253 := bbase (se 5 (by rfl) ⟨174152, by rfl⟩ : syracuseStep 3715253 = 348305) (by norm_num)
theorem B3354853 : Blo 1100624 3354853 := bbase (se 4 (by rfl) ⟨314517, by rfl⟩ : syracuseStep 3354853 = 629035) (by norm_num)
theorem B1650941 : Blo 1100624 1650941 := bbase (se 3 (by rfl) ⟨309551, by rfl⟩ : syracuseStep 1650941 = 619103) (by norm_num)
theorem B1650965 : Blo 1100624 1650965 := bbase (se 6 (by rfl) ⟨38694, by rfl⟩ : syracuseStep 1650965 = 77389) (by norm_num)
theorem B1650989 : Blo 1100624 1650989 := bbase (se 3 (by rfl) ⟨309560, by rfl⟩ : syracuseStep 1650989 = 619121) (by norm_num)
theorem B1651013 : Blo 1100624 1651013 := bbase (se 4 (by rfl) ⟨154782, by rfl⟩ : syracuseStep 1651013 = 309565) (by norm_num)
theorem B1651037 : Blo 1100624 1651037 := bbase (se 3 (by rfl) ⟨309569, by rfl⟩ : syracuseStep 1651037 = 619139) (by norm_num)
theorem B1651061 : Blo 1100624 1651061 := bbase (se 5 (by rfl) ⟨77393, by rfl⟩ : syracuseStep 1651061 = 154787) (by norm_num)
theorem B1651085 : Blo 1100624 1651085 := bbase (se 3 (by rfl) ⟨309578, by rfl⟩ : syracuseStep 1651085 = 619157) (by norm_num)
theorem B1651109 : Blo 1100624 1651109 := bbase (se 4 (by rfl) ⟨154791, by rfl⟩ : syracuseStep 1651109 = 309583) (by norm_num)
theorem B1651133 : Blo 1100624 1651133 := bbase (se 3 (by rfl) ⟨309587, by rfl⟩ : syracuseStep 1651133 = 619175) (by norm_num)
theorem B1651157 : Blo 1100624 1651157 := bbase (se 7 (by rfl) ⟨19349, by rfl⟩ : syracuseStep 1651157 = 38699) (by norm_num)
theorem B1651181 : Blo 1100624 1651181 := bbase (se 3 (by rfl) ⟨309596, by rfl⟩ : syracuseStep 1651181 = 619193) (by norm_num)
theorem B1651205 : Blo 1100624 1651205 := bbase (se 4 (by rfl) ⟨154800, by rfl⟩ : syracuseStep 1651205 = 309601) (by norm_num)
theorem B1651229 : Blo 1100624 1651229 := bbase (se 3 (by rfl) ⟨309605, by rfl⟩ : syracuseStep 1651229 = 619211) (by norm_num)
theorem B1651253 : Blo 1100624 1651253 := bbase (se 5 (by rfl) ⟨77402, by rfl⟩ : syracuseStep 1651253 = 154805) (by norm_num)
theorem B1323577 : Blo 1100624 1323577 := bbase (se 2 (by rfl) ⟨496341, by rfl⟩ : syracuseStep 1323577 = 992683) (by norm_num)
theorem B1651277 : Blo 1100624 1651277 := bbase (se 3 (by rfl) ⟨309614, by rfl⟩ : syracuseStep 1651277 = 619229) (by norm_num)
theorem B1323605 : Blo 1100624 1323605 := bbase (se 8 (by rfl) ⟨7755, by rfl⟩ : syracuseStep 1323605 = 15511) (by norm_num)
theorem B1651301 : Blo 1100624 1651301 := bbase (se 4 (by rfl) ⟨154809, by rfl⟩ : syracuseStep 1651301 = 309619) (by norm_num)
theorem B3715685 : Blo 1100624 3715685 := bbase (se 4 (by rfl) ⟨348345, by rfl⟩ : syracuseStep 3715685 = 696691) (by norm_num)
theorem B1651325 : Blo 1100624 1651325 := bbase (se 3 (by rfl) ⟨309623, by rfl⟩ : syracuseStep 1651325 = 619247) (by norm_num)
theorem B1651349 : Blo 1100624 1651349 := bbase (se 6 (by rfl) ⟨38703, by rfl⟩ : syracuseStep 1651349 = 77407) (by norm_num)
theorem B1651373 : Blo 1100624 1651373 := bbase (se 3 (by rfl) ⟨309632, by rfl⟩ : syracuseStep 1651373 = 619265) (by norm_num)
theorem B1651397 : Blo 1100624 1651397 := bbase (se 4 (by rfl) ⟨154818, by rfl⟩ : syracuseStep 1651397 = 309637) (by norm_num)
theorem B1651421 : Blo 1100624 1651421 := bbase (se 3 (by rfl) ⟨309641, by rfl⟩ : syracuseStep 1651421 = 619283) (by norm_num)
theorem B1651445 : Blo 1100624 1651445 := bbase (se 5 (by rfl) ⟨77411, by rfl⟩ : syracuseStep 1651445 = 154823) (by norm_num)
theorem B1258249 : Blo 1100624 1258249 := bbase (se 2 (by rfl) ⟨471843, by rfl⟩ : syracuseStep 1258249 = 943687) (by norm_num)
theorem B1651469 : Blo 1100624 1651469 := bbase (se 3 (by rfl) ⟨309650, by rfl⟩ : syracuseStep 1651469 = 619301) (by norm_num)
theorem B1323793 : Blo 1100624 1323793 := bbase (se 2 (by rfl) ⟨496422, by rfl⟩ : syracuseStep 1323793 = 992845) (by norm_num)
theorem B1651493 : Blo 1100624 1651493 := bbase (se 4 (by rfl) ⟨154827, by rfl⟩ : syracuseStep 1651493 = 309655) (by norm_num)
theorem B5583653 : Blo 1100624 5583653 := bbase (se 4 (by rfl) ⟨523467, by rfl⟩ : syracuseStep 5583653 = 1046935) (by norm_num)
theorem B1651517 : Blo 1100624 1651517 := bbase (se 3 (by rfl) ⟨309659, by rfl⟩ : syracuseStep 1651517 = 619319) (by norm_num)
theorem B1651541 : Blo 1100624 1651541 := bbase (se 9 (by rfl) ⟨4838, by rfl⟩ : syracuseStep 1651541 = 9677) (by norm_num)
theorem B1651565 : Blo 1100624 1651565 := bbase (se 3 (by rfl) ⟨309668, by rfl⟩ : syracuseStep 1651565 = 619337) (by norm_num)
theorem B1651589 : Blo 1100624 1651589 := bbase (se 4 (by rfl) ⟨154836, by rfl⟩ : syracuseStep 1651589 = 309673) (by norm_num)
theorem B1323913 : Blo 1100624 1323913 := bbase (se 2 (by rfl) ⟨496467, by rfl⟩ : syracuseStep 1323913 = 992935) (by norm_num)
theorem B1651613 : Blo 1100624 1651613 := bbase (se 3 (by rfl) ⟨309677, by rfl⟩ : syracuseStep 1651613 = 619355) (by norm_num)
theorem B1651637 : Blo 1100624 1651637 := bbase (se 5 (by rfl) ⟨77420, by rfl⟩ : syracuseStep 1651637 = 154841) (by norm_num)
theorem B1651661 : Blo 1100624 1651661 := bbase (se 3 (by rfl) ⟨309686, by rfl⟩ : syracuseStep 1651661 = 619373) (by norm_num)
theorem B3978197 : Blo 1100624 3978197 := bbase (se 7 (by rfl) ⟨46619, by rfl⟩ : syracuseStep 3978197 = 93239) (by norm_num)
theorem B1651685 : Blo 1100624 1651685 := bbase (se 4 (by rfl) ⟨154845, by rfl⟩ : syracuseStep 1651685 = 309691) (by norm_num)
theorem B1651709 : Blo 1100624 1651709 := bbase (se 3 (by rfl) ⟨309695, by rfl⟩ : syracuseStep 1651709 = 619391) (by norm_num)
theorem B3716117 : Blo 1100624 3716117 := bbase (se 6 (by rfl) ⟨87096, by rfl⟩ : syracuseStep 3716117 = 174193) (by norm_num)
theorem B1651733 : Blo 1100624 1651733 := bbase (se 6 (by rfl) ⟨38712, by rfl⟩ : syracuseStep 1651733 = 77425) (by norm_num)
theorem B1651757 : Blo 1100624 1651757 := bbase (se 3 (by rfl) ⟨309704, by rfl⟩ : syracuseStep 1651757 = 619409) (by norm_num)
theorem B1651781 : Blo 1100624 1651781 := bbase (se 4 (by rfl) ⟨154854, by rfl⟩ : syracuseStep 1651781 = 309709) (by norm_num)
theorem B2241605 : Blo 1100624 2241605 := bbase (se 4 (by rfl) ⟨210150, by rfl⟩ : syracuseStep 2241605 = 420301) (by norm_num)
theorem B1651805 : Blo 1100624 1651805 := bbase (se 3 (by rfl) ⟨309713, by rfl⟩ : syracuseStep 1651805 = 619427) (by norm_num)
theorem B5289077 : Blo 1100624 5289077 := bbase (se 5 (by rfl) ⟨247925, by rfl⟩ : syracuseStep 5289077 = 495851) (by norm_num)
theorem B1651829 : Blo 1100624 1651829 := bbase (se 5 (by rfl) ⟨77429, by rfl⟩ : syracuseStep 1651829 = 154859) (by norm_num)
theorem B1651853 : Blo 1100624 1651853 := bbase (se 3 (by rfl) ⟨309722, by rfl⟩ : syracuseStep 1651853 = 619445) (by norm_num)
theorem B1651877 : Blo 1100624 1651877 := bbase (se 4 (by rfl) ⟨154863, by rfl⟩ : syracuseStep 1651877 = 309727) (by norm_num)
theorem B4240565 : Blo 1100624 4240565 := bbase (se 5 (by rfl) ⟨198776, by rfl⟩ : syracuseStep 4240565 = 397553) (by norm_num)
theorem B1651901 : Blo 1100624 1651901 := bbase (se 3 (by rfl) ⟨309731, by rfl⟩ : syracuseStep 1651901 = 619463) (by norm_num)
theorem B1651925 : Blo 1100624 1651925 := bbase (se 7 (by rfl) ⟨19358, by rfl⟩ : syracuseStep 1651925 = 38717) (by norm_num)
theorem B1651949 : Blo 1100624 1651949 := bbase (se 3 (by rfl) ⟨309740, by rfl⟩ : syracuseStep 1651949 = 619481) (by norm_num)
theorem B1651973 : Blo 1100624 1651973 := bbase (se 4 (by rfl) ⟨154872, by rfl⟩ : syracuseStep 1651973 = 309745) (by norm_num)
theorem B1651997 : Blo 1100624 1651997 := bbase (se 3 (by rfl) ⟨309749, by rfl⟩ : syracuseStep 1651997 = 619499) (by norm_num)
theorem B1652021 : Blo 1100624 1652021 := bbase (se 5 (by rfl) ⟨77438, by rfl⟩ : syracuseStep 1652021 = 154877) (by norm_num)
theorem B1652045 : Blo 1100624 1652045 := bbase (se 3 (by rfl) ⟨309758, by rfl⟩ : syracuseStep 1652045 = 619517) (by norm_num)
theorem B1652069 : Blo 1100624 1652069 := bbase (se 4 (by rfl) ⟨154881, by rfl⟩ : syracuseStep 1652069 = 309763) (by norm_num)
theorem B1488245 : Blo 1100624 1488245 := bbase (se 5 (by rfl) ⟨69761, by rfl⟩ : syracuseStep 1488245 = 139523) (by norm_num)
theorem B1652093 : Blo 1100624 1652093 := bbase (se 3 (by rfl) ⟨309767, by rfl⟩ : syracuseStep 1652093 = 619535) (by norm_num)
theorem B1652117 : Blo 1100624 1652117 := bbase (se 6 (by rfl) ⟨38721, by rfl⟩ : syracuseStep 1652117 = 77443) (by norm_num)
theorem B1652141 : Blo 1100624 1652141 := bbase (se 3 (by rfl) ⟨309776, by rfl⟩ : syracuseStep 1652141 = 619553) (by norm_num)
theorem B3716549 : Blo 1100624 3716549 := bbase (se 4 (by rfl) ⟨348426, by rfl⟩ : syracuseStep 3716549 = 696853) (by norm_num)
theorem B1652165 : Blo 1100624 1652165 := bbase (se 4 (by rfl) ⟨154890, by rfl⟩ : syracuseStep 1652165 = 309781) (by norm_num)
theorem B1652189 : Blo 1100624 1652189 := bbase (se 3 (by rfl) ⟨309785, by rfl⟩ : syracuseStep 1652189 = 619571) (by norm_num)
theorem B1652213 : Blo 1100624 1652213 := bbase (se 5 (by rfl) ⟨77447, by rfl⟩ : syracuseStep 1652213 = 154895) (by norm_num)
theorem B1652237 : Blo 1100624 1652237 := bbase (se 3 (by rfl) ⟨309794, by rfl⟩ : syracuseStep 1652237 = 619589) (by norm_num)
theorem B1652261 : Blo 1100624 1652261 := bbase (se 4 (by rfl) ⟨154899, by rfl⟩ : syracuseStep 1652261 = 309799) (by norm_num)
theorem B1652285 : Blo 1100624 1652285 := bbase (se 3 (by rfl) ⟨309803, by rfl⟩ : syracuseStep 1652285 = 619607) (by norm_num)
theorem B1652309 : Blo 1100624 1652309 := bbase (se 8 (by rfl) ⟨9681, by rfl⟩ : syracuseStep 1652309 = 19363) (by norm_num)
theorem B1652333 : Blo 1100624 1652333 := bbase (se 3 (by rfl) ⟨309812, by rfl⟩ : syracuseStep 1652333 = 619625) (by norm_num)
theorem B1652357 : Blo 1100624 1652357 := bbase (se 4 (by rfl) ⟨154908, by rfl⟩ : syracuseStep 1652357 = 309817) (by norm_num)
theorem B1652381 : Blo 1100624 1652381 := bbase (se 3 (by rfl) ⟨309821, by rfl⟩ : syracuseStep 1652381 = 619643) (by norm_num)
theorem B1652405 : Blo 1100624 1652405 := bbase (se 5 (by rfl) ⟨77456, by rfl⟩ : syracuseStep 1652405 = 154913) (by norm_num)
theorem B1652429 : Blo 1100624 1652429 := bbase (se 3 (by rfl) ⟨309830, by rfl⟩ : syracuseStep 1652429 = 619661) (by norm_num)
theorem B1652453 : Blo 1100624 1652453 := bbase (se 4 (by rfl) ⟨154917, by rfl⟩ : syracuseStep 1652453 = 309835) (by norm_num)
theorem B1652477 : Blo 1100624 1652477 := bbase (se 3 (by rfl) ⟨309839, by rfl⟩ : syracuseStep 1652477 = 619679) (by norm_num)
theorem B1652501 : Blo 1100624 1652501 := bbase (se 6 (by rfl) ⟨38730, by rfl⟩ : syracuseStep 1652501 = 77461) (by norm_num)
theorem B1652525 : Blo 1100624 1652525 := bbase (se 3 (by rfl) ⟨309848, by rfl⟩ : syracuseStep 1652525 = 619697) (by norm_num)
theorem B1652549 : Blo 1100624 1652549 := bbase (se 4 (by rfl) ⟨154926, by rfl⟩ : syracuseStep 1652549 = 309853) (by norm_num)
theorem B1652573 : Blo 1100624 1652573 := bbase (se 3 (by rfl) ⟨309857, by rfl⟩ : syracuseStep 1652573 = 619715) (by norm_num)
theorem B3716981 : Blo 1100624 3716981 := bbase (se 5 (by rfl) ⟨174233, by rfl⟩ : syracuseStep 3716981 = 348467) (by norm_num)
theorem B1652597 : Blo 1100624 1652597 := bbase (se 5 (by rfl) ⟨77465, by rfl⟩ : syracuseStep 1652597 = 154931) (by norm_num)
theorem B1652621 : Blo 1100624 1652621 := bbase (se 3 (by rfl) ⟨309866, by rfl⟩ : syracuseStep 1652621 = 619733) (by norm_num)
theorem B1193869 : Blo 1100624 1193869 := bbase (se 3 (by rfl) ⟨223850, by rfl⟩ : syracuseStep 1193869 = 447701) (by norm_num)
theorem B1652645 : Blo 1100624 1652645 := bbase (se 4 (by rfl) ⟨154935, by rfl⟩ : syracuseStep 1652645 = 309871) (by norm_num)
theorem B1652669 : Blo 1100624 1652669 := bbase (se 3 (by rfl) ⟨309875, by rfl⟩ : syracuseStep 1652669 = 619751) (by norm_num)
theorem B1652693 : Blo 1100624 1652693 := bbase (se 7 (by rfl) ⟨19367, by rfl⟩ : syracuseStep 1652693 = 38735) (by norm_num)
theorem B1652717 : Blo 1100624 1652717 := bbase (se 3 (by rfl) ⟨309884, by rfl⟩ : syracuseStep 1652717 = 619769) (by norm_num)
theorem B1652741 : Blo 1100624 1652741 := bbase (se 4 (by rfl) ⟨154944, by rfl⟩ : syracuseStep 1652741 = 309889) (by norm_num)
theorem B1652765 : Blo 1100624 1652765 := bbase (se 3 (by rfl) ⟨309893, by rfl⟩ : syracuseStep 1652765 = 619787) (by norm_num)
theorem B3586085 : Blo 1100624 3586085 := bbase (se 4 (by rfl) ⟨336195, by rfl⟩ : syracuseStep 3586085 = 672391) (by norm_num)
theorem B1652789 : Blo 1100624 1652789 := bbase (se 5 (by rfl) ⟨77474, by rfl⟩ : syracuseStep 1652789 = 154949) (by norm_num)
theorem B5584949 : Blo 1100624 5584949 := bbase (se 5 (by rfl) ⟨261794, by rfl⟩ : syracuseStep 5584949 = 523589) (by norm_num)
theorem B1652813 : Blo 1100624 1652813 := bbase (se 3 (by rfl) ⟨309902, by rfl⟩ : syracuseStep 1652813 = 619805) (by norm_num)
theorem B1652837 : Blo 1100624 1652837 := bbase (se 4 (by rfl) ⟨154953, by rfl⟩ : syracuseStep 1652837 = 309907) (by norm_num)
theorem B1652861 : Blo 1100624 1652861 := bbase (se 3 (by rfl) ⟨309911, by rfl⟩ : syracuseStep 1652861 = 619823) (by norm_num)
theorem B1652885 : Blo 1100624 1652885 := bbase (se 6 (by rfl) ⟨38739, by rfl⟩ : syracuseStep 1652885 = 77479) (by norm_num)
theorem B1652909 : Blo 1100624 1652909 := bbase (se 3 (by rfl) ⟨309920, by rfl⟩ : syracuseStep 1652909 = 619841) (by norm_num)
theorem B1652933 : Blo 1100624 1652933 := bbase (se 4 (by rfl) ⟨154962, by rfl⟩ : syracuseStep 1652933 = 309925) (by norm_num)
theorem B1652957 : Blo 1100624 1652957 := bbase (se 3 (by rfl) ⟨309929, by rfl⟩ : syracuseStep 1652957 = 619859) (by norm_num)
theorem B1652981 : Blo 1100624 1652981 := bbase (se 5 (by rfl) ⟨77483, by rfl⟩ : syracuseStep 1652981 = 154967) (by norm_num)
theorem B1653005 : Blo 1100624 1653005 := bbase (se 3 (by rfl) ⟨309938, by rfl⟩ : syracuseStep 1653005 = 619877) (by norm_num)
theorem B3717413 : Blo 1100624 3717413 := bbase (se 4 (by rfl) ⟨348507, by rfl⟩ : syracuseStep 3717413 = 697015) (by norm_num)
theorem B1653029 : Blo 1100624 1653029 := bbase (se 4 (by rfl) ⟨154971, by rfl⟩ : syracuseStep 1653029 = 309943) (by norm_num)
theorem B1653053 : Blo 1100624 1653053 := bbase (se 3 (by rfl) ⟨309947, by rfl⟩ : syracuseStep 1653053 = 619895) (by norm_num)
theorem B1653077 : Blo 1100624 1653077 := bbase (se 10 (by rfl) ⟨2421, by rfl⟩ : syracuseStep 1653077 = 4843) (by norm_num)
theorem B1653101 : Blo 1100624 1653101 := bbase (se 3 (by rfl) ⟨309956, by rfl⟩ : syracuseStep 1653101 = 619913) (by norm_num)
theorem B1653125 : Blo 1100624 1653125 := bbase (se 4 (by rfl) ⟨154980, by rfl⟩ : syracuseStep 1653125 = 309961) (by norm_num)
theorem B1653149 : Blo 1100624 1653149 := bbase (se 3 (by rfl) ⟨309965, by rfl⟩ : syracuseStep 1653149 = 619931) (by norm_num)
theorem B1325489 : Blo 1100624 1325489 := bbase (se 2 (by rfl) ⟨497058, by rfl⟩ : syracuseStep 1325489 = 994117) (by norm_num)
theorem B1653173 : Blo 1100624 1653173 := bbase (se 5 (by rfl) ⟨77492, by rfl⟩ : syracuseStep 1653173 = 154985) (by norm_num)
theorem B1653197 : Blo 1100624 1653197 := bbase (se 3 (by rfl) ⟨309974, by rfl⟩ : syracuseStep 1653197 = 619949) (by norm_num)
theorem B1653221 : Blo 1100624 1653221 := bbase (se 4 (by rfl) ⟨154989, by rfl⟩ : syracuseStep 1653221 = 309979) (by norm_num)
theorem B1653245 : Blo 1100624 1653245 := bbase (se 3 (by rfl) ⟨309983, by rfl⟩ : syracuseStep 1653245 = 619967) (by norm_num)
theorem B1653269 : Blo 1100624 1653269 := bbase (se 6 (by rfl) ⟨38748, by rfl⟩ : syracuseStep 1653269 = 77497) (by norm_num)
theorem B1653293 : Blo 1100624 1653293 := bbase (se 3 (by rfl) ⟨309992, by rfl⟩ : syracuseStep 1653293 = 619985) (by norm_num)
theorem B1653317 : Blo 1100624 1653317 := bbase (se 4 (by rfl) ⟨154998, by rfl⟩ : syracuseStep 1653317 = 309997) (by norm_num)
theorem B1653341 : Blo 1100624 1653341 := bbase (se 3 (by rfl) ⟨310001, by rfl⟩ : syracuseStep 1653341 = 620003) (by norm_num)
theorem B1653365 : Blo 1100624 1653365 := bbase (se 5 (by rfl) ⟨77501, by rfl⟩ : syracuseStep 1653365 = 155003) (by norm_num)
theorem B1653389 : Blo 1100624 1653389 := bbase (se 3 (by rfl) ⟨310010, by rfl⟩ : syracuseStep 1653389 = 620021) (by norm_num)
theorem B1653413 : Blo 1100624 1653413 := bbase (se 4 (by rfl) ⟨155007, by rfl⟩ : syracuseStep 1653413 = 310015) (by norm_num)
theorem B1653437 : Blo 1100624 1653437 := bbase (se 3 (by rfl) ⟨310019, by rfl⟩ : syracuseStep 1653437 = 620039) (by norm_num)
theorem B3717845 : Blo 1100624 3717845 := bbase (se 7 (by rfl) ⟨43568, by rfl⟩ : syracuseStep 3717845 = 87137) (by norm_num)
theorem B1653461 : Blo 1100624 1653461 := bbase (se 7 (by rfl) ⟨19376, by rfl⟩ : syracuseStep 1653461 = 38753) (by norm_num)
theorem B1653485 : Blo 1100624 1653485 := bbase (se 3 (by rfl) ⟨310028, by rfl⟩ : syracuseStep 1653485 = 620057) (by norm_num)
theorem B1653509 : Blo 1100624 1653509 := bbase (se 4 (by rfl) ⟨155016, by rfl⟩ : syracuseStep 1653509 = 310033) (by norm_num)
theorem B1653533 : Blo 1100624 1653533 := bbase (se 3 (by rfl) ⟨310037, by rfl⟩ : syracuseStep 1653533 = 620075) (by norm_num)
theorem B1653557 : Blo 1100624 1653557 := bbase (se 5 (by rfl) ⟨77510, by rfl⟩ : syracuseStep 1653557 = 155021) (by norm_num)
theorem B1653581 : Blo 1100624 1653581 := bbase (se 3 (by rfl) ⟨310046, by rfl⟩ : syracuseStep 1653581 = 620093) (by norm_num)
theorem B1653605 : Blo 1100624 1653605 := bbase (se 4 (by rfl) ⟨155025, by rfl⟩ : syracuseStep 1653605 = 310051) (by norm_num)
theorem B1653629 : Blo 1100624 1653629 := bbase (se 3 (by rfl) ⟨310055, by rfl⟩ : syracuseStep 1653629 = 620111) (by norm_num)
theorem B1653653 : Blo 1100624 1653653 := bbase (se 6 (by rfl) ⟨38757, by rfl⟩ : syracuseStep 1653653 = 77515) (by norm_num)
theorem B1653677 : Blo 1100624 1653677 := bbase (se 3 (by rfl) ⟨310064, by rfl⟩ : syracuseStep 1653677 = 620129) (by norm_num)
theorem B1653701 : Blo 1100624 1653701 := bbase (se 4 (by rfl) ⟨155034, by rfl⟩ : syracuseStep 1653701 = 310069) (by norm_num)
theorem B1653725 : Blo 1100624 1653725 := bbase (se 3 (by rfl) ⟨310073, by rfl⟩ : syracuseStep 1653725 = 620147) (by norm_num)
theorem B1653749 : Blo 1100624 1653749 := bbase (se 5 (by rfl) ⟨77519, by rfl⟩ : syracuseStep 1653749 = 155039) (by norm_num)
theorem B1653773 : Blo 1100624 1653773 := bbase (se 3 (by rfl) ⟨310082, by rfl⟩ : syracuseStep 1653773 = 620165) (by norm_num)
theorem B1653797 : Blo 1100624 1653797 := bbase (se 4 (by rfl) ⟨155043, by rfl⟩ : syracuseStep 1653797 = 310087) (by norm_num)
theorem B1653821 : Blo 1100624 1653821 := bbase (se 3 (by rfl) ⟨310091, by rfl⟩ : syracuseStep 1653821 = 620183) (by norm_num)
theorem B1653845 : Blo 1100624 1653845 := bbase (se 8 (by rfl) ⟨9690, by rfl⟩ : syracuseStep 1653845 = 19381) (by norm_num)
theorem B1326181 : Blo 1100624 1326181 := bbase (se 4 (by rfl) ⟨124329, by rfl⟩ : syracuseStep 1326181 = 248659) (by norm_num)
theorem B1653869 : Blo 1100624 1653869 := bbase (se 3 (by rfl) ⟨310100, by rfl⟩ : syracuseStep 1653869 = 620201) (by norm_num)
theorem B3718277 : Blo 1100624 3718277 := bbase (se 4 (by rfl) ⟨348588, by rfl⟩ : syracuseStep 3718277 = 697177) (by norm_num)
theorem B1653893 : Blo 1100624 1653893 := bbase (se 4 (by rfl) ⟨155052, by rfl⟩ : syracuseStep 1653893 = 310105) (by norm_num)
theorem B8371349 : Blo 1100624 8371349 := bbase (se 6 (by rfl) ⟨196203, by rfl⟩ : syracuseStep 8371349 = 392407) (by norm_num)
theorem B1653917 : Blo 1100624 1653917 := bbase (se 3 (by rfl) ⟨310109, by rfl⟩ : syracuseStep 1653917 = 620219) (by norm_num)
theorem B5291173 : Blo 1100624 5291173 := bbase (se 4 (by rfl) ⟨496047, by rfl⟩ : syracuseStep 5291173 = 992095) (by norm_num)
theorem B1653941 : Blo 1100624 1653941 := bbase (se 5 (by rfl) ⟨77528, by rfl⟩ : syracuseStep 1653941 = 155057) (by norm_num)
theorem B10599605 : Blo 1100624 10599605 := bbase (se 5 (by rfl) ⟨496856, by rfl⟩ : syracuseStep 10599605 = 993713) (by norm_num)
theorem B1326277 : Blo 1100624 1326277 := bbase (se 4 (by rfl) ⟨124338, by rfl⟩ : syracuseStep 1326277 = 248677) (by norm_num)
theorem B1653965 : Blo 1100624 1653965 := bbase (se 3 (by rfl) ⟨310118, by rfl⟩ : syracuseStep 1653965 = 620237) (by norm_num)
theorem B1653989 : Blo 1100624 1653989 := bbase (se 4 (by rfl) ⟨155061, by rfl⟩ : syracuseStep 1653989 = 310123) (by norm_num)
theorem B1654013 : Blo 1100624 1654013 := bbase (se 3 (by rfl) ⟨310127, by rfl⟩ : syracuseStep 1654013 = 620255) (by norm_num)
theorem B1654037 : Blo 1100624 1654037 := bbase (se 6 (by rfl) ⟨38766, by rfl⟩ : syracuseStep 1654037 = 77533) (by norm_num)
theorem B1654061 : Blo 1100624 1654061 := bbase (se 3 (by rfl) ⟨310136, by rfl⟩ : syracuseStep 1654061 = 620273) (by norm_num)
theorem B1654085 : Blo 1100624 1654085 := bbase (se 4 (by rfl) ⟨155070, by rfl⟩ : syracuseStep 1654085 = 310141) (by norm_num)
theorem B5586245 : Blo 1100624 5586245 := bbase (se 4 (by rfl) ⟨523710, by rfl⟩ : syracuseStep 5586245 = 1047421) (by norm_num)
theorem B1654109 : Blo 1100624 1654109 := bbase (se 3 (by rfl) ⟨310145, by rfl⟩ : syracuseStep 1654109 = 620291) (by norm_num)
theorem B1654133 : Blo 1100624 1654133 := bbase (se 5 (by rfl) ⟨77537, by rfl⟩ : syracuseStep 1654133 = 155075) (by norm_num)
theorem B3980677 : Blo 1100624 3980677 := bbase (se 4 (by rfl) ⟨373188, by rfl⟩ : syracuseStep 3980677 = 746377) (by norm_num)
theorem B1654157 : Blo 1100624 1654157 := bbase (se 3 (by rfl) ⟨310154, by rfl⟩ : syracuseStep 1654157 = 620309) (by norm_num)
theorem B1654181 : Blo 1100624 1654181 := bbase (se 4 (by rfl) ⟨155079, by rfl⟩ : syracuseStep 1654181 = 310159) (by norm_num)
theorem B1654205 : Blo 1100624 1654205 := bbase (se 3 (by rfl) ⟨310163, by rfl⟩ : syracuseStep 1654205 = 620327) (by norm_num)
theorem B1654229 : Blo 1100624 1654229 := bbase (se 7 (by rfl) ⟨19385, by rfl⟩ : syracuseStep 1654229 = 38771) (by norm_num)
theorem B1654253 : Blo 1100624 1654253 := bbase (se 3 (by rfl) ⟨310172, by rfl⟩ : syracuseStep 1654253 = 620345) (by norm_num)
theorem B1654277 : Blo 1100624 1654277 := bbase (se 4 (by rfl) ⟨155088, by rfl⟩ : syracuseStep 1654277 = 310177) (by norm_num)
theorem B1654301 : Blo 1100624 1654301 := bbase (se 3 (by rfl) ⟨310181, by rfl⟩ : syracuseStep 1654301 = 620363) (by norm_num)
theorem B3718709 : Blo 1100624 3718709 := bbase (se 5 (by rfl) ⟨174314, by rfl⟩ : syracuseStep 3718709 = 348629) (by norm_num)
theorem B7945781 : Blo 1100624 7945781 := bbase (se 5 (by rfl) ⟨372458, by rfl⟩ : syracuseStep 7945781 = 744917) (by norm_num)
theorem B1654325 : Blo 1100624 1654325 := bbase (se 5 (by rfl) ⟨77546, by rfl⟩ : syracuseStep 1654325 = 155093) (by norm_num)
theorem B1654349 : Blo 1100624 1654349 := bbase (se 3 (by rfl) ⟨310190, by rfl⟩ : syracuseStep 1654349 = 620381) (by norm_num)
theorem B1654373 : Blo 1100624 1654373 := bbase (se 4 (by rfl) ⟨155097, by rfl⟩ : syracuseStep 1654373 = 310195) (by norm_num)
theorem B1654397 : Blo 1100624 1654397 := bbase (se 3 (by rfl) ⟨310199, by rfl⟩ : syracuseStep 1654397 = 620399) (by norm_num)
theorem B1654421 : Blo 1100624 1654421 := bbase (se 6 (by rfl) ⟨38775, by rfl⟩ : syracuseStep 1654421 = 77551) (by norm_num)
theorem B1654445 : Blo 1100624 1654445 := bbase (se 3 (by rfl) ⟨310208, by rfl⟩ : syracuseStep 1654445 = 620417) (by norm_num)
theorem B1654469 : Blo 1100624 1654469 := bbase (se 4 (by rfl) ⟨155106, by rfl⟩ : syracuseStep 1654469 = 310213) (by norm_num)
theorem B1654493 : Blo 1100624 1654493 := bbase (se 3 (by rfl) ⟨310217, by rfl⟩ : syracuseStep 1654493 = 620435) (by norm_num)
theorem B1654517 : Blo 1100624 1654517 := bbase (se 5 (by rfl) ⟨77555, by rfl⟩ : syracuseStep 1654517 = 155111) (by norm_num)
theorem B1654541 : Blo 1100624 1654541 := bbase (se 3 (by rfl) ⟨310226, by rfl⟩ : syracuseStep 1654541 = 620453) (by norm_num)
theorem B1654565 : Blo 1100624 1654565 := bbase (se 4 (by rfl) ⟨155115, by rfl⟩ : syracuseStep 1654565 = 310231) (by norm_num)
theorem B1654589 : Blo 1100624 1654589 := bbase (se 3 (by rfl) ⟨310235, by rfl⟩ : syracuseStep 1654589 = 620471) (by norm_num)
theorem B1654613 : Blo 1100624 1654613 := bbase (se 9 (by rfl) ⟨4847, by rfl⟩ : syracuseStep 1654613 = 9695) (by norm_num)
theorem B1654637 : Blo 1100624 1654637 := bbase (se 3 (by rfl) ⟨310244, by rfl⟩ : syracuseStep 1654637 = 620489) (by norm_num)
theorem B1654661 : Blo 1100624 1654661 := bbase (se 4 (by rfl) ⟨155124, by rfl⟩ : syracuseStep 1654661 = 310249) (by norm_num)
theorem B1654685 : Blo 1100624 1654685 := bbase (se 3 (by rfl) ⟨310253, by rfl⟩ : syracuseStep 1654685 = 620507) (by norm_num)
theorem B1654709 : Blo 1100624 1654709 := bbase (se 5 (by rfl) ⟨77564, by rfl⟩ : syracuseStep 1654709 = 155129) (by norm_num)
theorem B1654733 : Blo 1100624 1654733 := bbase (se 3 (by rfl) ⟨310262, by rfl⟩ : syracuseStep 1654733 = 620525) (by norm_num)
theorem B3719141 : Blo 1100624 3719141 := bbase (se 4 (by rfl) ⟨348669, by rfl⟩ : syracuseStep 3719141 = 697339) (by norm_num)
theorem B1654757 : Blo 1100624 1654757 := bbase (se 4 (by rfl) ⟨155133, by rfl⟩ : syracuseStep 1654757 = 310267) (by norm_num)
theorem B1654781 : Blo 1100624 1654781 := bbase (se 3 (by rfl) ⟨310271, by rfl⟩ : syracuseStep 1654781 = 620543) (by norm_num)
theorem B1654805 : Blo 1100624 1654805 := bbase (se 6 (by rfl) ⟨38784, by rfl⟩ : syracuseStep 1654805 = 77569) (by norm_num)
theorem B1654829 : Blo 1100624 1654829 := bbase (se 3 (by rfl) ⟨310280, by rfl⟩ : syracuseStep 1654829 = 620561) (by norm_num)
theorem B1491013 : Blo 1100624 1491013 := bbase (se 4 (by rfl) ⟨139782, by rfl⟩ : syracuseStep 1491013 = 279565) (by norm_num)
theorem B1654853 : Blo 1100624 1654853 := bbase (se 4 (by rfl) ⟨155142, by rfl⟩ : syracuseStep 1654853 = 310285) (by norm_num)
theorem B1654877 : Blo 1100624 1654877 := bbase (se 3 (by rfl) ⟨310289, by rfl⟩ : syracuseStep 1654877 = 620579) (by norm_num)
theorem B1654901 : Blo 1100624 1654901 := bbase (se 5 (by rfl) ⟨77573, by rfl⟩ : syracuseStep 1654901 = 155147) (by norm_num)
theorem B1654925 : Blo 1100624 1654925 := bbase (se 3 (by rfl) ⟨310298, by rfl⟩ : syracuseStep 1654925 = 620597) (by norm_num)
theorem B1654949 : Blo 1100624 1654949 := bbase (se 4 (by rfl) ⟨155151, by rfl⟩ : syracuseStep 1654949 = 310303) (by norm_num)
theorem B1654973 : Blo 1100624 1654973 := bbase (se 3 (by rfl) ⟨310307, by rfl⟩ : syracuseStep 1654973 = 620615) (by norm_num)
theorem B26820821 : Blo 1100624 26820821 := bbase (se 7 (by rfl) ⟨314306, by rfl⟩ : syracuseStep 26820821 = 628613) (by norm_num)
theorem B1654997 : Blo 1100624 1654997 := bbase (se 7 (by rfl) ⟨19394, by rfl⟩ : syracuseStep 1654997 = 38789) (by norm_num)
theorem B1655021 : Blo 1100624 1655021 := bbase (se 3 (by rfl) ⟨310316, by rfl⟩ : syracuseStep 1655021 = 620633) (by norm_num)
theorem B1655045 : Blo 1100624 1655045 := bbase (se 4 (by rfl) ⟨155160, by rfl⟩ : syracuseStep 1655045 = 310321) (by norm_num)
theorem B1655069 : Blo 1100624 1655069 := bbase (se 3 (by rfl) ⟨310325, by rfl⟩ : syracuseStep 1655069 = 620651) (by norm_num)
theorem B1655093 : Blo 1100624 1655093 := bbase (se 5 (by rfl) ⟨77582, by rfl⟩ : syracuseStep 1655093 = 155165) (by norm_num)
theorem B1655117 : Blo 1100624 1655117 := bbase (se 3 (by rfl) ⟨310334, by rfl⟩ : syracuseStep 1655117 = 620669) (by norm_num)
theorem B1655141 : Blo 1100624 1655141 := bbase (se 4 (by rfl) ⟨155169, by rfl⟩ : syracuseStep 1655141 = 310339) (by norm_num)
theorem B1655165 : Blo 1100624 1655165 := bbase (se 3 (by rfl) ⟨310343, by rfl⟩ : syracuseStep 1655165 = 620687) (by norm_num)
theorem B1393033 : Blo 1100624 1393033 := bbase (se 2 (by rfl) ⟨522387, by rfl⟩ : syracuseStep 1393033 = 1044775) (by norm_num)
theorem B3719573 : Blo 1100624 3719573 := bbase (se 6 (by rfl) ⟨87177, by rfl⟩ : syracuseStep 3719573 = 174355) (by norm_num)
theorem B1655189 : Blo 1100624 1655189 := bbase (se 6 (by rfl) ⟨38793, by rfl⟩ : syracuseStep 1655189 = 77587) (by norm_num)
theorem B7553429 : Blo 1100624 7553429 := bbase (se 6 (by rfl) ⟨177033, by rfl⟩ : syracuseStep 7553429 = 354067) (by norm_num)
theorem B2015653 : Blo 1100624 2015653 := bbase (se 4 (by rfl) ⟨188967, by rfl⟩ : syracuseStep 2015653 = 377935) (by norm_num)
theorem B1655213 : Blo 1100624 1655213 := bbase (se 3 (by rfl) ⟨310352, by rfl⟩ : syracuseStep 1655213 = 620705) (by norm_num)
theorem B1655237 : Blo 1100624 1655237 := bbase (se 4 (by rfl) ⟨155178, by rfl⟩ : syracuseStep 1655237 = 310357) (by norm_num)
theorem B1655261 : Blo 1100624 1655261 := bbase (se 3 (by rfl) ⟨310361, by rfl⟩ : syracuseStep 1655261 = 620723) (by norm_num)
theorem B1393129 : Blo 1100624 1393129 := bbase (se 2 (by rfl) ⟨522423, by rfl⟩ : syracuseStep 1393129 = 1044847) (by norm_num)
theorem B1655285 : Blo 1100624 1655285 := bbase (se 5 (by rfl) ⟨77591, by rfl⟩ : syracuseStep 1655285 = 155183) (by norm_num)
theorem B1655309 : Blo 1100624 1655309 := bbase (se 3 (by rfl) ⟨310370, by rfl⟩ : syracuseStep 1655309 = 620741) (by norm_num)
theorem B1655333 : Blo 1100624 1655333 := bbase (se 4 (by rfl) ⟨155187, by rfl⟩ : syracuseStep 1655333 = 310375) (by norm_num)
theorem B1655357 : Blo 1100624 1655357 := bbase (se 3 (by rfl) ⟨310379, by rfl⟩ : syracuseStep 1655357 = 620759) (by norm_num)
theorem B1655381 : Blo 1100624 1655381 := bbase (se 8 (by rfl) ⟨9699, by rfl⟩ : syracuseStep 1655381 = 19399) (by norm_num)
theorem B5587541 : Blo 1100624 5587541 := bbase (se 8 (by rfl) ⟨32739, by rfl⟩ : syracuseStep 5587541 = 65479) (by norm_num)
theorem B1655405 : Blo 1100624 1655405 := bbase (se 3 (by rfl) ⟨310388, by rfl⟩ : syracuseStep 1655405 = 620777) (by norm_num)
theorem B1655429 : Blo 1100624 1655429 := bbase (se 4 (by rfl) ⟨155196, by rfl⟩ : syracuseStep 1655429 = 310393) (by norm_num)
theorem B1393301 : Blo 1100624 1393301 := bbase (se 6 (by rfl) ⟨32655, by rfl⟩ : syracuseStep 1393301 = 65311) (by norm_num)
theorem B1655453 : Blo 1100624 1655453 := bbase (se 3 (by rfl) ⟨310397, by rfl⟩ : syracuseStep 1655453 = 620795) (by norm_num)
theorem B1655477 : Blo 1100624 1655477 := bbase (se 5 (by rfl) ⟨77600, by rfl⟩ : syracuseStep 1655477 = 155201) (by norm_num)
theorem B1393357 : Blo 1100624 1393357 := bbase (se 3 (by rfl) ⟨261254, by rfl⟩ : syracuseStep 1393357 = 522509) (by norm_num)
theorem B1655501 : Blo 1100624 1655501 := bbase (se 3 (by rfl) ⟨310406, by rfl⟩ : syracuseStep 1655501 = 620813) (by norm_num)
theorem B1655525 : Blo 1100624 1655525 := bbase (se 4 (by rfl) ⟨155205, by rfl⟩ : syracuseStep 1655525 = 310411) (by norm_num)
theorem B1655549 : Blo 1100624 1655549 := bbase (se 3 (by rfl) ⟨310415, by rfl⟩ : syracuseStep 1655549 = 620831) (by norm_num)
theorem B1655573 : Blo 1100624 1655573 := bbase (se 6 (by rfl) ⟨38802, by rfl⟩ : syracuseStep 1655573 = 77605) (by norm_num)
theorem B1393453 : Blo 1100624 1393453 := bbase (se 3 (by rfl) ⟨261272, by rfl⟩ : syracuseStep 1393453 = 522545) (by norm_num)
theorem B1655597 : Blo 1100624 1655597 := bbase (se 3 (by rfl) ⟨310424, by rfl⟩ : syracuseStep 1655597 = 620849) (by norm_num)
theorem B3720005 : Blo 1100624 3720005 := bbase (se 4 (by rfl) ⟨348750, by rfl⟩ : syracuseStep 3720005 = 697501) (by norm_num)
theorem B1655621 : Blo 1100624 1655621 := bbase (se 4 (by rfl) ⟨155214, by rfl⟩ : syracuseStep 1655621 = 310429) (by norm_num)
theorem B1655645 : Blo 1100624 1655645 := bbase (se 3 (by rfl) ⟨310433, by rfl⟩ : syracuseStep 1655645 = 620867) (by norm_num)
theorem B1655669 : Blo 1100624 1655669 := bbase (se 5 (by rfl) ⟨77609, by rfl⟩ : syracuseStep 1655669 = 155219) (by norm_num)
theorem B1655693 : Blo 1100624 1655693 := bbase (se 3 (by rfl) ⟨310442, by rfl⟩ : syracuseStep 1655693 = 620885) (by norm_num)
theorem B1655717 : Blo 1100624 1655717 := bbase (se 4 (by rfl) ⟨155223, by rfl⟩ : syracuseStep 1655717 = 310447) (by norm_num)
theorem B1655741 : Blo 1100624 1655741 := bbase (se 3 (by rfl) ⟨310451, by rfl⟩ : syracuseStep 1655741 = 620903) (by norm_num)
theorem B1655765 : Blo 1100624 1655765 := bbase (se 7 (by rfl) ⟨19403, by rfl⟩ : syracuseStep 1655765 = 38807) (by norm_num)
theorem B1393625 : Blo 1100624 1393625 := bbase (se 2 (by rfl) ⟨522609, by rfl⟩ : syracuseStep 1393625 = 1045219) (by norm_num)
theorem B1655789 : Blo 1100624 1655789 := bbase (se 3 (by rfl) ⟨310460, by rfl⟩ : syracuseStep 1655789 = 620921) (by norm_num)
theorem B1491949 : Blo 1100624 1491949 := bbase (se 3 (by rfl) ⟨279740, by rfl⟩ : syracuseStep 1491949 = 559481) (by norm_num)
theorem B1655813 : Blo 1100624 1655813 := bbase (se 4 (by rfl) ⟨155232, by rfl⟩ : syracuseStep 1655813 = 310465) (by norm_num)
theorem B1393681 : Blo 1100624 1393681 := bbase (se 2 (by rfl) ⟨522630, by rfl⟩ : syracuseStep 1393681 = 1045261) (by norm_num)
theorem B1655837 : Blo 1100624 1655837 := bbase (se 3 (by rfl) ⟨310469, by rfl⟩ : syracuseStep 1655837 = 620939) (by norm_num)
theorem B1655861 : Blo 1100624 1655861 := bbase (se 5 (by rfl) ⟨77618, by rfl⟩ : syracuseStep 1655861 = 155237) (by norm_num)
theorem B1655885 : Blo 1100624 1655885 := bbase (se 3 (by rfl) ⟨310478, by rfl⟩ : syracuseStep 1655885 = 620957) (by norm_num)
theorem B1655909 : Blo 1100624 1655909 := bbase (se 4 (by rfl) ⟨155241, by rfl⟩ : syracuseStep 1655909 = 310483) (by norm_num)
theorem B1393777 : Blo 1100624 1393777 := bbase (se 2 (by rfl) ⟨522666, by rfl⟩ : syracuseStep 1393777 = 1045333) (by norm_num)
theorem B1655933 : Blo 1100624 1655933 := bbase (se 3 (by rfl) ⟨310487, by rfl⟩ : syracuseStep 1655933 = 620975) (by norm_num)
theorem B1655957 : Blo 1100624 1655957 := bbase (se 6 (by rfl) ⟨38811, by rfl⟩ : syracuseStep 1655957 = 77623) (by norm_num)
theorem B1655981 : Blo 1100624 1655981 := bbase (se 3 (by rfl) ⟨310496, by rfl⟩ : syracuseStep 1655981 = 620993) (by norm_num)
theorem B1656005 : Blo 1100624 1656005 := bbase (se 4 (by rfl) ⟨155250, by rfl⟩ : syracuseStep 1656005 = 310501) (by norm_num)
theorem B1656029 : Blo 1100624 1656029 := bbase (se 3 (by rfl) ⟨310505, by rfl⟩ : syracuseStep 1656029 = 621011) (by norm_num)
theorem B3720437 : Blo 1100624 3720437 := bbase (se 5 (by rfl) ⟨174395, by rfl⟩ : syracuseStep 3720437 = 348791) (by norm_num)
theorem B1656053 : Blo 1100624 1656053 := bbase (se 5 (by rfl) ⟨77627, by rfl⟩ : syracuseStep 1656053 = 155255) (by norm_num)
theorem B1656077 : Blo 1100624 1656077 := bbase (se 3 (by rfl) ⟨310514, by rfl⟩ : syracuseStep 1656077 = 621029) (by norm_num)
theorem B4179221 : Blo 1100624 4179221 := bbase (se 6 (by rfl) ⟨97950, by rfl⟩ : syracuseStep 4179221 = 195901) (by norm_num)
theorem B1393949 : Blo 1100624 1393949 := bbase (se 3 (by rfl) ⟨261365, by rfl⟩ : syracuseStep 1393949 = 522731) (by norm_num)
theorem B1656101 : Blo 1100624 1656101 := bbase (se 4 (by rfl) ⟨155259, by rfl⟩ : syracuseStep 1656101 = 310519) (by norm_num)
theorem B1656125 : Blo 1100624 1656125 := bbase (se 3 (by rfl) ⟨310523, by rfl⟩ : syracuseStep 1656125 = 621047) (by norm_num)
theorem B1394005 : Blo 1100624 1394005 := bbase (se 12 (by rfl) ⟨510, by rfl⟩ : syracuseStep 1394005 = 1021) (by norm_num)
theorem B1656149 : Blo 1100624 1656149 := bbase (se 12 (by rfl) ⟨606, by rfl⟩ : syracuseStep 1656149 = 1213) (by norm_num)
theorem B1983845 : Blo 1100624 1983845 := bbase (se 4 (by rfl) ⟨185985, by rfl⟩ : syracuseStep 1983845 = 371971) (by norm_num)
theorem B1656173 : Blo 1100624 1656173 := bbase (se 3 (by rfl) ⟨310532, by rfl⟩ : syracuseStep 1656173 = 621065) (by norm_num)
theorem B1656197 : Blo 1100624 1656197 := bbase (se 4 (by rfl) ⟨155268, by rfl⟩ : syracuseStep 1656197 = 310537) (by norm_num)
theorem B1656221 : Blo 1100624 1656221 := bbase (se 3 (by rfl) ⟨310541, by rfl⟩ : syracuseStep 1656221 = 621083) (by norm_num)
theorem B1394101 : Blo 1100624 1394101 := bbase (se 5 (by rfl) ⟨65348, by rfl⟩ : syracuseStep 1394101 = 130697) (by norm_num)
theorem B1656245 : Blo 1100624 1656245 := bbase (se 5 (by rfl) ⟨77636, by rfl⟩ : syracuseStep 1656245 = 155273) (by norm_num)
theorem B1656269 : Blo 1100624 1656269 := bbase (se 3 (by rfl) ⟨310550, by rfl⟩ : syracuseStep 1656269 = 621101) (by norm_num)
theorem B1656293 : Blo 1100624 1656293 := bbase (se 4 (by rfl) ⟨155277, by rfl⟩ : syracuseStep 1656293 = 310555) (by norm_num)
theorem B1656317 : Blo 1100624 1656317 := bbase (se 3 (by rfl) ⟨310559, by rfl⟩ : syracuseStep 1656317 = 621119) (by norm_num)
theorem B1656341 : Blo 1100624 1656341 := bbase (se 6 (by rfl) ⟨38820, by rfl⟩ : syracuseStep 1656341 = 77641) (by norm_num)
theorem B1656365 : Blo 1100624 1656365 := bbase (se 3 (by rfl) ⟨310568, by rfl⟩ : syracuseStep 1656365 = 621137) (by norm_num)
theorem B4179509 : Blo 1100624 4179509 := bbase (se 5 (by rfl) ⟨195914, by rfl⟩ : syracuseStep 4179509 = 391829) (by norm_num)
theorem B1656389 : Blo 1100624 1656389 := bbase (se 4 (by rfl) ⟨155286, by rfl⟩ : syracuseStep 1656389 = 310573) (by norm_num)
theorem B6702677 : Blo 1100624 6702677 := bbase (se 8 (by rfl) ⟨39273, by rfl⟩ : syracuseStep 6702677 = 78547) (by norm_num)
theorem B1656413 : Blo 1100624 1656413 := bbase (se 3 (by rfl) ⟨310577, by rfl⟩ : syracuseStep 1656413 = 621155) (by norm_num)
theorem B1394273 : Blo 1100624 1394273 := bbase (se 2 (by rfl) ⟨522852, by rfl⟩ : syracuseStep 1394273 = 1045705) (by norm_num)
theorem B1656437 : Blo 1100624 1656437 := bbase (se 5 (by rfl) ⟨77645, by rfl⟩ : syracuseStep 1656437 = 155291) (by norm_num)
theorem B1984133 : Blo 1100624 1984133 := bbase (se 4 (by rfl) ⟨186012, by rfl⟩ : syracuseStep 1984133 = 372025) (by norm_num)
theorem B1656461 : Blo 1100624 1656461 := bbase (se 3 (by rfl) ⟨310586, by rfl⟩ : syracuseStep 1656461 = 621173) (by norm_num)
theorem B1394329 : Blo 1100624 1394329 := bbase (se 2 (by rfl) ⟨522873, by rfl⟩ : syracuseStep 1394329 = 1045747) (by norm_num)
theorem B3720869 : Blo 1100624 3720869 := bbase (se 4 (by rfl) ⟨348831, by rfl⟩ : syracuseStep 3720869 = 697663) (by norm_num)
theorem B1656485 : Blo 1100624 1656485 := bbase (se 4 (by rfl) ⟨155295, by rfl⟩ : syracuseStep 1656485 = 310591) (by norm_num)
theorem B1656509 : Blo 1100624 1656509 := bbase (se 3 (by rfl) ⟨310595, by rfl⟩ : syracuseStep 1656509 = 621191) (by norm_num)
theorem B1656533 : Blo 1100624 1656533 := bbase (se 7 (by rfl) ⟨19412, by rfl⟩ : syracuseStep 1656533 = 38825) (by norm_num)
theorem B4474597 : Blo 1100624 4474597 := bbase (se 4 (by rfl) ⟨419493, by rfl⟩ : syracuseStep 4474597 = 838987) (by norm_num)
theorem B1656557 : Blo 1100624 1656557 := bbase (se 3 (by rfl) ⟨310604, by rfl⟩ : syracuseStep 1656557 = 621209) (by norm_num)
theorem B1394425 : Blo 1100624 1394425 := bbase (se 2 (by rfl) ⟨522909, by rfl⟩ : syracuseStep 1394425 = 1045819) (by norm_num)
theorem B1656581 : Blo 1100624 1656581 := bbase (se 4 (by rfl) ⟨155304, by rfl⟩ : syracuseStep 1656581 = 310609) (by norm_num)
theorem B1656605 : Blo 1100624 1656605 := bbase (se 3 (by rfl) ⟨310613, by rfl⟩ : syracuseStep 1656605 = 621227) (by norm_num)
theorem B1656629 : Blo 1100624 1656629 := bbase (se 5 (by rfl) ⟨77654, by rfl⟩ : syracuseStep 1656629 = 155309) (by norm_num)
theorem B1656653 : Blo 1100624 1656653 := bbase (se 3 (by rfl) ⟨310622, by rfl⟩ : syracuseStep 1656653 = 621245) (by norm_num)
theorem B4704101 : Blo 1100624 4704101 := bbase (se 4 (by rfl) ⟨441009, by rfl⟩ : syracuseStep 4704101 = 882019) (by norm_num)
theorem B5588837 : Blo 1100624 5588837 := bbase (se 4 (by rfl) ⟨523953, by rfl⟩ : syracuseStep 5588837 = 1047907) (by norm_num)
theorem B1656677 : Blo 1100624 1656677 := bbase (se 4 (by rfl) ⟨155313, by rfl⟩ : syracuseStep 1656677 = 310627) (by norm_num)
theorem B1656701 : Blo 1100624 1656701 := bbase (se 3 (by rfl) ⟨310631, by rfl⟩ : syracuseStep 1656701 = 621263) (by norm_num)
theorem B1656725 : Blo 1100624 1656725 := bbase (se 6 (by rfl) ⟨38829, by rfl⟩ : syracuseStep 1656725 = 77659) (by norm_num)
theorem B1394597 : Blo 1100624 1394597 := bbase (se 4 (by rfl) ⟨130743, by rfl⟩ : syracuseStep 1394597 = 261487) (by norm_num)
theorem B1656749 : Blo 1100624 1656749 := bbase (se 3 (by rfl) ⟨310640, by rfl⟩ : syracuseStep 1656749 = 621281) (by norm_num)
theorem B1656773 : Blo 1100624 1656773 := bbase (se 4 (by rfl) ⟨155322, by rfl⟩ : syracuseStep 1656773 = 310645) (by norm_num)
theorem B1394653 : Blo 1100624 1394653 := bbase (se 3 (by rfl) ⟨261497, by rfl⟩ : syracuseStep 1394653 = 522995) (by norm_num)
theorem B1656797 : Blo 1100624 1656797 := bbase (se 3 (by rfl) ⟨310649, by rfl⟩ : syracuseStep 1656797 = 621299) (by norm_num)
theorem B1656821 : Blo 1100624 1656821 := bbase (se 5 (by rfl) ⟨77663, by rfl⟩ : syracuseStep 1656821 = 155327) (by norm_num)
theorem B1656845 : Blo 1100624 1656845 := bbase (se 3 (by rfl) ⟨310658, by rfl⟩ : syracuseStep 1656845 = 621317) (by norm_num)
theorem B1656869 : Blo 1100624 1656869 := bbase (se 4 (by rfl) ⟨155331, by rfl⟩ : syracuseStep 1656869 = 310663) (by norm_num)
theorem B1394749 : Blo 1100624 1394749 := bbase (se 3 (by rfl) ⟨261515, by rfl⟩ : syracuseStep 1394749 = 523031) (by norm_num)
theorem B1656893 : Blo 1100624 1656893 := bbase (se 3 (by rfl) ⟨310667, by rfl⟩ : syracuseStep 1656893 = 621335) (by norm_num)
theorem B3721301 : Blo 1100624 3721301 := bbase (se 8 (by rfl) ⟨21804, by rfl⟩ : syracuseStep 3721301 = 43609) (by norm_num)
theorem B1656917 : Blo 1100624 1656917 := bbase (se 8 (by rfl) ⟨9708, by rfl⟩ : syracuseStep 1656917 = 19417) (by norm_num)
theorem B4245605 : Blo 1100624 4245605 := bbase (se 4 (by rfl) ⟨398025, by rfl⟩ : syracuseStep 4245605 = 796051) (by norm_num)
theorem B8472757 : Blo 1100624 8472757 := bbase (se 5 (by rfl) ⟨397160, by rfl⟩ : syracuseStep 8472757 = 794321) (by norm_num)
theorem B1394921 : Blo 1100624 1394921 := bbase (se 2 (by rfl) ⟨523095, by rfl⟩ : syracuseStep 1394921 = 1046191) (by norm_num)
theorem B1394977 : Blo 1100624 1394977 := bbase (se 2 (by rfl) ⟨523116, by rfl⟩ : syracuseStep 1394977 = 1046233) (by norm_num)
theorem B1395073 : Blo 1100624 1395073 := bbase (se 2 (by rfl) ⟨523152, by rfl⟩ : syracuseStep 1395073 = 1046305) (by norm_num)
theorem B2476421 : Blo 1100624 2476421 := bbase (se 4 (by rfl) ⟨232164, by rfl⟩ : syracuseStep 2476421 = 464329) (by norm_num)
theorem B2476493 : Blo 1100624 2476493 := bbase (se 3 (by rfl) ⟨464342, by rfl⟩ : syracuseStep 2476493 = 928685) (by norm_num)
theorem B3721733 : Blo 1100624 3721733 := bbase (se 4 (by rfl) ⟨348912, by rfl⟩ : syracuseStep 3721733 = 697825) (by norm_num)
theorem B2476565 : Blo 1100624 2476565 := bbase (se 6 (by rfl) ⟨58044, by rfl⟩ : syracuseStep 2476565 = 116089) (by norm_num)
theorem B1395245 : Blo 1100624 1395245 := bbase (se 3 (by rfl) ⟨261608, by rfl⟩ : syracuseStep 1395245 = 523217) (by norm_num)
theorem B2476637 : Blo 1100624 2476637 := bbase (se 3 (by rfl) ⟨464369, by rfl⟩ : syracuseStep 2476637 = 928739) (by norm_num)
theorem B1395301 : Blo 1100624 1395301 := bbase (se 4 (by rfl) ⟨130809, by rfl⟩ : syracuseStep 1395301 = 261619) (by norm_num)
theorem B2476709 : Blo 1100624 2476709 := bbase (se 4 (by rfl) ⟨232191, by rfl⟩ : syracuseStep 2476709 = 464383) (by norm_num)
theorem B1395397 : Blo 1100624 1395397 := bbase (se 4 (by rfl) ⟨130818, by rfl⟩ : syracuseStep 1395397 = 261637) (by norm_num)
theorem B4180693 : Blo 1100624 4180693 := bbase (se 7 (by rfl) ⟨48992, by rfl⟩ : syracuseStep 4180693 = 97985) (by norm_num)
theorem B2476781 : Blo 1100624 2476781 := bbase (se 3 (by rfl) ⟨464396, by rfl⟩ : syracuseStep 2476781 = 928793) (by norm_num)
theorem B2476853 : Blo 1100624 2476853 := bbase (se 5 (by rfl) ⟨116102, by rfl⟩ : syracuseStep 2476853 = 232205) (by norm_num)
theorem B7064405 : Blo 1100624 7064405 := bbase (se 9 (by rfl) ⟨20696, by rfl⟩ : syracuseStep 7064405 = 41393) (by norm_num)
theorem B1395569 : Blo 1100624 1395569 := bbase (se 2 (by rfl) ⟨523338, by rfl⟩ : syracuseStep 1395569 = 1046677) (by norm_num)
theorem B2476925 : Blo 1100624 2476925 := bbase (se 3 (by rfl) ⟨464423, by rfl⟩ : syracuseStep 2476925 = 928847) (by norm_num)
theorem B1395625 : Blo 1100624 1395625 := bbase (se 2 (by rfl) ⟨523359, by rfl⟩ : syracuseStep 1395625 = 1046719) (by norm_num)
theorem B3722165 : Blo 1100624 3722165 := bbase (se 5 (by rfl) ⟨174476, by rfl⟩ : syracuseStep 3722165 = 348953) (by norm_num)
theorem B2476997 : Blo 1100624 2476997 := bbase (se 4 (by rfl) ⟨232218, by rfl⟩ : syracuseStep 2476997 = 464437) (by norm_num)
theorem B31738837 : Blo 1100624 31738837 := bbase (se 7 (by rfl) ⟨371939, by rfl⟩ : syracuseStep 31738837 = 743879) (by norm_num)
theorem B5295077 : Blo 1100624 5295077 := bbase (se 4 (by rfl) ⟨496413, by rfl⟩ : syracuseStep 5295077 = 992827) (by norm_num)
theorem B4180997 : Blo 1100624 4180997 := bbase (se 4 (by rfl) ⟨391968, by rfl⟩ : syracuseStep 4180997 = 783937) (by norm_num)
theorem B1395721 : Blo 1100624 1395721 := bbase (se 2 (by rfl) ⟨523395, by rfl⟩ : syracuseStep 1395721 = 1046791) (by norm_num)
theorem B2477069 : Blo 1100624 2477069 := bbase (se 3 (by rfl) ⟨464450, by rfl⟩ : syracuseStep 2477069 = 928901) (by norm_num)
theorem B1985581 : Blo 1100624 1985581 := bbase (se 3 (by rfl) ⟨372296, by rfl⟩ : syracuseStep 1985581 = 744593) (by norm_num)
theorem B2477141 : Blo 1100624 2477141 := bbase (se 8 (by rfl) ⟨14514, by rfl⟩ : syracuseStep 2477141 = 29029) (by norm_num)
theorem B5590133 : Blo 1100624 5590133 := bbase (se 5 (by rfl) ⟨262037, by rfl⟩ : syracuseStep 5590133 = 524075) (by norm_num)
theorem B2477213 : Blo 1100624 2477213 := bbase (se 3 (by rfl) ⟨464477, by rfl⟩ : syracuseStep 2477213 = 928955) (by norm_num)
theorem B1395893 : Blo 1100624 1395893 := bbase (se 5 (by rfl) ⟨65432, by rfl⟩ : syracuseStep 1395893 = 130865) (by norm_num)
theorem B1985725 : Blo 1100624 1985725 := bbase (se 3 (by rfl) ⟨372323, by rfl⟩ : syracuseStep 1985725 = 744647) (by norm_num)
theorem B2477285 : Blo 1100624 2477285 := bbase (se 4 (by rfl) ⟨232245, by rfl⟩ : syracuseStep 2477285 = 464491) (by norm_num)
theorem B1395949 : Blo 1100624 1395949 := bbase (se 3 (by rfl) ⟨261740, by rfl⟩ : syracuseStep 1395949 = 523481) (by norm_num)
theorem B2870549 : Blo 1100624 2870549 := bbase (se 6 (by rfl) ⟨67278, by rfl⟩ : syracuseStep 2870549 = 134557) (by norm_num)
theorem B2477357 : Blo 1100624 2477357 := bbase (se 3 (by rfl) ⟨464504, by rfl⟩ : syracuseStep 2477357 = 929009) (by norm_num)
theorem B1396045 : Blo 1100624 1396045 := bbase (se 3 (by rfl) ⟨261758, by rfl⟩ : syracuseStep 1396045 = 523517) (by norm_num)
theorem B3722597 : Blo 1100624 3722597 := bbase (se 4 (by rfl) ⟨348993, by rfl⟩ : syracuseStep 3722597 = 697987) (by norm_num)
theorem B2477429 : Blo 1100624 2477429 := bbase (se 5 (by rfl) ⟨116129, by rfl⟩ : syracuseStep 2477429 = 232259) (by norm_num)
theorem B2477501 : Blo 1100624 2477501 := bbase (se 3 (by rfl) ⟨464531, by rfl⟩ : syracuseStep 2477501 = 929063) (by norm_num)
theorem B1396217 : Blo 1100624 1396217 := bbase (se 2 (by rfl) ⟨523581, by rfl⟩ : syracuseStep 1396217 = 1047163) (by norm_num)
theorem B2477573 : Blo 1100624 2477573 := bbase (se 4 (by rfl) ⟨232272, by rfl⟩ : syracuseStep 2477573 = 464545) (by norm_num)
theorem B1396273 : Blo 1100624 1396273 := bbase (se 2 (by rfl) ⟨523602, by rfl⟩ : syracuseStep 1396273 = 1047205) (by norm_num)
theorem B2477645 : Blo 1100624 2477645 := bbase (se 3 (by rfl) ⟨464558, by rfl⟩ : syracuseStep 2477645 = 929117) (by norm_num)
theorem B4705877 : Blo 1100624 4705877 := bbase (se 8 (by rfl) ⟨27573, by rfl⟩ : syracuseStep 4705877 = 55147) (by norm_num)
theorem B6278741 : Blo 1100624 6278741 := bbase (se 8 (by rfl) ⟨36789, by rfl⟩ : syracuseStep 6278741 = 73579) (by norm_num)
theorem B1396369 : Blo 1100624 1396369 := bbase (se 2 (by rfl) ⟨523638, by rfl⟩ : syracuseStep 1396369 = 1047277) (by norm_num)
theorem B2477717 : Blo 1100624 2477717 := bbase (se 6 (by rfl) ⟨58071, by rfl⟩ : syracuseStep 2477717 = 116143) (by norm_num)
theorem B2477789 : Blo 1100624 2477789 := bbase (se 3 (by rfl) ⟨464585, by rfl⟩ : syracuseStep 2477789 = 929171) (by norm_num)
theorem B3723029 : Blo 1100624 3723029 := bbase (se 6 (by rfl) ⟨87258, by rfl⟩ : syracuseStep 3723029 = 174517) (by norm_num)
theorem B2477861 : Blo 1100624 2477861 := bbase (se 4 (by rfl) ⟨232299, by rfl⟩ : syracuseStep 2477861 = 464599) (by norm_num)
theorem B1396541 : Blo 1100624 1396541 := bbase (se 3 (by rfl) ⟨261851, by rfl⟩ : syracuseStep 1396541 = 523703) (by norm_num)
theorem B2477933 : Blo 1100624 2477933 := bbase (se 3 (by rfl) ⟨464612, by rfl⟩ : syracuseStep 2477933 = 929225) (by norm_num)
theorem B1396597 : Blo 1100624 1396597 := bbase (se 5 (by rfl) ⟨65465, by rfl⟩ : syracuseStep 1396597 = 130931) (by norm_num)
theorem B2478005 : Blo 1100624 2478005 := bbase (se 5 (by rfl) ⟨116156, by rfl⟩ : syracuseStep 2478005 = 232313) (by norm_num)
theorem B1396693 : Blo 1100624 1396693 := bbase (se 7 (by rfl) ⟨16367, by rfl⟩ : syracuseStep 1396693 = 32735) (by norm_num)
theorem B1986533 : Blo 1100624 1986533 := bbase (se 4 (by rfl) ⟨186237, by rfl⟩ : syracuseStep 1986533 = 372475) (by norm_num)
theorem B2478077 : Blo 1100624 2478077 := bbase (se 3 (by rfl) ⟨464639, by rfl⟩ : syracuseStep 2478077 = 929279) (by norm_num)
theorem B2478149 : Blo 1100624 2478149 := bbase (se 4 (by rfl) ⟨232326, by rfl⟩ : syracuseStep 2478149 = 464653) (by norm_num)
theorem B1396865 : Blo 1100624 1396865 := bbase (se 2 (by rfl) ⟨523824, by rfl⟩ : syracuseStep 1396865 = 1047649) (by norm_num)
theorem B2478221 : Blo 1100624 2478221 := bbase (se 3 (by rfl) ⟨464666, by rfl⟩ : syracuseStep 2478221 = 929333) (by norm_num)
theorem B1396921 : Blo 1100624 1396921 := bbase (se 2 (by rfl) ⟨523845, by rfl⟩ : syracuseStep 1396921 = 1047691) (by norm_num)
theorem B3723461 : Blo 1100624 3723461 := bbase (se 4 (by rfl) ⟨349074, by rfl⟩ : syracuseStep 3723461 = 698149) (by norm_num)
theorem B2478293 : Blo 1100624 2478293 := bbase (se 7 (by rfl) ⟨29042, by rfl⟩ : syracuseStep 2478293 = 58085) (by norm_num)
theorem B2511125 : Blo 1100624 2511125 := bbase (se 6 (by rfl) ⟨58854, by rfl⟩ : syracuseStep 2511125 = 117709) (by norm_num)
theorem B1397017 : Blo 1100624 1397017 := bbase (se 2 (by rfl) ⟨523881, by rfl⟩ : syracuseStep 1397017 = 1047763) (by norm_num)
theorem B2478365 : Blo 1100624 2478365 := bbase (se 3 (by rfl) ⟨464693, by rfl⟩ : syracuseStep 2478365 = 929387) (by norm_num)
theorem B2478437 : Blo 1100624 2478437 := bbase (se 4 (by rfl) ⟨232353, by rfl⟩ : syracuseStep 2478437 = 464707) (by norm_num)
theorem B1888637 : Blo 1100624 1888637 := bbase (se 3 (by rfl) ⟨354119, by rfl⟩ : syracuseStep 1888637 = 708239) (by norm_num)
theorem B5591429 : Blo 1100624 5591429 := bbase (se 4 (by rfl) ⟨524196, by rfl⟩ : syracuseStep 5591429 = 1048393) (by norm_num)
theorem B3527077 : Blo 1100624 3527077 := bbase (se 4 (by rfl) ⟨330663, by rfl⟩ : syracuseStep 3527077 = 661327) (by norm_num)
theorem B2478509 : Blo 1100624 2478509 := bbase (se 3 (by rfl) ⟨464720, by rfl⟩ : syracuseStep 2478509 = 929441) (by norm_num)
theorem B1397189 : Blo 1100624 1397189 := bbase (se 4 (by rfl) ⟨130986, by rfl⟩ : syracuseStep 1397189 = 261973) (by norm_num)
theorem B2478581 : Blo 1100624 2478581 := bbase (se 5 (by rfl) ⟨116183, by rfl⟩ : syracuseStep 2478581 = 232367) (by norm_num)
theorem B1397245 : Blo 1100624 1397245 := bbase (se 3 (by rfl) ⟨261983, by rfl⟩ : syracuseStep 1397245 = 523967) (by norm_num)
theorem B4706869 : Blo 1100624 4706869 := bbase (se 5 (by rfl) ⟨220634, by rfl⟩ : syracuseStep 4706869 = 441269) (by norm_num)
theorem B2478653 : Blo 1100624 2478653 := bbase (se 3 (by rfl) ⟨464747, by rfl⟩ : syracuseStep 2478653 = 929495) (by norm_num)
theorem B1397341 : Blo 1100624 1397341 := bbase (se 3 (by rfl) ⟨262001, by rfl⟩ : syracuseStep 1397341 = 524003) (by norm_num)
theorem B3723893 : Blo 1100624 3723893 := bbase (se 5 (by rfl) ⟨174557, by rfl⟩ : syracuseStep 3723893 = 349115) (by norm_num)
theorem B2478725 : Blo 1100624 2478725 := bbase (se 4 (by rfl) ⟨232380, by rfl⟩ : syracuseStep 2478725 = 464761) (by norm_num)
theorem B2478797 : Blo 1100624 2478797 := bbase (se 3 (by rfl) ⟨464774, by rfl⟩ : syracuseStep 2478797 = 929549) (by norm_num)
theorem B1594093 : Blo 1100624 1594093 := bbase (se 3 (by rfl) ⟨298892, by rfl⟩ : syracuseStep 1594093 = 597785) (by norm_num)
theorem B1397513 : Blo 1100624 1397513 := bbase (se 2 (by rfl) ⟨524067, by rfl⟩ : syracuseStep 1397513 = 1048135) (by norm_num)
theorem B2478869 : Blo 1100624 2478869 := bbase (se 6 (by rfl) ⟨58098, by rfl⟩ : syracuseStep 2478869 = 116197) (by norm_num)
theorem B1397569 : Blo 1100624 1397569 := bbase (se 2 (by rfl) ⟨524088, by rfl⟩ : syracuseStep 1397569 = 1048177) (by norm_num)
theorem B2478941 : Blo 1100624 2478941 := bbase (se 3 (by rfl) ⟨464801, by rfl⟩ : syracuseStep 2478941 = 929603) (by norm_num)
theorem B1397665 : Blo 1100624 1397665 := bbase (se 2 (by rfl) ⟨524124, by rfl⟩ : syracuseStep 1397665 = 1048249) (by norm_num)
theorem B2479013 : Blo 1100624 2479013 := bbase (se 4 (by rfl) ⟨232407, by rfl⟩ : syracuseStep 2479013 = 464815) (by norm_num)
theorem B2479085 : Blo 1100624 2479085 := bbase (se 3 (by rfl) ⟨464828, by rfl⟩ : syracuseStep 2479085 = 929657) (by norm_num)
theorem B3724325 : Blo 1100624 3724325 := bbase (se 4 (by rfl) ⟨349155, by rfl⟩ : syracuseStep 3724325 = 698311) (by norm_num)
theorem B2479157 : Blo 1100624 2479157 := bbase (se 5 (by rfl) ⟨116210, by rfl⟩ : syracuseStep 2479157 = 232421) (by norm_num)
theorem B4183109 : Blo 1100624 4183109 := bbase (se 4 (by rfl) ⟨392166, by rfl⟩ : syracuseStep 4183109 = 784333) (by norm_num)
theorem B1397837 : Blo 1100624 1397837 := bbase (se 3 (by rfl) ⟨262094, by rfl⟩ : syracuseStep 1397837 = 524189) (by norm_num)
theorem B5657701 : Blo 1100624 5657701 := bbase (se 4 (by rfl) ⟨530409, by rfl⟩ : syracuseStep 5657701 = 1060819) (by norm_num)
theorem B2479229 : Blo 1100624 2479229 := bbase (se 3 (by rfl) ⟨464855, by rfl⟩ : syracuseStep 2479229 = 929711) (by norm_num)
theorem B1397893 : Blo 1100624 1397893 := bbase (se 4 (by rfl) ⟨131052, by rfl⟩ : syracuseStep 1397893 = 262105) (by norm_num)
theorem B2479301 : Blo 1100624 2479301 := bbase (se 4 (by rfl) ⟨232434, by rfl⟩ : syracuseStep 2479301 = 464869) (by norm_num)
theorem B1397989 : Blo 1100624 1397989 := bbase (se 4 (by rfl) ⟨131061, by rfl⟩ : syracuseStep 1397989 = 262123) (by norm_num)
theorem B2512117 : Blo 1100624 2512117 := bbase (se 5 (by rfl) ⟨117755, by rfl⟩ : syracuseStep 2512117 = 235511) (by norm_num)
theorem B2479373 : Blo 1100624 2479373 := bbase (se 3 (by rfl) ⟨464882, by rfl⟩ : syracuseStep 2479373 = 929765) (by norm_num)
theorem B3626293 : Blo 1100624 3626293 := bbase (se 5 (by rfl) ⟨169982, by rfl⟩ : syracuseStep 3626293 = 339965) (by norm_num)
theorem B2479445 : Blo 1100624 2479445 := bbase (se 15 (by rfl) ⟨113, by rfl⟩ : syracuseStep 2479445 = 227) (by norm_num)
theorem B4183397 : Blo 1100624 4183397 := bbase (se 4 (by rfl) ⟨392193, by rfl⟩ : syracuseStep 4183397 = 784387) (by norm_num)
theorem B3134837 : Blo 1100624 3134837 := bbase (se 5 (by rfl) ⟨146945, by rfl⟩ : syracuseStep 3134837 = 293891) (by norm_num)
theorem B7853429 : Blo 1100624 7853429 := bbase (se 5 (by rfl) ⟨368129, by rfl⟩ : syracuseStep 7853429 = 736259) (by norm_num)
theorem B2479517 : Blo 1100624 2479517 := bbase (se 3 (by rfl) ⟨464909, by rfl⟩ : syracuseStep 2479517 = 929819) (by norm_num)
theorem B2512309 : Blo 1100624 2512309 := bbase (se 5 (by rfl) ⟨117764, by rfl⟩ : syracuseStep 2512309 = 235529) (by norm_num)
theorem B3724757 : Blo 1100624 3724757 := bbase (se 7 (by rfl) ⟨43649, by rfl⟩ : syracuseStep 3724757 = 87299) (by norm_num)
theorem B2479589 : Blo 1100624 2479589 := bbase (se 4 (by rfl) ⟨232461, by rfl⟩ : syracuseStep 2479589 = 464923) (by norm_num)
theorem B13391381 : Blo 1100624 13391381 := bbase (se 6 (by rfl) ⟨313860, by rfl⟩ : syracuseStep 13391381 = 627721) (by norm_num)
theorem B2479661 : Blo 1100624 2479661 := bbase (se 3 (by rfl) ⟨464936, by rfl⟩ : syracuseStep 2479661 = 929873) (by norm_num)
theorem B2152021 : Blo 1100624 2152021 := bbase (se 8 (by rfl) ⟨12609, by rfl⟩ : syracuseStep 2152021 = 25219) (by norm_num)
theorem B2479733 : Blo 1100624 2479733 := bbase (se 5 (by rfl) ⟨116237, by rfl⟩ : syracuseStep 2479733 = 232475) (by norm_num)
theorem B1791653 : Blo 1100624 1791653 := bbase (se 4 (by rfl) ⟨167967, by rfl⟩ : syracuseStep 1791653 = 335935) (by norm_num)
theorem B2479805 : Blo 1100624 2479805 := bbase (se 3 (by rfl) ⟨464963, by rfl⟩ : syracuseStep 2479805 = 929927) (by norm_num)
theorem B2479877 : Blo 1100624 2479877 := bbase (se 4 (by rfl) ⟨232488, by rfl⟩ : syracuseStep 2479877 = 464977) (by norm_num)
theorem B5297957 : Blo 1100624 5297957 := bbase (se 4 (by rfl) ⟨496683, by rfl⟩ : syracuseStep 5297957 = 993367) (by norm_num)
theorem B2479949 : Blo 1100624 2479949 := bbase (se 3 (by rfl) ⟨464990, by rfl⟩ : syracuseStep 2479949 = 929981) (by norm_num)
theorem B1857397 : Blo 1100624 1857397 := bbase (se 5 (by rfl) ⟨87065, by rfl⟩ : syracuseStep 1857397 = 174131) (by norm_num)
theorem B3725189 : Blo 1100624 3725189 := bbase (se 4 (by rfl) ⟨349236, by rfl⟩ : syracuseStep 3725189 = 698473) (by norm_num)
theorem B2480021 : Blo 1100624 2480021 := bbase (se 6 (by rfl) ⟨58125, by rfl⟩ : syracuseStep 2480021 = 116251) (by norm_num)
theorem B1857485 : Blo 1100624 1857485 := bbase (se 3 (by rfl) ⟨348278, by rfl⟩ : syracuseStep 1857485 = 696557) (by norm_num)
theorem B2480093 : Blo 1100624 2480093 := bbase (se 3 (by rfl) ⟨465017, by rfl⟩ : syracuseStep 2480093 = 930035) (by norm_num)
theorem B2480165 : Blo 1100624 2480165 := bbase (se 4 (by rfl) ⟨232515, by rfl⟩ : syracuseStep 2480165 = 465031) (by norm_num)
theorem B1857613 : Blo 1100624 1857613 := bbase (se 3 (by rfl) ⟨348302, by rfl⟩ : syracuseStep 1857613 = 696605) (by norm_num)
theorem B2480237 : Blo 1100624 2480237 := bbase (se 3 (by rfl) ⟨465044, by rfl⟩ : syracuseStep 2480237 = 930089) (by norm_num)
theorem B1857701 : Blo 1100624 1857701 := bbase (se 4 (by rfl) ⟨174159, by rfl⟩ : syracuseStep 1857701 = 348319) (by norm_num)
theorem B2480309 : Blo 1100624 2480309 := bbase (se 5 (by rfl) ⟨116264, by rfl⟩ : syracuseStep 2480309 = 232529) (by norm_num)
theorem B2480381 : Blo 1100624 2480381 := bbase (se 3 (by rfl) ⟨465071, by rfl⟩ : syracuseStep 2480381 = 930143) (by norm_num)
theorem B1857829 : Blo 1100624 1857829 := bbase (se 4 (by rfl) ⟨174171, by rfl⟩ : syracuseStep 1857829 = 348343) (by norm_num)
theorem B3725621 : Blo 1100624 3725621 := bbase (se 5 (by rfl) ⟨174638, by rfl⟩ : syracuseStep 3725621 = 349277) (by norm_num)
theorem B2480453 : Blo 1100624 2480453 := bbase (se 4 (by rfl) ⟨232542, by rfl⟩ : syracuseStep 2480453 = 465085) (by norm_num)
theorem B1857917 : Blo 1100624 1857917 := bbase (se 3 (by rfl) ⟨348359, by rfl⟩ : syracuseStep 1857917 = 696719) (by norm_num)
theorem B2480525 : Blo 1100624 2480525 := bbase (se 3 (by rfl) ⟨465098, by rfl⟩ : syracuseStep 2480525 = 930197) (by norm_num)
theorem B2480597 : Blo 1100624 2480597 := bbase (se 7 (by rfl) ⟨29069, by rfl⟩ : syracuseStep 2480597 = 58139) (by norm_num)
theorem B1858045 : Blo 1100624 1858045 := bbase (se 3 (by rfl) ⟨348383, by rfl⟩ : syracuseStep 1858045 = 696767) (by norm_num)
theorem B2513405 : Blo 1100624 2513405 := bbase (se 3 (by rfl) ⟨471263, by rfl⟩ : syracuseStep 2513405 = 942527) (by norm_num)
theorem B4184581 : Blo 1100624 4184581 := bbase (se 4 (by rfl) ⟨392304, by rfl⟩ : syracuseStep 4184581 = 784609) (by norm_num)
theorem B2480669 : Blo 1100624 2480669 := bbase (se 3 (by rfl) ⟨465125, by rfl⟩ : syracuseStep 2480669 = 930251) (by norm_num)
theorem B1989157 : Blo 1100624 1989157 := bbase (se 4 (by rfl) ⟨186483, by rfl⟩ : syracuseStep 1989157 = 372967) (by norm_num)
theorem B1858133 : Blo 1100624 1858133 := bbase (se 8 (by rfl) ⟨10887, by rfl⟩ : syracuseStep 1858133 = 21775) (by norm_num)
theorem B2480741 : Blo 1100624 2480741 := bbase (se 4 (by rfl) ⟨232569, by rfl⟩ : syracuseStep 2480741 = 465139) (by norm_num)
theorem B1432205 : Blo 1100624 1432205 := bbase (se 3 (by rfl) ⟨268538, by rfl⟩ : syracuseStep 1432205 = 537077) (by norm_num)
theorem B2480813 : Blo 1100624 2480813 := bbase (se 3 (by rfl) ⟨465152, by rfl⟩ : syracuseStep 2480813 = 930305) (by norm_num)
theorem B1989301 : Blo 1100624 1989301 := bbase (se 5 (by rfl) ⟨93248, by rfl⟩ : syracuseStep 1989301 = 186497) (by norm_num)
theorem B1858261 : Blo 1100624 1858261 := bbase (se 7 (by rfl) ⟨21776, by rfl⟩ : syracuseStep 1858261 = 43553) (by norm_num)
theorem B3627733 : Blo 1100624 3627733 := bbase (se 7 (by rfl) ⟨42512, by rfl⟩ : syracuseStep 3627733 = 85025) (by norm_num)
theorem B3726053 : Blo 1100624 3726053 := bbase (se 4 (by rfl) ⟨349317, by rfl⟩ : syracuseStep 3726053 = 698635) (by norm_num)
theorem B2480885 : Blo 1100624 2480885 := bbase (se 5 (by rfl) ⟨116291, by rfl⟩ : syracuseStep 2480885 = 232583) (by norm_num)
theorem B8379125 : Blo 1100624 8379125 := bbase (se 5 (by rfl) ⟨392771, by rfl⟩ : syracuseStep 8379125 = 785543) (by norm_num)
theorem B1858349 : Blo 1100624 1858349 := bbase (se 3 (by rfl) ⟨348440, by rfl⟩ : syracuseStep 1858349 = 696881) (by norm_num)
theorem B4184885 : Blo 1100624 4184885 := bbase (se 5 (by rfl) ⟨196166, by rfl⟩ : syracuseStep 4184885 = 392333) (by norm_num)
theorem B2480957 : Blo 1100624 2480957 := bbase (se 3 (by rfl) ⟨465179, by rfl⟩ : syracuseStep 2480957 = 930359) (by norm_num)
theorem B2481029 : Blo 1100624 2481029 := bbase (se 4 (by rfl) ⟨232596, by rfl⟩ : syracuseStep 2481029 = 465193) (by norm_num)
theorem B1792901 : Blo 1100624 1792901 := bbase (se 4 (by rfl) ⟨168084, by rfl⟩ : syracuseStep 1792901 = 336169) (by norm_num)
theorem B1989517 : Blo 1100624 1989517 := bbase (se 3 (by rfl) ⟨373034, by rfl⟩ : syracuseStep 1989517 = 746069) (by norm_num)
theorem B3136421 : Blo 1100624 3136421 := bbase (se 4 (by rfl) ⟨294039, by rfl⟩ : syracuseStep 3136421 = 588079) (by norm_num)
theorem B1858477 : Blo 1100624 1858477 := bbase (se 3 (by rfl) ⟨348464, by rfl⟩ : syracuseStep 1858477 = 696929) (by norm_num)
theorem B2481101 : Blo 1100624 2481101 := bbase (se 3 (by rfl) ⟨465206, by rfl⟩ : syracuseStep 2481101 = 930413) (by norm_num)
theorem B1858565 : Blo 1100624 1858565 := bbase (se 4 (by rfl) ⟨174240, by rfl⟩ : syracuseStep 1858565 = 348481) (by norm_num)
theorem B2481173 : Blo 1100624 2481173 := bbase (se 6 (by rfl) ⟨58152, by rfl⟩ : syracuseStep 2481173 = 116305) (by norm_num)
theorem B9428021 : Blo 1100624 9428021 := bbase (se 5 (by rfl) ⟨441938, by rfl⟩ : syracuseStep 9428021 = 883877) (by norm_num)
theorem B2481245 : Blo 1100624 2481245 := bbase (se 3 (by rfl) ⟨465233, by rfl⟩ : syracuseStep 2481245 = 930467) (by norm_num)
theorem B1858693 : Blo 1100624 1858693 := bbase (se 4 (by rfl) ⟨174252, by rfl⟩ : syracuseStep 1858693 = 348505) (by norm_num)
theorem B3726485 : Blo 1100624 3726485 := bbase (se 6 (by rfl) ⟨87339, by rfl⟩ : syracuseStep 3726485 = 174679) (by norm_num)
theorem B2481317 : Blo 1100624 2481317 := bbase (se 4 (by rfl) ⟨232623, by rfl⟩ : syracuseStep 2481317 = 465247) (by norm_num)
theorem B2645173 : Blo 1100624 2645173 := bbase (se 5 (by rfl) ⟨123992, by rfl⟩ : syracuseStep 2645173 = 247985) (by norm_num)
theorem B3529909 : Blo 1100624 3529909 := bbase (se 5 (by rfl) ⟨165464, by rfl⟩ : syracuseStep 3529909 = 330929) (by norm_num)
theorem B1858781 : Blo 1100624 1858781 := bbase (se 3 (by rfl) ⟨348521, by rfl⟩ : syracuseStep 1858781 = 697043) (by norm_num)
theorem B2481389 : Blo 1100624 2481389 := bbase (se 3 (by rfl) ⟨465260, by rfl⟩ : syracuseStep 2481389 = 930521) (by norm_num)
theorem B3529973 : Blo 1100624 3529973 := bbase (se 5 (by rfl) ⟨165467, by rfl⟩ : syracuseStep 3529973 = 330935) (by norm_num)
theorem B2481461 : Blo 1100624 2481461 := bbase (se 5 (by rfl) ⟨116318, by rfl⟩ : syracuseStep 2481461 = 232637) (by norm_num)
theorem B1858909 : Blo 1100624 1858909 := bbase (se 3 (by rfl) ⟨348545, by rfl⟩ : syracuseStep 1858909 = 697091) (by norm_num)
theorem B2645365 : Blo 1100624 2645365 := bbase (se 5 (by rfl) ⟨124001, by rfl⟩ : syracuseStep 2645365 = 248003) (by norm_num)
theorem B2481533 : Blo 1100624 2481533 := bbase (se 3 (by rfl) ⟨465287, by rfl⟩ : syracuseStep 2481533 = 930575) (by norm_num)
theorem B5037461 : Blo 1100624 5037461 := bbase (se 6 (by rfl) ⟨118065, by rfl⟩ : syracuseStep 5037461 = 236131) (by norm_num)
theorem B2645405 : Blo 1100624 2645405 := bbase (se 3 (by rfl) ⟨496013, by rfl⟩ : syracuseStep 2645405 = 992027) (by norm_num)
theorem B1858997 : Blo 1100624 1858997 := bbase (se 5 (by rfl) ⟨87140, by rfl⟩ : syracuseStep 1858997 = 174281) (by norm_num)
theorem B2481605 : Blo 1100624 2481605 := bbase (se 4 (by rfl) ⟨232650, by rfl⟩ : syracuseStep 2481605 = 465301) (by norm_num)
theorem B2579941 : Blo 1100624 2579941 := bbase (se 4 (by rfl) ⟨241869, by rfl⟩ : syracuseStep 2579941 = 483739) (by norm_num)
theorem B2481677 : Blo 1100624 2481677 := bbase (se 3 (by rfl) ⟨465314, by rfl⟩ : syracuseStep 2481677 = 930629) (by norm_num)
theorem B1859125 : Blo 1100624 1859125 := bbase (se 5 (by rfl) ⟨87146, by rfl⟩ : syracuseStep 1859125 = 174293) (by norm_num)
theorem B3137093 : Blo 1100624 3137093 := bbase (se 4 (by rfl) ⟨294102, by rfl⟩ : syracuseStep 3137093 = 588205) (by norm_num)
theorem B3726917 : Blo 1100624 3726917 := bbase (se 4 (by rfl) ⟨349398, by rfl⟩ : syracuseStep 3726917 = 698797) (by norm_num)
theorem B2481749 : Blo 1100624 2481749 := bbase (se 8 (by rfl) ⟨14541, by rfl⟩ : syracuseStep 2481749 = 29083) (by norm_num)
theorem B1859213 : Blo 1100624 1859213 := bbase (se 3 (by rfl) ⟨348602, by rfl⟩ : syracuseStep 1859213 = 697205) (by norm_num)
theorem B2481821 : Blo 1100624 2481821 := bbase (se 3 (by rfl) ⟨465341, by rfl⟩ : syracuseStep 2481821 = 930683) (by norm_num)
theorem B1990325 : Blo 1100624 1990325 := bbase (se 5 (by rfl) ⟨93296, by rfl⟩ : syracuseStep 1990325 = 186593) (by norm_num)
theorem B2645693 : Blo 1100624 2645693 := bbase (se 3 (by rfl) ⟨496067, by rfl⟩ : syracuseStep 2645693 = 992135) (by norm_num)
theorem B2481893 : Blo 1100624 2481893 := bbase (se 4 (by rfl) ⟨232677, by rfl⟩ : syracuseStep 2481893 = 465355) (by norm_num)
theorem B1859341 : Blo 1100624 1859341 := bbase (se 3 (by rfl) ⟨348626, by rfl⟩ : syracuseStep 1859341 = 697253) (by norm_num)
theorem B2481965 : Blo 1100624 2481965 := bbase (se 3 (by rfl) ⟨465368, by rfl⟩ : syracuseStep 2481965 = 930737) (by norm_num)
theorem B1859429 : Blo 1100624 1859429 := bbase (se 4 (by rfl) ⟨174321, by rfl⟩ : syracuseStep 1859429 = 348643) (by norm_num)
theorem B2350957 : Blo 1100624 2350957 := bbase (se 3 (by rfl) ⟨440804, by rfl⟩ : syracuseStep 2350957 = 881609) (by norm_num)
theorem B2482037 : Blo 1100624 2482037 := bbase (se 5 (by rfl) ⟨116345, by rfl⟩ : syracuseStep 2482037 = 232691) (by norm_num)
theorem B2514845 : Blo 1100624 2514845 := bbase (se 3 (by rfl) ⟨471533, by rfl⟩ : syracuseStep 2514845 = 943067) (by norm_num)
theorem B5300149 : Blo 1100624 5300149 := bbase (se 5 (by rfl) ⟨248444, by rfl⟩ : syracuseStep 5300149 = 496889) (by norm_num)
theorem B2482109 : Blo 1100624 2482109 := bbase (se 3 (by rfl) ⟨465395, by rfl⟩ : syracuseStep 2482109 = 930791) (by norm_num)
theorem B1859557 : Blo 1100624 1859557 := bbase (se 4 (by rfl) ⟨174333, by rfl⟩ : syracuseStep 1859557 = 348667) (by norm_num)
theorem B3137525 : Blo 1100624 3137525 := bbase (se 5 (by rfl) ⟨147071, by rfl⟩ : syracuseStep 3137525 = 294143) (by norm_num)
theorem B3727349 : Blo 1100624 3727349 := bbase (se 5 (by rfl) ⟨174719, by rfl⟩ : syracuseStep 3727349 = 349439) (by norm_num)
theorem B2482181 : Blo 1100624 2482181 := bbase (se 4 (by rfl) ⟨232704, by rfl⟩ : syracuseStep 2482181 = 465409) (by norm_num)
theorem B2154533 : Blo 1100624 2154533 := bbase (se 4 (by rfl) ⟨201987, by rfl⟩ : syracuseStep 2154533 = 403975) (by norm_num)
theorem B1859645 : Blo 1100624 1859645 := bbase (se 3 (by rfl) ⟨348683, by rfl⟩ : syracuseStep 1859645 = 697367) (by norm_num)
theorem B2482253 : Blo 1100624 2482253 := bbase (se 3 (by rfl) ⟨465422, by rfl⟩ : syracuseStep 2482253 = 930845) (by norm_num)
theorem B2384005 : Blo 1100624 2384005 := bbase (se 4 (by rfl) ⟨223500, by rfl⟩ : syracuseStep 2384005 = 447001) (by norm_num)
theorem B2482325 : Blo 1100624 2482325 := bbase (se 6 (by rfl) ⟨58179, by rfl⟩ : syracuseStep 2482325 = 116359) (by norm_num)
theorem B1859773 : Blo 1100624 1859773 := bbase (se 3 (by rfl) ⟨348707, by rfl⟩ : syracuseStep 1859773 = 697415) (by norm_num)
theorem B2482397 : Blo 1100624 2482397 := bbase (se 3 (by rfl) ⟨465449, by rfl⟩ : syracuseStep 2482397 = 930899) (by norm_num)
theorem B1859861 : Blo 1100624 1859861 := bbase (se 6 (by rfl) ⟨43590, by rfl⟩ : syracuseStep 1859861 = 87181) (by norm_num)
theorem B2482469 : Blo 1100624 2482469 := bbase (se 4 (by rfl) ⟨232731, by rfl⟩ : syracuseStep 2482469 = 465463) (by norm_num)
theorem B5661029 : Blo 1100624 5661029 := bbase (se 4 (by rfl) ⟨530721, by rfl⟩ : syracuseStep 5661029 = 1061443) (by norm_num)
theorem B2482541 : Blo 1100624 2482541 := bbase (se 3 (by rfl) ⟨465476, by rfl⟩ : syracuseStep 2482541 = 930953) (by norm_num)
theorem B1859989 : Blo 1100624 1859989 := bbase (se 6 (by rfl) ⟨43593, by rfl⟩ : syracuseStep 1859989 = 87187) (by norm_num)
theorem B3727781 : Blo 1100624 3727781 := bbase (se 4 (by rfl) ⟨349479, by rfl⟩ : syracuseStep 3727781 = 698959) (by norm_num)
theorem B2482613 : Blo 1100624 2482613 := bbase (se 5 (by rfl) ⟨116372, by rfl⟩ : syracuseStep 2482613 = 232745) (by norm_num)
theorem B1860077 : Blo 1100624 1860077 := bbase (se 3 (by rfl) ⟨348764, by rfl⟩ : syracuseStep 1860077 = 697529) (by norm_num)
theorem B2482685 : Blo 1100624 2482685 := bbase (se 3 (by rfl) ⟨465503, by rfl⟩ : syracuseStep 2482685 = 931007) (by norm_num)
theorem B13591061 : Blo 1100624 13591061 := bbase (se 6 (by rfl) ⟨318540, by rfl⟩ : syracuseStep 13591061 = 637081) (by norm_num)
theorem B2122309 : Blo 1100624 2122309 := bbase (se 4 (by rfl) ⟨198966, by rfl⟩ : syracuseStep 2122309 = 397933) (by norm_num)
theorem B2482757 : Blo 1100624 2482757 := bbase (se 4 (by rfl) ⟨232758, by rfl⟩ : syracuseStep 2482757 = 465517) (by norm_num)
theorem B1860205 : Blo 1100624 1860205 := bbase (se 3 (by rfl) ⟨348788, by rfl⟩ : syracuseStep 1860205 = 697577) (by norm_num)
theorem B2482829 : Blo 1100624 2482829 := bbase (se 3 (by rfl) ⟨465530, by rfl⟩ : syracuseStep 2482829 = 931061) (by norm_num)
theorem B1860293 : Blo 1100624 1860293 := bbase (se 4 (by rfl) ⟨174402, by rfl⟩ : syracuseStep 1860293 = 348805) (by norm_num)
theorem B2482901 : Blo 1100624 2482901 := bbase (se 7 (by rfl) ⟨29096, by rfl⟩ : syracuseStep 2482901 = 58193) (by norm_num)
theorem B2351845 : Blo 1100624 2351845 := bbase (se 4 (by rfl) ⟨220485, by rfl⟩ : syracuseStep 2351845 = 440971) (by norm_num)
theorem B3138277 : Blo 1100624 3138277 := bbase (se 4 (by rfl) ⟨294213, by rfl⟩ : syracuseStep 3138277 = 588427) (by norm_num)
theorem B2089709 : Blo 1100624 2089709 := bbase (se 3 (by rfl) ⟨391820, by rfl⟩ : syracuseStep 2089709 = 783641) (by norm_num)
theorem B2482973 : Blo 1100624 2482973 := bbase (se 3 (by rfl) ⟨465557, by rfl⟩ : syracuseStep 2482973 = 931115) (by norm_num)
theorem B1860421 : Blo 1100624 1860421 := bbase (se 4 (by rfl) ⟨174414, by rfl⟩ : syracuseStep 1860421 = 348829) (by norm_num)
theorem B2483045 : Blo 1100624 2483045 := bbase (se 4 (by rfl) ⟨232785, by rfl⟩ : syracuseStep 2483045 = 465571) (by norm_num)
theorem B4186997 : Blo 1100624 4186997 := bbase (se 5 (by rfl) ⟨196265, by rfl⟩ : syracuseStep 4186997 = 392531) (by norm_num)
theorem B1860509 : Blo 1100624 1860509 := bbase (se 3 (by rfl) ⟨348845, by rfl⟩ : syracuseStep 1860509 = 697691) (by norm_num)
theorem B2483117 : Blo 1100624 2483117 := bbase (se 3 (by rfl) ⟨465584, by rfl⟩ : syracuseStep 2483117 = 931169) (by norm_num)
theorem B22668245 : Blo 1100624 22668245 := bbase (se 7 (by rfl) ⟨265643, by rfl⟩ : syracuseStep 22668245 = 531287) (by norm_num)
theorem B2483189 : Blo 1100624 2483189 := bbase (se 5 (by rfl) ⟨116399, by rfl⟩ : syracuseStep 2483189 = 232799) (by norm_num)
theorem B1860637 : Blo 1100624 1860637 := bbase (se 3 (by rfl) ⟨348869, by rfl⟩ : syracuseStep 1860637 = 697739) (by norm_num)
theorem B2483261 : Blo 1100624 2483261 := bbase (se 3 (by rfl) ⟨465611, by rfl⟩ : syracuseStep 2483261 = 931223) (by norm_num)
theorem B1860725 : Blo 1100624 1860725 := bbase (se 5 (by rfl) ⟨87221, by rfl⟩ : syracuseStep 1860725 = 174443) (by norm_num)
theorem B2483333 : Blo 1100624 2483333 := bbase (se 4 (by rfl) ⟨232812, by rfl⟩ : syracuseStep 2483333 = 465625) (by norm_num)
theorem B4187285 : Blo 1100624 4187285 := bbase (se 6 (by rfl) ⟨98139, by rfl⟩ : syracuseStep 4187285 = 196279) (by norm_num)
theorem B2483405 : Blo 1100624 2483405 := bbase (se 3 (by rfl) ⟨465638, by rfl⟩ : syracuseStep 2483405 = 931277) (by norm_num)
theorem B2352341 : Blo 1100624 2352341 := bbase (se 7 (by rfl) ⟨27566, by rfl⟩ : syracuseStep 2352341 = 55133) (by norm_num)
theorem B1238233 : Blo 1100624 1238233 := bbase (se 2 (by rfl) ⟨464337, by rfl⟩ : syracuseStep 1238233 = 928675) (by norm_num)
theorem B1860853 : Blo 1100624 1860853 := bbase (se 5 (by rfl) ⟨87227, by rfl⟩ : syracuseStep 1860853 = 174455) (by norm_num)
theorem B1238269 : Blo 1100624 1238269 := bbase (se 3 (by rfl) ⟨232175, by rfl⟩ : syracuseStep 1238269 = 464351) (by norm_num)
theorem B2483477 : Blo 1100624 2483477 := bbase (se 6 (by rfl) ⟨58206, by rfl⟩ : syracuseStep 2483477 = 116413) (by norm_num)
theorem B1238305 : Blo 1100624 1238305 := bbase (se 2 (by rfl) ⟨464364, by rfl⟩ : syracuseStep 1238305 = 928729) (by norm_num)
theorem B2516285 : Blo 1100624 2516285 := bbase (se 3 (by rfl) ⟨471803, by rfl⟩ : syracuseStep 2516285 = 943607) (by norm_num)
theorem B1238341 : Blo 1100624 1238341 := bbase (se 4 (by rfl) ⟨116094, by rfl⟩ : syracuseStep 1238341 = 232189) (by norm_num)
theorem B1860941 : Blo 1100624 1860941 := bbase (se 3 (by rfl) ⟨348926, by rfl⟩ : syracuseStep 1860941 = 697853) (by norm_num)
theorem B2483549 : Blo 1100624 2483549 := bbase (se 3 (by rfl) ⟨465665, by rfl⟩ : syracuseStep 2483549 = 931331) (by norm_num)
theorem B1238377 : Blo 1100624 1238377 := bbase (se 2 (by rfl) ⟨464391, by rfl⟩ : syracuseStep 1238377 = 928783) (by norm_num)
theorem B1238413 : Blo 1100624 1238413 := bbase (se 3 (by rfl) ⟨232202, by rfl⟩ : syracuseStep 1238413 = 464405) (by norm_num)
theorem B2483621 : Blo 1100624 2483621 := bbase (se 4 (by rfl) ⟨232839, by rfl⟩ : syracuseStep 2483621 = 465679) (by norm_num)
theorem B1238449 : Blo 1100624 1238449 := bbase (se 2 (by rfl) ⟨464418, by rfl⟩ : syracuseStep 1238449 = 928837) (by norm_num)
theorem B4711877 : Blo 1100624 4711877 := bbase (se 4 (by rfl) ⟨441738, by rfl⟩ : syracuseStep 4711877 = 883477) (by norm_num)
theorem B1861069 : Blo 1100624 1861069 := bbase (se 3 (by rfl) ⟨348950, by rfl⟩ : syracuseStep 1861069 = 697901) (by norm_num)
theorem B1238485 : Blo 1100624 1238485 := bbase (se 7 (by rfl) ⟨14513, by rfl⟩ : syracuseStep 1238485 = 29027) (by norm_num)
theorem B2090461 : Blo 1100624 2090461 := bbase (se 3 (by rfl) ⟨391961, by rfl⟩ : syracuseStep 2090461 = 783923) (by norm_num)
theorem B2483693 : Blo 1100624 2483693 := bbase (se 3 (by rfl) ⟨465692, by rfl⟩ : syracuseStep 2483693 = 931385) (by norm_num)
theorem B1238521 : Blo 1100624 1238521 := bbase (se 2 (by rfl) ⟨464445, by rfl⟩ : syracuseStep 1238521 = 928891) (by norm_num)
theorem B1238557 : Blo 1100624 1238557 := bbase (se 3 (by rfl) ⟨232229, by rfl⟩ : syracuseStep 1238557 = 464459) (by norm_num)
theorem B1861157 : Blo 1100624 1861157 := bbase (se 4 (by rfl) ⟨174483, by rfl⟩ : syracuseStep 1861157 = 348967) (by norm_num)
theorem B2483765 : Blo 1100624 2483765 := bbase (se 5 (by rfl) ⟨116426, by rfl⟩ : syracuseStep 2483765 = 232853) (by norm_num)
theorem B1238593 : Blo 1100624 1238593 := bbase (se 2 (by rfl) ⟨464472, by rfl⟩ : syracuseStep 1238593 = 928945) (by norm_num)
theorem B1238629 : Blo 1100624 1238629 := bbase (se 4 (by rfl) ⟨116121, by rfl⟩ : syracuseStep 1238629 = 232243) (by norm_num)
theorem B2090605 : Blo 1100624 2090605 := bbase (se 3 (by rfl) ⟨391988, by rfl⟩ : syracuseStep 2090605 = 783977) (by norm_num)
theorem B2483837 : Blo 1100624 2483837 := bbase (se 3 (by rfl) ⟨465719, by rfl⟩ : syracuseStep 2483837 = 931439) (by norm_num)
theorem B1238665 : Blo 1100624 1238665 := bbase (se 2 (by rfl) ⟨464499, by rfl⟩ : syracuseStep 1238665 = 928999) (by norm_num)
theorem B1861285 : Blo 1100624 1861285 := bbase (se 4 (by rfl) ⟨174495, by rfl⟩ : syracuseStep 1861285 = 348991) (by norm_num)
theorem B1238701 : Blo 1100624 1238701 := bbase (se 3 (by rfl) ⟨232256, by rfl⟩ : syracuseStep 1238701 = 464513) (by norm_num)
theorem B2483909 : Blo 1100624 2483909 := bbase (se 4 (by rfl) ⟨232866, by rfl⟩ : syracuseStep 2483909 = 465733) (by norm_num)
theorem B1238737 : Blo 1100624 1238737 := bbase (se 2 (by rfl) ⟨464526, by rfl⟩ : syracuseStep 1238737 = 929053) (by norm_num)
theorem B4712165 : Blo 1100624 4712165 := bbase (se 4 (by rfl) ⟨441765, by rfl⟩ : syracuseStep 4712165 = 883531) (by norm_num)
theorem B1238773 : Blo 1100624 1238773 := bbase (se 5 (by rfl) ⟨58067, by rfl⟩ : syracuseStep 1238773 = 116135) (by norm_num)
theorem B1861373 : Blo 1100624 1861373 := bbase (se 3 (by rfl) ⟨349007, by rfl⟩ : syracuseStep 1861373 = 698015) (by norm_num)
theorem B2090765 : Blo 1100624 2090765 := bbase (se 3 (by rfl) ⟨392018, by rfl⟩ : syracuseStep 2090765 = 784037) (by norm_num)
theorem B2483981 : Blo 1100624 2483981 := bbase (se 3 (by rfl) ⟨465746, by rfl⟩ : syracuseStep 2483981 = 931493) (by norm_num)
theorem B1238809 : Blo 1100624 1238809 := bbase (se 2 (by rfl) ⟨464553, by rfl⟩ : syracuseStep 1238809 = 929107) (by norm_num)
theorem B1238845 : Blo 1100624 1238845 := bbase (se 3 (by rfl) ⟨232283, by rfl⟩ : syracuseStep 1238845 = 464567) (by norm_num)
theorem B2484053 : Blo 1100624 2484053 := bbase (se 9 (by rfl) ⟨7277, by rfl⟩ : syracuseStep 2484053 = 14555) (by norm_num)
theorem B1238881 : Blo 1100624 1238881 := bbase (se 2 (by rfl) ⟨464580, by rfl⟩ : syracuseStep 1238881 = 929161) (by norm_num)
theorem B1861501 : Blo 1100624 1861501 := bbase (se 3 (by rfl) ⟨349031, by rfl⟩ : syracuseStep 1861501 = 698063) (by norm_num)
theorem B1238917 : Blo 1100624 1238917 := bbase (se 4 (by rfl) ⟨116148, by rfl⟩ : syracuseStep 1238917 = 232297) (by norm_num)
theorem B2090909 : Blo 1100624 2090909 := bbase (se 3 (by rfl) ⟨392045, by rfl⟩ : syracuseStep 2090909 = 784091) (by norm_num)
theorem B2484125 : Blo 1100624 2484125 := bbase (se 3 (by rfl) ⟨465773, by rfl⟩ : syracuseStep 2484125 = 931547) (by norm_num)
theorem B1238953 : Blo 1100624 1238953 := bbase (se 2 (by rfl) ⟨464607, by rfl⟩ : syracuseStep 1238953 = 929215) (by norm_num)
theorem B1238989 : Blo 1100624 1238989 := bbase (se 3 (by rfl) ⟨232310, by rfl⟩ : syracuseStep 1238989 = 464621) (by norm_num)
theorem B1861589 : Blo 1100624 1861589 := bbase (se 7 (by rfl) ⟨21815, by rfl⟩ : syracuseStep 1861589 = 43631) (by norm_num)
theorem B2484197 : Blo 1100624 2484197 := bbase (se 4 (by rfl) ⟨232893, by rfl⟩ : syracuseStep 2484197 = 465787) (by norm_num)
theorem B1239025 : Blo 1100624 1239025 := bbase (se 2 (by rfl) ⟨464634, by rfl⟩ : syracuseStep 1239025 = 929269) (by norm_num)
theorem B1239061 : Blo 1100624 1239061 := bbase (se 6 (by rfl) ⟨29040, by rfl⟩ : syracuseStep 1239061 = 58081) (by norm_num)
theorem B2484269 : Blo 1100624 2484269 := bbase (se 3 (by rfl) ⟨465800, by rfl⟩ : syracuseStep 2484269 = 931601) (by norm_num)
theorem B2353205 : Blo 1100624 2353205 := bbase (se 5 (by rfl) ⟨110306, by rfl⟩ : syracuseStep 2353205 = 220613) (by norm_num)
theorem B1239097 : Blo 1100624 1239097 := bbase (se 2 (by rfl) ⟨464661, by rfl⟩ : syracuseStep 1239097 = 929323) (by norm_num)
theorem B1861717 : Blo 1100624 1861717 := bbase (se 8 (by rfl) ⟨10908, by rfl⟩ : syracuseStep 1861717 = 21817) (by norm_num)
theorem B1239133 : Blo 1100624 1239133 := bbase (se 3 (by rfl) ⟨232337, by rfl⟩ : syracuseStep 1239133 = 464675) (by norm_num)
theorem B2484341 : Blo 1100624 2484341 := bbase (se 5 (by rfl) ⟨116453, by rfl⟩ : syracuseStep 2484341 = 232907) (by norm_num)
theorem B1239169 : Blo 1100624 1239169 := bbase (se 2 (by rfl) ⟨464688, by rfl⟩ : syracuseStep 1239169 = 929377) (by norm_num)
theorem B1239205 : Blo 1100624 1239205 := bbase (se 4 (by rfl) ⟨116175, by rfl⟩ : syracuseStep 1239205 = 232351) (by norm_num)
theorem B1861805 : Blo 1100624 1861805 := bbase (se 3 (by rfl) ⟨349088, by rfl⟩ : syracuseStep 1861805 = 698177) (by norm_num)
theorem B2091197 : Blo 1100624 2091197 := bbase (se 3 (by rfl) ⟨392099, by rfl⟩ : syracuseStep 2091197 = 784199) (by norm_num)
theorem B2484413 : Blo 1100624 2484413 := bbase (se 3 (by rfl) ⟨465827, by rfl⟩ : syracuseStep 2484413 = 931655) (by norm_num)
theorem B2353349 : Blo 1100624 2353349 := bbase (se 4 (by rfl) ⟨220626, by rfl⟩ : syracuseStep 2353349 = 441253) (by norm_num)
theorem B3532997 : Blo 1100624 3532997 := bbase (se 4 (by rfl) ⟨331218, by rfl⟩ : syracuseStep 3532997 = 662437) (by norm_num)
theorem B1239241 : Blo 1100624 1239241 := bbase (se 2 (by rfl) ⟨464715, by rfl⟩ : syracuseStep 1239241 = 929431) (by norm_num)
theorem B1239277 : Blo 1100624 1239277 := bbase (se 3 (by rfl) ⟨232364, by rfl⟩ : syracuseStep 1239277 = 464729) (by norm_num)
theorem B2484485 : Blo 1100624 2484485 := bbase (se 4 (by rfl) ⟨232920, by rfl⟩ : syracuseStep 2484485 = 465841) (by norm_num)
theorem B1239313 : Blo 1100624 1239313 := bbase (se 2 (by rfl) ⟨464742, by rfl⟩ : syracuseStep 1239313 = 929485) (by norm_num)
theorem B1861933 : Blo 1100624 1861933 := bbase (se 3 (by rfl) ⟨349112, by rfl⟩ : syracuseStep 1861933 = 698225) (by norm_num)
theorem B1239349 : Blo 1100624 1239349 := bbase (se 5 (by rfl) ⟨58094, by rfl⟩ : syracuseStep 1239349 = 116189) (by norm_num)
theorem B4188469 : Blo 1100624 4188469 := bbase (se 5 (by rfl) ⟨196334, by rfl⟩ : syracuseStep 4188469 = 392669) (by norm_num)
theorem B2484557 : Blo 1100624 2484557 := bbase (se 3 (by rfl) ⟨465854, by rfl⟩ : syracuseStep 2484557 = 931709) (by norm_num)
theorem B2091349 : Blo 1100624 2091349 := bbase (se 10 (by rfl) ⟨3063, by rfl⟩ : syracuseStep 2091349 = 6127) (by norm_num)
theorem B1239385 : Blo 1100624 1239385 := bbase (se 2 (by rfl) ⟨464769, by rfl⟩ : syracuseStep 1239385 = 929539) (by norm_num)
theorem B1239421 : Blo 1100624 1239421 := bbase (se 3 (by rfl) ⟨232391, by rfl⟩ : syracuseStep 1239421 = 464783) (by norm_num)
theorem B1862021 : Blo 1100624 1862021 := bbase (se 4 (by rfl) ⟨174564, by rfl⟩ : syracuseStep 1862021 = 349129) (by norm_num)
theorem B1567117 : Blo 1100624 1567117 := bbase (se 3 (by rfl) ⟨293834, by rfl⟩ : syracuseStep 1567117 = 587669) (by norm_num)
theorem B2484629 : Blo 1100624 2484629 := bbase (se 6 (by rfl) ⟨58233, by rfl⟩ : syracuseStep 2484629 = 116467) (by norm_num)
theorem B1239457 : Blo 1100624 1239457 := bbase (se 2 (by rfl) ⟨464796, by rfl⟩ : syracuseStep 1239457 = 929593) (by norm_num)
theorem B1239493 : Blo 1100624 1239493 := bbase (se 4 (by rfl) ⟨116202, by rfl⟩ : syracuseStep 1239493 = 232405) (by norm_num)
theorem B4712917 : Blo 1100624 4712917 := bbase (se 7 (by rfl) ⟨55229, by rfl⟩ : syracuseStep 4712917 = 110459) (by norm_num)
theorem B2484701 : Blo 1100624 2484701 := bbase (se 3 (by rfl) ⟨465881, by rfl⟩ : syracuseStep 2484701 = 931763) (by norm_num)
theorem B1239529 : Blo 1100624 1239529 := bbase (se 2 (by rfl) ⟨464823, by rfl⟩ : syracuseStep 1239529 = 929647) (by norm_num)
theorem B1862149 : Blo 1100624 1862149 := bbase (se 4 (by rfl) ⟨174576, by rfl⟩ : syracuseStep 1862149 = 349153) (by norm_num)
theorem B1239565 : Blo 1100624 1239565 := bbase (se 3 (by rfl) ⟨232418, by rfl⟩ : syracuseStep 1239565 = 464837) (by norm_num)
theorem B2484773 : Blo 1100624 2484773 := bbase (se 4 (by rfl) ⟨232947, by rfl⟩ : syracuseStep 2484773 = 465895) (by norm_num)
theorem B1239601 : Blo 1100624 1239601 := bbase (se 2 (by rfl) ⟨464850, by rfl⟩ : syracuseStep 1239601 = 929701) (by norm_num)
theorem B1239637 : Blo 1100624 1239637 := bbase (se 8 (by rfl) ⟨7263, by rfl⟩ : syracuseStep 1239637 = 14527) (by norm_num)
theorem B1862237 : Blo 1100624 1862237 := bbase (se 3 (by rfl) ⟨349169, by rfl⟩ : syracuseStep 1862237 = 698339) (by norm_num)
theorem B4188773 : Blo 1100624 4188773 := bbase (se 4 (by rfl) ⟨392697, by rfl⟩ : syracuseStep 4188773 = 785395) (by norm_num)
theorem B2484845 : Blo 1100624 2484845 := bbase (se 3 (by rfl) ⟨465908, by rfl⟩ : syracuseStep 2484845 = 931817) (by norm_num)
theorem B1239673 : Blo 1100624 1239673 := bbase (se 2 (by rfl) ⟨464877, by rfl⟩ : syracuseStep 1239673 = 929755) (by norm_num)
theorem B2091653 : Blo 1100624 2091653 := bbase (se 4 (by rfl) ⟨196092, by rfl⟩ : syracuseStep 2091653 = 392185) (by norm_num)
theorem B1239709 : Blo 1100624 1239709 := bbase (se 3 (by rfl) ⟨232445, by rfl⟩ : syracuseStep 1239709 = 464891) (by norm_num)
theorem B1764013 : Blo 1100624 1764013 := bbase (se 3 (by rfl) ⟨330752, by rfl⟩ : syracuseStep 1764013 = 661505) (by norm_num)
theorem B2484917 : Blo 1100624 2484917 := bbase (se 5 (by rfl) ⟨116480, by rfl⟩ : syracuseStep 2484917 = 232961) (by norm_num)
theorem B1239745 : Blo 1100624 1239745 := bbase (se 2 (by rfl) ⟨464904, by rfl⟩ : syracuseStep 1239745 = 929809) (by norm_num)
theorem B5663429 : Blo 1100624 5663429 := bbase (se 4 (by rfl) ⟨530946, by rfl⟩ : syracuseStep 5663429 = 1061893) (by norm_num)
theorem B1567453 : Blo 1100624 1567453 := bbase (se 3 (by rfl) ⟨293897, by rfl⟩ : syracuseStep 1567453 = 587795) (by norm_num)
theorem B1862365 : Blo 1100624 1862365 := bbase (se 3 (by rfl) ⟨349193, by rfl⟩ : syracuseStep 1862365 = 698387) (by norm_num)
theorem B1239781 : Blo 1100624 1239781 := bbase (se 4 (by rfl) ⟨116229, by rfl⟩ : syracuseStep 1239781 = 232459) (by norm_num)
theorem B10611445 : Blo 1100624 10611445 := bbase (se 5 (by rfl) ⟨497411, by rfl⟩ : syracuseStep 10611445 = 994823) (by norm_num)
theorem B2484989 : Blo 1100624 2484989 := bbase (se 3 (by rfl) ⟨465935, by rfl⟩ : syracuseStep 2484989 = 931871) (by norm_num)
theorem B1239817 : Blo 1100624 1239817 := bbase (se 2 (by rfl) ⟨464931, by rfl⟩ : syracuseStep 1239817 = 929863) (by norm_num)
theorem B1239853 : Blo 1100624 1239853 := bbase (se 3 (by rfl) ⟨232472, by rfl⟩ : syracuseStep 1239853 = 464945) (by norm_num)
theorem B1862453 : Blo 1100624 1862453 := bbase (se 5 (by rfl) ⟨87302, by rfl⟩ : syracuseStep 1862453 = 174605) (by norm_num)
theorem B2485061 : Blo 1100624 2485061 := bbase (se 4 (by rfl) ⟨232974, by rfl⟩ : syracuseStep 2485061 = 465949) (by norm_num)
theorem B1239889 : Blo 1100624 1239889 := bbase (se 2 (by rfl) ⟨464958, by rfl⟩ : syracuseStep 1239889 = 929917) (by norm_num)
theorem B1239925 : Blo 1100624 1239925 := bbase (se 5 (by rfl) ⟨58121, by rfl⟩ : syracuseStep 1239925 = 116243) (by norm_num)
theorem B2485133 : Blo 1100624 2485133 := bbase (se 3 (by rfl) ⟨465962, by rfl⟩ : syracuseStep 2485133 = 931925) (by norm_num)
theorem B1239961 : Blo 1100624 1239961 := bbase (se 2 (by rfl) ⟨464985, by rfl⟩ : syracuseStep 1239961 = 929971) (by norm_num)
theorem B1764269 : Blo 1100624 1764269 := bbase (se 3 (by rfl) ⟨330800, by rfl⟩ : syracuseStep 1764269 = 661601) (by norm_num)
theorem B2354093 : Blo 1100624 2354093 := bbase (se 3 (by rfl) ⟨441392, by rfl⟩ : syracuseStep 2354093 = 882785) (by norm_num)
theorem B1567669 : Blo 1100624 1567669 := bbase (se 5 (by rfl) ⟨73484, by rfl⟩ : syracuseStep 1567669 = 146969) (by norm_num)
theorem B1862581 : Blo 1100624 1862581 := bbase (se 5 (by rfl) ⟨87308, by rfl⟩ : syracuseStep 1862581 = 174617) (by norm_num)
theorem B1239997 : Blo 1100624 1239997 := bbase (se 3 (by rfl) ⟨232499, by rfl⟩ : syracuseStep 1239997 = 464999) (by norm_num)
theorem B11332565 : Blo 1100624 11332565 := bbase (se 7 (by rfl) ⟨132803, by rfl⟩ : syracuseStep 11332565 = 265607) (by norm_num)
theorem B2485205 : Blo 1100624 2485205 := bbase (se 7 (by rfl) ⟨29123, by rfl⟩ : syracuseStep 2485205 = 58247) (by norm_num)
theorem B1240033 : Blo 1100624 1240033 := bbase (se 2 (by rfl) ⟨465012, by rfl⟩ : syracuseStep 1240033 = 930025) (by norm_num)
theorem B1240069 : Blo 1100624 1240069 := bbase (se 4 (by rfl) ⟨116256, by rfl⟩ : syracuseStep 1240069 = 232513) (by norm_num)
theorem B1862669 : Blo 1100624 1862669 := bbase (se 3 (by rfl) ⟨349250, by rfl⟩ : syracuseStep 1862669 = 698501) (by norm_num)
theorem B2485277 : Blo 1100624 2485277 := bbase (se 3 (by rfl) ⟨465989, by rfl⟩ : syracuseStep 2485277 = 931979) (by norm_num)
theorem B1240105 : Blo 1100624 1240105 := bbase (se 2 (by rfl) ⟨465039, by rfl⟩ : syracuseStep 1240105 = 930079) (by norm_num)
theorem B1240141 : Blo 1100624 1240141 := bbase (se 3 (by rfl) ⟨232526, by rfl⟩ : syracuseStep 1240141 = 465053) (by norm_num)
theorem B2485349 : Blo 1100624 2485349 := bbase (se 4 (by rfl) ⟨233001, by rfl⟩ : syracuseStep 2485349 = 466003) (by norm_num)
theorem B1764461 : Blo 1100624 1764461 := bbase (se 3 (by rfl) ⟨330836, by rfl⟩ : syracuseStep 1764461 = 661673) (by norm_num)
theorem B1240177 : Blo 1100624 1240177 := bbase (se 2 (by rfl) ⟨465066, by rfl⟩ : syracuseStep 1240177 = 930133) (by norm_num)
theorem B5663861 : Blo 1100624 5663861 := bbase (se 5 (by rfl) ⟨265493, by rfl⟩ : syracuseStep 5663861 = 530987) (by norm_num)
theorem B1862797 : Blo 1100624 1862797 := bbase (se 3 (by rfl) ⟨349274, by rfl⟩ : syracuseStep 1862797 = 698549) (by norm_num)
theorem B1240213 : Blo 1100624 1240213 := bbase (se 6 (by rfl) ⟨29067, by rfl⟩ : syracuseStep 1240213 = 58135) (by norm_num)
theorem B4713653 : Blo 1100624 4713653 := bbase (se 5 (by rfl) ⟨220952, by rfl⟩ : syracuseStep 4713653 = 441905) (by norm_num)
theorem B1240249 : Blo 1100624 1240249 := bbase (se 2 (by rfl) ⟨465093, by rfl⟩ : syracuseStep 1240249 = 930187) (by norm_num)
theorem B2649277 : Blo 1100624 2649277 := bbase (se 3 (by rfl) ⟨496739, by rfl⟩ : syracuseStep 2649277 = 993479) (by norm_num)
theorem B1240285 : Blo 1100624 1240285 := bbase (se 3 (by rfl) ⟨232553, by rfl⟩ : syracuseStep 1240285 = 465107) (by norm_num)
theorem B1862885 : Blo 1100624 1862885 := bbase (se 4 (by rfl) ⟨174645, by rfl⟩ : syracuseStep 1862885 = 349291) (by norm_num)
theorem B1240321 : Blo 1100624 1240321 := bbase (se 2 (by rfl) ⟨465120, by rfl⟩ : syracuseStep 1240321 = 930241) (by norm_num)
theorem B1240357 : Blo 1100624 1240357 := bbase (se 4 (by rfl) ⟨116283, by rfl⟩ : syracuseStep 1240357 = 232567) (by norm_num)
theorem B1568045 : Blo 1100624 1568045 := bbase (se 3 (by rfl) ⟨294008, by rfl⟩ : syracuseStep 1568045 = 588017) (by norm_num)
theorem B1240393 : Blo 1100624 1240393 := bbase (se 2 (by rfl) ⟨465147, by rfl⟩ : syracuseStep 1240393 = 930295) (by norm_num)
theorem B1863013 : Blo 1100624 1863013 := bbase (se 4 (by rfl) ⟨174657, by rfl⟩ : syracuseStep 1863013 = 349315) (by norm_num)
theorem B1240429 : Blo 1100624 1240429 := bbase (se 3 (by rfl) ⟨232580, by rfl⟩ : syracuseStep 1240429 = 465161) (by norm_num)
theorem B1273201 : Blo 1100624 1273201 := bbase (se 2 (by rfl) ⟨477450, by rfl⟩ : syracuseStep 1273201 = 954901) (by norm_num)
theorem B2092405 : Blo 1100624 2092405 := bbase (se 5 (by rfl) ⟨98081, by rfl⟩ : syracuseStep 2092405 = 196163) (by norm_num)
theorem B1240465 : Blo 1100624 1240465 := bbase (se 2 (by rfl) ⟨465174, by rfl⟩ : syracuseStep 1240465 = 930349) (by norm_num)
theorem B1240501 : Blo 1100624 1240501 := bbase (se 5 (by rfl) ⟨58148, by rfl⟩ : syracuseStep 1240501 = 116297) (by norm_num)
theorem B1863101 : Blo 1100624 1863101 := bbase (se 3 (by rfl) ⟨349331, by rfl⟩ : syracuseStep 1863101 = 698663) (by norm_num)
theorem B6286805 : Blo 1100624 6286805 := bbase (se 7 (by rfl) ⟨73673, by rfl⟩ : syracuseStep 6286805 = 147347) (by norm_num)
theorem B1240537 : Blo 1100624 1240537 := bbase (se 2 (by rfl) ⟨465201, by rfl⟩ : syracuseStep 1240537 = 930403) (by norm_num)
theorem B1240573 : Blo 1100624 1240573 := bbase (se 3 (by rfl) ⟨232607, by rfl⟩ : syracuseStep 1240573 = 465215) (by norm_num)
theorem B2092549 : Blo 1100624 2092549 := bbase (se 4 (by rfl) ⟨196176, by rfl⟩ : syracuseStep 2092549 = 392353) (by norm_num)
theorem B3141125 : Blo 1100624 3141125 := bbase (se 4 (by rfl) ⟨294480, by rfl⟩ : syracuseStep 3141125 = 588961) (by norm_num)
theorem B1240609 : Blo 1100624 1240609 := bbase (se 2 (by rfl) ⟨465228, by rfl⟩ : syracuseStep 1240609 = 930457) (by norm_num)
theorem B1863229 : Blo 1100624 1863229 := bbase (se 3 (by rfl) ⟨349355, by rfl⟩ : syracuseStep 1863229 = 698711) (by norm_num)
theorem B1240645 : Blo 1100624 1240645 := bbase (se 4 (by rfl) ⟨116310, by rfl⟩ : syracuseStep 1240645 = 232621) (by norm_num)
theorem B1240681 : Blo 1100624 1240681 := bbase (se 2 (by rfl) ⟨465255, by rfl⟩ : syracuseStep 1240681 = 930511) (by norm_num)
theorem B1240717 : Blo 1100624 1240717 := bbase (se 3 (by rfl) ⟨232634, by rfl⟩ : syracuseStep 1240717 = 465269) (by norm_num)
theorem B1863317 : Blo 1100624 1863317 := bbase (se 6 (by rfl) ⟨43671, by rfl⟩ : syracuseStep 1863317 = 87343) (by norm_num)
theorem B2354845 : Blo 1100624 2354845 := bbase (se 3 (by rfl) ⟨441533, by rfl⟩ : syracuseStep 2354845 = 883067) (by norm_num)
theorem B2092709 : Blo 1100624 2092709 := bbase (se 4 (by rfl) ⟨196191, by rfl⟩ : syracuseStep 2092709 = 392383) (by norm_num)
theorem B1240753 : Blo 1100624 1240753 := bbase (se 2 (by rfl) ⟨465282, by rfl⟩ : syracuseStep 1240753 = 930565) (by norm_num)
theorem B1240789 : Blo 1100624 1240789 := bbase (se 7 (by rfl) ⟨14540, by rfl⟩ : syracuseStep 1240789 = 29081) (by norm_num)
theorem B1240825 : Blo 1100624 1240825 := bbase (se 2 (by rfl) ⟨465309, by rfl⟩ : syracuseStep 1240825 = 930619) (by norm_num)
theorem B1863445 : Blo 1100624 1863445 := bbase (se 6 (by rfl) ⟨43674, by rfl⟩ : syracuseStep 1863445 = 87349) (by norm_num)
theorem B1240861 : Blo 1100624 1240861 := bbase (se 3 (by rfl) ⟨232661, by rfl⟩ : syracuseStep 1240861 = 465323) (by norm_num)
theorem B2354989 : Blo 1100624 2354989 := bbase (se 3 (by rfl) ⟨441560, by rfl⟩ : syracuseStep 2354989 = 883121) (by norm_num)
theorem B2092853 : Blo 1100624 2092853 := bbase (se 5 (by rfl) ⟨98102, by rfl⟩ : syracuseStep 2092853 = 196205) (by norm_num)
theorem B1240897 : Blo 1100624 1240897 := bbase (se 2 (by rfl) ⟨465336, by rfl⟩ : syracuseStep 1240897 = 930673) (by norm_num)
theorem B2649941 : Blo 1100624 2649941 := bbase (se 9 (by rfl) ⟨7763, by rfl⟩ : syracuseStep 2649941 = 15527) (by norm_num)
theorem B5304149 : Blo 1100624 5304149 := bbase (se 9 (by rfl) ⟨15539, by rfl⟩ : syracuseStep 5304149 = 31079) (by norm_num)
theorem B7958357 : Blo 1100624 7958357 := bbase (se 9 (by rfl) ⟨23315, by rfl⟩ : syracuseStep 7958357 = 46631) (by norm_num)
theorem B1240933 : Blo 1100624 1240933 := bbase (se 4 (by rfl) ⟨116337, by rfl⟩ : syracuseStep 1240933 = 232675) (by norm_num)
theorem B1863533 : Blo 1100624 1863533 := bbase (se 3 (by rfl) ⟨349412, by rfl⟩ : syracuseStep 1863533 = 698825) (by norm_num)
theorem B2977669 : Blo 1100624 2977669 := bbase (se 4 (by rfl) ⟨279156, by rfl⟩ : syracuseStep 2977669 = 558313) (by norm_num)
theorem B1240969 : Blo 1100624 1240969 := bbase (se 2 (by rfl) ⟨465363, by rfl⟩ : syracuseStep 1240969 = 930727) (by norm_num)
theorem B1241005 : Blo 1100624 1241005 := bbase (se 3 (by rfl) ⟨232688, by rfl⟩ : syracuseStep 1241005 = 465377) (by norm_num)
theorem B1241041 : Blo 1100624 1241041 := bbase (se 2 (by rfl) ⟨465390, by rfl⟩ : syracuseStep 1241041 = 930781) (by norm_num)
theorem B1175509 : Blo 1100624 1175509 := bbase (se 7 (by rfl) ⟨13775, by rfl⟩ : syracuseStep 1175509 = 27551) (by norm_num)
theorem B1863661 : Blo 1100624 1863661 := bbase (se 3 (by rfl) ⟨349436, by rfl⟩ : syracuseStep 1863661 = 698873) (by norm_num)
theorem B1241077 : Blo 1100624 1241077 := bbase (se 5 (by rfl) ⟨58175, by rfl⟩ : syracuseStep 1241077 = 116351) (by norm_num)
theorem B1765397 : Blo 1100624 1765397 := bbase (se 6 (by rfl) ⟨41376, by rfl⟩ : syracuseStep 1765397 = 82753) (by norm_num)
theorem B1241113 : Blo 1100624 1241113 := bbase (se 2 (by rfl) ⟨465417, by rfl⟩ : syracuseStep 1241113 = 930835) (by norm_num)
theorem B1175581 : Blo 1100624 1175581 := bbase (se 3 (by rfl) ⟨220421, by rfl⟩ : syracuseStep 1175581 = 440843) (by norm_num)
theorem B1208353 : Blo 1100624 1208353 := bbase (se 2 (by rfl) ⟨453132, by rfl⟩ : syracuseStep 1208353 = 906265) (by norm_num)
theorem B1241149 : Blo 1100624 1241149 := bbase (se 3 (by rfl) ⟨232715, by rfl⟩ : syracuseStep 1241149 = 465431) (by norm_num)
theorem B1863749 : Blo 1100624 1863749 := bbase (se 4 (by rfl) ⟨174726, by rfl⟩ : syracuseStep 1863749 = 349453) (by norm_num)
theorem B2093141 : Blo 1100624 2093141 := bbase (se 8 (by rfl) ⟨12264, by rfl⟩ : syracuseStep 2093141 = 24529) (by norm_num)
theorem B1241185 : Blo 1100624 1241185 := bbase (se 2 (by rfl) ⟨465444, by rfl⟩ : syracuseStep 1241185 = 930889) (by norm_num)
theorem B2650229 : Blo 1100624 2650229 := bbase (se 5 (by rfl) ⟨124229, by rfl⟩ : syracuseStep 2650229 = 248459) (by norm_num)
theorem B1241221 : Blo 1100624 1241221 := bbase (se 4 (by rfl) ⟨116364, by rfl⟩ : syracuseStep 1241221 = 232729) (by norm_num)
theorem B2355365 : Blo 1100624 2355365 := bbase (se 4 (by rfl) ⟨220815, by rfl⟩ : syracuseStep 2355365 = 441631) (by norm_num)
theorem B1241257 : Blo 1100624 1241257 := bbase (se 2 (by rfl) ⟨465471, by rfl⟩ : syracuseStep 1241257 = 930943) (by norm_num)
theorem B1863877 : Blo 1100624 1863877 := bbase (se 4 (by rfl) ⟨174738, by rfl⟩ : syracuseStep 1863877 = 349477) (by norm_num)
theorem B1241293 : Blo 1100624 1241293 := bbase (se 3 (by rfl) ⟨232742, by rfl⟩ : syracuseStep 1241293 = 465485) (by norm_num)
theorem B2093293 : Blo 1100624 2093293 := bbase (se 3 (by rfl) ⟨392492, by rfl⟩ : syracuseStep 2093293 = 784985) (by norm_num)
theorem B1241329 : Blo 1100624 1241329 := bbase (se 2 (by rfl) ⟨465498, by rfl⟩ : syracuseStep 1241329 = 930997) (by norm_num)
theorem B1241365 : Blo 1100624 1241365 := bbase (se 6 (by rfl) ⟨29094, by rfl⟩ : syracuseStep 1241365 = 58189) (by norm_num)
theorem B1863965 : Blo 1100624 1863965 := bbase (se 3 (by rfl) ⟨349493, by rfl⟩ : syracuseStep 1863965 = 698987) (by norm_num)
theorem B1241401 : Blo 1100624 1241401 := bbase (se 2 (by rfl) ⟨465525, by rfl⟩ : syracuseStep 1241401 = 931051) (by norm_num)
theorem B1241437 : Blo 1100624 1241437 := bbase (se 3 (by rfl) ⟨232769, by rfl⟩ : syracuseStep 1241437 = 465539) (by norm_num)
theorem B1241473 : Blo 1100624 1241473 := bbase (se 2 (by rfl) ⟨465552, by rfl⟩ : syracuseStep 1241473 = 931105) (by norm_num)
theorem B1175953 : Blo 1100624 1175953 := bbase (se 2 (by rfl) ⟨440982, by rfl⟩ : syracuseStep 1175953 = 881965) (by norm_num)
theorem B1765781 : Blo 1100624 1765781 := bbase (se 6 (by rfl) ⟨41385, by rfl⟩ : syracuseStep 1765781 = 82771) (by norm_num)
theorem B1241509 : Blo 1100624 1241509 := bbase (se 4 (by rfl) ⟨116391, by rfl⟩ : syracuseStep 1241509 = 232783) (by norm_num)
theorem B1241545 : Blo 1100624 1241545 := bbase (se 2 (by rfl) ⟨465579, by rfl⟩ : syracuseStep 1241545 = 931159) (by norm_num)
theorem B1241581 : Blo 1100624 1241581 := bbase (se 3 (by rfl) ⟨232796, by rfl⟩ : syracuseStep 1241581 = 465593) (by norm_num)
theorem B1241617 : Blo 1100624 1241617 := bbase (se 2 (by rfl) ⟨465606, by rfl⟩ : syracuseStep 1241617 = 931213) (by norm_num)
theorem B1765909 : Blo 1100624 1765909 := bbase (se 6 (by rfl) ⟨41388, by rfl⟩ : syracuseStep 1765909 = 82777) (by norm_num)
theorem B2355733 : Blo 1100624 2355733 := bbase (se 6 (by rfl) ⟨55212, by rfl⟩ : syracuseStep 2355733 = 110425) (by norm_num)
theorem B2093597 : Blo 1100624 2093597 := bbase (se 3 (by rfl) ⟨392549, by rfl⟩ : syracuseStep 2093597 = 785099) (by norm_num)
theorem B1241653 : Blo 1100624 1241653 := bbase (se 5 (by rfl) ⟨58202, by rfl⟩ : syracuseStep 1241653 = 116405) (by norm_num)
theorem B1241689 : Blo 1100624 1241689 := bbase (se 2 (by rfl) ⟨465633, by rfl⟩ : syracuseStep 1241689 = 931267) (by norm_num)
theorem B6287989 : Blo 1100624 6287989 := bbase (se 5 (by rfl) ⟨294749, by rfl⟩ : syracuseStep 6287989 = 589499) (by norm_num)
theorem B1241725 : Blo 1100624 1241725 := bbase (se 3 (by rfl) ⟨232823, by rfl⟩ : syracuseStep 1241725 = 465647) (by norm_num)
theorem B1241761 : Blo 1100624 1241761 := bbase (se 2 (by rfl) ⟨465660, by rfl⟩ : syracuseStep 1241761 = 931321) (by norm_num)
theorem B3142309 : Blo 1100624 3142309 := bbase (se 4 (by rfl) ⟨294591, by rfl⟩ : syracuseStep 3142309 = 589183) (by norm_num)
theorem B4190885 : Blo 1100624 4190885 := bbase (se 4 (by rfl) ⟨392895, by rfl⟩ : syracuseStep 4190885 = 785791) (by norm_num)
theorem B1569469 : Blo 1100624 1569469 := bbase (se 3 (by rfl) ⟨294275, by rfl⟩ : syracuseStep 1569469 = 588551) (by norm_num)
theorem B1241797 : Blo 1100624 1241797 := bbase (se 4 (by rfl) ⟨116418, by rfl⟩ : syracuseStep 1241797 = 232837) (by norm_num)
theorem B1241833 : Blo 1100624 1241833 := bbase (se 2 (by rfl) ⟨465687, by rfl⟩ : syracuseStep 1241833 = 931375) (by norm_num)
theorem B1176329 : Blo 1100624 1176329 := bbase (se 2 (by rfl) ⟨441123, by rfl⟩ : syracuseStep 1176329 = 882247) (by norm_num)
theorem B1241869 : Blo 1100624 1241869 := bbase (se 3 (by rfl) ⟨232850, by rfl⟩ : syracuseStep 1241869 = 465701) (by norm_num)
theorem B1241905 : Blo 1100624 1241905 := bbase (se 2 (by rfl) ⟨465714, by rfl⟩ : syracuseStep 1241905 = 931429) (by norm_num)
theorem B3142469 : Blo 1100624 3142469 := bbase (se 4 (by rfl) ⟨294606, by rfl⟩ : syracuseStep 3142469 = 589213) (by norm_num)
theorem B1176401 : Blo 1100624 1176401 := bbase (se 2 (by rfl) ⟨441150, by rfl⟩ : syracuseStep 1176401 = 882301) (by norm_num)
theorem B1241941 : Blo 1100624 1241941 := bbase (se 9 (by rfl) ⟨3638, by rfl⟩ : syracuseStep 1241941 = 7277) (by norm_num)
theorem B1241977 : Blo 1100624 1241977 := bbase (se 2 (by rfl) ⟨465741, by rfl⟩ : syracuseStep 1241977 = 931483) (by norm_num)
theorem B1242013 : Blo 1100624 1242013 := bbase (se 3 (by rfl) ⟨232877, by rfl⟩ : syracuseStep 1242013 = 465755) (by norm_num)
theorem B1242049 : Blo 1100624 1242049 := bbase (se 2 (by rfl) ⟨465768, by rfl⟩ : syracuseStep 1242049 = 931537) (by norm_num)
theorem B4191173 : Blo 1100624 4191173 := bbase (se 4 (by rfl) ⟨392922, by rfl⟩ : syracuseStep 4191173 = 785845) (by norm_num)
theorem B1242085 : Blo 1100624 1242085 := bbase (se 4 (by rfl) ⟨116445, by rfl⟩ : syracuseStep 1242085 = 232891) (by norm_num)
theorem B1242121 : Blo 1100624 1242121 := bbase (se 2 (by rfl) ⟨465795, by rfl⟩ : syracuseStep 1242121 = 931591) (by norm_num)
theorem B1176589 : Blo 1100624 1176589 := bbase (se 3 (by rfl) ⟨220610, by rfl⟩ : syracuseStep 1176589 = 441221) (by norm_num)
theorem B1242157 : Blo 1100624 1242157 := bbase (se 3 (by rfl) ⟨232904, by rfl⟩ : syracuseStep 1242157 = 465809) (by norm_num)
theorem B3142709 : Blo 1100624 3142709 := bbase (se 5 (by rfl) ⟨147314, by rfl⟩ : syracuseStep 3142709 = 294629) (by norm_num)
theorem B1242193 : Blo 1100624 1242193 := bbase (se 2 (by rfl) ⟨465822, by rfl⟩ : syracuseStep 1242193 = 931645) (by norm_num)
theorem B1242229 : Blo 1100624 1242229 := bbase (se 5 (by rfl) ⟨58229, by rfl⟩ : syracuseStep 1242229 = 116459) (by norm_num)
theorem B1242265 : Blo 1100624 1242265 := bbase (se 2 (by rfl) ⟨465849, by rfl⟩ : syracuseStep 1242265 = 931699) (by norm_num)
theorem B1242301 : Blo 1100624 1242301 := bbase (se 3 (by rfl) ⟨232931, by rfl⟩ : syracuseStep 1242301 = 465863) (by norm_num)
theorem B1176773 : Blo 1100624 1176773 := bbase (se 4 (by rfl) ⟨110322, by rfl⟩ : syracuseStep 1176773 = 220645) (by norm_num)
theorem B1242337 : Blo 1100624 1242337 := bbase (se 2 (by rfl) ⟨465876, by rfl⟩ : syracuseStep 1242337 = 931753) (by norm_num)
theorem B3142901 : Blo 1100624 3142901 := bbase (se 5 (by rfl) ⟨147323, by rfl⟩ : syracuseStep 3142901 = 294647) (by norm_num)
theorem B1242373 : Blo 1100624 1242373 := bbase (se 4 (by rfl) ⟨116472, by rfl⟩ : syracuseStep 1242373 = 232945) (by norm_num)
theorem B1570061 : Blo 1100624 1570061 := bbase (se 3 (by rfl) ⟨294386, by rfl⟩ : syracuseStep 1570061 = 588773) (by norm_num)
theorem B2094349 : Blo 1100624 2094349 := bbase (se 3 (by rfl) ⟨392690, by rfl⟩ : syracuseStep 2094349 = 785381) (by norm_num)
theorem B1242409 : Blo 1100624 1242409 := bbase (se 2 (by rfl) ⟨465903, by rfl⟩ : syracuseStep 1242409 = 931807) (by norm_num)
theorem B1242445 : Blo 1100624 1242445 := bbase (se 3 (by rfl) ⟨232958, by rfl⟩ : syracuseStep 1242445 = 465917) (by norm_num)
theorem B1570141 : Blo 1100624 1570141 := bbase (se 3 (by rfl) ⟨294401, by rfl⟩ : syracuseStep 1570141 = 588803) (by norm_num)
theorem B2979173 : Blo 1100624 2979173 := bbase (se 4 (by rfl) ⟨279297, by rfl⟩ : syracuseStep 2979173 = 558595) (by norm_num)
theorem B1242481 : Blo 1100624 1242481 := bbase (se 2 (by rfl) ⟨465930, by rfl⟩ : syracuseStep 1242481 = 931861) (by norm_num)
theorem B1242517 : Blo 1100624 1242517 := bbase (se 6 (by rfl) ⟨29121, by rfl⟩ : syracuseStep 1242517 = 58243) (by norm_num)
theorem B2094493 : Blo 1100624 2094493 := bbase (se 3 (by rfl) ⟨392717, by rfl⟩ : syracuseStep 2094493 = 785435) (by norm_num)
theorem B2553245 : Blo 1100624 2553245 := bbase (se 3 (by rfl) ⟨478733, by rfl⟩ : syracuseStep 2553245 = 957467) (by norm_num)
theorem B1242553 : Blo 1100624 1242553 := bbase (se 2 (by rfl) ⟨465957, by rfl⟩ : syracuseStep 1242553 = 931915) (by norm_num)
theorem B1570261 : Blo 1100624 1570261 := bbase (se 7 (by rfl) ⟨18401, by rfl⟩ : syracuseStep 1570261 = 36803) (by norm_num)
theorem B1242589 : Blo 1100624 1242589 := bbase (se 3 (by rfl) ⟨232985, by rfl⟩ : syracuseStep 1242589 = 465971) (by norm_num)
theorem B1766909 : Blo 1100624 1766909 := bbase (se 3 (by rfl) ⟨331295, by rfl⟩ : syracuseStep 1766909 = 662591) (by norm_num)
theorem B1242625 : Blo 1100624 1242625 := bbase (se 2 (by rfl) ⟨465984, by rfl⟩ : syracuseStep 1242625 = 931969) (by norm_num)
theorem B1242661 : Blo 1100624 1242661 := bbase (se 4 (by rfl) ⟨116499, by rfl⟩ : syracuseStep 1242661 = 232999) (by norm_num)
theorem B1570357 : Blo 1100624 1570357 := bbase (se 5 (by rfl) ⟨73610, by rfl⟩ : syracuseStep 1570357 = 147221) (by norm_num)
theorem B2094653 : Blo 1100624 2094653 := bbase (se 3 (by rfl) ⟨392747, by rfl⟩ : syracuseStep 2094653 = 785495) (by norm_num)
theorem B1242697 : Blo 1100624 1242697 := bbase (se 2 (by rfl) ⟨466011, by rfl⟩ : syracuseStep 1242697 = 932023) (by norm_num)
theorem B1341041 : Blo 1100624 1341041 := bbase (se 2 (by rfl) ⟨502890, by rfl⟩ : syracuseStep 1341041 = 1005781) (by norm_num)
theorem B1767037 : Blo 1100624 1767037 := bbase (se 3 (by rfl) ⟨331319, by rfl⟩ : syracuseStep 1767037 = 662639) (by norm_num)
theorem B2094797 : Blo 1100624 2094797 := bbase (se 3 (by rfl) ⟨392774, by rfl⟩ : syracuseStep 2094797 = 785549) (by norm_num)
theorem B2979605 : Blo 1100624 2979605 := bbase (se 6 (by rfl) ⟨69834, by rfl⟩ : syracuseStep 2979605 = 139669) (by norm_num)
theorem B3536789 : Blo 1100624 3536789 := bbase (se 6 (by rfl) ⟨82893, by rfl⟩ : syracuseStep 3536789 = 165787) (by norm_num)
theorem B1177525 : Blo 1100624 1177525 := bbase (se 5 (by rfl) ⟨55196, by rfl⟩ : syracuseStep 1177525 = 110393) (by norm_num)
theorem B2095085 : Blo 1100624 2095085 := bbase (se 3 (by rfl) ⟨392828, by rfl⟩ : syracuseStep 2095085 = 785657) (by norm_num)
theorem B2357237 : Blo 1100624 2357237 := bbase (se 5 (by rfl) ⟨110495, by rfl⟩ : syracuseStep 2357237 = 220991) (by norm_num)
theorem B1177597 : Blo 1100624 1177597 := bbase (se 3 (by rfl) ⟨220799, by rfl⟩ : syracuseStep 1177597 = 441599) (by norm_num)
theorem B1767421 : Blo 1100624 1767421 := bbase (se 3 (by rfl) ⟨331391, by rfl⟩ : syracuseStep 1767421 = 662783) (by norm_num)
theorem B1570853 : Blo 1100624 1570853 := bbase (se 4 (by rfl) ⟨147267, by rfl⟩ : syracuseStep 1570853 = 294535) (by norm_num)
theorem B4192357 : Blo 1100624 4192357 := bbase (se 4 (by rfl) ⟨393033, by rfl⟩ : syracuseStep 4192357 = 786067) (by norm_num)
theorem B2652277 : Blo 1100624 2652277 := bbase (se 5 (by rfl) ⟨124325, by rfl⟩ : syracuseStep 2652277 = 248651) (by norm_num)
theorem B2095237 : Blo 1100624 2095237 := bbase (se 4 (by rfl) ⟨196428, by rfl⟩ : syracuseStep 2095237 = 392857) (by norm_num)
theorem B2357381 : Blo 1100624 2357381 := bbase (se 4 (by rfl) ⟨221004, by rfl⟩ : syracuseStep 2357381 = 442009) (by norm_num)
theorem B1177777 : Blo 1100624 1177777 := bbase (se 2 (by rfl) ⟨441666, by rfl⟩ : syracuseStep 1177777 = 883333) (by norm_num)
theorem B3143893 : Blo 1100624 3143893 := bbase (se 7 (by rfl) ⟨36842, by rfl⟩ : syracuseStep 3143893 = 73685) (by norm_num)
theorem B1767677 : Blo 1100624 1767677 := bbase (se 3 (by rfl) ⟨331439, by rfl⟩ : syracuseStep 1767677 = 662879) (by norm_num)
theorem B8386901 : Blo 1100624 8386901 := bbase (se 10 (by rfl) ⟨12285, by rfl⟩ : syracuseStep 8386901 = 24571) (by norm_num)
theorem B4192661 : Blo 1100624 4192661 := bbase (se 6 (by rfl) ⟨98265, by rfl⟩ : syracuseStep 4192661 = 196531) (by norm_num)
theorem B4716949 : Blo 1100624 4716949 := bbase (se 6 (by rfl) ⟨110553, by rfl⟩ : syracuseStep 4716949 = 221107) (by norm_num)
theorem B2095541 : Blo 1100624 2095541 := bbase (se 5 (by rfl) ⟨98228, by rfl⟩ : syracuseStep 2095541 = 196457) (by norm_num)
theorem B2357741 : Blo 1100624 2357741 := bbase (se 3 (by rfl) ⟨442076, by rfl⟩ : syracuseStep 2357741 = 884153) (by norm_num)
theorem B1341937 : Blo 1100624 1341937 := bbase (se 2 (by rfl) ⟨503226, by rfl⟩ : syracuseStep 1341937 = 1006453) (by norm_num)
theorem B6289973 : Blo 1100624 6289973 := bbase (se 5 (by rfl) ⟨294842, by rfl⟩ : syracuseStep 6289973 = 589685) (by norm_num)
theorem B1571405 : Blo 1100624 1571405 := bbase (se 3 (by rfl) ⟨294638, by rfl⟩ : syracuseStep 1571405 = 589277) (by norm_num)
theorem B1178221 : Blo 1100624 1178221 := bbase (se 3 (by rfl) ⟨220916, by rfl⟩ : syracuseStep 1178221 = 441833) (by norm_num)
theorem B1178345 : Blo 1100624 1178345 := bbase (se 2 (by rfl) ⟨441879, by rfl⟩ : syracuseStep 1178345 = 883759) (by norm_num)
theorem B3537701 : Blo 1100624 3537701 := bbase (se 4 (by rfl) ⟨331659, by rfl⟩ : syracuseStep 3537701 = 663319) (by norm_num)
theorem B9436085 : Blo 1100624 9436085 := bbase (se 5 (by rfl) ⟨442316, by rfl⟩ : syracuseStep 9436085 = 884633) (by norm_num)
theorem B1178597 : Blo 1100624 1178597 := bbase (se 4 (by rfl) ⟨110493, by rfl⟩ : syracuseStep 1178597 = 220987) (by norm_num)
theorem B1768549 : Blo 1100624 1768549 := bbase (se 4 (by rfl) ⟨165801, by rfl⟩ : syracuseStep 1768549 = 331603) (by norm_num)
theorem B2096293 : Blo 1100624 2096293 := bbase (se 4 (by rfl) ⟨196527, by rfl⟩ : syracuseStep 2096293 = 393055) (by norm_num)
theorem B1768645 : Blo 1100624 1768645 := bbase (se 4 (by rfl) ⟨165810, by rfl⟩ : syracuseStep 1768645 = 331621) (by norm_num)
theorem B15924437 : Blo 1100624 15924437 := bbase (se 7 (by rfl) ⟨186614, by rfl⟩ : syracuseStep 15924437 = 373229) (by norm_num)
theorem B3144997 : Blo 1100624 3144997 := bbase (se 4 (by rfl) ⟨294843, by rfl⟩ : syracuseStep 3144997 = 589687) (by norm_num)
theorem B2096437 : Blo 1100624 2096437 := bbase (se 5 (by rfl) ⟨98270, by rfl⟩ : syracuseStep 2096437 = 196541) (by norm_num)
theorem B1572157 : Blo 1100624 1572157 := bbase (se 3 (by rfl) ⟨294779, by rfl⟩ : syracuseStep 1572157 = 589559) (by norm_num)
theorem B1768805 : Blo 1100624 1768805 := bbase (se 4 (by rfl) ⟨165825, by rfl⟩ : syracuseStep 1768805 = 331651) (by norm_num)
theorem B2358629 : Blo 1100624 2358629 := bbase (se 4 (by rfl) ⟨221121, by rfl⟩ : syracuseStep 2358629 = 442243) (by norm_num)
theorem B5307781 : Blo 1100624 5307781 := bbase (se 4 (by rfl) ⟨497604, by rfl⟩ : syracuseStep 5307781 = 995209) (by norm_num)
theorem B7077269 : Blo 1100624 7077269 := bbase (se 6 (by rfl) ⟨165873, by rfl⟩ : syracuseStep 7077269 = 331747) (by norm_num)
theorem B1179041 : Blo 1100624 1179041 := bbase (se 2 (by rfl) ⟨442140, by rfl⟩ : syracuseStep 1179041 = 884281) (by norm_num)
theorem B2096597 : Blo 1100624 2096597 := bbase (se 7 (by rfl) ⟨24569, by rfl⟩ : syracuseStep 2096597 = 49139) (by norm_num)
theorem B2358877 : Blo 1100624 2358877 := bbase (se 3 (by rfl) ⟨442289, by rfl⟩ : syracuseStep 2358877 = 884579) (by norm_num)
theorem B2096741 : Blo 1100624 2096741 := bbase (se 4 (by rfl) ⟨196569, by rfl⟩ : syracuseStep 2096741 = 393139) (by norm_num)
theorem B1638005 : Blo 1100624 1638005 := bbase (se 5 (by rfl) ⟨76781, by rfl⟩ : syracuseStep 1638005 = 153563) (by norm_num)
theorem B1179289 : Blo 1100624 1179289 := bbase (se 2 (by rfl) ⟨442233, by rfl⟩ : syracuseStep 1179289 = 884467) (by norm_num)
theorem B2981573 : Blo 1100624 2981573 := bbase (se 4 (by rfl) ⟨279522, by rfl⟩ : syracuseStep 2981573 = 559045) (by norm_num)
theorem B1343281 : Blo 1100624 1343281 := bbase (se 2 (by rfl) ⟨503730, by rfl⟩ : syracuseStep 1343281 = 1007461) (by norm_num)
theorem B6356789 : Blo 1100624 6356789 := bbase (se 5 (by rfl) ⟨297974, by rfl⟩ : syracuseStep 6356789 = 595949) (by norm_num)
theorem B2097029 : Blo 1100624 2097029 := bbase (se 4 (by rfl) ⟨196596, by rfl⟩ : syracuseStep 2097029 = 393193) (by norm_num)
theorem B3178673 : Blo 1100624 3178673 := bstep (se 2 (by rfl) ⟨1192002, by rfl⟩ : syracuseStep 3178673 = 2384005) B2384005
theorem B22610117 : Blo 1100624 22610117 := bstep (se 4 (by rfl) ⟨2119698, by rfl⟩ : syracuseStep 22610117 = 4239397) B4239397
theorem B2687537 : Blo 1100624 2687537 := bstep (se 2 (by rfl) ⟨1007826, by rfl⟩ : syracuseStep 2687537 = 2015653) B2015653
theorem B2786147 : Blo 1100624 2786147 := bstep (se 1 (by rfl) ⟨2089610, by rfl⟩ : syracuseStep 2786147 = 4179221) B4179221
theorem B2786339 : Blo 1100624 2786339 := bstep (se 1 (by rfl) ⟨2089754, by rfl⟩ : syracuseStep 2786339 = 4179509) B4179509
theorem B7537805 : Blo 1100624 7537805 := bstep (se 3 (by rfl) ⟨1413338, by rfl⟩ : syracuseStep 7537805 = 2826677) B2826677
theorem B1115731 : Blo 1100624 1115731 := bstep (se 1 (by rfl) ⟨836798, by rfl⟩ : syracuseStep 1115731 = 1673597) B1673597
theorem B12551921 : Blo 1100624 12551921 := bstep (se 2 (by rfl) ⟨4706970, by rfl⟩ : syracuseStep 12551921 = 9413941) B9413941
theorem B2787281 : Blo 1100624 2787281 := bstep (se 2 (by rfl) ⟨1045230, by rfl⟩ : syracuseStep 2787281 = 2090461) B2090461
theorem B2787331 : Blo 1100624 2787331 := bstep (se 1 (by rfl) ⟨2090498, by rfl⟩ : syracuseStep 2787331 = 4180997) B4180997
theorem B2787473 : Blo 1100624 2787473 := bstep (se 2 (by rfl) ⟨1045302, by rfl⟩ : syracuseStep 2787473 = 2090605) B2090605
theorem B5966129 : Blo 1100624 5966129 := bstep (se 2 (by rfl) ⟨2237298, by rfl⟩ : syracuseStep 5966129 = 4474597) B4474597
theorem B3771089 : Blo 1100624 3771089 := bstep (se 2 (by rfl) ⟨1414158, by rfl⟩ : syracuseStep 3771089 = 2828317) B2828317
theorem B1674083 : Blo 1100624 1674083 := bstep (se 1 (by rfl) ⟨1255562, by rfl⟩ : syracuseStep 1674083 = 2511125) B2511125
theorem B2788465 : Blo 1100624 2788465 := bstep (se 2 (by rfl) ⟨1045674, by rfl⟩ : syracuseStep 2788465 = 2091349) B2091349
theorem B2788739 : Blo 1100624 2788739 := bstep (se 1 (by rfl) ⟨2091554, by rfl⟩ : syracuseStep 2788739 = 4183109) B4183109
theorem B1117619 : Blo 1100624 1117619 := bstep (se 1 (by rfl) ⟨838214, by rfl⟩ : syracuseStep 1117619 = 1676429) B1676429
theorem B2788931 : Blo 1100624 2788931 := bstep (se 1 (by rfl) ⟨2091698, by rfl⟩ : syracuseStep 2788931 = 4183397) B4183397
theorem B5574257 : Blo 1100624 5574257 := bstep (se 2 (by rfl) ⟨2090346, by rfl⟩ : syracuseStep 5574257 = 4180693) B4180693
theorem B5968205 : Blo 1100624 5968205 := bstep (se 3 (by rfl) ⟨1119038, by rfl⟩ : syracuseStep 5968205 = 2238077) B2238077
theorem B1675603 : Blo 1100624 1675603 := bstep (se 1 (by rfl) ⟨1256702, by rfl⟩ : syracuseStep 1675603 = 2513405) B2513405
theorem B14127473 : Blo 1100624 14127473 := bstep (se 2 (by rfl) ⟨5297802, by rfl⟩ : syracuseStep 14127473 = 10595605) B10595605
theorem B2789873 : Blo 1100624 2789873 := bstep (se 2 (by rfl) ⟨1046202, by rfl⟩ : syracuseStep 2789873 = 2092405) B2092405
theorem B2789923 : Blo 1100624 2789923 := bstep (se 1 (by rfl) ⟨2092442, by rfl⟩ : syracuseStep 2789923 = 4184885) B4184885
theorem B3347021 : Blo 1100624 3347021 := bstep (se 3 (by rfl) ⟨627566, by rfl⟩ : syracuseStep 3347021 = 1255133) B1255133
theorem B2790065 : Blo 1100624 2790065 := bstep (se 2 (by rfl) ⟨1046274, by rfl⟩ : syracuseStep 2790065 = 2092549) B2092549
theorem B6132485 : Blo 1100624 6132485 := bstep (se 4 (by rfl) ⟨574920, by rfl⟩ : syracuseStep 6132485 = 1149841) B1149841
theorem B5575715 : Blo 1100624 5575715 := bstep (se 1 (by rfl) ⟨4181786, by rfl⟩ : syracuseStep 5575715 = 8363573) B8363573
theorem B3970225 : Blo 1100624 3970225 := bstep (se 2 (by rfl) ⟨1488834, by rfl⟩ : syracuseStep 3970225 = 2977669) B2977669
theorem B1611137 : Blo 1100624 1611137 := bstep (se 2 (by rfl) ⟨604176, by rfl⟩ : syracuseStep 1611137 = 1208353) B1208353
theorem B10065293 : Blo 1100624 10065293 := bstep (se 3 (by rfl) ⟨1887242, by rfl⟩ : syracuseStep 10065293 = 3774485) B3774485
theorem B2791057 : Blo 1100624 2791057 := bstep (se 2 (by rfl) ⟨1046646, by rfl⟩ : syracuseStep 2791057 = 2093293) B2093293
theorem B21173987 : Blo 1100624 21173987 := bstep (se 1 (by rfl) ⟨15880490, by rfl⟩ : syracuseStep 21173987 = 31760981) B31760981
theorem B14718773 : Blo 1100624 14718773 := bstep (se 5 (by rfl) ⟨689942, by rfl⟩ : syracuseStep 14718773 = 1379885) B1379885
theorem B5576525 : Blo 1100624 5576525 := bstep (se 3 (by rfl) ⟨1045598, by rfl⟩ : syracuseStep 5576525 = 2091197) B2091197
theorem B2791331 : Blo 1100624 2791331 := bstep (se 1 (by rfl) ⟨2093498, by rfl⟩ : syracuseStep 2791331 = 4186997) B4186997
theorem B15112163 : Blo 1100624 15112163 := bstep (se 1 (by rfl) ⟨11334122, by rfl⟩ : syracuseStep 15112163 = 22668245) B22668245
theorem B2791523 : Blo 1100624 2791523 := bstep (se 1 (by rfl) ⟨2093642, by rfl⟩ : syracuseStep 2791523 = 4187285) B4187285
theorem B10590533 : Blo 1100624 10590533 := bstep (se 4 (by rfl) ⟨992862, by rfl⟩ : syracuseStep 10590533 = 1985725) B1985725
theorem B14129477 : Blo 1100624 14129477 := bstep (se 4 (by rfl) ⟨1324638, by rfl⟩ : syracuseStep 14129477 = 2649277) B2649277
theorem B1677665 : Blo 1100624 1677665 := bstep (se 2 (by rfl) ⟨629124, by rfl⟩ : syracuseStep 1677665 = 1258249) B1258249
theorem B12098117 : Blo 1100624 12098117 := bstep (se 4 (by rfl) ⟨1134198, by rfl⟩ : syracuseStep 12098117 = 2268397) B2268397
theorem B7543601 : Blo 1100624 7543601 := bstep (se 2 (by rfl) ⟨2828850, by rfl⟩ : syracuseStep 7543601 = 5657701) B5657701
theorem B15276853 : Blo 1100624 15276853 := bstep (se 5 (by rfl) ⟨716102, by rfl⟩ : syracuseStep 15276853 = 1432205) B1432205
theorem B2792465 : Blo 1100624 2792465 := bstep (se 2 (by rfl) ⟨1047174, by rfl⟩ : syracuseStep 2792465 = 2094349) B2094349
theorem B2792515 : Blo 1100624 2792515 := bstep (se 1 (by rfl) ⟨2094386, by rfl⟩ : syracuseStep 2792515 = 4188773) B4188773
theorem B3775619 : Blo 1100624 3775619 := bstep (se 1 (by rfl) ⟨2831714, by rfl⟩ : syracuseStep 3775619 = 5663429) B5663429
theorem B2792657 : Blo 1100624 2792657 := bstep (se 2 (by rfl) ⟨1047246, by rfl⟩ : syracuseStep 2792657 = 2094493) B2094493
theorem B3349745 : Blo 1100624 3349745 := bstep (se 2 (by rfl) ⟨1256154, by rfl⟩ : syracuseStep 3349745 = 2512309) B2512309
theorem B6790405 : Blo 1100624 6790405 := bstep (se 4 (by rfl) ⟨636600, by rfl⟩ : syracuseStep 6790405 = 1273201) B1273201
theorem B3775907 : Blo 1100624 3775907 := bstep (se 1 (by rfl) ⟨2831930, by rfl⟩ : syracuseStep 3775907 = 5663861) B5663861
theorem B57187781 : Blo 1100624 57187781 := bstep (se 4 (by rfl) ⟨5361354, by rfl⟩ : syracuseStep 57187781 = 10722709) B10722709
theorem B1908611 : Blo 1100624 1908611 := bstep (se 1 (by rfl) ⟨1431458, by rfl⟩ : syracuseStep 1908611 = 2862917) B2862917
theorem B2793649 : Blo 1100624 2793649 := bstep (se 2 (by rfl) ⟨1047618, by rfl⟩ : syracuseStep 2793649 = 2095237) B2095237
theorem B2793923 : Blo 1100624 2793923 := bstep (se 1 (by rfl) ⟨2095442, by rfl⟩ : syracuseStep 2793923 = 4190885) B4190885
theorem B2794115 : Blo 1100624 2794115 := bstep (se 1 (by rfl) ⟨2095586, by rfl⟩ : syracuseStep 2794115 = 4191173) B4191173
theorem B5579441 : Blo 1100624 5579441 := bstep (se 2 (by rfl) ⟨2092290, by rfl⟩ : syracuseStep 5579441 = 4184581) B4184581
theorem B2827043 : Blo 1100624 2827043 := bstep (se 1 (by rfl) ⟨2120282, by rfl⟩ : syracuseStep 2827043 = 4240565) B4240565
theorem B5449037 : Blo 1100624 5449037 := bstep (se 3 (by rfl) ⟨1021694, by rfl⟩ : syracuseStep 5449037 = 2043389) B2043389
theorem B7054897 : Blo 1100624 7054897 := bstep (se 2 (by rfl) ⟨2645586, by rfl⟩ : syracuseStep 7054897 = 5291173) B5291173
theorem B2795057 : Blo 1100624 2795057 := bstep (se 2 (by rfl) ⟨1048146, by rfl⟩ : syracuseStep 2795057 = 2096293) B2096293
theorem B2795107 : Blo 1100624 2795107 := bstep (se 1 (by rfl) ⟨2096330, by rfl⟩ : syracuseStep 2795107 = 4192661) B4192661
theorem B4368013 : Blo 1100624 4368013 := bstep (se 3 (by rfl) ⟨819002, by rfl⟩ : syracuseStep 4368013 = 1638005) B1638005
theorem B2795249 : Blo 1100624 2795249 := bstep (se 2 (by rfl) ⟨1048218, by rfl⟩ : syracuseStep 2795249 = 2096437) B2096437
theorem B4466765 : Blo 1100624 4466765 := bstep (se 3 (by rfl) ⟨837518, by rfl⟩ : syracuseStep 4466765 = 1675037) B1675037
theorem B5580899 : Blo 1100624 5580899 := bstep (se 1 (by rfl) ⟨4185674, by rfl⟩ : syracuseStep 5580899 = 8371349) B8371349
theorem B3353005 : Blo 1100624 3353005 := bstep (se 3 (by rfl) ⟨628688, by rfl⟩ : syracuseStep 3353005 = 1257377) B1257377
theorem B4237859 : Blo 1100624 4237859 := bstep (se 1 (by rfl) ⟨3178394, by rfl⟩ : syracuseStep 4237859 = 6356789) B6356789
theorem B5745421 : Blo 1100624 5745421 := bstep (se 3 (by rfl) ⟨1077266, by rfl⟩ : syracuseStep 5745421 = 2154533) B2154533
theorem B5581709 : Blo 1100624 5581709 := bstep (se 3 (by rfl) ⟨1046570, by rfl⟩ : syracuseStep 5581709 = 2093141) B2093141
theorem B2829745 : Blo 1100624 2829745 := bstep (se 2 (by rfl) ⟨1061154, by rfl⟩ : syracuseStep 2829745 = 2122309) B2122309
theorem B1322563 : Blo 1100624 1322563 := bstep (se 1 (by rfl) ⟨991922, by rfl⟩ : syracuseStep 1322563 = 1983845) B1983845
theorem B3714659 : Blo 1100624 3714659 := bstep (se 1 (by rfl) ⟨2785994, by rfl⟩ : syracuseStep 3714659 = 5571989) B5571989
theorem B26783459 : Blo 1100624 26783459 := bstep (se 1 (by rfl) ⟨20087594, by rfl⟩ : syracuseStep 26783459 = 40175189) B40175189
theorem B4468451 : Blo 1100624 4468451 := bstep (se 1 (by rfl) ⟨3351338, by rfl⟩ : syracuseStep 4468451 = 6702677) B6702677
theorem B3714929 : Blo 1100624 3714929 := bstep (se 2 (by rfl) ⟨1393098, by rfl⟩ : syracuseStep 3714929 = 2786197) B2786197
theorem B28225421 : Blo 1100624 28225421 := bstep (se 3 (by rfl) ⟨5292266, by rfl⟩ : syracuseStep 28225421 = 10584533) B10584533
theorem B9416675 : Blo 1100624 9416675 := bstep (se 1 (by rfl) ⟨7062506, by rfl⟩ : syracuseStep 9416675 = 14125013) B14125013
theorem B2830403 : Blo 1100624 2830403 := bstep (se 1 (by rfl) ⟨2122802, by rfl⟩ : syracuseStep 2830403 = 4245605) B4245605
theorem B1650947 : Blo 1100624 1650947 := bstep (se 1 (by rfl) ⟨1238210, by rfl⟩ : syracuseStep 1650947 = 2476421) B2476421
theorem B1650977 : Blo 1100624 1650977 := bstep (se 2 (by rfl) ⟨619116, by rfl⟩ : syracuseStep 1650977 = 1238233) B1238233
theorem B1650995 : Blo 1100624 1650995 := bstep (se 1 (by rfl) ⟨1238246, by rfl⟩ : syracuseStep 1650995 = 2476493) B2476493
theorem B1651025 : Blo 1100624 1651025 := bstep (se 2 (by rfl) ⟨619134, by rfl⟩ : syracuseStep 1651025 = 1238269) B1238269
theorem B1651043 : Blo 1100624 1651043 := bstep (se 1 (by rfl) ⟨1238282, by rfl⟩ : syracuseStep 1651043 = 2476565) B2476565
theorem B1651073 : Blo 1100624 1651073 := bstep (se 2 (by rfl) ⟨619152, by rfl⟩ : syracuseStep 1651073 = 1238305) B1238305
theorem B3715469 : Blo 1100624 3715469 := bstep (se 3 (by rfl) ⟨696650, by rfl⟩ : syracuseStep 3715469 = 1393301) B1393301
theorem B1651091 : Blo 1100624 1651091 := bstep (se 1 (by rfl) ⟨1238318, by rfl⟩ : syracuseStep 1651091 = 2476637) B2476637
theorem B1651121 : Blo 1100624 1651121 := bstep (se 2 (by rfl) ⟨619170, by rfl⟩ : syracuseStep 1651121 = 1238341) B1238341
theorem B1651139 : Blo 1100624 1651139 := bstep (se 1 (by rfl) ⟨1238354, by rfl⟩ : syracuseStep 1651139 = 2476709) B2476709
theorem B3715523 : Blo 1100624 3715523 := bstep (se 1 (by rfl) ⟨2786642, by rfl⟩ : syracuseStep 3715523 = 5573285) B5573285
theorem B1651169 : Blo 1100624 1651169 := bstep (se 2 (by rfl) ⟨619188, by rfl⟩ : syracuseStep 1651169 = 1238377) B1238377
theorem B10596835 : Blo 1100624 10596835 := bstep (se 1 (by rfl) ⟨7947626, by rfl⟩ : syracuseStep 10596835 = 15895253) B15895253
theorem B1651187 : Blo 1100624 1651187 := bstep (se 1 (by rfl) ⟨1238390, by rfl⟩ : syracuseStep 1651187 = 2476781) B2476781
theorem B1651217 : Blo 1100624 1651217 := bstep (se 2 (by rfl) ⟨619206, by rfl⟩ : syracuseStep 1651217 = 1238413) B1238413
theorem B1651235 : Blo 1100624 1651235 := bstep (se 1 (by rfl) ⟨1238426, by rfl⟩ : syracuseStep 1651235 = 2476853) B2476853
theorem B1651265 : Blo 1100624 1651265 := bstep (se 2 (by rfl) ⟨619224, by rfl⟩ : syracuseStep 1651265 = 1238449) B1238449
theorem B1651283 : Blo 1100624 1651283 := bstep (se 1 (by rfl) ⟨1238462, by rfl⟩ : syracuseStep 1651283 = 2476925) B2476925
theorem B1651313 : Blo 1100624 1651313 := bstep (se 2 (by rfl) ⟨619242, by rfl⟩ : syracuseStep 1651313 = 1238485) B1238485
theorem B1651331 : Blo 1100624 1651331 := bstep (se 1 (by rfl) ⟨1238498, by rfl⟩ : syracuseStep 1651331 = 2476997) B2476997
theorem B1651361 : Blo 1100624 1651361 := bstep (se 2 (by rfl) ⟨619260, by rfl⟩ : syracuseStep 1651361 = 1238521) B1238521
theorem B1651379 : Blo 1100624 1651379 := bstep (se 1 (by rfl) ⟨1238534, by rfl⟩ : syracuseStep 1651379 = 2477069) B2477069
theorem B1651409 : Blo 1100624 1651409 := bstep (se 2 (by rfl) ⟨619278, by rfl⟩ : syracuseStep 1651409 = 1238557) B1238557
theorem B3715793 : Blo 1100624 3715793 := bstep (se 2 (by rfl) ⟨1393422, by rfl⟩ : syracuseStep 3715793 = 2786845) B2786845
theorem B1651427 : Blo 1100624 1651427 := bstep (se 1 (by rfl) ⟨1238570, by rfl⟩ : syracuseStep 1651427 = 2477141) B2477141
theorem B1651457 : Blo 1100624 1651457 := bstep (se 2 (by rfl) ⟨619296, by rfl⟩ : syracuseStep 1651457 = 1238593) B1238593
theorem B1651475 : Blo 1100624 1651475 := bstep (se 1 (by rfl) ⟨1238606, by rfl⟩ : syracuseStep 1651475 = 2477213) B2477213
theorem B1651505 : Blo 1100624 1651505 := bstep (se 2 (by rfl) ⟨619314, by rfl⟩ : syracuseStep 1651505 = 1238629) B1238629
theorem B1651523 : Blo 1100624 1651523 := bstep (se 1 (by rfl) ⟨1238642, by rfl⟩ : syracuseStep 1651523 = 2477285) B2477285
theorem B1651553 : Blo 1100624 1651553 := bstep (se 2 (by rfl) ⟨619332, by rfl⟩ : syracuseStep 1651553 = 1238665) B1238665
theorem B1913699 : Blo 1100624 1913699 := bstep (se 1 (by rfl) ⟨1435274, by rfl⟩ : syracuseStep 1913699 = 2870549) B2870549
theorem B15872881 : Blo 1100624 15872881 := bstep (se 2 (by rfl) ⟨5952330, by rfl⟩ : syracuseStep 15872881 = 11904661) B11904661
theorem B1651571 : Blo 1100624 1651571 := bstep (se 1 (by rfl) ⟨1238678, by rfl⟩ : syracuseStep 1651571 = 2477357) B2477357
theorem B1651601 : Blo 1100624 1651601 := bstep (se 2 (by rfl) ⟨619350, by rfl⟩ : syracuseStep 1651601 = 1238701) B1238701
theorem B1651619 : Blo 1100624 1651619 := bstep (se 1 (by rfl) ⟨1238714, by rfl⟩ : syracuseStep 1651619 = 2477429) B2477429
theorem B1651649 : Blo 1100624 1651649 := bstep (se 2 (by rfl) ⟨619368, by rfl⟩ : syracuseStep 1651649 = 1238737) B1238737
theorem B1651667 : Blo 1100624 1651667 := bstep (se 1 (by rfl) ⟨1238750, by rfl⟩ : syracuseStep 1651667 = 2477501) B2477501
theorem B1651697 : Blo 1100624 1651697 := bstep (se 2 (by rfl) ⟨619386, by rfl⟩ : syracuseStep 1651697 = 1238773) B1238773
theorem B1651715 : Blo 1100624 1651715 := bstep (se 1 (by rfl) ⟨1238786, by rfl⟩ : syracuseStep 1651715 = 2477573) B2477573
theorem B1651745 : Blo 1100624 1651745 := bstep (se 2 (by rfl) ⟨619404, by rfl⟩ : syracuseStep 1651745 = 1238809) B1238809
theorem B1651763 : Blo 1100624 1651763 := bstep (se 1 (by rfl) ⟨1238822, by rfl⟩ : syracuseStep 1651763 = 2477645) B2477645
theorem B1651793 : Blo 1100624 1651793 := bstep (se 2 (by rfl) ⟨619422, by rfl⟩ : syracuseStep 1651793 = 1238845) B1238845
theorem B1651811 : Blo 1100624 1651811 := bstep (se 1 (by rfl) ⟨1238858, by rfl⟩ : syracuseStep 1651811 = 2477717) B2477717
theorem B1651841 : Blo 1100624 1651841 := bstep (se 2 (by rfl) ⟨619440, by rfl⟩ : syracuseStep 1651841 = 1238881) B1238881
theorem B1651859 : Blo 1100624 1651859 := bstep (se 1 (by rfl) ⟨1238894, by rfl⟩ : syracuseStep 1651859 = 2477789) B2477789
theorem B1651889 : Blo 1100624 1651889 := bstep (se 2 (by rfl) ⟨619458, by rfl⟩ : syracuseStep 1651889 = 1238917) B1238917
theorem B1651907 : Blo 1100624 1651907 := bstep (se 1 (by rfl) ⟨1238930, by rfl⟩ : syracuseStep 1651907 = 2477861) B2477861
theorem B1651937 : Blo 1100624 1651937 := bstep (se 2 (by rfl) ⟨619476, by rfl⟩ : syracuseStep 1651937 = 1238953) B1238953
theorem B10073315 : Blo 1100624 10073315 := bstep (se 1 (by rfl) ⟨7554986, by rfl⟩ : syracuseStep 10073315 = 15109973) B15109973
theorem B3716333 : Blo 1100624 3716333 := bstep (se 3 (by rfl) ⟨696812, by rfl⟩ : syracuseStep 3716333 = 1393625) B1393625
theorem B1651955 : Blo 1100624 1651955 := bstep (se 1 (by rfl) ⟨1238966, by rfl⟩ : syracuseStep 1651955 = 2477933) B2477933
theorem B7156997 : Blo 1100624 7156997 := bstep (se 4 (by rfl) ⟨670968, by rfl⟩ : syracuseStep 7156997 = 1341937) B1341937
theorem B1651985 : Blo 1100624 1651985 := bstep (se 2 (by rfl) ⟨619494, by rfl⟩ : syracuseStep 1651985 = 1238989) B1238989
theorem B3716387 : Blo 1100624 3716387 := bstep (se 1 (by rfl) ⟨2787290, by rfl⟩ : syracuseStep 3716387 = 5574581) B5574581
theorem B1652003 : Blo 1100624 1652003 := bstep (se 1 (by rfl) ⟨1239002, by rfl⟩ : syracuseStep 1652003 = 2478005) B2478005
theorem B1652033 : Blo 1100624 1652033 := bstep (se 2 (by rfl) ⟨619512, by rfl⟩ : syracuseStep 1652033 = 1239025) B1239025
theorem B1324355 : Blo 1100624 1324355 := bstep (se 1 (by rfl) ⟨993266, by rfl⟩ : syracuseStep 1324355 = 1986533) B1986533
theorem B1652051 : Blo 1100624 1652051 := bstep (se 1 (by rfl) ⟨1239038, by rfl⟩ : syracuseStep 1652051 = 2478077) B2478077
theorem B1652081 : Blo 1100624 1652081 := bstep (se 2 (by rfl) ⟨619530, by rfl⟩ : syracuseStep 1652081 = 1239061) B1239061
theorem B1652099 : Blo 1100624 1652099 := bstep (se 1 (by rfl) ⟨1239074, by rfl⟩ : syracuseStep 1652099 = 2478149) B2478149
theorem B1652129 : Blo 1100624 1652129 := bstep (se 2 (by rfl) ⟨619548, by rfl⟩ : syracuseStep 1652129 = 1239097) B1239097
theorem B3978659 : Blo 1100624 3978659 := bstep (se 1 (by rfl) ⟨2983994, by rfl⟩ : syracuseStep 3978659 = 5967989) B5967989
theorem B1652147 : Blo 1100624 1652147 := bstep (se 1 (by rfl) ⟨1239110, by rfl⟩ : syracuseStep 1652147 = 2478221) B2478221
theorem B1652177 : Blo 1100624 1652177 := bstep (se 2 (by rfl) ⟨619566, by rfl⟩ : syracuseStep 1652177 = 1239133) B1239133
theorem B1652195 : Blo 1100624 1652195 := bstep (se 1 (by rfl) ⟨1239146, by rfl⟩ : syracuseStep 1652195 = 2478293) B2478293
theorem B1652225 : Blo 1100624 1652225 := bstep (se 2 (by rfl) ⟨619584, by rfl⟩ : syracuseStep 1652225 = 1239169) B1239169
theorem B5977613 : Blo 1100624 5977613 := bstep (se 3 (by rfl) ⟨1120802, by rfl⟩ : syracuseStep 5977613 = 2241605) B2241605
theorem B1652243 : Blo 1100624 1652243 := bstep (se 1 (by rfl) ⟨1239182, by rfl⟩ : syracuseStep 1652243 = 2478365) B2478365
theorem B3716657 : Blo 1100624 3716657 := bstep (se 2 (by rfl) ⟨1393746, by rfl⟩ : syracuseStep 3716657 = 2787493) B2787493
theorem B1652273 : Blo 1100624 1652273 := bstep (se 2 (by rfl) ⟨619602, by rfl⟩ : syracuseStep 1652273 = 1239205) B1239205
theorem B1652291 : Blo 1100624 1652291 := bstep (se 1 (by rfl) ⟨1239218, by rfl⟩ : syracuseStep 1652291 = 2478437) B2478437
theorem B4470349 : Blo 1100624 4470349 := bstep (se 3 (by rfl) ⟨838190, by rfl⟩ : syracuseStep 4470349 = 1676381) B1676381
theorem B1652321 : Blo 1100624 1652321 := bstep (se 2 (by rfl) ⟨619620, by rfl⟩ : syracuseStep 1652321 = 1239241) B1239241
theorem B8500835 : Blo 1100624 8500835 := bstep (se 1 (by rfl) ⟨6375626, by rfl⟩ : syracuseStep 8500835 = 12751253) B12751253
theorem B1652339 : Blo 1100624 1652339 := bstep (se 1 (by rfl) ⟨1239254, by rfl⟩ : syracuseStep 1652339 = 2478509) B2478509
theorem B14104205 : Blo 1100624 14104205 := bstep (se 3 (by rfl) ⟨2644538, by rfl⟩ : syracuseStep 14104205 = 5289077) B5289077
theorem B1652369 : Blo 1100624 1652369 := bstep (se 2 (by rfl) ⟨619638, by rfl⟩ : syracuseStep 1652369 = 1239277) B1239277
theorem B1652387 : Blo 1100624 1652387 := bstep (se 1 (by rfl) ⟨1239290, by rfl⟩ : syracuseStep 1652387 = 2478581) B2478581
theorem B1652417 : Blo 1100624 1652417 := bstep (se 2 (by rfl) ⟨619656, by rfl⟩ : syracuseStep 1652417 = 1239313) B1239313
theorem B1652435 : Blo 1100624 1652435 := bstep (se 1 (by rfl) ⟨1239326, by rfl⟩ : syracuseStep 1652435 = 2478653) B2478653
theorem B8369891 : Blo 1100624 8369891 := bstep (se 1 (by rfl) ⟨6277418, by rfl⟩ : syracuseStep 8369891 = 12554837) B12554837
theorem B1652465 : Blo 1100624 1652465 := bstep (se 2 (by rfl) ⟨619674, by rfl⟩ : syracuseStep 1652465 = 1239349) B1239349
theorem B5584625 : Blo 1100624 5584625 := bstep (se 2 (by rfl) ⟨2094234, by rfl⟩ : syracuseStep 5584625 = 4188469) B4188469
theorem B1652483 : Blo 1100624 1652483 := bstep (se 1 (by rfl) ⟨1239362, by rfl⟩ : syracuseStep 1652483 = 2478725) B2478725
theorem B1652513 : Blo 1100624 1652513 := bstep (se 2 (by rfl) ⟨619692, by rfl⟩ : syracuseStep 1652513 = 1239385) B1239385
theorem B1652531 : Blo 1100624 1652531 := bstep (se 1 (by rfl) ⟨1239398, by rfl⟩ : syracuseStep 1652531 = 2478797) B2478797
theorem B1652561 : Blo 1100624 1652561 := bstep (se 2 (by rfl) ⟨619710, by rfl⟩ : syracuseStep 1652561 = 1239421) B1239421
theorem B1652579 : Blo 1100624 1652579 := bstep (se 1 (by rfl) ⟨1239434, by rfl⟩ : syracuseStep 1652579 = 2478869) B2478869
theorem B1652609 : Blo 1100624 1652609 := bstep (se 2 (by rfl) ⟨619728, by rfl⟩ : syracuseStep 1652609 = 1239457) B1239457
theorem B6272909 : Blo 1100624 6272909 := bstep (se 3 (by rfl) ⟨1176170, by rfl⟩ : syracuseStep 6272909 = 2352341) B2352341
theorem B1652627 : Blo 1100624 1652627 := bstep (se 1 (by rfl) ⟨1239470, by rfl⟩ : syracuseStep 1652627 = 2478941) B2478941
theorem B1652657 : Blo 1100624 1652657 := bstep (se 2 (by rfl) ⟨619746, by rfl⟩ : syracuseStep 1652657 = 1239493) B1239493
theorem B1652675 : Blo 1100624 1652675 := bstep (se 1 (by rfl) ⟨1239506, by rfl⟩ : syracuseStep 1652675 = 2479013) B2479013
theorem B1652705 : Blo 1100624 1652705 := bstep (se 2 (by rfl) ⟨619764, by rfl⟩ : syracuseStep 1652705 = 1239529) B1239529
theorem B1652723 : Blo 1100624 1652723 := bstep (se 1 (by rfl) ⟨1239542, by rfl⟩ : syracuseStep 1652723 = 2479085) B2479085
theorem B1652753 : Blo 1100624 1652753 := bstep (se 2 (by rfl) ⟨619782, by rfl⟩ : syracuseStep 1652753 = 1239565) B1239565
theorem B1652771 : Blo 1100624 1652771 := bstep (se 1 (by rfl) ⟨1239578, by rfl⟩ : syracuseStep 1652771 = 2479157) B2479157
theorem B1652801 : Blo 1100624 1652801 := bstep (se 2 (by rfl) ⟨619800, by rfl⟩ : syracuseStep 1652801 = 1239601) B1239601
theorem B3717197 : Blo 1100624 3717197 := bstep (se 3 (by rfl) ⟨696974, by rfl⟩ : syracuseStep 3717197 = 1393949) B1393949
theorem B1652819 : Blo 1100624 1652819 := bstep (se 1 (by rfl) ⟨1239614, by rfl⟩ : syracuseStep 1652819 = 2479229) B2479229
theorem B1652849 : Blo 1100624 1652849 := bstep (se 2 (by rfl) ⟨619818, by rfl⟩ : syracuseStep 1652849 = 1239637) B1239637
theorem B3717251 : Blo 1100624 3717251 := bstep (se 1 (by rfl) ⟨2787938, by rfl⟩ : syracuseStep 3717251 = 5575877) B5575877
theorem B1652867 : Blo 1100624 1652867 := bstep (se 1 (by rfl) ⟨1239650, by rfl⟩ : syracuseStep 1652867 = 2479301) B2479301
theorem B1652897 : Blo 1100624 1652897 := bstep (se 2 (by rfl) ⟨619836, by rfl⟩ : syracuseStep 1652897 = 1239673) B1239673
theorem B1652915 : Blo 1100624 1652915 := bstep (se 1 (by rfl) ⟨1239686, by rfl⟩ : syracuseStep 1652915 = 2479373) B2479373
theorem B1652945 : Blo 1100624 1652945 := bstep (se 2 (by rfl) ⟨619854, by rfl⟩ : syracuseStep 1652945 = 1239709) B1239709
theorem B1652963 : Blo 1100624 1652963 := bstep (se 1 (by rfl) ⟨1239722, by rfl⟩ : syracuseStep 1652963 = 2479445) B2479445
theorem B1652993 : Blo 1100624 1652993 := bstep (se 2 (by rfl) ⟨619872, by rfl⟩ : syracuseStep 1652993 = 1239745) B1239745
theorem B1653011 : Blo 1100624 1653011 := bstep (se 1 (by rfl) ⟨1239758, by rfl⟩ : syracuseStep 1653011 = 2479517) B2479517
theorem B1653041 : Blo 1100624 1653041 := bstep (se 2 (by rfl) ⟨619890, by rfl⟩ : syracuseStep 1653041 = 1239781) B1239781
theorem B1653059 : Blo 1100624 1653059 := bstep (se 1 (by rfl) ⟨1239794, by rfl⟩ : syracuseStep 1653059 = 2479589) B2479589
theorem B1653089 : Blo 1100624 1653089 := bstep (se 2 (by rfl) ⟨619908, by rfl⟩ : syracuseStep 1653089 = 1239817) B1239817
theorem B8927587 : Blo 1100624 8927587 := bstep (se 1 (by rfl) ⟨6695690, by rfl⟩ : syracuseStep 8927587 = 13391381) B13391381
theorem B1653107 : Blo 1100624 1653107 := bstep (se 1 (by rfl) ⟨1239830, by rfl⟩ : syracuseStep 1653107 = 2479661) B2479661
theorem B3717521 : Blo 1100624 3717521 := bstep (se 2 (by rfl) ⟨1394070, by rfl⟩ : syracuseStep 3717521 = 2788141) B2788141
theorem B1653137 : Blo 1100624 1653137 := bstep (se 2 (by rfl) ⟨619926, by rfl⟩ : syracuseStep 1653137 = 1239853) B1239853
theorem B1653155 : Blo 1100624 1653155 := bstep (se 1 (by rfl) ⟨1239866, by rfl⟩ : syracuseStep 1653155 = 2479733) B2479733
theorem B1653185 : Blo 1100624 1653185 := bstep (se 2 (by rfl) ⟨619944, by rfl⟩ : syracuseStep 1653185 = 1239889) B1239889
theorem B1653203 : Blo 1100624 1653203 := bstep (se 1 (by rfl) ⟨1239902, by rfl⟩ : syracuseStep 1653203 = 2479805) B2479805
theorem B1653233 : Blo 1100624 1653233 := bstep (se 2 (by rfl) ⟨619962, by rfl⟩ : syracuseStep 1653233 = 1239925) B1239925
theorem B1653251 : Blo 1100624 1653251 := bstep (se 1 (by rfl) ⟨1239938, by rfl⟩ : syracuseStep 1653251 = 2479877) B2479877
theorem B1653281 : Blo 1100624 1653281 := bstep (se 2 (by rfl) ⟨619980, by rfl⟩ : syracuseStep 1653281 = 1239961) B1239961
theorem B1653299 : Blo 1100624 1653299 := bstep (se 1 (by rfl) ⟨1239974, by rfl⟩ : syracuseStep 1653299 = 2479949) B2479949
theorem B15874613 : Blo 1100624 15874613 := bstep (se 5 (by rfl) ⟨744122, by rfl⟩ : syracuseStep 15874613 = 1488245) B1488245
theorem B1653329 : Blo 1100624 1653329 := bstep (se 2 (by rfl) ⟨619998, by rfl⟩ : syracuseStep 1653329 = 1239997) B1239997
theorem B1653347 : Blo 1100624 1653347 := bstep (se 1 (by rfl) ⟨1240010, by rfl⟩ : syracuseStep 1653347 = 2480021) B2480021
theorem B42318449 : Blo 1100624 42318449 := bstep (se 2 (by rfl) ⟨15869418, by rfl⟩ : syracuseStep 42318449 = 31738837) B31738837
theorem B1653377 : Blo 1100624 1653377 := bstep (se 2 (by rfl) ⟨620016, by rfl⟩ : syracuseStep 1653377 = 1240033) B1240033
theorem B1653395 : Blo 1100624 1653395 := bstep (se 1 (by rfl) ⟨1240046, by rfl⟩ : syracuseStep 1653395 = 2480093) B2480093
theorem B1653425 : Blo 1100624 1653425 := bstep (se 2 (by rfl) ⟨620034, by rfl⟩ : syracuseStep 1653425 = 1240069) B1240069
theorem B1653443 : Blo 1100624 1653443 := bstep (se 1 (by rfl) ⟨1240082, by rfl⟩ : syracuseStep 1653443 = 2480165) B2480165
theorem B1653473 : Blo 1100624 1653473 := bstep (se 2 (by rfl) ⟨620052, by rfl⟩ : syracuseStep 1653473 = 1240105) B1240105
theorem B1653491 : Blo 1100624 1653491 := bstep (se 1 (by rfl) ⟨1240118, by rfl⟩ : syracuseStep 1653491 = 2480237) B2480237
theorem B7060229 : Blo 1100624 7060229 := bstep (se 4 (by rfl) ⟨661896, by rfl⟩ : syracuseStep 7060229 = 1323793) B1323793
theorem B1653521 : Blo 1100624 1653521 := bstep (se 2 (by rfl) ⟨620070, by rfl⟩ : syracuseStep 1653521 = 1240141) B1240141
theorem B1653539 : Blo 1100624 1653539 := bstep (se 1 (by rfl) ⟨1240154, by rfl⟩ : syracuseStep 1653539 = 2480309) B2480309
theorem B1653569 : Blo 1100624 1653569 := bstep (se 2 (by rfl) ⟨620088, by rfl⟩ : syracuseStep 1653569 = 1240177) B1240177
theorem B1653587 : Blo 1100624 1653587 := bstep (se 1 (by rfl) ⟨1240190, by rfl⟩ : syracuseStep 1653587 = 2480381) B2480381
theorem B1653617 : Blo 1100624 1653617 := bstep (se 2 (by rfl) ⟨620106, by rfl⟩ : syracuseStep 1653617 = 1240213) B1240213
theorem B1653635 : Blo 1100624 1653635 := bstep (se 1 (by rfl) ⟨1240226, by rfl⟩ : syracuseStep 1653635 = 2480453) B2480453
theorem B1653665 : Blo 1100624 1653665 := bstep (se 2 (by rfl) ⟨620124, by rfl⟩ : syracuseStep 1653665 = 1240249) B1240249
theorem B3718061 : Blo 1100624 3718061 := bstep (se 3 (by rfl) ⟨697136, by rfl⟩ : syracuseStep 3718061 = 1394273) B1394273
theorem B1653683 : Blo 1100624 1653683 := bstep (se 1 (by rfl) ⟨1240262, by rfl⟩ : syracuseStep 1653683 = 2480525) B2480525
theorem B1653713 : Blo 1100624 1653713 := bstep (se 2 (by rfl) ⟨620142, by rfl⟩ : syracuseStep 1653713 = 1240285) B1240285
theorem B3718115 : Blo 1100624 3718115 := bstep (se 1 (by rfl) ⟨2788586, by rfl⟩ : syracuseStep 3718115 = 5577173) B5577173
theorem B1653731 : Blo 1100624 1653731 := bstep (se 1 (by rfl) ⟨1240298, by rfl⟩ : syracuseStep 1653731 = 2480597) B2480597
theorem B1883123 : Blo 1100624 1883123 := bstep (se 1 (by rfl) ⟨1412342, by rfl⟩ : syracuseStep 1883123 = 2824685) B2824685
theorem B1653761 : Blo 1100624 1653761 := bstep (se 2 (by rfl) ⟨620160, by rfl⟩ : syracuseStep 1653761 = 1240321) B1240321
theorem B3587075 : Blo 1100624 3587075 := bstep (se 1 (by rfl) ⟨2690306, by rfl⟩ : syracuseStep 3587075 = 5380613) B5380613
theorem B5291021 : Blo 1100624 5291021 := bstep (se 3 (by rfl) ⟨992066, by rfl⟩ : syracuseStep 5291021 = 1984133) B1984133
theorem B1653779 : Blo 1100624 1653779 := bstep (se 1 (by rfl) ⟨1240334, by rfl⟩ : syracuseStep 1653779 = 2480669) B2480669
theorem B1653809 : Blo 1100624 1653809 := bstep (se 2 (by rfl) ⟨620178, by rfl⟩ : syracuseStep 1653809 = 1240357) B1240357
theorem B1653827 : Blo 1100624 1653827 := bstep (se 1 (by rfl) ⟨1240370, by rfl⟩ : syracuseStep 1653827 = 2480741) B2480741
theorem B1653857 : Blo 1100624 1653857 := bstep (se 2 (by rfl) ⟨620196, by rfl⟩ : syracuseStep 1653857 = 1240393) B1240393
theorem B1653875 : Blo 1100624 1653875 := bstep (se 1 (by rfl) ⟨1240406, by rfl⟩ : syracuseStep 1653875 = 2480813) B2480813
theorem B1653905 : Blo 1100624 1653905 := bstep (se 2 (by rfl) ⟨620214, by rfl⟩ : syracuseStep 1653905 = 1240429) B1240429
theorem B1653923 : Blo 1100624 1653923 := bstep (se 1 (by rfl) ⟨1240442, by rfl⟩ : syracuseStep 1653923 = 2480885) B2480885
theorem B5586083 : Blo 1100624 5586083 := bstep (se 1 (by rfl) ⟨4189562, by rfl⟩ : syracuseStep 5586083 = 8379125) B8379125
theorem B1653953 : Blo 1100624 1653953 := bstep (se 2 (by rfl) ⟨620232, by rfl⟩ : syracuseStep 1653953 = 1240465) B1240465
theorem B1653971 : Blo 1100624 1653971 := bstep (se 1 (by rfl) ⟨1240478, by rfl⟩ : syracuseStep 1653971 = 2480957) B2480957
theorem B3718385 : Blo 1100624 3718385 := bstep (se 2 (by rfl) ⟨1394394, by rfl⟩ : syracuseStep 3718385 = 2788789) B2788789
theorem B1654001 : Blo 1100624 1654001 := bstep (se 2 (by rfl) ⟨620250, by rfl⟩ : syracuseStep 1654001 = 1240501) B1240501
theorem B1654019 : Blo 1100624 1654019 := bstep (se 1 (by rfl) ⟨1240514, by rfl⟩ : syracuseStep 1654019 = 2481029) B2481029
theorem B1195267 : Blo 1100624 1195267 := bstep (se 1 (by rfl) ⟨896450, by rfl⟩ : syracuseStep 1195267 = 1792901) B1792901
theorem B1654049 : Blo 1100624 1654049 := bstep (se 2 (by rfl) ⟨620268, by rfl⟩ : syracuseStep 1654049 = 1240537) B1240537
theorem B1654067 : Blo 1100624 1654067 := bstep (se 1 (by rfl) ⟨1240550, by rfl⟩ : syracuseStep 1654067 = 2481101) B2481101
theorem B1654097 : Blo 1100624 1654097 := bstep (se 2 (by rfl) ⟨620286, by rfl⟩ : syracuseStep 1654097 = 1240573) B1240573
theorem B1654115 : Blo 1100624 1654115 := bstep (se 1 (by rfl) ⟨1240586, by rfl⟩ : syracuseStep 1654115 = 2481173) B2481173
theorem B8928625 : Blo 1100624 8928625 := bstep (se 2 (by rfl) ⟨3348234, by rfl⟩ : syracuseStep 8928625 = 6696469) B6696469
theorem B1654145 : Blo 1100624 1654145 := bstep (se 2 (by rfl) ⟨620304, by rfl⟩ : syracuseStep 1654145 = 1240609) B1240609
theorem B7945613 : Blo 1100624 7945613 := bstep (se 3 (by rfl) ⟨1489802, by rfl⟩ : syracuseStep 7945613 = 2979605) B2979605
theorem B1490321 : Blo 1100624 1490321 := bstep (se 2 (by rfl) ⟨558870, by rfl⟩ : syracuseStep 1490321 = 1117741) B1117741
theorem B1654163 : Blo 1100624 1654163 := bstep (se 1 (by rfl) ⟨1240622, by rfl⟩ : syracuseStep 1654163 = 2481245) B2481245
theorem B1654193 : Blo 1100624 1654193 := bstep (se 2 (by rfl) ⟨620322, by rfl⟩ : syracuseStep 1654193 = 1240645) B1240645
theorem B1654211 : Blo 1100624 1654211 := bstep (se 1 (by rfl) ⟨1240658, by rfl⟩ : syracuseStep 1654211 = 2481317) B2481317
theorem B1654241 : Blo 1100624 1654241 := bstep (se 2 (by rfl) ⟨620340, by rfl⟩ : syracuseStep 1654241 = 1240681) B1240681
theorem B1654259 : Blo 1100624 1654259 := bstep (se 1 (by rfl) ⟨1240694, by rfl⟩ : syracuseStep 1654259 = 2481389) B2481389
theorem B1654289 : Blo 1100624 1654289 := bstep (se 2 (by rfl) ⟨620358, by rfl⟩ : syracuseStep 1654289 = 1240717) B1240717
theorem B1654307 : Blo 1100624 1654307 := bstep (se 1 (by rfl) ⟨1240730, by rfl⟩ : syracuseStep 1654307 = 2481461) B2481461
theorem B1654337 : Blo 1100624 1654337 := bstep (se 2 (by rfl) ⟨620376, by rfl⟩ : syracuseStep 1654337 = 1240753) B1240753
theorem B1654355 : Blo 1100624 1654355 := bstep (se 1 (by rfl) ⟨1240766, by rfl⟩ : syracuseStep 1654355 = 2481533) B2481533
theorem B3358307 : Blo 1100624 3358307 := bstep (se 1 (by rfl) ⟨2518730, by rfl⟩ : syracuseStep 3358307 = 5037461) B5037461
theorem B1654385 : Blo 1100624 1654385 := bstep (se 2 (by rfl) ⟨620394, by rfl⟩ : syracuseStep 1654385 = 1240789) B1240789
theorem B1654403 : Blo 1100624 1654403 := bstep (se 1 (by rfl) ⟨1240802, by rfl⟩ : syracuseStep 1654403 = 2481605) B2481605
theorem B1654433 : Blo 1100624 1654433 := bstep (se 2 (by rfl) ⟨620412, by rfl⟩ : syracuseStep 1654433 = 1240825) B1240825
theorem B1654451 : Blo 1100624 1654451 := bstep (se 1 (by rfl) ⟨1240838, by rfl⟩ : syracuseStep 1654451 = 2481677) B2481677
theorem B1654481 : Blo 1100624 1654481 := bstep (se 2 (by rfl) ⟨620430, by rfl⟩ : syracuseStep 1654481 = 1240861) B1240861
theorem B1654499 : Blo 1100624 1654499 := bstep (se 1 (by rfl) ⟨1240874, by rfl⟩ : syracuseStep 1654499 = 2481749) B2481749
theorem B1654529 : Blo 1100624 1654529 := bstep (se 2 (by rfl) ⟨620448, by rfl⟩ : syracuseStep 1654529 = 1240897) B1240897
theorem B3718925 : Blo 1100624 3718925 := bstep (se 3 (by rfl) ⟨697298, by rfl⟩ : syracuseStep 3718925 = 1394597) B1394597
theorem B1654547 : Blo 1100624 1654547 := bstep (se 1 (by rfl) ⟨1240910, by rfl⟩ : syracuseStep 1654547 = 2481821) B2481821
theorem B1326883 : Blo 1100624 1326883 := bstep (se 1 (by rfl) ⟨995162, by rfl⟩ : syracuseStep 1326883 = 1990325) B1990325
theorem B1654577 : Blo 1100624 1654577 := bstep (se 2 (by rfl) ⟨620466, by rfl⟩ : syracuseStep 1654577 = 1240933) B1240933
theorem B3718979 : Blo 1100624 3718979 := bstep (se 1 (by rfl) ⟨2789234, by rfl⟩ : syracuseStep 3718979 = 5578469) B5578469
theorem B1654595 : Blo 1100624 1654595 := bstep (se 1 (by rfl) ⟨1240946, by rfl⟩ : syracuseStep 1654595 = 2481893) B2481893
theorem B1654625 : Blo 1100624 1654625 := bstep (se 2 (by rfl) ⟨620484, by rfl⟩ : syracuseStep 1654625 = 1240969) B1240969
theorem B1654643 : Blo 1100624 1654643 := bstep (se 1 (by rfl) ⟨1240982, by rfl⟩ : syracuseStep 1654643 = 2481965) B2481965
theorem B1654673 : Blo 1100624 1654673 := bstep (se 2 (by rfl) ⟨620502, by rfl⟩ : syracuseStep 1654673 = 1241005) B1241005
theorem B1654691 : Blo 1100624 1654691 := bstep (se 1 (by rfl) ⟨1241018, by rfl⟩ : syracuseStep 1654691 = 2482037) B2482037
theorem B1654721 : Blo 1100624 1654721 := bstep (se 2 (by rfl) ⟨620520, by rfl⟩ : syracuseStep 1654721 = 1241041) B1241041
theorem B5586893 : Blo 1100624 5586893 := bstep (se 3 (by rfl) ⟨1047542, by rfl⟩ : syracuseStep 5586893 = 2095085) B2095085
theorem B1654739 : Blo 1100624 1654739 := bstep (se 1 (by rfl) ⟨1241054, by rfl⟩ : syracuseStep 1654739 = 2482109) B2482109
theorem B11321315 : Blo 1100624 11321315 := bstep (se 1 (by rfl) ⟨8490986, by rfl⟩ : syracuseStep 11321315 = 16981973) B16981973
theorem B1654769 : Blo 1100624 1654769 := bstep (se 2 (by rfl) ⟨620538, by rfl⟩ : syracuseStep 1654769 = 1241077) B1241077
theorem B1654787 : Blo 1100624 1654787 := bstep (se 1 (by rfl) ⟨1241090, by rfl⟩ : syracuseStep 1654787 = 2482181) B2482181
theorem B1654817 : Blo 1100624 1654817 := bstep (se 2 (by rfl) ⟨620556, by rfl⟩ : syracuseStep 1654817 = 1241113) B1241113
theorem B1654835 : Blo 1100624 1654835 := bstep (se 1 (by rfl) ⟨1241126, by rfl⟩ : syracuseStep 1654835 = 2482253) B2482253
theorem B6275141 : Blo 1100624 6275141 := bstep (se 4 (by rfl) ⟨588294, by rfl⟩ : syracuseStep 6275141 = 1176589) B1176589
theorem B3719249 : Blo 1100624 3719249 := bstep (se 2 (by rfl) ⟨1394718, by rfl⟩ : syracuseStep 3719249 = 2789437) B2789437
theorem B1654865 : Blo 1100624 1654865 := bstep (se 2 (by rfl) ⟨620574, by rfl⟩ : syracuseStep 1654865 = 1241149) B1241149
theorem B1654883 : Blo 1100624 1654883 := bstep (se 1 (by rfl) ⟨1241162, by rfl⟩ : syracuseStep 1654883 = 2482325) B2482325
theorem B1654913 : Blo 1100624 1654913 := bstep (se 2 (by rfl) ⟨620592, by rfl⟩ : syracuseStep 1654913 = 1241185) B1241185
theorem B1654931 : Blo 1100624 1654931 := bstep (se 1 (by rfl) ⟨1241198, by rfl⟩ : syracuseStep 1654931 = 2482397) B2482397
theorem B1654961 : Blo 1100624 1654961 := bstep (se 2 (by rfl) ⟨620610, by rfl⟩ : syracuseStep 1654961 = 1241221) B1241221
theorem B1654979 : Blo 1100624 1654979 := bstep (se 1 (by rfl) ⟨1241234, by rfl⟩ : syracuseStep 1654979 = 2482469) B2482469
theorem B1655009 : Blo 1100624 1655009 := bstep (se 2 (by rfl) ⟨620628, by rfl⟩ : syracuseStep 1655009 = 1241257) B1241257
theorem B1655027 : Blo 1100624 1655027 := bstep (se 1 (by rfl) ⟨1241270, by rfl⟩ : syracuseStep 1655027 = 2482541) B2482541
theorem B1655057 : Blo 1100624 1655057 := bstep (se 2 (by rfl) ⟨620646, by rfl⟩ : syracuseStep 1655057 = 1241293) B1241293
theorem B1655075 : Blo 1100624 1655075 := bstep (se 1 (by rfl) ⟨1241306, by rfl⟩ : syracuseStep 1655075 = 2482613) B2482613
theorem B4473137 : Blo 1100624 4473137 := bstep (se 2 (by rfl) ⟨1677426, by rfl⟩ : syracuseStep 4473137 = 3354853) B3354853
theorem B1655105 : Blo 1100624 1655105 := bstep (se 2 (by rfl) ⟨620664, by rfl⟩ : syracuseStep 1655105 = 1241329) B1241329
theorem B1655123 : Blo 1100624 1655123 := bstep (se 1 (by rfl) ⟨1241342, by rfl⟩ : syracuseStep 1655123 = 2482685) B2482685
theorem B9060707 : Blo 1100624 9060707 := bstep (se 1 (by rfl) ⟨6795530, by rfl⟩ : syracuseStep 9060707 = 13591061) B13591061
theorem B1655153 : Blo 1100624 1655153 := bstep (se 2 (by rfl) ⟨620682, by rfl⟩ : syracuseStep 1655153 = 1241365) B1241365
theorem B1655171 : Blo 1100624 1655171 := bstep (se 1 (by rfl) ⟨1241378, by rfl⟩ : syracuseStep 1655171 = 2482757) B2482757
theorem B1655201 : Blo 1100624 1655201 := bstep (se 2 (by rfl) ⟨620700, by rfl⟩ : syracuseStep 1655201 = 1241401) B1241401
theorem B1655219 : Blo 1100624 1655219 := bstep (se 1 (by rfl) ⟨1241414, by rfl⟩ : syracuseStep 1655219 = 2482829) B2482829
theorem B1655249 : Blo 1100624 1655249 := bstep (se 2 (by rfl) ⟨620718, by rfl⟩ : syracuseStep 1655249 = 1241437) B1241437
theorem B1655267 : Blo 1100624 1655267 := bstep (se 1 (by rfl) ⟨1241450, by rfl⟩ : syracuseStep 1655267 = 2482901) B2482901
theorem B1393139 : Blo 1100624 1393139 := bstep (se 1 (by rfl) ⟨1044854, by rfl⟩ : syracuseStep 1393139 = 2089709) B2089709
theorem B1655297 : Blo 1100624 1655297 := bstep (se 2 (by rfl) ⟨620736, by rfl⟩ : syracuseStep 1655297 = 1241473) B1241473
theorem B1655315 : Blo 1100624 1655315 := bstep (se 1 (by rfl) ⟨1241486, by rfl⟩ : syracuseStep 1655315 = 2482973) B2482973
theorem B4702769 : Blo 1100624 4702769 := bstep (se 2 (by rfl) ⟨1763538, by rfl⟩ : syracuseStep 4702769 = 3527077) B3527077
theorem B1655345 : Blo 1100624 1655345 := bstep (se 2 (by rfl) ⟨620754, by rfl⟩ : syracuseStep 1655345 = 1241509) B1241509
theorem B1655363 : Blo 1100624 1655363 := bstep (se 1 (by rfl) ⟨1241522, by rfl⟩ : syracuseStep 1655363 = 2483045) B2483045
theorem B1655393 : Blo 1100624 1655393 := bstep (se 2 (by rfl) ⟨620772, by rfl⟩ : syracuseStep 1655393 = 1241545) B1241545
theorem B3719789 : Blo 1100624 3719789 := bstep (se 3 (by rfl) ⟨697460, by rfl⟩ : syracuseStep 3719789 = 1394921) B1394921
theorem B1655411 : Blo 1100624 1655411 := bstep (se 1 (by rfl) ⟨1241558, by rfl⟩ : syracuseStep 1655411 = 2483117) B2483117
theorem B1655441 : Blo 1100624 1655441 := bstep (se 2 (by rfl) ⟨620790, by rfl⟩ : syracuseStep 1655441 = 1241581) B1241581
theorem B3719843 : Blo 1100624 3719843 := bstep (se 1 (by rfl) ⟨2789882, by rfl⟩ : syracuseStep 3719843 = 5579765) B5579765
theorem B1655459 : Blo 1100624 1655459 := bstep (se 1 (by rfl) ⟨1241594, by rfl⟩ : syracuseStep 1655459 = 2483189) B2483189
theorem B1655489 : Blo 1100624 1655489 := bstep (se 2 (by rfl) ⟨620808, by rfl⟩ : syracuseStep 1655489 = 1241617) B1241617
theorem B1655507 : Blo 1100624 1655507 := bstep (se 1 (by rfl) ⟨1241630, by rfl⟩ : syracuseStep 1655507 = 2483261) B2483261
theorem B6275825 : Blo 1100624 6275825 := bstep (se 2 (by rfl) ⟨2353434, by rfl⟩ : syracuseStep 6275825 = 4706869) B4706869
theorem B1655537 : Blo 1100624 1655537 := bstep (se 2 (by rfl) ⟨620826, by rfl⟩ : syracuseStep 1655537 = 1241653) B1241653
theorem B1655555 : Blo 1100624 1655555 := bstep (se 1 (by rfl) ⟨1241666, by rfl⟩ : syracuseStep 1655555 = 2483333) B2483333
theorem B1655585 : Blo 1100624 1655585 := bstep (se 2 (by rfl) ⟨620844, by rfl⟩ : syracuseStep 1655585 = 1241689) B1241689
theorem B1655603 : Blo 1100624 1655603 := bstep (se 1 (by rfl) ⟨1241702, by rfl⟩ : syracuseStep 1655603 = 2483405) B2483405
theorem B1655633 : Blo 1100624 1655633 := bstep (se 2 (by rfl) ⟨620862, by rfl⟩ : syracuseStep 1655633 = 1241725) B1241725
theorem B1655651 : Blo 1100624 1655651 := bstep (se 1 (by rfl) ⟨1241738, by rfl⟩ : syracuseStep 1655651 = 2483477) B2483477
theorem B1655681 : Blo 1100624 1655681 := bstep (se 2 (by rfl) ⟨620880, by rfl⟩ : syracuseStep 1655681 = 1241761) B1241761
theorem B1655699 : Blo 1100624 1655699 := bstep (se 1 (by rfl) ⟨1241774, by rfl⟩ : syracuseStep 1655699 = 2483549) B2483549
theorem B3720113 : Blo 1100624 3720113 := bstep (se 2 (by rfl) ⟨1395042, by rfl⟩ : syracuseStep 3720113 = 2790085) B2790085
theorem B1655729 : Blo 1100624 1655729 := bstep (se 2 (by rfl) ⟨620898, by rfl⟩ : syracuseStep 1655729 = 1241797) B1241797
theorem B1655747 : Blo 1100624 1655747 := bstep (se 1 (by rfl) ⟨1241810, by rfl⟩ : syracuseStep 1655747 = 2483621) B2483621
theorem B1655777 : Blo 1100624 1655777 := bstep (se 2 (by rfl) ⟨620916, by rfl⟩ : syracuseStep 1655777 = 1241833) B1241833
theorem B1655795 : Blo 1100624 1655795 := bstep (se 1 (by rfl) ⟨1241846, by rfl⟩ : syracuseStep 1655795 = 2483693) B2483693
theorem B1655825 : Blo 1100624 1655825 := bstep (se 2 (by rfl) ⟨620934, by rfl⟩ : syracuseStep 1655825 = 1241869) B1241869
theorem B1655843 : Blo 1100624 1655843 := bstep (se 1 (by rfl) ⟨1241882, by rfl⟩ : syracuseStep 1655843 = 2483765) B2483765
theorem B1655873 : Blo 1100624 1655873 := bstep (se 2 (by rfl) ⟨620952, by rfl⟩ : syracuseStep 1655873 = 1241905) B1241905
theorem B1655891 : Blo 1100624 1655891 := bstep (se 1 (by rfl) ⟨1241918, by rfl⟩ : syracuseStep 1655891 = 2483837) B2483837
theorem B1655921 : Blo 1100624 1655921 := bstep (se 2 (by rfl) ⟨620970, by rfl⟩ : syracuseStep 1655921 = 1241941) B1241941
theorem B1655939 : Blo 1100624 1655939 := bstep (se 1 (by rfl) ⟨1241954, by rfl⟩ : syracuseStep 1655939 = 2483909) B2483909
theorem B1655969 : Blo 1100624 1655969 := bstep (se 2 (by rfl) ⟨620988, by rfl⟩ : syracuseStep 1655969 = 1241977) B1241977
theorem B1393843 : Blo 1100624 1393843 := bstep (se 1 (by rfl) ⟨1045382, by rfl⟩ : syracuseStep 1393843 = 2090765) B2090765
theorem B14304437 : Blo 1100624 14304437 := bstep (se 5 (by rfl) ⟨670520, by rfl⟩ : syracuseStep 14304437 = 1341041) B1341041
theorem B1655987 : Blo 1100624 1655987 := bstep (se 1 (by rfl) ⟨1241990, by rfl⟩ : syracuseStep 1655987 = 2483981) B2483981
theorem B1656017 : Blo 1100624 1656017 := bstep (se 2 (by rfl) ⟨621006, by rfl⟩ : syracuseStep 1656017 = 1242013) B1242013
theorem B1656035 : Blo 1100624 1656035 := bstep (se 1 (by rfl) ⟨1242026, by rfl⟩ : syracuseStep 1656035 = 2484053) B2484053
theorem B1656065 : Blo 1100624 1656065 := bstep (se 2 (by rfl) ⟨621024, by rfl⟩ : syracuseStep 1656065 = 1242049) B1242049
theorem B1393939 : Blo 1100624 1393939 := bstep (se 1 (by rfl) ⟨1045454, by rfl⟩ : syracuseStep 1393939 = 2090909) B2090909
theorem B1656083 : Blo 1100624 1656083 := bstep (se 1 (by rfl) ⟨1242062, by rfl⟩ : syracuseStep 1656083 = 2484125) B2484125
theorem B4179235 : Blo 1100624 4179235 := bstep (se 1 (by rfl) ⟨3134426, by rfl⟩ : syracuseStep 4179235 = 6268853) B6268853
theorem B1656113 : Blo 1100624 1656113 := bstep (se 2 (by rfl) ⟨621042, by rfl⟩ : syracuseStep 1656113 = 1242085) B1242085
theorem B1656131 : Blo 1100624 1656131 := bstep (se 1 (by rfl) ⟨1242098, by rfl⟩ : syracuseStep 1656131 = 2484197) B2484197
theorem B1656161 : Blo 1100624 1656161 := bstep (se 2 (by rfl) ⟨621060, by rfl⟩ : syracuseStep 1656161 = 1242121) B1242121
theorem B1656179 : Blo 1100624 1656179 := bstep (se 1 (by rfl) ⟨1242134, by rfl⟩ : syracuseStep 1656179 = 2484269) B2484269
theorem B1656209 : Blo 1100624 1656209 := bstep (se 2 (by rfl) ⟨621078, by rfl⟩ : syracuseStep 1656209 = 1242157) B1242157
theorem B1656227 : Blo 1100624 1656227 := bstep (se 1 (by rfl) ⟨1242170, by rfl⟩ : syracuseStep 1656227 = 2484341) B2484341
theorem B1656257 : Blo 1100624 1656257 := bstep (se 2 (by rfl) ⟨621096, by rfl⟩ : syracuseStep 1656257 = 1242193) B1242193
theorem B3720653 : Blo 1100624 3720653 := bstep (se 3 (by rfl) ⟨697622, by rfl⟩ : syracuseStep 3720653 = 1395245) B1395245
theorem B1656275 : Blo 1100624 1656275 := bstep (se 1 (by rfl) ⟨1242206, by rfl⟩ : syracuseStep 1656275 = 2484413) B2484413
theorem B1656305 : Blo 1100624 1656305 := bstep (se 2 (by rfl) ⟨621114, by rfl⟩ : syracuseStep 1656305 = 1242229) B1242229
theorem B3720707 : Blo 1100624 3720707 := bstep (se 1 (by rfl) ⟨2790530, by rfl⟩ : syracuseStep 3720707 = 5581061) B5581061
theorem B1656323 : Blo 1100624 1656323 := bstep (se 1 (by rfl) ⟨1242242, by rfl⟩ : syracuseStep 1656323 = 2484485) B2484485
theorem B1656353 : Blo 1100624 1656353 := bstep (se 2 (by rfl) ⟨621132, by rfl⟩ : syracuseStep 1656353 = 1242265) B1242265
theorem B1656371 : Blo 1100624 1656371 := bstep (se 1 (by rfl) ⟨1242278, by rfl⟩ : syracuseStep 1656371 = 2484557) B2484557
theorem B1656401 : Blo 1100624 1656401 := bstep (se 2 (by rfl) ⟨621150, by rfl⟩ : syracuseStep 1656401 = 1242301) B1242301
theorem B1656419 : Blo 1100624 1656419 := bstep (se 1 (by rfl) ⟨1242314, by rfl⟩ : syracuseStep 1656419 = 2484629) B2484629
theorem B1656449 : Blo 1100624 1656449 := bstep (se 2 (by rfl) ⟨621168, by rfl⟩ : syracuseStep 1656449 = 1242337) B1242337
theorem B1656467 : Blo 1100624 1656467 := bstep (se 1 (by rfl) ⟨1242350, by rfl⟩ : syracuseStep 1656467 = 2484701) B2484701
theorem B1656497 : Blo 1100624 1656497 := bstep (se 2 (by rfl) ⟨621186, by rfl⟩ : syracuseStep 1656497 = 1242373) B1242373
theorem B1656515 : Blo 1100624 1656515 := bstep (se 1 (by rfl) ⟨1242386, by rfl⟩ : syracuseStep 1656515 = 2484773) B2484773
theorem B1656545 : Blo 1100624 1656545 := bstep (se 2 (by rfl) ⟨621204, by rfl⟩ : syracuseStep 1656545 = 1242409) B1242409
theorem B4835057 : Blo 1100624 4835057 := bstep (se 2 (by rfl) ⟨1813146, by rfl⟩ : syracuseStep 4835057 = 3626293) B3626293
theorem B1656563 : Blo 1100624 1656563 := bstep (se 1 (by rfl) ⟨1242422, by rfl⟩ : syracuseStep 1656563 = 2484845) B2484845
theorem B1394435 : Blo 1100624 1394435 := bstep (se 1 (by rfl) ⟨1045826, by rfl⟩ : syracuseStep 1394435 = 2091653) B2091653
theorem B3720977 : Blo 1100624 3720977 := bstep (se 2 (by rfl) ⟨1395366, by rfl⟩ : syracuseStep 3720977 = 2790733) B2790733
theorem B1656593 : Blo 1100624 1656593 := bstep (se 2 (by rfl) ⟨621222, by rfl⟩ : syracuseStep 1656593 = 1242445) B1242445
theorem B1656611 : Blo 1100624 1656611 := bstep (se 1 (by rfl) ⟨1242458, by rfl⟩ : syracuseStep 1656611 = 2484917) B2484917
theorem B1656641 : Blo 1100624 1656641 := bstep (se 2 (by rfl) ⟨621240, by rfl⟩ : syracuseStep 1656641 = 1242481) B1242481
theorem B1656659 : Blo 1100624 1656659 := bstep (se 1 (by rfl) ⟨1242494, by rfl⟩ : syracuseStep 1656659 = 2484989) B2484989
theorem B1656689 : Blo 1100624 1656689 := bstep (se 2 (by rfl) ⟨621258, by rfl⟩ : syracuseStep 1656689 = 1242517) B1242517
theorem B1656707 : Blo 1100624 1656707 := bstep (se 1 (by rfl) ⟨1242530, by rfl⟩ : syracuseStep 1656707 = 2485061) B2485061
theorem B1656737 : Blo 1100624 1656737 := bstep (se 2 (by rfl) ⟨621276, by rfl⟩ : syracuseStep 1656737 = 1242553) B1242553
theorem B1656755 : Blo 1100624 1656755 := bstep (se 1 (by rfl) ⟨1242566, by rfl⟩ : syracuseStep 1656755 = 2485133) B2485133
theorem B1656785 : Blo 1100624 1656785 := bstep (se 2 (by rfl) ⟨621294, by rfl⟩ : syracuseStep 1656785 = 1242589) B1242589
theorem B7555043 : Blo 1100624 7555043 := bstep (se 1 (by rfl) ⟨5666282, by rfl⟩ : syracuseStep 7555043 = 11332565) B11332565
theorem B1656803 : Blo 1100624 1656803 := bstep (se 1 (by rfl) ⟨1242602, by rfl⟩ : syracuseStep 1656803 = 2485205) B2485205
theorem B1656833 : Blo 1100624 1656833 := bstep (se 2 (by rfl) ⟨621312, by rfl⟩ : syracuseStep 1656833 = 1242625) B1242625
theorem B1656851 : Blo 1100624 1656851 := bstep (se 1 (by rfl) ⟨1242638, by rfl⟩ : syracuseStep 1656851 = 2485277) B2485277
theorem B1656881 : Blo 1100624 1656881 := bstep (se 2 (by rfl) ⟨621330, by rfl⟩ : syracuseStep 1656881 = 1242661) B1242661
theorem B1656899 : Blo 1100624 1656899 := bstep (se 1 (by rfl) ⟨1242674, by rfl⟩ : syracuseStep 1656899 = 2485349) B2485349
theorem B1656929 : Blo 1100624 1656929 := bstep (se 2 (by rfl) ⟨621348, by rfl⟩ : syracuseStep 1656929 = 1242697) B1242697
theorem B2869361 : Blo 1100624 2869361 := bstep (se 2 (by rfl) ⟨1076010, by rfl⟩ : syracuseStep 2869361 = 2152021) B2152021
theorem B6277283 : Blo 1100624 6277283 := bstep (se 1 (by rfl) ⟨4707962, by rfl⟩ : syracuseStep 6277283 = 9415925) B9415925
theorem B3721517 : Blo 1100624 3721517 := bstep (se 3 (by rfl) ⟨697784, by rfl⟩ : syracuseStep 3721517 = 1395569) B1395569
theorem B4475213 : Blo 1100624 4475213 := bstep (se 3 (by rfl) ⟨839102, by rfl⟩ : syracuseStep 4475213 = 1678205) B1678205
theorem B3721571 : Blo 1100624 3721571 := bstep (se 1 (by rfl) ⟨2791178, by rfl⟩ : syracuseStep 3721571 = 5582357) B5582357
theorem B1395139 : Blo 1100624 1395139 := bstep (se 1 (by rfl) ⟨1046354, by rfl⟩ : syracuseStep 1395139 = 2092709) B2092709
theorem B2476529 : Blo 1100624 2476529 := bstep (se 2 (by rfl) ⟨928698, by rfl⟩ : syracuseStep 2476529 = 1857397) B1857397
theorem B2476547 : Blo 1100624 2476547 := bstep (se 1 (by rfl) ⟨1857410, by rfl⟩ : syracuseStep 2476547 = 3714821) B3714821
theorem B1591825 : Blo 1100624 1591825 := bstep (se 2 (by rfl) ⟨596934, by rfl⟩ : syracuseStep 1591825 = 1193869) B1193869
theorem B1395235 : Blo 1100624 1395235 := bstep (se 1 (by rfl) ⟨1046426, by rfl⟩ : syracuseStep 1395235 = 2092853) B2092853
theorem B3721841 : Blo 1100624 3721841 := bstep (se 2 (by rfl) ⟨1395690, by rfl⟩ : syracuseStep 3721841 = 2791381) B2791381
theorem B3066499 : Blo 1100624 3066499 := bstep (se 1 (by rfl) ⟨2299874, by rfl⟩ : syracuseStep 3066499 = 4599749) B4599749
theorem B2476817 : Blo 1100624 2476817 := bstep (se 2 (by rfl) ⟨928806, by rfl⟩ : syracuseStep 2476817 = 1857613) B1857613
theorem B2476835 : Blo 1100624 2476835 := bstep (se 1 (by rfl) ⟨1857626, by rfl⟩ : syracuseStep 2476835 = 3715253) B3715253
theorem B5589809 : Blo 1100624 5589809 := bstep (se 2 (by rfl) ⟨2096178, by rfl⟩ : syracuseStep 5589809 = 4192357) B4192357
theorem B1100627 : Blo 1100624 1100627 := bstep (se 1 (by rfl) ⟨825470, by rfl⟩ : syracuseStep 1100627 = 1650941) B1650941
theorem B1100643 : Blo 1100624 1100643 := bstep (se 1 (by rfl) ⟨825482, by rfl⟩ : syracuseStep 1100643 = 1650965) B1650965
theorem B1100659 : Blo 1100624 1100659 := bstep (se 1 (by rfl) ⟨825494, by rfl⟩ : syracuseStep 1100659 = 1650989) B1650989
theorem B1100675 : Blo 1100624 1100675 := bstep (se 1 (by rfl) ⟨825506, by rfl⟩ : syracuseStep 1100675 = 1651013) B1651013
theorem B1100691 : Blo 1100624 1100691 := bstep (se 1 (by rfl) ⟨825518, by rfl⟩ : syracuseStep 1100691 = 1651037) B1651037
theorem B1100707 : Blo 1100624 1100707 := bstep (se 1 (by rfl) ⟨825530, by rfl⟩ : syracuseStep 1100707 = 1651061) B1651061
theorem B1100723 : Blo 1100624 1100723 := bstep (se 1 (by rfl) ⟨825542, by rfl⟩ : syracuseStep 1100723 = 1651085) B1651085
theorem B1100739 : Blo 1100624 1100739 := bstep (se 1 (by rfl) ⟨825554, by rfl⟩ : syracuseStep 1100739 = 1651109) B1651109
theorem B8375237 : Blo 1100624 8375237 := bstep (se 4 (by rfl) ⟨785178, by rfl⟩ : syracuseStep 8375237 = 1570357) B1570357
theorem B4705229 : Blo 1100624 4705229 := bstep (se 3 (by rfl) ⟨882230, by rfl⟩ : syracuseStep 4705229 = 1764461) B1764461
theorem B1100755 : Blo 1100624 1100755 := bstep (se 1 (by rfl) ⟨825566, by rfl⟩ : syracuseStep 1100755 = 1651133) B1651133
theorem B1100771 : Blo 1100624 1100771 := bstep (se 1 (by rfl) ⟨825578, by rfl⟩ : syracuseStep 1100771 = 1651157) B1651157
theorem B1100787 : Blo 1100624 1100787 := bstep (se 1 (by rfl) ⟨825590, by rfl⟩ : syracuseStep 1100787 = 1651181) B1651181
theorem B1100803 : Blo 1100624 1100803 := bstep (se 1 (by rfl) ⟨825602, by rfl⟩ : syracuseStep 1100803 = 1651205) B1651205
theorem B1100819 : Blo 1100624 1100819 := bstep (se 1 (by rfl) ⟨825614, by rfl⟩ : syracuseStep 1100819 = 1651229) B1651229
theorem B1395731 : Blo 1100624 1395731 := bstep (se 1 (by rfl) ⟨1046798, by rfl⟩ : syracuseStep 1395731 = 2093597) B2093597
theorem B1100835 : Blo 1100624 1100835 := bstep (se 1 (by rfl) ⟨825626, by rfl⟩ : syracuseStep 1100835 = 1651253) B1651253
theorem B2477105 : Blo 1100624 2477105 := bstep (se 2 (by rfl) ⟨928914, by rfl⟩ : syracuseStep 2477105 = 1857829) B1857829
theorem B1100851 : Blo 1100624 1100851 := bstep (se 1 (by rfl) ⟨825638, by rfl⟩ : syracuseStep 1100851 = 1651277) B1651277
theorem B1100867 : Blo 1100624 1100867 := bstep (se 1 (by rfl) ⟨825650, by rfl⟩ : syracuseStep 1100867 = 1651301) B1651301
theorem B2477123 : Blo 1100624 2477123 := bstep (se 1 (by rfl) ⟨1857842, by rfl⟩ : syracuseStep 2477123 = 3715685) B3715685
theorem B1100883 : Blo 1100624 1100883 := bstep (se 1 (by rfl) ⟨825662, by rfl⟩ : syracuseStep 1100883 = 1651325) B1651325
theorem B1100899 : Blo 1100624 1100899 := bstep (se 1 (by rfl) ⟨825674, by rfl⟩ : syracuseStep 1100899 = 1651349) B1651349
theorem B1100915 : Blo 1100624 1100915 := bstep (se 1 (by rfl) ⟨825686, by rfl⟩ : syracuseStep 1100915 = 1651373) B1651373
theorem B1100931 : Blo 1100624 1100931 := bstep (se 1 (by rfl) ⟨825698, by rfl⟩ : syracuseStep 1100931 = 1651397) B1651397
theorem B3722381 : Blo 1100624 3722381 := bstep (se 3 (by rfl) ⟨697946, by rfl⟩ : syracuseStep 3722381 = 1395893) B1395893
theorem B1100947 : Blo 1100624 1100947 := bstep (se 1 (by rfl) ⟨825710, by rfl⟩ : syracuseStep 1100947 = 1651421) B1651421
theorem B1100963 : Blo 1100624 1100963 := bstep (se 1 (by rfl) ⟨825722, by rfl⟩ : syracuseStep 1100963 = 1651445) B1651445
theorem B1100979 : Blo 1100624 1100979 := bstep (se 1 (by rfl) ⟨825734, by rfl⟩ : syracuseStep 1100979 = 1651469) B1651469
theorem B1100995 : Blo 1100624 1100995 := bstep (se 1 (by rfl) ⟨825746, by rfl⟩ : syracuseStep 1100995 = 1651493) B1651493
theorem B3722435 : Blo 1100624 3722435 := bstep (se 1 (by rfl) ⟨2791826, by rfl⟩ : syracuseStep 3722435 = 5583653) B5583653
theorem B1101011 : Blo 1100624 1101011 := bstep (se 1 (by rfl) ⟨825758, by rfl⟩ : syracuseStep 1101011 = 1651517) B1651517
theorem B1101027 : Blo 1100624 1101027 := bstep (se 1 (by rfl) ⟨825770, by rfl⟩ : syracuseStep 1101027 = 1651541) B1651541
theorem B1101043 : Blo 1100624 1101043 := bstep (se 1 (by rfl) ⟨825782, by rfl⟩ : syracuseStep 1101043 = 1651565) B1651565
theorem B1101059 : Blo 1100624 1101059 := bstep (se 1 (by rfl) ⟨825794, by rfl⟩ : syracuseStep 1101059 = 1651589) B1651589
theorem B1101075 : Blo 1100624 1101075 := bstep (se 1 (by rfl) ⟨825806, by rfl⟩ : syracuseStep 1101075 = 1651613) B1651613
theorem B1101091 : Blo 1100624 1101091 := bstep (se 1 (by rfl) ⟨825818, by rfl⟩ : syracuseStep 1101091 = 1651637) B1651637
theorem B1101107 : Blo 1100624 1101107 := bstep (se 1 (by rfl) ⟨825830, by rfl⟩ : syracuseStep 1101107 = 1651661) B1651661
theorem B1101123 : Blo 1100624 1101123 := bstep (se 1 (by rfl) ⟨825842, by rfl⟩ : syracuseStep 1101123 = 1651685) B1651685
theorem B2477393 : Blo 1100624 2477393 := bstep (se 2 (by rfl) ⟨929022, by rfl⟩ : syracuseStep 2477393 = 1858045) B1858045
theorem B1101139 : Blo 1100624 1101139 := bstep (se 1 (by rfl) ⟨825854, by rfl⟩ : syracuseStep 1101139 = 1651709) B1651709
theorem B2477411 : Blo 1100624 2477411 := bstep (se 1 (by rfl) ⟨1858058, by rfl⟩ : syracuseStep 2477411 = 3716117) B3716117
theorem B1101155 : Blo 1100624 1101155 := bstep (se 1 (by rfl) ⟨825866, by rfl⟩ : syracuseStep 1101155 = 1651733) B1651733
theorem B1101171 : Blo 1100624 1101171 := bstep (se 1 (by rfl) ⟨825878, by rfl⟩ : syracuseStep 1101171 = 1651757) B1651757
theorem B1101187 : Blo 1100624 1101187 := bstep (se 1 (by rfl) ⟨825890, by rfl⟩ : syracuseStep 1101187 = 1651781) B1651781
theorem B1101203 : Blo 1100624 1101203 := bstep (se 1 (by rfl) ⟨825902, by rfl⟩ : syracuseStep 1101203 = 1651805) B1651805
theorem B1101219 : Blo 1100624 1101219 := bstep (se 1 (by rfl) ⟨825914, by rfl⟩ : syracuseStep 1101219 = 1651829) B1651829
theorem B1101235 : Blo 1100624 1101235 := bstep (se 1 (by rfl) ⟨825926, by rfl⟩ : syracuseStep 1101235 = 1651853) B1651853
theorem B1101251 : Blo 1100624 1101251 := bstep (se 1 (by rfl) ⟨825938, by rfl⟩ : syracuseStep 1101251 = 1651877) B1651877
theorem B4181453 : Blo 1100624 4181453 := bstep (se 3 (by rfl) ⟨784022, by rfl⟩ : syracuseStep 4181453 = 1568045) B1568045
theorem B3722705 : Blo 1100624 3722705 := bstep (se 2 (by rfl) ⟨1396014, by rfl⟩ : syracuseStep 3722705 = 2792029) B2792029
theorem B1101267 : Blo 1100624 1101267 := bstep (se 1 (by rfl) ⟨825950, by rfl⟩ : syracuseStep 1101267 = 1651901) B1651901
theorem B1101283 : Blo 1100624 1101283 := bstep (se 1 (by rfl) ⟨825962, by rfl⟩ : syracuseStep 1101283 = 1651925) B1651925
theorem B1101299 : Blo 1100624 1101299 := bstep (se 1 (by rfl) ⟨825974, by rfl⟩ : syracuseStep 1101299 = 1651949) B1651949
theorem B1101315 : Blo 1100624 1101315 := bstep (se 1 (by rfl) ⟨825986, by rfl⟩ : syracuseStep 1101315 = 1651973) B1651973
theorem B1101331 : Blo 1100624 1101331 := bstep (se 1 (by rfl) ⟨825998, by rfl⟩ : syracuseStep 1101331 = 1651997) B1651997
theorem B1101347 : Blo 1100624 1101347 := bstep (se 1 (by rfl) ⟨826010, by rfl⟩ : syracuseStep 1101347 = 1652021) B1652021
theorem B4902449 : Blo 1100624 4902449 := bstep (se 2 (by rfl) ⟨1838418, by rfl⟩ : syracuseStep 4902449 = 3676837) B3676837
theorem B1101363 : Blo 1100624 1101363 := bstep (se 1 (by rfl) ⟨826022, by rfl⟩ : syracuseStep 1101363 = 1652045) B1652045
theorem B1101379 : Blo 1100624 1101379 := bstep (se 1 (by rfl) ⟨826034, by rfl⟩ : syracuseStep 1101379 = 1652069) B1652069
theorem B1986115 : Blo 1100624 1986115 := bstep (se 1 (by rfl) ⟨1489586, by rfl⟩ : syracuseStep 1986115 = 2979173) B2979173
theorem B1101395 : Blo 1100624 1101395 := bstep (se 1 (by rfl) ⟨826046, by rfl⟩ : syracuseStep 1101395 = 1652093) B1652093
theorem B1101411 : Blo 1100624 1101411 := bstep (se 1 (by rfl) ⟨826058, by rfl⟩ : syracuseStep 1101411 = 1652117) B1652117
theorem B2477681 : Blo 1100624 2477681 := bstep (se 2 (by rfl) ⟨929130, by rfl⟩ : syracuseStep 2477681 = 1858261) B1858261
theorem B4836977 : Blo 1100624 4836977 := bstep (se 2 (by rfl) ⟨1813866, by rfl⟩ : syracuseStep 4836977 = 3627733) B3627733
theorem B1101427 : Blo 1100624 1101427 := bstep (se 1 (by rfl) ⟨826070, by rfl⟩ : syracuseStep 1101427 = 1652141) B1652141
theorem B2477699 : Blo 1100624 2477699 := bstep (se 1 (by rfl) ⟨1858274, by rfl⟩ : syracuseStep 2477699 = 3716549) B3716549
theorem B1101443 : Blo 1100624 1101443 := bstep (se 1 (by rfl) ⟨826082, by rfl⟩ : syracuseStep 1101443 = 1652165) B1652165
theorem B1101459 : Blo 1100624 1101459 := bstep (se 1 (by rfl) ⟨826094, by rfl⟩ : syracuseStep 1101459 = 1652189) B1652189
theorem B1101475 : Blo 1100624 1101475 := bstep (se 1 (by rfl) ⟨826106, by rfl⟩ : syracuseStep 1101475 = 1652213) B1652213
theorem B1101491 : Blo 1100624 1101491 := bstep (se 1 (by rfl) ⟨826118, by rfl⟩ : syracuseStep 1101491 = 1652237) B1652237
theorem B1101507 : Blo 1100624 1101507 := bstep (se 1 (by rfl) ⟨826130, by rfl⟩ : syracuseStep 1101507 = 1652261) B1652261
theorem B1101523 : Blo 1100624 1101523 := bstep (se 1 (by rfl) ⟨826142, by rfl⟩ : syracuseStep 1101523 = 1652285) B1652285
theorem B1396435 : Blo 1100624 1396435 := bstep (se 1 (by rfl) ⟨1047326, by rfl⟩ : syracuseStep 1396435 = 2094653) B2094653
theorem B1101539 : Blo 1100624 1101539 := bstep (se 1 (by rfl) ⟨826154, by rfl⟩ : syracuseStep 1101539 = 1652309) B1652309
theorem B1101555 : Blo 1100624 1101555 := bstep (se 1 (by rfl) ⟨826166, by rfl⟩ : syracuseStep 1101555 = 1652333) B1652333
theorem B1101571 : Blo 1100624 1101571 := bstep (se 1 (by rfl) ⟨826178, by rfl⟩ : syracuseStep 1101571 = 1652357) B1652357
theorem B1101587 : Blo 1100624 1101587 := bstep (se 1 (by rfl) ⟨826190, by rfl⟩ : syracuseStep 1101587 = 1652381) B1652381
theorem B1101603 : Blo 1100624 1101603 := bstep (se 1 (by rfl) ⟨826202, by rfl⟩ : syracuseStep 1101603 = 1652405) B1652405
theorem B1101619 : Blo 1100624 1101619 := bstep (se 1 (by rfl) ⟨826214, by rfl⟩ : syracuseStep 1101619 = 1652429) B1652429
theorem B1396531 : Blo 1100624 1396531 := bstep (se 1 (by rfl) ⟨1047398, by rfl⟩ : syracuseStep 1396531 = 2094797) B2094797
theorem B1101635 : Blo 1100624 1101635 := bstep (se 1 (by rfl) ⟨826226, by rfl⟩ : syracuseStep 1101635 = 1652453) B1652453
theorem B1101651 : Blo 1100624 1101651 := bstep (se 1 (by rfl) ⟨826238, by rfl⟩ : syracuseStep 1101651 = 1652477) B1652477
theorem B1101667 : Blo 1100624 1101667 := bstep (se 1 (by rfl) ⟨826250, by rfl⟩ : syracuseStep 1101667 = 1652501) B1652501
theorem B1101683 : Blo 1100624 1101683 := bstep (se 1 (by rfl) ⟨826262, by rfl⟩ : syracuseStep 1101683 = 1652525) B1652525
theorem B1101699 : Blo 1100624 1101699 := bstep (se 1 (by rfl) ⟨826274, by rfl⟩ : syracuseStep 1101699 = 1652549) B1652549
theorem B2477969 : Blo 1100624 2477969 := bstep (se 2 (by rfl) ⟨929238, by rfl⟩ : syracuseStep 2477969 = 1858477) B1858477
theorem B1101715 : Blo 1100624 1101715 := bstep (se 1 (by rfl) ⟨826286, by rfl⟩ : syracuseStep 1101715 = 1652573) B1652573
theorem B2477987 : Blo 1100624 2477987 := bstep (se 1 (by rfl) ⟨1858490, by rfl⟩ : syracuseStep 2477987 = 3716981) B3716981
theorem B1101731 : Blo 1100624 1101731 := bstep (se 1 (by rfl) ⟨826298, by rfl⟩ : syracuseStep 1101731 = 1652597) B1652597
theorem B1101747 : Blo 1100624 1101747 := bstep (se 1 (by rfl) ⟨826310, by rfl⟩ : syracuseStep 1101747 = 1652621) B1652621
theorem B1101763 : Blo 1100624 1101763 := bstep (se 1 (by rfl) ⟨826322, by rfl⟩ : syracuseStep 1101763 = 1652645) B1652645
theorem B1101779 : Blo 1100624 1101779 := bstep (se 1 (by rfl) ⟨826334, by rfl⟩ : syracuseStep 1101779 = 1652669) B1652669
theorem B1101795 : Blo 1100624 1101795 := bstep (se 1 (by rfl) ⟨826346, by rfl⟩ : syracuseStep 1101795 = 1652693) B1652693
theorem B3723245 : Blo 1100624 3723245 := bstep (se 3 (by rfl) ⟨698108, by rfl⟩ : syracuseStep 3723245 = 1396217) B1396217
theorem B1101811 : Blo 1100624 1101811 := bstep (se 1 (by rfl) ⟨826358, by rfl⟩ : syracuseStep 1101811 = 1652717) B1652717
theorem B1101827 : Blo 1100624 1101827 := bstep (se 1 (by rfl) ⟨826370, by rfl⟩ : syracuseStep 1101827 = 1652741) B1652741
theorem B1101843 : Blo 1100624 1101843 := bstep (se 1 (by rfl) ⟨826382, by rfl⟩ : syracuseStep 1101843 = 1652765) B1652765
theorem B1101859 : Blo 1100624 1101859 := bstep (se 1 (by rfl) ⟨826394, by rfl⟩ : syracuseStep 1101859 = 1652789) B1652789
theorem B3723299 : Blo 1100624 3723299 := bstep (se 1 (by rfl) ⟨2792474, by rfl⟩ : syracuseStep 3723299 = 5584949) B5584949
theorem B1101875 : Blo 1100624 1101875 := bstep (se 1 (by rfl) ⟨826406, by rfl⟩ : syracuseStep 1101875 = 1652813) B1652813
theorem B1101891 : Blo 1100624 1101891 := bstep (se 1 (by rfl) ⟨826418, by rfl⟩ : syracuseStep 1101891 = 1652837) B1652837
theorem B1101907 : Blo 1100624 1101907 := bstep (se 1 (by rfl) ⟨826430, by rfl⟩ : syracuseStep 1101907 = 1652861) B1652861
theorem B1101923 : Blo 1100624 1101923 := bstep (se 1 (by rfl) ⟨826442, by rfl⟩ : syracuseStep 1101923 = 1652885) B1652885
theorem B1101939 : Blo 1100624 1101939 := bstep (se 1 (by rfl) ⟨826454, by rfl⟩ : syracuseStep 1101939 = 1652909) B1652909
theorem B1101955 : Blo 1100624 1101955 := bstep (se 1 (by rfl) ⟨826466, by rfl⟩ : syracuseStep 1101955 = 1652933) B1652933
theorem B21188749 : Blo 1100624 21188749 := bstep (se 3 (by rfl) ⟨3972890, by rfl⟩ : syracuseStep 21188749 = 7945781) B7945781
theorem B1101971 : Blo 1100624 1101971 := bstep (se 1 (by rfl) ⟨826478, by rfl⟩ : syracuseStep 1101971 = 1652957) B1652957
theorem B1101987 : Blo 1100624 1101987 := bstep (se 1 (by rfl) ⟨826490, by rfl⟩ : syracuseStep 1101987 = 1652981) B1652981
theorem B2478257 : Blo 1100624 2478257 := bstep (se 2 (by rfl) ⟨929346, by rfl⟩ : syracuseStep 2478257 = 1858693) B1858693
theorem B1102003 : Blo 1100624 1102003 := bstep (se 1 (by rfl) ⟨826502, by rfl⟩ : syracuseStep 1102003 = 1653005) B1653005
theorem B2478275 : Blo 1100624 2478275 := bstep (se 1 (by rfl) ⟨1858706, by rfl⟩ : syracuseStep 2478275 = 3717413) B3717413
theorem B1102019 : Blo 1100624 1102019 := bstep (se 1 (by rfl) ⟨826514, by rfl⟩ : syracuseStep 1102019 = 1653029) B1653029
theorem B1102035 : Blo 1100624 1102035 := bstep (se 1 (by rfl) ⟨826526, by rfl⟩ : syracuseStep 1102035 = 1653053) B1653053
theorem B1102051 : Blo 1100624 1102051 := bstep (se 1 (by rfl) ⟨826538, by rfl⟩ : syracuseStep 1102051 = 1653077) B1653077
theorem B5591267 : Blo 1100624 5591267 := bstep (se 1 (by rfl) ⟨4193450, by rfl⟩ : syracuseStep 5591267 = 8386901) B8386901
theorem B3526897 : Blo 1100624 3526897 := bstep (se 2 (by rfl) ⟨1322586, by rfl⟩ : syracuseStep 3526897 = 2645173) B2645173
theorem B4706545 : Blo 1100624 4706545 := bstep (se 2 (by rfl) ⟨1764954, by rfl⟩ : syracuseStep 4706545 = 3529909) B3529909
theorem B1102067 : Blo 1100624 1102067 := bstep (se 1 (by rfl) ⟨826550, by rfl⟩ : syracuseStep 1102067 = 1653101) B1653101
theorem B1102083 : Blo 1100624 1102083 := bstep (se 1 (by rfl) ⟨826562, by rfl⟩ : syracuseStep 1102083 = 1653125) B1653125
theorem B1102099 : Blo 1100624 1102099 := bstep (se 1 (by rfl) ⟨826574, by rfl⟩ : syracuseStep 1102099 = 1653149) B1653149
theorem B1102115 : Blo 1100624 1102115 := bstep (se 1 (by rfl) ⟨826586, by rfl⟩ : syracuseStep 1102115 = 1653173) B1653173
theorem B1397027 : Blo 1100624 1397027 := bstep (se 1 (by rfl) ⟨1047770, by rfl⟩ : syracuseStep 1397027 = 2095541) B2095541
theorem B3723569 : Blo 1100624 3723569 := bstep (se 2 (by rfl) ⟨1396338, by rfl⟩ : syracuseStep 3723569 = 2792677) B2792677
theorem B1102131 : Blo 1100624 1102131 := bstep (se 1 (by rfl) ⟨826598, by rfl⟩ : syracuseStep 1102131 = 1653197) B1653197
theorem B1102147 : Blo 1100624 1102147 := bstep (se 1 (by rfl) ⟨826610, by rfl⟩ : syracuseStep 1102147 = 1653221) B1653221
theorem B1102163 : Blo 1100624 1102163 := bstep (se 1 (by rfl) ⟨826622, by rfl⟩ : syracuseStep 1102163 = 1653245) B1653245
theorem B1102179 : Blo 1100624 1102179 := bstep (se 1 (by rfl) ⟨826634, by rfl⟩ : syracuseStep 1102179 = 1653269) B1653269
theorem B1102195 : Blo 1100624 1102195 := bstep (se 1 (by rfl) ⟨826646, by rfl⟩ : syracuseStep 1102195 = 1653293) B1653293
theorem B1102211 : Blo 1100624 1102211 := bstep (se 1 (by rfl) ⟨826658, by rfl⟩ : syracuseStep 1102211 = 1653317) B1653317
theorem B1102227 : Blo 1100624 1102227 := bstep (se 1 (by rfl) ⟨826670, by rfl⟩ : syracuseStep 1102227 = 1653341) B1653341
theorem B1102243 : Blo 1100624 1102243 := bstep (se 1 (by rfl) ⟨826682, by rfl⟩ : syracuseStep 1102243 = 1653365) B1653365
theorem B1102259 : Blo 1100624 1102259 := bstep (se 1 (by rfl) ⟨826694, by rfl⟩ : syracuseStep 1102259 = 1653389) B1653389
theorem B1102275 : Blo 1100624 1102275 := bstep (se 1 (by rfl) ⟨826706, by rfl⟩ : syracuseStep 1102275 = 1653413) B1653413
theorem B2478545 : Blo 1100624 2478545 := bstep (se 2 (by rfl) ⟨929454, by rfl⟩ : syracuseStep 2478545 = 1858909) B1858909
theorem B1102291 : Blo 1100624 1102291 := bstep (se 1 (by rfl) ⟨826718, by rfl⟩ : syracuseStep 1102291 = 1653437) B1653437
theorem B2478563 : Blo 1100624 2478563 := bstep (se 1 (by rfl) ⟨1858922, by rfl⟩ : syracuseStep 2478563 = 3717845) B3717845
theorem B1102307 : Blo 1100624 1102307 := bstep (se 1 (by rfl) ⟨826730, by rfl⟩ : syracuseStep 1102307 = 1653461) B1653461
theorem B3527153 : Blo 1100624 3527153 := bstep (se 2 (by rfl) ⟨1322682, by rfl⟩ : syracuseStep 3527153 = 2645365) B2645365
theorem B1102323 : Blo 1100624 1102323 := bstep (se 1 (by rfl) ⟨826742, by rfl⟩ : syracuseStep 1102323 = 1653485) B1653485
theorem B1102339 : Blo 1100624 1102339 := bstep (se 1 (by rfl) ⟨826754, by rfl⟩ : syracuseStep 1102339 = 1653509) B1653509
theorem B1102355 : Blo 1100624 1102355 := bstep (se 1 (by rfl) ⟨826766, by rfl⟩ : syracuseStep 1102355 = 1653533) B1653533
theorem B1102371 : Blo 1100624 1102371 := bstep (se 1 (by rfl) ⟨826778, by rfl⟩ : syracuseStep 1102371 = 1653557) B1653557
theorem B1102387 : Blo 1100624 1102387 := bstep (se 1 (by rfl) ⟨826790, by rfl⟩ : syracuseStep 1102387 = 1653581) B1653581
theorem B1102403 : Blo 1100624 1102403 := bstep (se 1 (by rfl) ⟨826802, by rfl⟩ : syracuseStep 1102403 = 1653605) B1653605
theorem B1102419 : Blo 1100624 1102419 := bstep (se 1 (by rfl) ⟨826814, by rfl⟩ : syracuseStep 1102419 = 1653629) B1653629
theorem B1102435 : Blo 1100624 1102435 := bstep (se 1 (by rfl) ⟨826826, by rfl⟩ : syracuseStep 1102435 = 1653653) B1653653
theorem B1102451 : Blo 1100624 1102451 := bstep (se 1 (by rfl) ⟨826838, by rfl⟩ : syracuseStep 1102451 = 1653677) B1653677
theorem B1102467 : Blo 1100624 1102467 := bstep (se 1 (by rfl) ⟨826850, by rfl⟩ : syracuseStep 1102467 = 1653701) B1653701
theorem B1102483 : Blo 1100624 1102483 := bstep (se 1 (by rfl) ⟨826862, by rfl⟩ : syracuseStep 1102483 = 1653725) B1653725
theorem B1102499 : Blo 1100624 1102499 := bstep (se 1 (by rfl) ⟨826874, by rfl⟩ : syracuseStep 1102499 = 1653749) B1653749
theorem B1102515 : Blo 1100624 1102515 := bstep (se 1 (by rfl) ⟨826886, by rfl⟩ : syracuseStep 1102515 = 1653773) B1653773
theorem B1102531 : Blo 1100624 1102531 := bstep (se 1 (by rfl) ⟨826898, by rfl⟩ : syracuseStep 1102531 = 1653797) B1653797
theorem B1102547 : Blo 1100624 1102547 := bstep (se 1 (by rfl) ⟨826910, by rfl⟩ : syracuseStep 1102547 = 1653821) B1653821
theorem B1102563 : Blo 1100624 1102563 := bstep (se 1 (by rfl) ⟨826922, by rfl⟩ : syracuseStep 1102563 = 1653845) B1653845
theorem B2478833 : Blo 1100624 2478833 := bstep (se 2 (by rfl) ⟨929562, by rfl⟩ : syracuseStep 2478833 = 1859125) B1859125
theorem B1102579 : Blo 1100624 1102579 := bstep (se 1 (by rfl) ⟨826934, by rfl⟩ : syracuseStep 1102579 = 1653869) B1653869
theorem B2478851 : Blo 1100624 2478851 := bstep (se 1 (by rfl) ⟨1859138, by rfl⟩ : syracuseStep 2478851 = 3718277) B3718277
theorem B1102595 : Blo 1100624 1102595 := bstep (se 1 (by rfl) ⟨826946, by rfl⟩ : syracuseStep 1102595 = 1653893) B1653893
theorem B1102611 : Blo 1100624 1102611 := bstep (se 1 (by rfl) ⟨826958, by rfl⟩ : syracuseStep 1102611 = 1653917) B1653917
theorem B1102627 : Blo 1100624 1102627 := bstep (se 1 (by rfl) ⟨826970, by rfl⟩ : syracuseStep 1102627 = 1653941) B1653941
theorem B7066403 : Blo 1100624 7066403 := bstep (se 1 (by rfl) ⟨5299802, by rfl⟩ : syracuseStep 7066403 = 10599605) B10599605
theorem B1102643 : Blo 1100624 1102643 := bstep (se 1 (by rfl) ⟨826982, by rfl⟩ : syracuseStep 1102643 = 1653965) B1653965
theorem B1102659 : Blo 1100624 1102659 := bstep (se 1 (by rfl) ⟨826994, by rfl⟩ : syracuseStep 1102659 = 1653989) B1653989
theorem B3724109 : Blo 1100624 3724109 := bstep (se 3 (by rfl) ⟨698270, by rfl⟩ : syracuseStep 3724109 = 1396541) B1396541
theorem B1102675 : Blo 1100624 1102675 := bstep (se 1 (by rfl) ⟨827006, by rfl⟩ : syracuseStep 1102675 = 1654013) B1654013
theorem B1102691 : Blo 1100624 1102691 := bstep (se 1 (by rfl) ⟨827018, by rfl⟩ : syracuseStep 1102691 = 1654037) B1654037
theorem B1102707 : Blo 1100624 1102707 := bstep (se 1 (by rfl) ⟨827030, by rfl⟩ : syracuseStep 1102707 = 1654061) B1654061
theorem B1102723 : Blo 1100624 1102723 := bstep (se 1 (by rfl) ⟨827042, by rfl⟩ : syracuseStep 1102723 = 1654085) B1654085
theorem B3724163 : Blo 1100624 3724163 := bstep (se 1 (by rfl) ⟨2793122, by rfl⟩ : syracuseStep 3724163 = 5586245) B5586245
theorem B1102739 : Blo 1100624 1102739 := bstep (se 1 (by rfl) ⟨827054, by rfl⟩ : syracuseStep 1102739 = 1654109) B1654109
theorem B1102755 : Blo 1100624 1102755 := bstep (se 1 (by rfl) ⟨827066, by rfl⟩ : syracuseStep 1102755 = 1654133) B1654133
theorem B1102771 : Blo 1100624 1102771 := bstep (se 1 (by rfl) ⟨827078, by rfl⟩ : syracuseStep 1102771 = 1654157) B1654157
theorem B1102787 : Blo 1100624 1102787 := bstep (se 1 (by rfl) ⟨827090, by rfl⟩ : syracuseStep 1102787 = 1654181) B1654181
theorem B1102803 : Blo 1100624 1102803 := bstep (se 1 (by rfl) ⟨827102, by rfl⟩ : syracuseStep 1102803 = 1654205) B1654205
theorem B1102819 : Blo 1100624 1102819 := bstep (se 1 (by rfl) ⟨827114, by rfl⟩ : syracuseStep 1102819 = 1654229) B1654229
theorem B1397731 : Blo 1100624 1397731 := bstep (se 1 (by rfl) ⟨1048298, by rfl⟩ : syracuseStep 1397731 = 2096597) B2096597
theorem B1102835 : Blo 1100624 1102835 := bstep (se 1 (by rfl) ⟨827126, by rfl⟩ : syracuseStep 1102835 = 1654253) B1654253
theorem B1102851 : Blo 1100624 1102851 := bstep (se 1 (by rfl) ⟨827138, by rfl⟩ : syracuseStep 1102851 = 1654277) B1654277
theorem B5592077 : Blo 1100624 5592077 := bstep (se 3 (by rfl) ⟨1048514, by rfl⟩ : syracuseStep 5592077 = 2097029) B2097029
theorem B2479121 : Blo 1100624 2479121 := bstep (se 2 (by rfl) ⟨929670, by rfl⟩ : syracuseStep 2479121 = 1859341) B1859341
theorem B1102867 : Blo 1100624 1102867 := bstep (se 1 (by rfl) ⟨827150, by rfl⟩ : syracuseStep 1102867 = 1654301) B1654301
theorem B2479139 : Blo 1100624 2479139 := bstep (se 1 (by rfl) ⟨1859354, by rfl⟩ : syracuseStep 2479139 = 3718709) B3718709
theorem B1102883 : Blo 1100624 1102883 := bstep (se 1 (by rfl) ⟨827162, by rfl⟩ : syracuseStep 1102883 = 1654325) B1654325
theorem B1102899 : Blo 1100624 1102899 := bstep (se 1 (by rfl) ⟨827174, by rfl⟩ : syracuseStep 1102899 = 1654349) B1654349
theorem B1791041 : Blo 1100624 1791041 := bstep (se 2 (by rfl) ⟨671640, by rfl⟩ : syracuseStep 1791041 = 1343281) B1343281
theorem B1102915 : Blo 1100624 1102915 := bstep (se 1 (by rfl) ⟨827186, by rfl⟩ : syracuseStep 1102915 = 1654373) B1654373
theorem B1397827 : Blo 1100624 1397827 := bstep (se 1 (by rfl) ⟨1048370, by rfl⟩ : syracuseStep 1397827 = 2096741) B2096741
theorem B6706253 : Blo 1100624 6706253 := bstep (se 3 (by rfl) ⟨1257422, by rfl⟩ : syracuseStep 6706253 = 2514845) B2514845
theorem B1102931 : Blo 1100624 1102931 := bstep (se 1 (by rfl) ⟨827198, by rfl⟩ : syracuseStep 1102931 = 1654397) B1654397
theorem B1102947 : Blo 1100624 1102947 := bstep (se 1 (by rfl) ⟨827210, by rfl⟩ : syracuseStep 1102947 = 1654421) B1654421
theorem B1102963 : Blo 1100624 1102963 := bstep (se 1 (by rfl) ⟨827222, by rfl⟩ : syracuseStep 1102963 = 1654445) B1654445
theorem B1102979 : Blo 1100624 1102979 := bstep (se 1 (by rfl) ⟨827234, by rfl⟩ : syracuseStep 1102979 = 1654469) B1654469
theorem B1987715 : Blo 1100624 1987715 := bstep (se 1 (by rfl) ⟨1490786, by rfl⟩ : syracuseStep 1987715 = 2981573) B2981573
theorem B3134609 : Blo 1100624 3134609 := bstep (se 2 (by rfl) ⟨1175478, by rfl⟩ : syracuseStep 3134609 = 2350957) B2350957
theorem B3724433 : Blo 1100624 3724433 := bstep (se 2 (by rfl) ⟨1396662, by rfl⟩ : syracuseStep 3724433 = 2793325) B2793325
theorem B1102995 : Blo 1100624 1102995 := bstep (se 1 (by rfl) ⟨827246, by rfl⟩ : syracuseStep 1102995 = 1654493) B1654493
theorem B1103011 : Blo 1100624 1103011 := bstep (se 1 (by rfl) ⟨827258, by rfl⟩ : syracuseStep 1103011 = 1654517) B1654517
theorem B1103027 : Blo 1100624 1103027 := bstep (se 1 (by rfl) ⟨827270, by rfl⟩ : syracuseStep 1103027 = 1654541) B1654541
theorem B1103043 : Blo 1100624 1103043 := bstep (se 1 (by rfl) ⟨827282, by rfl⟩ : syracuseStep 1103043 = 1654565) B1654565
theorem B1103059 : Blo 1100624 1103059 := bstep (se 1 (by rfl) ⟨827294, by rfl⟩ : syracuseStep 1103059 = 1654589) B1654589
theorem B1103075 : Blo 1100624 1103075 := bstep (se 1 (by rfl) ⟨827306, by rfl⟩ : syracuseStep 1103075 = 1654613) B1654613
theorem B7066865 : Blo 1100624 7066865 := bstep (se 2 (by rfl) ⟨2650074, by rfl⟩ : syracuseStep 7066865 = 5300149) B5300149
theorem B1103091 : Blo 1100624 1103091 := bstep (se 1 (by rfl) ⟨827318, by rfl⟩ : syracuseStep 1103091 = 1654637) B1654637
theorem B1103107 : Blo 1100624 1103107 := bstep (se 1 (by rfl) ⟨827330, by rfl⟩ : syracuseStep 1103107 = 1654661) B1654661
theorem B1103123 : Blo 1100624 1103123 := bstep (se 1 (by rfl) ⟨827342, by rfl⟩ : syracuseStep 1103123 = 1654685) B1654685
theorem B1103139 : Blo 1100624 1103139 := bstep (se 1 (by rfl) ⟨827354, by rfl⟩ : syracuseStep 1103139 = 1654709) B1654709
theorem B2479409 : Blo 1100624 2479409 := bstep (se 2 (by rfl) ⟨929778, by rfl⟩ : syracuseStep 2479409 = 1859557) B1859557
theorem B1103155 : Blo 1100624 1103155 := bstep (se 1 (by rfl) ⟨827366, by rfl⟩ : syracuseStep 1103155 = 1654733) B1654733
theorem B2479427 : Blo 1100624 2479427 := bstep (se 1 (by rfl) ⟨1859570, by rfl⟩ : syracuseStep 2479427 = 3719141) B3719141
theorem B6280517 : Blo 1100624 6280517 := bstep (se 4 (by rfl) ⟨588798, by rfl⟩ : syracuseStep 6280517 = 1177597) B1177597
theorem B1103171 : Blo 1100624 1103171 := bstep (se 1 (by rfl) ⟨827378, by rfl⟩ : syracuseStep 1103171 = 1654757) B1654757
theorem B1103187 : Blo 1100624 1103187 := bstep (se 1 (by rfl) ⟨827390, by rfl⟩ : syracuseStep 1103187 = 1654781) B1654781
theorem B1103203 : Blo 1100624 1103203 := bstep (se 1 (by rfl) ⟨827402, by rfl⟩ : syracuseStep 1103203 = 1654805) B1654805
theorem B1103219 : Blo 1100624 1103219 := bstep (se 1 (by rfl) ⟨827414, by rfl⟩ : syracuseStep 1103219 = 1654829) B1654829
theorem B1103235 : Blo 1100624 1103235 := bstep (se 1 (by rfl) ⟨827426, by rfl⟩ : syracuseStep 1103235 = 1654853) B1654853
theorem B1103251 : Blo 1100624 1103251 := bstep (se 1 (by rfl) ⟨827438, by rfl⟩ : syracuseStep 1103251 = 1654877) B1654877
theorem B1103267 : Blo 1100624 1103267 := bstep (se 1 (by rfl) ⟨827450, by rfl⟩ : syracuseStep 1103267 = 1654901) B1654901
theorem B1103283 : Blo 1100624 1103283 := bstep (se 1 (by rfl) ⟨827462, by rfl⟩ : syracuseStep 1103283 = 1654925) B1654925
theorem B1103299 : Blo 1100624 1103299 := bstep (se 1 (by rfl) ⟨827474, by rfl⟩ : syracuseStep 1103299 = 1654949) B1654949
theorem B1103315 : Blo 1100624 1103315 := bstep (se 1 (by rfl) ⟨827486, by rfl⟩ : syracuseStep 1103315 = 1654973) B1654973
theorem B17880547 : Blo 1100624 17880547 := bstep (se 1 (by rfl) ⟨13410410, by rfl⟩ : syracuseStep 17880547 = 26820821) B26820821
theorem B1103331 : Blo 1100624 1103331 := bstep (se 1 (by rfl) ⟨827498, by rfl⟩ : syracuseStep 1103331 = 1654997) B1654997
theorem B1103347 : Blo 1100624 1103347 := bstep (se 1 (by rfl) ⟨827510, by rfl⟩ : syracuseStep 1103347 = 1655021) B1655021
theorem B1103363 : Blo 1100624 1103363 := bstep (se 1 (by rfl) ⟨827522, by rfl⟩ : syracuseStep 1103363 = 1655045) B1655045
theorem B1103379 : Blo 1100624 1103379 := bstep (se 1 (by rfl) ⟨827534, by rfl⟩ : syracuseStep 1103379 = 1655069) B1655069
theorem B1103395 : Blo 1100624 1103395 := bstep (se 1 (by rfl) ⟨827546, by rfl⟩ : syracuseStep 1103395 = 1655093) B1655093
theorem B1103411 : Blo 1100624 1103411 := bstep (se 1 (by rfl) ⟨827558, by rfl⟩ : syracuseStep 1103411 = 1655117) B1655117
theorem B1103427 : Blo 1100624 1103427 := bstep (se 1 (by rfl) ⟨827570, by rfl⟩ : syracuseStep 1103427 = 1655141) B1655141
theorem B3528269 : Blo 1100624 3528269 := bstep (se 3 (by rfl) ⟨661550, by rfl⟩ : syracuseStep 3528269 = 1323101) B1323101
theorem B2479697 : Blo 1100624 2479697 := bstep (se 2 (by rfl) ⟨929886, by rfl⟩ : syracuseStep 2479697 = 1859773) B1859773
theorem B1103443 : Blo 1100624 1103443 := bstep (se 1 (by rfl) ⟨827582, by rfl⟩ : syracuseStep 1103443 = 1655165) B1655165
theorem B2479715 : Blo 1100624 2479715 := bstep (se 1 (by rfl) ⟨1859786, by rfl⟩ : syracuseStep 2479715 = 3719573) B3719573
theorem B1103459 : Blo 1100624 1103459 := bstep (se 1 (by rfl) ⟨827594, by rfl⟩ : syracuseStep 1103459 = 1655189) B1655189
theorem B5035619 : Blo 1100624 5035619 := bstep (se 1 (by rfl) ⟨3776714, by rfl⟩ : syracuseStep 5035619 = 7553429) B7553429
theorem B1103475 : Blo 1100624 1103475 := bstep (se 1 (by rfl) ⟨827606, by rfl⟩ : syracuseStep 1103475 = 1655213) B1655213
theorem B1103491 : Blo 1100624 1103491 := bstep (se 1 (by rfl) ⟨827618, by rfl⟩ : syracuseStep 1103491 = 1655237) B1655237
theorem B1103507 : Blo 1100624 1103507 := bstep (se 1 (by rfl) ⟨827630, by rfl⟩ : syracuseStep 1103507 = 1655261) B1655261
theorem B1103523 : Blo 1100624 1103523 := bstep (se 1 (by rfl) ⟨827642, by rfl⟩ : syracuseStep 1103523 = 1655285) B1655285
theorem B3724973 : Blo 1100624 3724973 := bstep (se 3 (by rfl) ⟨698432, by rfl⟩ : syracuseStep 3724973 = 1396865) B1396865
theorem B1103539 : Blo 1100624 1103539 := bstep (se 1 (by rfl) ⟨827654, by rfl⟩ : syracuseStep 1103539 = 1655309) B1655309
theorem B1988291 : Blo 1100624 1988291 := bstep (se 1 (by rfl) ⟨1491218, by rfl⟩ : syracuseStep 1988291 = 2982437) B2982437
theorem B1103555 : Blo 1100624 1103555 := bstep (se 1 (by rfl) ⟨827666, by rfl⟩ : syracuseStep 1103555 = 1655333) B1655333
theorem B7952069 : Blo 1100624 7952069 := bstep (se 4 (by rfl) ⟨745506, by rfl⟩ : syracuseStep 7952069 = 1491013) B1491013
theorem B1103571 : Blo 1100624 1103571 := bstep (se 1 (by rfl) ⟨827678, by rfl⟩ : syracuseStep 1103571 = 1655357) B1655357
theorem B1103587 : Blo 1100624 1103587 := bstep (se 1 (by rfl) ⟨827690, by rfl⟩ : syracuseStep 1103587 = 1655381) B1655381
theorem B3725027 : Blo 1100624 3725027 := bstep (se 1 (by rfl) ⟨2793770, by rfl⟩ : syracuseStep 3725027 = 5587541) B5587541
theorem B1103603 : Blo 1100624 1103603 := bstep (se 1 (by rfl) ⟨827702, by rfl⟩ : syracuseStep 1103603 = 1655405) B1655405
theorem B1103619 : Blo 1100624 1103619 := bstep (se 1 (by rfl) ⟨827714, by rfl⟩ : syracuseStep 1103619 = 1655429) B1655429
theorem B6280973 : Blo 1100624 6280973 := bstep (se 3 (by rfl) ⟨1177682, by rfl⟩ : syracuseStep 6280973 = 2355365) B2355365
theorem B1103635 : Blo 1100624 1103635 := bstep (se 1 (by rfl) ⟨827726, by rfl⟩ : syracuseStep 1103635 = 1655453) B1655453
theorem B6706979 : Blo 1100624 6706979 := bstep (se 1 (by rfl) ⟨5030234, by rfl⟩ : syracuseStep 6706979 = 10060469) B10060469
theorem B1103651 : Blo 1100624 1103651 := bstep (se 1 (by rfl) ⟨827738, by rfl⟩ : syracuseStep 1103651 = 1655477) B1655477
theorem B1103667 : Blo 1100624 1103667 := bstep (se 1 (by rfl) ⟨827750, by rfl⟩ : syracuseStep 1103667 = 1655501) B1655501
theorem B1103683 : Blo 1100624 1103683 := bstep (se 1 (by rfl) ⟨827762, by rfl⟩ : syracuseStep 1103683 = 1655525) B1655525
theorem B1103699 : Blo 1100624 1103699 := bstep (se 1 (by rfl) ⟨827774, by rfl⟩ : syracuseStep 1103699 = 1655549) B1655549
theorem B1857377 : Blo 1100624 1857377 := bstep (se 2 (by rfl) ⟨696516, by rfl⟩ : syracuseStep 1857377 = 1393033) B1393033
theorem B1103715 : Blo 1100624 1103715 := bstep (se 1 (by rfl) ⟨827786, by rfl⟩ : syracuseStep 1103715 = 1655573) B1655573
theorem B2479985 : Blo 1100624 2479985 := bstep (se 2 (by rfl) ⟨929994, by rfl⟩ : syracuseStep 2479985 = 1859989) B1859989
theorem B1103731 : Blo 1100624 1103731 := bstep (se 1 (by rfl) ⟨827798, by rfl⟩ : syracuseStep 1103731 = 1655597) B1655597
theorem B2480003 : Blo 1100624 2480003 := bstep (se 1 (by rfl) ⟨1860002, by rfl⟩ : syracuseStep 2480003 = 3720005) B3720005
theorem B1103747 : Blo 1100624 1103747 := bstep (se 1 (by rfl) ⟨827810, by rfl⟩ : syracuseStep 1103747 = 1655621) B1655621
theorem B1103763 : Blo 1100624 1103763 := bstep (se 1 (by rfl) ⟨827822, by rfl⟩ : syracuseStep 1103763 = 1655645) B1655645
theorem B1103779 : Blo 1100624 1103779 := bstep (se 1 (by rfl) ⟨827834, by rfl⟩ : syracuseStep 1103779 = 1655669) B1655669
theorem B1103795 : Blo 1100624 1103795 := bstep (se 1 (by rfl) ⟨827846, by rfl⟩ : syracuseStep 1103795 = 1655693) B1655693
theorem B1103811 : Blo 1100624 1103811 := bstep (se 1 (by rfl) ⟨827858, by rfl⟩ : syracuseStep 1103811 = 1655717) B1655717
theorem B1103827 : Blo 1100624 1103827 := bstep (se 1 (by rfl) ⟨827870, by rfl⟩ : syracuseStep 1103827 = 1655741) B1655741
theorem B1857505 : Blo 1100624 1857505 := bstep (se 2 (by rfl) ⟨696564, by rfl⟩ : syracuseStep 1857505 = 1393129) B1393129
theorem B1103843 : Blo 1100624 1103843 := bstep (se 1 (by rfl) ⟨827882, by rfl⟩ : syracuseStep 1103843 = 1655765) B1655765
theorem B3725297 : Blo 1100624 3725297 := bstep (se 2 (by rfl) ⟨1396986, by rfl⟩ : syracuseStep 3725297 = 2793973) B2793973
theorem B1103859 : Blo 1100624 1103859 := bstep (se 1 (by rfl) ⟨827894, by rfl⟩ : syracuseStep 1103859 = 1655789) B1655789
theorem B1857539 : Blo 1100624 1857539 := bstep (se 1 (by rfl) ⟨1393154, by rfl⟩ : syracuseStep 1857539 = 2786309) B2786309
theorem B1103875 : Blo 1100624 1103875 := bstep (se 1 (by rfl) ⟨827906, by rfl⟩ : syracuseStep 1103875 = 1655813) B1655813
theorem B1103891 : Blo 1100624 1103891 := bstep (se 1 (by rfl) ⟨827918, by rfl⟩ : syracuseStep 1103891 = 1655837) B1655837
theorem B1103907 : Blo 1100624 1103907 := bstep (se 1 (by rfl) ⟨827930, by rfl⟩ : syracuseStep 1103907 = 1655861) B1655861
theorem B1103923 : Blo 1100624 1103923 := bstep (se 1 (by rfl) ⟨827942, by rfl⟩ : syracuseStep 1103923 = 1655885) B1655885
theorem B1103939 : Blo 1100624 1103939 := bstep (se 1 (by rfl) ⟨827954, by rfl⟩ : syracuseStep 1103939 = 1655909) B1655909
theorem B1103955 : Blo 1100624 1103955 := bstep (se 1 (by rfl) ⟨827966, by rfl⟩ : syracuseStep 1103955 = 1655933) B1655933
theorem B1103971 : Blo 1100624 1103971 := bstep (se 1 (by rfl) ⟨827978, by rfl⟩ : syracuseStep 1103971 = 1655957) B1655957
theorem B1103987 : Blo 1100624 1103987 := bstep (se 1 (by rfl) ⟨827990, by rfl⟩ : syracuseStep 1103987 = 1655981) B1655981
theorem B1857667 : Blo 1100624 1857667 := bstep (se 1 (by rfl) ⟨1393250, by rfl⟩ : syracuseStep 1857667 = 2786501) B2786501
theorem B1104003 : Blo 1100624 1104003 := bstep (se 1 (by rfl) ⟨828002, by rfl⟩ : syracuseStep 1104003 = 1656005) B1656005
theorem B2480273 : Blo 1100624 2480273 := bstep (se 2 (by rfl) ⟨930102, by rfl⟩ : syracuseStep 2480273 = 1860205) B1860205
theorem B1104019 : Blo 1100624 1104019 := bstep (se 1 (by rfl) ⟨828014, by rfl⟩ : syracuseStep 1104019 = 1656029) B1656029
theorem B2480291 : Blo 1100624 2480291 := bstep (se 1 (by rfl) ⟨1860218, by rfl⟩ : syracuseStep 2480291 = 3720437) B3720437
theorem B1104035 : Blo 1100624 1104035 := bstep (se 1 (by rfl) ⟨828026, by rfl⟩ : syracuseStep 1104035 = 1656053) B1656053
theorem B1104051 : Blo 1100624 1104051 := bstep (se 1 (by rfl) ⟨828038, by rfl⟩ : syracuseStep 1104051 = 1656077) B1656077
theorem B1104067 : Blo 1100624 1104067 := bstep (se 1 (by rfl) ⟨828050, by rfl⟩ : syracuseStep 1104067 = 1656101) B1656101
theorem B1104083 : Blo 1100624 1104083 := bstep (se 1 (by rfl) ⟨828062, by rfl⟩ : syracuseStep 1104083 = 1656125) B1656125
theorem B1104099 : Blo 1100624 1104099 := bstep (se 1 (by rfl) ⟨828074, by rfl⟩ : syracuseStep 1104099 = 1656149) B1656149
theorem B1104115 : Blo 1100624 1104115 := bstep (se 1 (by rfl) ⟨828086, by rfl⟩ : syracuseStep 1104115 = 1656173) B1656173
theorem B1104131 : Blo 1100624 1104131 := bstep (se 1 (by rfl) ⟨828098, by rfl⟩ : syracuseStep 1104131 = 1656197) B1656197
theorem B15096077 : Blo 1100624 15096077 := bstep (se 3 (by rfl) ⟨2830514, by rfl⟩ : syracuseStep 15096077 = 5661029) B5661029
theorem B1857809 : Blo 1100624 1857809 := bstep (se 2 (by rfl) ⟨696678, by rfl⟩ : syracuseStep 1857809 = 1393357) B1393357
theorem B1104147 : Blo 1100624 1104147 := bstep (se 1 (by rfl) ⟨828110, by rfl⟩ : syracuseStep 1104147 = 1656221) B1656221
theorem B1104163 : Blo 1100624 1104163 := bstep (se 1 (by rfl) ⟨828122, by rfl⟩ : syracuseStep 1104163 = 1656245) B1656245
theorem B4184369 : Blo 1100624 4184369 := bstep (se 2 (by rfl) ⟨1569138, by rfl⟩ : syracuseStep 4184369 = 3138277) B3138277
theorem B1104179 : Blo 1100624 1104179 := bstep (se 1 (by rfl) ⟨828134, by rfl⟩ : syracuseStep 1104179 = 1656269) B1656269
theorem B1104195 : Blo 1100624 1104195 := bstep (se 1 (by rfl) ⟨828146, by rfl⟩ : syracuseStep 1104195 = 1656293) B1656293
theorem B11917637 : Blo 1100624 11917637 := bstep (se 4 (by rfl) ⟨1117278, by rfl⟩ : syracuseStep 11917637 = 2234557) B2234557
theorem B5036365 : Blo 1100624 5036365 := bstep (se 3 (by rfl) ⟨944318, by rfl⟩ : syracuseStep 5036365 = 1888637) B1888637
theorem B1104211 : Blo 1100624 1104211 := bstep (se 1 (by rfl) ⟨828158, by rfl⟩ : syracuseStep 1104211 = 1656317) B1656317
theorem B1104227 : Blo 1100624 1104227 := bstep (se 1 (by rfl) ⟨828170, by rfl⟩ : syracuseStep 1104227 = 1656341) B1656341
theorem B1104243 : Blo 1100624 1104243 := bstep (se 1 (by rfl) ⟨828182, by rfl⟩ : syracuseStep 1104243 = 1656365) B1656365
theorem B1104259 : Blo 1100624 1104259 := bstep (se 1 (by rfl) ⟨828194, by rfl⟩ : syracuseStep 1104259 = 1656389) B1656389
theorem B1857937 : Blo 1100624 1857937 := bstep (se 2 (by rfl) ⟨696726, by rfl⟩ : syracuseStep 1857937 = 1393453) B1393453
theorem B1104275 : Blo 1100624 1104275 := bstep (se 1 (by rfl) ⟨828206, by rfl⟩ : syracuseStep 1104275 = 1656413) B1656413
theorem B2120099 : Blo 1100624 2120099 := bstep (se 1 (by rfl) ⟨1590074, by rfl⟩ : syracuseStep 2120099 = 3180149) B3180149
theorem B1104291 : Blo 1100624 1104291 := bstep (se 1 (by rfl) ⟨828218, by rfl⟩ : syracuseStep 1104291 = 1656437) B1656437
theorem B2480561 : Blo 1100624 2480561 := bstep (se 2 (by rfl) ⟨930210, by rfl⟩ : syracuseStep 2480561 = 1860421) B1860421
theorem B1857971 : Blo 1100624 1857971 := bstep (se 1 (by rfl) ⟨1393478, by rfl⟩ : syracuseStep 1857971 = 2786957) B2786957
theorem B1104307 : Blo 1100624 1104307 := bstep (se 1 (by rfl) ⟨828230, by rfl⟩ : syracuseStep 1104307 = 1656461) B1656461
theorem B2480579 : Blo 1100624 2480579 := bstep (se 1 (by rfl) ⟨1860434, by rfl⟩ : syracuseStep 2480579 = 3720869) B3720869
theorem B1104323 : Blo 1100624 1104323 := bstep (se 1 (by rfl) ⟨828242, by rfl⟩ : syracuseStep 1104323 = 1656485) B1656485
theorem B1104339 : Blo 1100624 1104339 := bstep (se 1 (by rfl) ⟨828254, by rfl⟩ : syracuseStep 1104339 = 1656509) B1656509
theorem B1104355 : Blo 1100624 1104355 := bstep (se 1 (by rfl) ⟨828266, by rfl⟩ : syracuseStep 1104355 = 1656533) B1656533
theorem B1104371 : Blo 1100624 1104371 := bstep (se 1 (by rfl) ⟨828278, by rfl⟩ : syracuseStep 1104371 = 1656557) B1656557
theorem B1104387 : Blo 1100624 1104387 := bstep (se 1 (by rfl) ⟨828290, by rfl⟩ : syracuseStep 1104387 = 1656581) B1656581
theorem B3725837 : Blo 1100624 3725837 := bstep (se 3 (by rfl) ⟨698594, by rfl⟩ : syracuseStep 3725837 = 1397189) B1397189
theorem B1104403 : Blo 1100624 1104403 := bstep (se 1 (by rfl) ⟨828302, by rfl⟩ : syracuseStep 1104403 = 1656605) B1656605
theorem B1104419 : Blo 1100624 1104419 := bstep (se 1 (by rfl) ⟨828314, by rfl⟩ : syracuseStep 1104419 = 1656629) B1656629
theorem B1858099 : Blo 1100624 1858099 := bstep (se 1 (by rfl) ⟨1393574, by rfl⟩ : syracuseStep 1858099 = 2787149) B2787149
theorem B1104435 : Blo 1100624 1104435 := bstep (se 1 (by rfl) ⟨828326, by rfl⟩ : syracuseStep 1104435 = 1656653) B1656653
theorem B3136067 : Blo 1100624 3136067 := bstep (se 1 (by rfl) ⟨2352050, by rfl⟩ : syracuseStep 3136067 = 4704101) B4704101
theorem B3725891 : Blo 1100624 3725891 := bstep (se 1 (by rfl) ⟨2794418, by rfl⟩ : syracuseStep 3725891 = 5588837) B5588837
theorem B1104451 : Blo 1100624 1104451 := bstep (se 1 (by rfl) ⟨828338, by rfl⟩ : syracuseStep 1104451 = 1656677) B1656677
theorem B1104467 : Blo 1100624 1104467 := bstep (se 1 (by rfl) ⟨828350, by rfl⟩ : syracuseStep 1104467 = 1656701) B1656701
theorem B1104483 : Blo 1100624 1104483 := bstep (se 1 (by rfl) ⟨828362, by rfl⟩ : syracuseStep 1104483 = 1656725) B1656725
theorem B1104499 : Blo 1100624 1104499 := bstep (se 1 (by rfl) ⟨828374, by rfl⟩ : syracuseStep 1104499 = 1656749) B1656749
theorem B1530499 : Blo 1100624 1530499 := bstep (se 1 (by rfl) ⟨1147874, by rfl⟩ : syracuseStep 1530499 = 2295749) B2295749
theorem B1104515 : Blo 1100624 1104515 := bstep (se 1 (by rfl) ⟨828386, by rfl⟩ : syracuseStep 1104515 = 1656773) B1656773
theorem B1989265 : Blo 1100624 1989265 := bstep (se 2 (by rfl) ⟨745974, by rfl⟩ : syracuseStep 1989265 = 1491949) B1491949
theorem B1104531 : Blo 1100624 1104531 := bstep (se 1 (by rfl) ⟨828398, by rfl⟩ : syracuseStep 1104531 = 1656797) B1656797
theorem B1104547 : Blo 1100624 1104547 := bstep (se 1 (by rfl) ⟨828410, by rfl⟩ : syracuseStep 1104547 = 1656821) B1656821
theorem B1104563 : Blo 1100624 1104563 := bstep (se 1 (by rfl) ⟨828422, by rfl⟩ : syracuseStep 1104563 = 1656845) B1656845
theorem B1858241 : Blo 1100624 1858241 := bstep (se 2 (by rfl) ⟨696840, by rfl⟩ : syracuseStep 1858241 = 1393681) B1393681
theorem B1104579 : Blo 1100624 1104579 := bstep (se 1 (by rfl) ⟨828434, by rfl⟩ : syracuseStep 1104579 = 1656869) B1656869
theorem B2480849 : Blo 1100624 2480849 := bstep (se 2 (by rfl) ⟨930318, by rfl⟩ : syracuseStep 2480849 = 1860637) B1860637
theorem B1104595 : Blo 1100624 1104595 := bstep (se 1 (by rfl) ⟨828446, by rfl⟩ : syracuseStep 1104595 = 1656893) B1656893
theorem B2480867 : Blo 1100624 2480867 := bstep (se 1 (by rfl) ⟨1860650, by rfl⟩ : syracuseStep 2480867 = 3721301) B3721301
theorem B1104611 : Blo 1100624 1104611 := bstep (se 1 (by rfl) ⟨828458, by rfl⟩ : syracuseStep 1104611 = 1656917) B1656917
theorem B1858369 : Blo 1100624 1858369 := bstep (se 2 (by rfl) ⟨696888, by rfl⟩ : syracuseStep 1858369 = 1393777) B1393777
theorem B3726161 : Blo 1100624 3726161 := bstep (se 2 (by rfl) ⟨1397310, by rfl⟩ : syracuseStep 3726161 = 2794621) B2794621
theorem B1858403 : Blo 1100624 1858403 := bstep (se 1 (by rfl) ⟨1393802, by rfl⟩ : syracuseStep 1858403 = 2787605) B2787605
theorem B3529613 : Blo 1100624 3529613 := bstep (se 3 (by rfl) ⟨661802, by rfl⟩ : syracuseStep 3529613 = 1323605) B1323605
theorem B1858531 : Blo 1100624 1858531 := bstep (se 1 (by rfl) ⟨1393898, by rfl⟩ : syracuseStep 1858531 = 2787797) B2787797
theorem B2481137 : Blo 1100624 2481137 := bstep (se 2 (by rfl) ⟨930426, by rfl⟩ : syracuseStep 2481137 = 1860853) B1860853
theorem B2481155 : Blo 1100624 2481155 := bstep (se 1 (by rfl) ⟨1860866, by rfl⟩ : syracuseStep 2481155 = 3721733) B3721733
theorem B1858673 : Blo 1100624 1858673 := bstep (se 2 (by rfl) ⟨697002, by rfl⟩ : syracuseStep 1858673 = 1394005) B1394005
theorem B8936675 : Blo 1100624 8936675 := bstep (se 1 (by rfl) ⟨6702506, by rfl⟩ : syracuseStep 8936675 = 13405013) B13405013
theorem B4709603 : Blo 1100624 4709603 := bstep (se 1 (by rfl) ⟨3532202, by rfl⟩ : syracuseStep 4709603 = 7064405) B7064405
theorem B1858801 : Blo 1100624 1858801 := bstep (se 2 (by rfl) ⟨697050, by rfl⟩ : syracuseStep 1858801 = 1394101) B1394101
theorem B2481425 : Blo 1100624 2481425 := bstep (se 2 (by rfl) ⟨930534, by rfl⟩ : syracuseStep 2481425 = 1861069) B1861069
theorem B1858835 : Blo 1100624 1858835 := bstep (se 1 (by rfl) ⟨1394126, by rfl⟩ : syracuseStep 1858835 = 2788253) B2788253
theorem B2481443 : Blo 1100624 2481443 := bstep (se 1 (by rfl) ⟨1861082, by rfl⟩ : syracuseStep 2481443 = 3722165) B3722165
theorem B3530051 : Blo 1100624 3530051 := bstep (se 1 (by rfl) ⟨2647538, by rfl⟩ : syracuseStep 3530051 = 5295077) B5295077
theorem B3136877 : Blo 1100624 3136877 := bstep (se 3 (by rfl) ⟨588164, by rfl⟩ : syracuseStep 3136877 = 1176329) B1176329
theorem B3726701 : Blo 1100624 3726701 := bstep (se 3 (by rfl) ⟨698756, by rfl⟩ : syracuseStep 3726701 = 1397513) B1397513
theorem B1858963 : Blo 1100624 1858963 := bstep (se 1 (by rfl) ⟨1394222, by rfl⟩ : syracuseStep 1858963 = 2788445) B2788445
theorem B3726755 : Blo 1100624 3726755 := bstep (se 1 (by rfl) ⟨2795066, by rfl⟩ : syracuseStep 3726755 = 5590133) B5590133
theorem B8052209 : Blo 1100624 8052209 := bstep (se 2 (by rfl) ⟨3019578, by rfl⟩ : syracuseStep 8052209 = 6039157) B6039157
theorem B1859105 : Blo 1100624 1859105 := bstep (se 2 (by rfl) ⟨697164, by rfl⟩ : syracuseStep 1859105 = 1394329) B1394329
theorem B3137069 : Blo 1100624 3137069 := bstep (se 3 (by rfl) ⟨588200, by rfl⟩ : syracuseStep 3137069 = 1176401) B1176401
theorem B2481713 : Blo 1100624 2481713 := bstep (se 2 (by rfl) ⟨930642, by rfl⟩ : syracuseStep 2481713 = 1861285) B1861285
theorem B2481731 : Blo 1100624 2481731 := bstep (se 1 (by rfl) ⟨1861298, by rfl⟩ : syracuseStep 2481731 = 3722597) B3722597
theorem B2645635 : Blo 1100624 2645635 := bstep (se 1 (by rfl) ⟨1984226, by rfl⟩ : syracuseStep 2645635 = 3968453) B3968453
theorem B1859233 : Blo 1100624 1859233 := bstep (se 2 (by rfl) ⟨697212, by rfl⟩ : syracuseStep 1859233 = 1394425) B1394425
theorem B3727025 : Blo 1100624 3727025 := bstep (se 2 (by rfl) ⟨1397634, by rfl⟩ : syracuseStep 3727025 = 2795269) B2795269
theorem B1859267 : Blo 1100624 1859267 := bstep (se 1 (by rfl) ⟨1394450, by rfl⟩ : syracuseStep 1859267 = 2788901) B2788901
theorem B4185827 : Blo 1100624 4185827 := bstep (se 1 (by rfl) ⟨3139370, by rfl⟩ : syracuseStep 4185827 = 6278741) B6278741
theorem B1859395 : Blo 1100624 1859395 := bstep (se 1 (by rfl) ⟨1394546, by rfl⟩ : syracuseStep 1859395 = 2789093) B2789093
theorem B2482001 : Blo 1100624 2482001 := bstep (se 2 (by rfl) ⟨930750, by rfl⟩ : syracuseStep 2482001 = 1861501) B1861501
theorem B2482019 : Blo 1100624 2482019 := bstep (se 1 (by rfl) ⟨1861514, by rfl⟩ : syracuseStep 2482019 = 3723029) B3723029
theorem B1859537 : Blo 1100624 1859537 := bstep (se 2 (by rfl) ⟨697326, by rfl⟩ : syracuseStep 1859537 = 1394653) B1394653
theorem B1859665 : Blo 1100624 1859665 := bstep (se 2 (by rfl) ⟨697374, by rfl⟩ : syracuseStep 1859665 = 1394749) B1394749
theorem B2482289 : Blo 1100624 2482289 := bstep (se 2 (by rfl) ⟨930858, by rfl⟩ : syracuseStep 2482289 = 1861717) B1861717
theorem B1859699 : Blo 1100624 1859699 := bstep (se 1 (by rfl) ⟨1394774, by rfl⟩ : syracuseStep 1859699 = 2789549) B2789549
theorem B2482307 : Blo 1100624 2482307 := bstep (se 1 (by rfl) ⟨1861730, by rfl⟩ : syracuseStep 2482307 = 3723461) B3723461
theorem B2646211 : Blo 1100624 2646211 := bstep (se 1 (by rfl) ⟨1984658, by rfl⟩ : syracuseStep 2646211 = 3969317) B3969317
theorem B3727565 : Blo 1100624 3727565 := bstep (se 3 (by rfl) ⟨698918, by rfl⟩ : syracuseStep 3727565 = 1397837) B1397837
theorem B11297009 : Blo 1100624 11297009 := bstep (se 2 (by rfl) ⟨4236378, by rfl⟩ : syracuseStep 11297009 = 8472757) B8472757
theorem B1859827 : Blo 1100624 1859827 := bstep (se 1 (by rfl) ⟨1394870, by rfl⟩ : syracuseStep 1859827 = 2789741) B2789741
theorem B3727619 : Blo 1100624 3727619 := bstep (se 1 (by rfl) ⟨2795714, by rfl⟩ : syracuseStep 3727619 = 5591429) B5591429
theorem B1859969 : Blo 1100624 1859969 := bstep (se 2 (by rfl) ⟨697488, by rfl⟩ : syracuseStep 1859969 = 1394977) B1394977
theorem B2482577 : Blo 1100624 2482577 := bstep (se 2 (by rfl) ⟨930966, by rfl⟩ : syracuseStep 2482577 = 1861933) B1861933
theorem B2482595 : Blo 1100624 2482595 := bstep (se 1 (by rfl) ⟨1861946, by rfl⟩ : syracuseStep 2482595 = 3723893) B3723893
theorem B1860097 : Blo 1100624 1860097 := bstep (se 2 (by rfl) ⟨697536, by rfl⟩ : syracuseStep 1860097 = 1395073) B1395073
theorem B3138061 : Blo 1100624 3138061 := bstep (se 3 (by rfl) ⟨588386, by rfl⟩ : syracuseStep 3138061 = 1176773) B1176773
theorem B2089489 : Blo 1100624 2089489 := bstep (se 2 (by rfl) ⟨783558, by rfl⟩ : syracuseStep 2089489 = 1567117) B1567117
theorem B3727889 : Blo 1100624 3727889 := bstep (se 2 (by rfl) ⟨1397958, by rfl⟩ : syracuseStep 3727889 = 2795917) B2795917
theorem B1860131 : Blo 1100624 1860131 := bstep (se 1 (by rfl) ⟨1395098, by rfl⟩ : syracuseStep 1860131 = 2790197) B2790197
theorem B2646595 : Blo 1100624 2646595 := bstep (se 1 (by rfl) ⟨1984946, by rfl⟩ : syracuseStep 2646595 = 3969893) B3969893
theorem B2515555 : Blo 1100624 2515555 := bstep (se 1 (by rfl) ⟨1886666, by rfl⟩ : syracuseStep 2515555 = 3773333) B3773333
theorem B6283889 : Blo 1100624 6283889 := bstep (se 2 (by rfl) ⟨2356458, by rfl⟩ : syracuseStep 6283889 = 4712917) B4712917
theorem B8381069 : Blo 1100624 8381069 := bstep (se 3 (by rfl) ⟨1571450, by rfl⟩ : syracuseStep 8381069 = 3142901) B3142901
theorem B1860259 : Blo 1100624 1860259 := bstep (se 1 (by rfl) ⟨1395194, by rfl⟩ : syracuseStep 1860259 = 2790389) B2790389
theorem B2482865 : Blo 1100624 2482865 := bstep (se 2 (by rfl) ⟨931074, by rfl⟩ : syracuseStep 2482865 = 1862149) B1862149
theorem B2482883 : Blo 1100624 2482883 := bstep (se 1 (by rfl) ⟨1862162, by rfl⟩ : syracuseStep 2482883 = 3724325) B3724325
theorem B4186829 : Blo 1100624 4186829 := bstep (se 3 (by rfl) ⟨785030, by rfl⟩ : syracuseStep 4186829 = 1570061) B1570061
theorem B1860401 : Blo 1100624 1860401 := bstep (se 2 (by rfl) ⟨697650, by rfl⟩ : syracuseStep 1860401 = 1395301) B1395301
theorem B6710093 : Blo 1100624 6710093 := bstep (se 3 (by rfl) ⟨1258142, by rfl⟩ : syracuseStep 6710093 = 2516285) B2516285
theorem B2352017 : Blo 1100624 2352017 := bstep (se 2 (by rfl) ⟨882006, by rfl⟩ : syracuseStep 2352017 = 1764013) B1764013
theorem B2089891 : Blo 1100624 2089891 := bstep (se 1 (by rfl) ⟨1567418, by rfl⟩ : syracuseStep 2089891 = 3134837) B3134837
theorem B5235619 : Blo 1100624 5235619 := bstep (se 1 (by rfl) ⟨3926714, by rfl⟩ : syracuseStep 5235619 = 7853429) B7853429
theorem B1860529 : Blo 1100624 1860529 := bstep (se 2 (by rfl) ⟨697698, by rfl⟩ : syracuseStep 1860529 = 1395397) B1395397
theorem B2089937 : Blo 1100624 2089937 := bstep (se 2 (by rfl) ⟨783726, by rfl⟩ : syracuseStep 2089937 = 1567453) B1567453
theorem B2483153 : Blo 1100624 2483153 := bstep (se 2 (by rfl) ⟨931182, by rfl⟩ : syracuseStep 2483153 = 1862365) B1862365
theorem B1860563 : Blo 1100624 1860563 := bstep (se 1 (by rfl) ⟨1395422, by rfl⟩ : syracuseStep 1860563 = 2790845) B2790845
theorem B2483171 : Blo 1100624 2483171 := bstep (se 1 (by rfl) ⟨1862378, by rfl⟩ : syracuseStep 2483171 = 3724757) B3724757
theorem B14148593 : Blo 1100624 14148593 := bstep (se 2 (by rfl) ⟨5305722, by rfl⟩ : syracuseStep 14148593 = 10611445) B10611445
theorem B1860691 : Blo 1100624 1860691 := bstep (se 1 (by rfl) ⟨1395518, by rfl⟩ : syracuseStep 1860691 = 2791037) B2791037
theorem B3531971 : Blo 1100624 3531971 := bstep (se 1 (by rfl) ⟨2648978, by rfl⟩ : syracuseStep 3531971 = 5297957) B5297957
theorem B12543173 : Blo 1100624 12543173 := bstep (se 4 (by rfl) ⟨1175922, by rfl⟩ : syracuseStep 12543173 = 2351845) B2351845
theorem B1860833 : Blo 1100624 1860833 := bstep (se 2 (by rfl) ⟨697812, by rfl⟩ : syracuseStep 1860833 = 1395625) B1395625
theorem B2090225 : Blo 1100624 2090225 := bstep (se 2 (by rfl) ⟨783834, by rfl⟩ : syracuseStep 2090225 = 1567669) B1567669
theorem B2483441 : Blo 1100624 2483441 := bstep (se 2 (by rfl) ⟨931290, by rfl⟩ : syracuseStep 2483441 = 1862581) B1862581
theorem B2483459 : Blo 1100624 2483459 := bstep (se 1 (by rfl) ⟨1862594, by rfl⟩ : syracuseStep 2483459 = 3725189) B3725189
theorem B1238323 : Blo 1100624 1238323 := bstep (se 1 (by rfl) ⟨928742, by rfl⟩ : syracuseStep 1238323 = 1857485) B1857485
theorem B1860961 : Blo 1100624 1860961 := bstep (se 2 (by rfl) ⟨697860, by rfl⟩ : syracuseStep 1860961 = 1395721) B1395721
theorem B1860995 : Blo 1100624 1860995 := bstep (se 1 (by rfl) ⟨1395746, by rfl⟩ : syracuseStep 1860995 = 2791493) B2791493
theorem B2647441 : Blo 1100624 2647441 := bstep (se 2 (by rfl) ⟨992790, by rfl⟩ : syracuseStep 2647441 = 1985581) B1985581
theorem B1238467 : Blo 1100624 1238467 := bstep (se 1 (by rfl) ⟨928850, by rfl⟩ : syracuseStep 1238467 = 1857701) B1857701
theorem B1861123 : Blo 1100624 1861123 := bstep (se 1 (by rfl) ⟨1395842, by rfl⟩ : syracuseStep 1861123 = 2791685) B2791685
theorem B4023821 : Blo 1100624 4023821 := bstep (se 3 (by rfl) ⟨754466, by rfl⟩ : syracuseStep 4023821 = 1508933) B1508933
theorem B2483729 : Blo 1100624 2483729 := bstep (se 2 (by rfl) ⟨931398, by rfl⟩ : syracuseStep 2483729 = 1862797) B1862797
theorem B2483747 : Blo 1100624 2483747 := bstep (se 1 (by rfl) ⟨1862810, by rfl⟩ : syracuseStep 2483747 = 3725621) B3725621
theorem B1238611 : Blo 1100624 1238611 := bstep (se 1 (by rfl) ⟨928958, by rfl⟩ : syracuseStep 1238611 = 1857917) B1857917
theorem B1861265 : Blo 1100624 1861265 := bstep (se 2 (by rfl) ⟨697974, by rfl⟩ : syracuseStep 1861265 = 1395949) B1395949
theorem B25192133 : Blo 1100624 25192133 := bstep (se 4 (by rfl) ⟨2361762, by rfl⟩ : syracuseStep 25192133 = 4723525) B4723525
theorem B1238755 : Blo 1100624 1238755 := bstep (se 1 (by rfl) ⟨929066, by rfl⟩ : syracuseStep 1238755 = 1858133) B1858133
theorem B4777741 : Blo 1100624 4777741 := bstep (se 3 (by rfl) ⟨895826, by rfl⟩ : syracuseStep 4777741 = 1791653) B1791653
theorem B1861393 : Blo 1100624 1861393 := bstep (se 2 (by rfl) ⟨698022, by rfl⟩ : syracuseStep 1861393 = 1396045) B1396045
theorem B2484017 : Blo 1100624 2484017 := bstep (se 2 (by rfl) ⟨931506, by rfl⟩ : syracuseStep 2484017 = 1863013) B1863013
theorem B1861427 : Blo 1100624 1861427 := bstep (se 1 (by rfl) ⟨1396070, by rfl⟩ : syracuseStep 1861427 = 2792141) B2792141
theorem B2484035 : Blo 1100624 2484035 := bstep (se 1 (by rfl) ⟨1863026, by rfl⟩ : syracuseStep 2484035 = 3726053) B3726053
theorem B1238899 : Blo 1100624 1238899 := bstep (se 1 (by rfl) ⟨929174, by rfl⟩ : syracuseStep 1238899 = 1858349) B1858349
theorem B1861555 : Blo 1100624 1861555 := bstep (se 1 (by rfl) ⟨1396166, by rfl⟩ : syracuseStep 1861555 = 2792333) B2792333
theorem B2090947 : Blo 1100624 2090947 := bstep (se 1 (by rfl) ⟨1568210, by rfl⟩ : syracuseStep 2090947 = 3136421) B3136421
theorem B1239043 : Blo 1100624 1239043 := bstep (se 1 (by rfl) ⟨929282, by rfl⟩ : syracuseStep 1239043 = 1858565) B1858565
theorem B6285347 : Blo 1100624 6285347 := bstep (se 1 (by rfl) ⟨4714010, by rfl⟩ : syracuseStep 6285347 = 9428021) B9428021
theorem B1861697 : Blo 1100624 1861697 := bstep (se 2 (by rfl) ⟨698136, by rfl⟩ : syracuseStep 1861697 = 1396273) B1396273
theorem B2484305 : Blo 1100624 2484305 := bstep (se 2 (by rfl) ⟨931614, by rfl⟩ : syracuseStep 2484305 = 1863229) B1863229
theorem B2484323 : Blo 1100624 2484323 := bstep (se 1 (by rfl) ⟨1863242, by rfl⟩ : syracuseStep 2484323 = 3726485) B3726485
theorem B1239187 : Blo 1100624 1239187 := bstep (se 1 (by rfl) ⟨929390, by rfl⟩ : syracuseStep 1239187 = 1858781) B1858781
theorem B2353315 : Blo 1100624 2353315 := bstep (se 1 (by rfl) ⟨1764986, by rfl⟩ : syracuseStep 2353315 = 3529973) B3529973
theorem B1861825 : Blo 1100624 1861825 := bstep (se 2 (by rfl) ⟨698184, by rfl⟩ : syracuseStep 1861825 = 1396369) B1396369
theorem B3139793 : Blo 1100624 3139793 := bstep (se 2 (by rfl) ⟨1177422, by rfl⟩ : syracuseStep 3139793 = 2354845) B2354845
theorem B1861859 : Blo 1100624 1861859 := bstep (se 1 (by rfl) ⟨1396394, by rfl⟩ : syracuseStep 1861859 = 2792789) B2792789
theorem B1763603 : Blo 1100624 1763603 := bstep (se 1 (by rfl) ⟨1322702, by rfl⟩ : syracuseStep 1763603 = 2645405) B2645405
theorem B1239331 : Blo 1100624 1239331 := bstep (se 1 (by rfl) ⟨929498, by rfl⟩ : syracuseStep 1239331 = 1858997) B1858997
theorem B1861987 : Blo 1100624 1861987 := bstep (se 1 (by rfl) ⟨1396490, by rfl⟩ : syracuseStep 1861987 = 2792981) B2792981
theorem B2484593 : Blo 1100624 2484593 := bstep (se 2 (by rfl) ⟨931722, by rfl⟩ : syracuseStep 2484593 = 1863445) B1863445
theorem B2091395 : Blo 1100624 2091395 := bstep (se 1 (by rfl) ⟨1568546, by rfl⟩ : syracuseStep 2091395 = 3137093) B3137093
theorem B2484611 : Blo 1100624 2484611 := bstep (se 1 (by rfl) ⟨1863458, by rfl⟩ : syracuseStep 2484611 = 3726917) B3726917
theorem B9431437 : Blo 1100624 9431437 := bstep (se 3 (by rfl) ⟨1768394, by rfl⟩ : syracuseStep 9431437 = 3536789) B3536789
theorem B3139985 : Blo 1100624 3139985 := bstep (se 2 (by rfl) ⟨1177494, by rfl⟩ : syracuseStep 3139985 = 2354989) B2354989
theorem B1239475 : Blo 1100624 1239475 := bstep (se 1 (by rfl) ⟨929606, by rfl⟩ : syracuseStep 1239475 = 1859213) B1859213
theorem B1763795 : Blo 1100624 1763795 := bstep (se 1 (by rfl) ⟨1322846, by rfl⟩ : syracuseStep 1763795 = 2645693) B2645693
theorem B1862129 : Blo 1100624 1862129 := bstep (se 2 (by rfl) ⟨698298, by rfl⟩ : syracuseStep 1862129 = 1396597) B1396597
theorem B1239619 : Blo 1100624 1239619 := bstep (se 1 (by rfl) ⟨929714, by rfl⟩ : syracuseStep 1239619 = 1859429) B1859429
theorem B1567345 : Blo 1100624 1567345 := bstep (se 2 (by rfl) ⟨587754, by rfl⟩ : syracuseStep 1567345 = 1175509) B1175509
theorem B1862257 : Blo 1100624 1862257 := bstep (se 2 (by rfl) ⟨698346, by rfl⟩ : syracuseStep 1862257 = 1396693) B1396693
theorem B2484881 : Blo 1100624 2484881 := bstep (se 2 (by rfl) ⟨931830, by rfl⟩ : syracuseStep 2484881 = 1863661) B1863661
theorem B1862291 : Blo 1100624 1862291 := bstep (se 1 (by rfl) ⟨1396718, by rfl⟩ : syracuseStep 1862291 = 2793437) B2793437
theorem B2091683 : Blo 1100624 2091683 := bstep (se 1 (by rfl) ⟨1568762, by rfl⟩ : syracuseStep 2091683 = 3137525) B3137525
theorem B2484899 : Blo 1100624 2484899 := bstep (se 1 (by rfl) ⟨1863674, by rfl⟩ : syracuseStep 2484899 = 3727349) B3727349
theorem B1567441 : Blo 1100624 1567441 := bstep (se 2 (by rfl) ⟨587790, by rfl⟩ : syracuseStep 1567441 = 1175581) B1175581
theorem B1239763 : Blo 1100624 1239763 := bstep (se 1 (by rfl) ⟨929822, by rfl⟩ : syracuseStep 1239763 = 1859645) B1859645
theorem B4188941 : Blo 1100624 4188941 := bstep (se 3 (by rfl) ⟨785426, by rfl⟩ : syracuseStep 4188941 = 1570853) B1570853
theorem B1862419 : Blo 1100624 1862419 := bstep (se 1 (by rfl) ⟨1396814, by rfl⟩ : syracuseStep 1862419 = 2793629) B2793629
theorem B1239907 : Blo 1100624 1239907 := bstep (se 1 (by rfl) ⟨929930, by rfl⟩ : syracuseStep 1239907 = 1859861) B1859861
theorem B1862561 : Blo 1100624 1862561 := bstep (se 2 (by rfl) ⟨698460, by rfl⟩ : syracuseStep 1862561 = 1396921) B1396921
theorem B2485169 : Blo 1100624 2485169 := bstep (se 2 (by rfl) ⟨931938, by rfl⟩ : syracuseStep 2485169 = 1863877) B1863877
theorem B2485187 : Blo 1100624 2485187 := bstep (se 1 (by rfl) ⟨1863890, by rfl⟩ : syracuseStep 2485187 = 3727781) B3727781
theorem B1240051 : Blo 1100624 1240051 := bstep (se 1 (by rfl) ⟨930038, by rfl⟩ : syracuseStep 1240051 = 1860077) B1860077
theorem B6286349 : Blo 1100624 6286349 := bstep (se 3 (by rfl) ⟨1178690, by rfl⟩ : syracuseStep 6286349 = 2357381) B2357381
theorem B2583569 : Blo 1100624 2583569 := bstep (se 2 (by rfl) ⟨968838, by rfl⟩ : syracuseStep 2583569 = 1937677) B1937677
theorem B1862689 : Blo 1100624 1862689 := bstep (se 2 (by rfl) ⟨698508, by rfl⟩ : syracuseStep 1862689 = 1397017) B1397017
theorem B1862723 : Blo 1100624 1862723 := bstep (se 1 (by rfl) ⟨1397042, by rfl⟩ : syracuseStep 1862723 = 2794085) B2794085
theorem B1240195 : Blo 1100624 1240195 := bstep (se 1 (by rfl) ⟨930146, by rfl⟩ : syracuseStep 1240195 = 1860293) B1860293
theorem B1567937 : Blo 1100624 1567937 := bstep (se 2 (by rfl) ⟨587976, by rfl⟩ : syracuseStep 1567937 = 1175953) B1175953
theorem B1862851 : Blo 1100624 1862851 := bstep (se 1 (by rfl) ⟨1397138, by rfl⟩ : syracuseStep 1862851 = 2794277) B2794277
theorem B1240339 : Blo 1100624 1240339 := bstep (se 1 (by rfl) ⟨930254, by rfl⟩ : syracuseStep 1240339 = 1860509) B1860509
theorem B4713805 : Blo 1100624 4713805 := bstep (se 3 (by rfl) ⟨883838, by rfl⟩ : syracuseStep 4713805 = 1767677) B1767677
theorem B1862993 : Blo 1100624 1862993 := bstep (se 2 (by rfl) ⟨698622, by rfl⟩ : syracuseStep 1862993 = 1397245) B1397245
theorem B2354545 : Blo 1100624 2354545 := bstep (se 2 (by rfl) ⟨882954, by rfl⟩ : syracuseStep 2354545 = 1765909) B1765909
theorem B3140977 : Blo 1100624 3140977 := bstep (se 2 (by rfl) ⟨1177866, by rfl⟩ : syracuseStep 3140977 = 2355733) B2355733
theorem B1764769 : Blo 1100624 1764769 := bstep (se 2 (by rfl) ⟨661788, by rfl⟩ : syracuseStep 1764769 = 1323577) B1323577
theorem B1240483 : Blo 1100624 1240483 := bstep (se 1 (by rfl) ⟨930362, by rfl⟩ : syracuseStep 1240483 = 1860725) B1860725
theorem B7531973 : Blo 1100624 7531973 := bstep (se 4 (by rfl) ⟨706122, by rfl⟩ : syracuseStep 7531973 = 1412245) B1412245
theorem B1863121 : Blo 1100624 1863121 := bstep (se 2 (by rfl) ⟨698670, by rfl⟩ : syracuseStep 1863121 = 1397341) B1397341
theorem B8383985 : Blo 1100624 8383985 := bstep (se 2 (by rfl) ⟨3143994, by rfl⟩ : syracuseStep 8383985 = 6287989) B6287989
theorem B1863155 : Blo 1100624 1863155 := bstep (se 1 (by rfl) ⟨1397366, by rfl⟩ : syracuseStep 1863155 = 2794733) B2794733
theorem B4189745 : Blo 1100624 4189745 := bstep (se 2 (by rfl) ⟨1571154, by rfl⟩ : syracuseStep 4189745 = 3142309) B3142309
theorem B1240627 : Blo 1100624 1240627 := bstep (se 1 (by rfl) ⟨930470, by rfl⟩ : syracuseStep 1240627 = 1860941) B1860941
theorem B2977357 : Blo 1100624 2977357 := bstep (se 3 (by rfl) ⟨558254, by rfl⟩ : syracuseStep 2977357 = 1116509) B1116509
theorem B2092625 : Blo 1100624 2092625 := bstep (se 2 (by rfl) ⟨784734, by rfl⟩ : syracuseStep 2092625 = 1569469) B1569469
theorem B1863283 : Blo 1100624 1863283 := bstep (se 1 (by rfl) ⟨1397462, by rfl⟩ : syracuseStep 1863283 = 2794925) B2794925
theorem B3141251 : Blo 1100624 3141251 := bstep (se 1 (by rfl) ⟨2355938, by rfl⟩ : syracuseStep 3141251 = 4711877) B4711877
theorem B2125457 : Blo 1100624 2125457 := bstep (se 2 (by rfl) ⟨797046, by rfl⟩ : syracuseStep 2125457 = 1594093) B1594093
theorem B1240771 : Blo 1100624 1240771 := bstep (se 1 (by rfl) ⟨930578, by rfl⟩ : syracuseStep 1240771 = 1861157) B1861157
theorem B7073477 : Blo 1100624 7073477 := bstep (se 4 (by rfl) ⟨663138, by rfl⟩ : syracuseStep 7073477 = 1326277) B1326277
theorem B9432773 : Blo 1100624 9432773 := bstep (se 4 (by rfl) ⟨884322, by rfl⟩ : syracuseStep 9432773 = 1768645) B1768645
theorem B1863425 : Blo 1100624 1863425 := bstep (se 2 (by rfl) ⟨698784, by rfl⟩ : syracuseStep 1863425 = 1397569) B1397569
theorem B3534637 : Blo 1100624 3534637 := bstep (se 3 (by rfl) ⟨662744, by rfl⟩ : syracuseStep 3534637 = 1325489) B1325489
theorem B3141443 : Blo 1100624 3141443 := bstep (se 1 (by rfl) ⟨2356082, by rfl⟩ : syracuseStep 3141443 = 4712165) B4712165
theorem B5959493 : Blo 1100624 5959493 := bstep (se 4 (by rfl) ⟨558702, by rfl⟩ : syracuseStep 5959493 = 1117405) B1117405
theorem B1240915 : Blo 1100624 1240915 := bstep (se 1 (by rfl) ⟨930686, by rfl⟩ : syracuseStep 1240915 = 1861373) B1861373
theorem B1765217 : Blo 1100624 1765217 := bstep (se 2 (by rfl) ⟨661956, by rfl⟩ : syracuseStep 1765217 = 1323913) B1323913
theorem B1863553 : Blo 1100624 1863553 := bstep (se 2 (by rfl) ⟨698832, by rfl⟩ : syracuseStep 1863553 = 1397665) B1397665
theorem B2977681 : Blo 1100624 2977681 := bstep (se 2 (by rfl) ⟨1116630, by rfl⟩ : syracuseStep 2977681 = 2233261) B2233261
theorem B1863587 : Blo 1100624 1863587 := bstep (se 1 (by rfl) ⟨1397690, by rfl⟩ : syracuseStep 1863587 = 2795381) B2795381
theorem B13397957 : Blo 1100624 13397957 := bstep (se 4 (by rfl) ⟨1256058, by rfl⟩ : syracuseStep 13397957 = 2512117) B2512117
theorem B1241059 : Blo 1100624 1241059 := bstep (se 1 (by rfl) ⟨930794, by rfl⟩ : syracuseStep 1241059 = 1861589) B1861589
theorem B1568803 : Blo 1100624 1568803 := bstep (se 1 (by rfl) ⟨1176602, by rfl⟩ : syracuseStep 1568803 = 2353205) B2353205
theorem B1863715 : Blo 1100624 1863715 := bstep (se 1 (by rfl) ⟨1397786, by rfl⟩ : syracuseStep 1863715 = 2795573) B2795573
theorem B1241203 : Blo 1100624 1241203 := bstep (se 1 (by rfl) ⟨930902, by rfl⟩ : syracuseStep 1241203 = 1861805) B1861805
theorem B1568899 : Blo 1100624 1568899 := bstep (se 1 (by rfl) ⟨1176674, by rfl⟩ : syracuseStep 1568899 = 2353349) B2353349
theorem B2355331 : Blo 1100624 2355331 := bstep (se 1 (by rfl) ⟨1766498, by rfl⟩ : syracuseStep 2355331 = 3532997) B3532997
theorem B1863857 : Blo 1100624 1863857 := bstep (se 2 (by rfl) ⟨698946, by rfl⟩ : syracuseStep 1863857 = 1397893) B1397893
theorem B4190413 : Blo 1100624 4190413 := bstep (se 3 (by rfl) ⟨785702, by rfl⟩ : syracuseStep 4190413 = 1571405) B1571405
theorem B1241347 : Blo 1100624 1241347 := bstep (se 1 (by rfl) ⟨931010, by rfl⟩ : syracuseStep 1241347 = 1862021) B1862021
theorem B1863985 : Blo 1100624 1863985 := bstep (se 2 (by rfl) ⟨698994, by rfl⟩ : syracuseStep 1863985 = 1397989) B1397989
theorem B1864019 : Blo 1100624 1864019 := bstep (se 1 (by rfl) ⟨1398014, by rfl⟩ : syracuseStep 1864019 = 2796029) B2796029
theorem B1241491 : Blo 1100624 1241491 := bstep (se 1 (by rfl) ⟨931118, by rfl⟩ : syracuseStep 1241491 = 1862237) B1862237
theorem B2093521 : Blo 1100624 2093521 := bstep (se 2 (by rfl) ⟨785070, by rfl⟩ : syracuseStep 2093521 = 1570141) B1570141
theorem B1241635 : Blo 1100624 1241635 := bstep (se 1 (by rfl) ⟨931226, by rfl⟩ : syracuseStep 1241635 = 1862453) B1862453
theorem B3142253 : Blo 1100624 3142253 := bstep (se 3 (by rfl) ⟨589172, by rfl⟩ : syracuseStep 3142253 = 1178345) B1178345
theorem B2093681 : Blo 1100624 2093681 := bstep (se 2 (by rfl) ⟨785130, by rfl⟩ : syracuseStep 2093681 = 1570261) B1570261
theorem B1176179 : Blo 1100624 1176179 := bstep (se 1 (by rfl) ⟨882134, by rfl⟩ : syracuseStep 1176179 = 1764269) B1764269
theorem B1569395 : Blo 1100624 1569395 := bstep (se 1 (by rfl) ⟨1177046, by rfl⟩ : syracuseStep 1569395 = 2354093) B2354093
theorem B1241779 : Blo 1100624 1241779 := bstep (se 1 (by rfl) ⟨931334, by rfl⟩ : syracuseStep 1241779 = 1862669) B1862669
theorem B3142435 : Blo 1100624 3142435 := bstep (se 1 (by rfl) ⟨2356826, by rfl⟩ : syracuseStep 3142435 = 4713653) B4713653
theorem B1241923 : Blo 1100624 1241923 := bstep (se 1 (by rfl) ⟨931442, by rfl⟩ : syracuseStep 1241923 = 1862885) B1862885
theorem B2356049 : Blo 1100624 2356049 := bstep (se 2 (by rfl) ⟨883518, by rfl⟩ : syracuseStep 2356049 = 1767037) B1767037
theorem B1242067 : Blo 1100624 1242067 := bstep (se 1 (by rfl) ⟨931550, by rfl⟩ : syracuseStep 1242067 = 1863101) B1863101
theorem B4191203 : Blo 1100624 4191203 := bstep (se 1 (by rfl) ⟨3143402, by rfl⟩ : syracuseStep 4191203 = 6286805) B6286805
theorem B2094083 : Blo 1100624 2094083 := bstep (se 1 (by rfl) ⟨1570562, by rfl⟩ : syracuseStep 2094083 = 3141125) B3141125
theorem B1242211 : Blo 1100624 1242211 := bstep (se 1 (by rfl) ⟨931658, by rfl⟩ : syracuseStep 1242211 = 1863317) B1863317
theorem B1766627 : Blo 1100624 1766627 := bstep (se 1 (by rfl) ⟨1324970, by rfl⟩ : syracuseStep 1766627 = 2649941) B2649941
theorem B3536099 : Blo 1100624 3536099 := bstep (se 1 (by rfl) ⟨2652074, by rfl⟩ : syracuseStep 3536099 = 5304149) B5304149
theorem B5305571 : Blo 1100624 5305571 := bstep (se 1 (by rfl) ⟨3979178, by rfl⟩ : syracuseStep 5305571 = 7958357) B7958357
theorem B1570033 : Blo 1100624 1570033 := bstep (se 2 (by rfl) ⟨588762, by rfl⟩ : syracuseStep 1570033 = 1177525) B1177525
theorem B1242355 : Blo 1100624 1242355 := bstep (se 1 (by rfl) ⟨931766, by rfl⟩ : syracuseStep 1242355 = 1863533) B1863533
theorem B9532685 : Blo 1100624 9532685 := bstep (se 3 (by rfl) ⟨1787378, by rfl⟩ : syracuseStep 9532685 = 3574757) B3574757
theorem B3142925 : Blo 1100624 3142925 := bstep (se 3 (by rfl) ⟨589298, by rfl⟩ : syracuseStep 3142925 = 1178597) B1178597
theorem B2356561 : Blo 1100624 2356561 := bstep (se 2 (by rfl) ⟨883710, by rfl⟩ : syracuseStep 2356561 = 1767421) B1767421
theorem B1176931 : Blo 1100624 1176931 := bstep (se 1 (by rfl) ⟨882698, by rfl⟩ : syracuseStep 1176931 = 1765397) B1765397
theorem B1242499 : Blo 1100624 1242499 := bstep (se 1 (by rfl) ⟨931874, by rfl⟩ : syracuseStep 1242499 = 1863749) B1863749
theorem B1766819 : Blo 1100624 1766819 := bstep (se 1 (by rfl) ⟨1325114, by rfl⟩ : syracuseStep 1766819 = 2650229) B2650229
theorem B2651555 : Blo 1100624 2651555 := bstep (se 1 (by rfl) ⟨1988666, by rfl⟩ : syracuseStep 2651555 = 3977333) B3977333
theorem B3536369 : Blo 1100624 3536369 := bstep (se 2 (by rfl) ⟨1326138, by rfl⟩ : syracuseStep 3536369 = 2652277) B2652277
theorem B10057229 : Blo 1100624 10057229 := bstep (se 3 (by rfl) ⟨1885730, by rfl⟩ : syracuseStep 10057229 = 3771461) B3771461
theorem B1242643 : Blo 1100624 1242643 := bstep (se 1 (by rfl) ⟨931982, by rfl⟩ : syracuseStep 1242643 = 1863965) B1863965
theorem B1570369 : Blo 1100624 1570369 := bstep (se 2 (by rfl) ⟨588888, by rfl⟩ : syracuseStep 1570369 = 1177777) B1177777
theorem B1177187 : Blo 1100624 1177187 := bstep (se 1 (by rfl) ⟨882890, by rfl⟩ : syracuseStep 1177187 = 1765781) B1765781
theorem B4191857 : Blo 1100624 4191857 := bstep (se 2 (by rfl) ⟨1571946, by rfl⟩ : syracuseStep 4191857 = 3143893) B3143893
theorem B5961413 : Blo 1100624 5961413 := bstep (se 4 (by rfl) ⟨558882, by rfl⟩ : syracuseStep 5961413 = 1117765) B1117765
theorem B6289265 : Blo 1100624 6289265 := bstep (se 2 (by rfl) ⟨2358474, by rfl⟩ : syracuseStep 6289265 = 4716949) B4716949
theorem B2094979 : Blo 1100624 2094979 := bstep (se 1 (by rfl) ⟨1571234, by rfl⟩ : syracuseStep 2094979 = 3142469) B3142469
theorem B2652131 : Blo 1100624 2652131 := bstep (se 1 (by rfl) ⟨1989098, by rfl⟩ : syracuseStep 2652131 = 3978197) B3978197
theorem B2095139 : Blo 1100624 2095139 := bstep (se 1 (by rfl) ⟨1571354, by rfl⟩ : syracuseStep 2095139 = 3142709) B3142709
theorem B2652209 : Blo 1100624 2652209 := bstep (se 2 (by rfl) ⟨994578, by rfl⟩ : syracuseStep 2652209 = 1989157) B1989157
theorem B1570961 : Blo 1100624 1570961 := bstep (se 2 (by rfl) ⟨589110, by rfl⟩ : syracuseStep 1570961 = 1178221) B1178221
theorem B2652401 : Blo 1100624 2652401 := bstep (se 2 (by rfl) ⟨994650, by rfl⟩ : syracuseStep 2652401 = 1989301) B1989301
theorem B1702163 : Blo 1100624 1702163 := bstep (se 1 (by rfl) ⟨1276622, by rfl⟩ : syracuseStep 1702163 = 2553245) B2553245
theorem B1177939 : Blo 1100624 1177939 := bstep (se 1 (by rfl) ⟨883454, by rfl⟩ : syracuseStep 1177939 = 1766909) B1766909
theorem B3144109 : Blo 1100624 3144109 := bstep (se 3 (by rfl) ⟨589520, by rfl⟩ : syracuseStep 3144109 = 1179041) B1179041
theorem B2652689 : Blo 1100624 2652689 := bstep (se 2 (by rfl) ⟨994758, by rfl⟩ : syracuseStep 2652689 = 1989517) B1989517
theorem B1571491 : Blo 1100624 1571491 := bstep (se 1 (by rfl) ⟨1178618, by rfl⟩ : syracuseStep 1571491 = 2357237) B2357237
theorem B2390723 : Blo 1100624 2390723 := bstep (se 1 (by rfl) ⟨1793042, by rfl⟩ : syracuseStep 2390723 = 3586085) B3586085
theorem B1768241 : Blo 1100624 1768241 := bstep (se 2 (by rfl) ⟨663090, by rfl⟩ : syracuseStep 1768241 = 1326181) B1326181
theorem B2358065 : Blo 1100624 2358065 := bstep (se 2 (by rfl) ⟨884274, by rfl⟩ : syracuseStep 2358065 = 1768549) B1768549
theorem B12549005 : Blo 1100624 12549005 := bstep (se 3 (by rfl) ⟨2352938, by rfl⟩ : syracuseStep 12549005 = 4705877) B4705877
theorem B1571827 : Blo 1100624 1571827 := bstep (se 1 (by rfl) ⟨1178870, by rfl⟩ : syracuseStep 1571827 = 2357741) B2357741
theorem B4193315 : Blo 1100624 4193315 := bstep (se 1 (by rfl) ⟨3144986, by rfl⟩ : syracuseStep 4193315 = 6289973) B6289973
theorem B4193329 : Blo 1100624 4193329 := bstep (se 2 (by rfl) ⟨1572498, by rfl⟩ : syracuseStep 4193329 = 3144997) B3144997
theorem B2096209 : Blo 1100624 2096209 := bstep (se 2 (by rfl) ⟨786078, by rfl⟩ : syracuseStep 2096209 = 1572157) B1572157
theorem B5307569 : Blo 1100624 5307569 := bstep (se 2 (by rfl) ⟨1990338, by rfl⟩ : syracuseStep 5307569 = 3980677) B3980677
theorem B7077041 : Blo 1100624 7077041 := bstep (se 2 (by rfl) ⟨2653890, by rfl⟩ : syracuseStep 7077041 = 5307781) B5307781
theorem B2358467 : Blo 1100624 2358467 := bstep (se 1 (by rfl) ⟨1768850, by rfl⟩ : syracuseStep 2358467 = 3537701) B3537701
theorem B6290723 : Blo 1100624 6290723 := bstep (se 1 (by rfl) ⟨4718042, by rfl⟩ : syracuseStep 6290723 = 9436085) B9436085
theorem B3439921 : Blo 1100624 3439921 := bstep (se 2 (by rfl) ⟨1289970, by rfl⟩ : syracuseStep 3439921 = 2579941) B2579941
theorem B3145169 : Blo 1100624 3145169 := bstep (se 2 (by rfl) ⟨1179438, by rfl⟩ : syracuseStep 3145169 = 2358877) B2358877
theorem B10616291 : Blo 1100624 10616291 := bstep (se 1 (by rfl) ⟨7962218, by rfl⟩ : syracuseStep 10616291 = 15924437) B15924437
theorem B2981357 : Blo 1100624 2981357 := bstep (se 3 (by rfl) ⟨559004, by rfl⟩ : syracuseStep 2981357 = 1118009) B1118009
theorem B1572385 : Blo 1100624 1572385 := bstep (se 2 (by rfl) ⟨589644, by rfl⟩ : syracuseStep 1572385 = 1179289) B1179289
theorem B1179203 : Blo 1100624 1179203 := bstep (se 1 (by rfl) ⟨884402, by rfl⟩ : syracuseStep 1179203 = 1768805) B1768805
theorem B1572419 : Blo 1100624 1572419 := bstep (se 1 (by rfl) ⟨1179314, by rfl⟩ : syracuseStep 1572419 = 2358629) B2358629
theorem B4718179 : Blo 1100624 4718179 := bstep (se 1 (by rfl) ⟨3538634, by rfl⟩ : syracuseStep 4718179 = 7077269) B7077269
theorem B2981485 : Blo 1100624 2981485 := bstep (se 3 (by rfl) ⟨559028, by rfl⟩ : syracuseStep 2981485 = 1118057) B1118057
theorem B2981681 : Blo 1100624 2981681 := bstep (se 2 (by rfl) ⟨1118130, by rfl⟩ : syracuseStep 2981681 = 2236261) B2236261
theorem B2982091 : Blo 1100624 2982091 := bstep (se 1 (by rfl) ⟨2236568, by rfl⟩ : syracuseStep 2982091 = 4473137) B4473137
theorem B60293645 : Blo 1100624 60293645 := bstep (se 3 (by rfl) ⟨11305058, by rfl⟩ : syracuseStep 60293645 = 22610117) B22610117
theorem B19104437 : Blo 1100624 19104437 := bstep (se 5 (by rfl) ⟨895520, by rfl⟩ : syracuseStep 19104437 = 1791041) B1791041
theorem B2785985 : Blo 1100624 2785985 := bstep (se 2 (by rfl) ⟨1044744, by rfl⟩ : syracuseStep 2785985 = 2089489) B2089489
theorem B9536291 : Blo 1100624 9536291 := bstep (se 1 (by rfl) ⟨7152218, by rfl⟩ : syracuseStep 9536291 = 14304437) B14304437
theorem B2786521 : Blo 1100624 2786521 := bstep (se 2 (by rfl) ⟨1044945, by rfl⟩ : syracuseStep 2786521 = 2089891) B2089891
theorem B6980825 : Blo 1100624 6980825 := bstep (se 2 (by rfl) ⟨2617809, by rfl⟩ : syracuseStep 6980825 = 5235619) B5235619
theorem B120620501 : Blo 1100624 120620501 := bstep (se 7 (by rfl) ⟨1413521, by rfl⟩ : syracuseStep 120620501 = 2827043) B2827043
theorem B2983475 : Blo 1100624 2983475 := bstep (se 1 (by rfl) ⟨2237606, by rfl⟩ : syracuseStep 2983475 = 4475213) B4475213
theorem B5572313 : Blo 1100624 5572313 := bstep (se 2 (by rfl) ⟨2089617, by rfl⟩ : syracuseStep 5572313 = 4179235) B4179235
theorem B1116055 : Blo 1100624 1116055 := bstep (se 1 (by rfl) ⟨837041, by rfl⟩ : syracuseStep 1116055 = 1674083) B1674083
theorem B9406529 : Blo 1100624 9406529 := bstep (se 2 (by rfl) ⟨3527448, by rfl⟩ : syracuseStep 9406529 = 7054897) B7054897
theorem B2787635 : Blo 1100624 2787635 := bstep (se 1 (by rfl) ⟨2090726, by rfl⟩ : syracuseStep 2787635 = 4181453) B4181453
theorem B2787929 : Blo 1100624 2787929 := bstep (se 2 (by rfl) ⟨1045473, by rfl⟩ : syracuseStep 2787929 = 2090947) B2090947
theorem B5573933 : Blo 1100624 5573933 := bstep (se 3 (by rfl) ⟨1045112, by rfl⟩ : syracuseStep 5573933 = 2090225) B2090225
theorem B4296365 : Blo 1100624 4296365 := bstep (se 3 (by rfl) ⟨805568, by rfl⟩ : syracuseStep 4296365 = 1611137) B1611137
theorem B8359685 : Blo 1100624 8359685 := bstep (se 4 (by rfl) ⟨783720, by rfl⟩ : syracuseStep 8359685 = 1567441) B1567441
theorem B30642245 : Blo 1100624 30642245 := bstep (se 4 (by rfl) ⟨2872710, by rfl⟩ : syracuseStep 30642245 = 5745421) B5745421
theorem B10064051 : Blo 1100624 10064051 := bstep (se 1 (by rfl) ⟨7548038, by rfl⟩ : syracuseStep 10064051 = 15096077) B15096077
theorem B2789579 : Blo 1100624 2789579 := bstep (se 1 (by rfl) ⟨2092184, by rfl⟩ : syracuseStep 2789579 = 4184369) B4184369
theorem B1118443 : Blo 1100624 1118443 := bstep (se 1 (by rfl) ⟨838832, by rfl⟩ : syracuseStep 1118443 = 1677665) B1677665
theorem B3772993 : Blo 1100624 3772993 := bstep (se 2 (by rfl) ⟨1414872, by rfl⟩ : syracuseStep 3772993 = 2829745) B2829745
theorem B3969809 : Blo 1100624 3969809 := bstep (se 2 (by rfl) ⟨1488678, by rfl⟩ : syracuseStep 3969809 = 2977357) B2977357
theorem B2233163 : Blo 1100624 2233163 := bstep (se 1 (by rfl) ⟨1674872, by rfl⟩ : syracuseStep 2233163 = 3349745) B3349745
theorem B2790551 : Blo 1100624 2790551 := bstep (se 1 (by rfl) ⟨2092913, by rfl⟩ : syracuseStep 2790551 = 4185827) B4185827
theorem B3970241 : Blo 1100624 3970241 := bstep (se 2 (by rfl) ⟨1488840, by rfl⟩ : syracuseStep 3970241 = 2977681) B2977681
theorem B28251665 : Blo 1100624 28251665 := bstep (se 2 (by rfl) ⟨10594374, by rfl⟩ : syracuseStep 28251665 = 21188749) B21188749
theorem B2234137 : Blo 1100624 2234137 := bstep (se 2 (by rfl) ⟨837801, by rfl⟩ : syracuseStep 2234137 = 1675603) B1675603
theorem B2791219 : Blo 1100624 2791219 := bstep (se 1 (by rfl) ⟨2093414, by rfl⟩ : syracuseStep 2791219 = 4186829) B4186829
theorem B2791361 : Blo 1100624 2791361 := bstep (se 2 (by rfl) ⟨1046760, by rfl⟩ : syracuseStep 2791361 = 2093521) B2093521
theorem B14129113 : Blo 1100624 14129113 := bstep (se 2 (by rfl) ⟨5298417, by rfl⟩ : syracuseStep 14129113 = 10596835) B10596835
theorem B8362115 : Blo 1100624 8362115 := bstep (se 1 (by rfl) ⟨6271586, by rfl⟩ : syracuseStep 8362115 = 12543173) B12543173
theorem B21174533 : Blo 1100624 21174533 := bstep (se 4 (by rfl) ⟨1985112, by rfl⟩ : syracuseStep 21174533 = 3970225) B3970225
theorem B5577821 : Blo 1100624 5577821 := bstep (se 3 (by rfl) ⟨1045841, by rfl⟩ : syracuseStep 5577821 = 2091683) B2091683
theorem B2792627 : Blo 1100624 2792627 := bstep (se 1 (by rfl) ⟨2094470, by rfl⟩ : syracuseStep 2792627 = 4188941) B4188941
theorem B5021315 : Blo 1100624 5021315 := bstep (se 1 (by rfl) ⟨3765986, by rfl⟩ : syracuseStep 5021315 = 7531973) B7531973
theorem B2793163 : Blo 1100624 2793163 := bstep (se 1 (by rfl) ⟨2094872, by rfl⟩ : syracuseStep 2793163 = 4189745) B4189745
theorem B9412301 : Blo 1100624 9412301 := bstep (se 3 (by rfl) ⟨1764806, by rfl⟩ : syracuseStep 9412301 = 3529613) B3529613
theorem B1416971 : Blo 1100624 1416971 := bstep (se 1 (by rfl) ⟨1062728, by rfl⟩ : syracuseStep 1416971 = 2125457) B2125457
theorem B2793305 : Blo 1100624 2793305 := bstep (se 2 (by rfl) ⟨1047489, by rfl⟩ : syracuseStep 2793305 = 2094979) B2094979
theorem B3972995 : Blo 1100624 3972995 := bstep (se 1 (by rfl) ⟨2979746, by rfl⟩ : syracuseStep 3972995 = 5959493) B5959493
theorem B18816947 : Blo 1100624 18816947 := bstep (se 1 (by rfl) ⟨14112710, by rfl⟩ : syracuseStep 18816947 = 28225421) B28225421
theorem B10068317 : Blo 1100624 10068317 := bstep (se 3 (by rfl) ⟨1887809, by rfl⟩ : syracuseStep 10068317 = 3775619) B3775619
theorem B11903449 : Blo 1100624 11903449 := bstep (se 2 (by rfl) ⟨4463793, by rfl⟩ : syracuseStep 11903449 = 8927587) B8927587
theorem B2794135 : Blo 1100624 2794135 := bstep (se 1 (by rfl) ⟨2095601, by rfl⟩ : syracuseStep 2794135 = 4191203) B4191203
theorem B2040665 : Blo 1100624 2040665 := bstep (se 2 (by rfl) ⟨765249, by rfl⟩ : syracuseStep 2040665 = 1530499) B1530499
theorem B3974189 : Blo 1100624 3974189 := bstep (se 3 (by rfl) ⟨745160, by rfl⟩ : syracuseStep 3974189 = 1490321) B1490321
theorem B2794571 : Blo 1100624 2794571 := bstep (se 1 (by rfl) ⟨2095928, by rfl⟩ : syracuseStep 2794571 = 4191857) B4191857
theorem B10069085 : Blo 1100624 10069085 := bstep (se 3 (by rfl) ⟨1887953, by rfl⟩ : syracuseStep 10069085 = 3775907) B3775907
theorem B3974275 : Blo 1100624 3974275 := bstep (se 1 (by rfl) ⟨2980706, by rfl⟩ : syracuseStep 3974275 = 5961413) B5961413
theorem B5579927 : Blo 1100624 5579927 := bstep (se 1 (by rfl) ⟨4184945, by rfl⟩ : syracuseStep 5579927 = 8369891) B8369891
theorem B2794945 : Blo 1100624 2794945 := bstep (se 2 (by rfl) ⟨1048104, by rfl⟩ : syracuseStep 2794945 = 2096209) B2096209
theorem B8365517 : Blo 1100624 8365517 := bstep (se 3 (by rfl) ⟨1568534, by rfl⟩ : syracuseStep 8365517 = 3137069) B3137069
theorem B8955485 : Blo 1100624 8955485 := bstep (se 3 (by rfl) ⟨1679153, by rfl⟩ : syracuseStep 8955485 = 3358307) B3358307
theorem B9053873 : Blo 1100624 9053873 := bstep (se 2 (by rfl) ⟨3395202, by rfl⟩ : syracuseStep 9053873 = 6790405) B6790405
theorem B11904833 : Blo 1100624 11904833 := bstep (se 2 (by rfl) ⟨4464312, by rfl⟩ : syracuseStep 11904833 = 8928625) B8928625
theorem B8366003 : Blo 1100624 8366003 := bstep (se 1 (by rfl) ⟨6274502, by rfl⟩ : syracuseStep 8366003 = 12549005) B12549005
theorem B1255415 : Blo 1100624 1255415 := bstep (se 1 (by rfl) ⟨941561, by rfl⟩ : syracuseStep 1255415 = 1883123) B1883123
theorem B2795543 : Blo 1100624 2795543 := bstep (se 1 (by rfl) ⟨2096657, by rfl⟩ : syracuseStep 2795543 = 4193315) B4193315
theorem B3975313 : Blo 1100624 3975313 := bstep (se 2 (by rfl) ⟨1490742, by rfl⟩ : syracuseStep 3975313 = 2981485) B2981485
theorem B7547543 : Blo 1100624 7547543 := bstep (se 1 (by rfl) ⟨5660657, by rfl⟩ : syracuseStep 7547543 = 11321315) B11321315
theorem B30125357 : Blo 1100624 30125357 := bstep (se 3 (by rfl) ⟨5648504, by rfl⟩ : syracuseStep 30125357 = 11297009) B11297009
theorem B8367461 : Blo 1100624 8367461 := bstep (se 4 (by rfl) ⟨784449, by rfl⟩ : syracuseStep 8367461 = 1568899) B1568899
theorem B5025203 : Blo 1100624 5025203 := bstep (se 1 (by rfl) ⟨3768902, by rfl⟩ : syracuseStep 5025203 = 7537805) B7537805
theorem B24161885 : Blo 1100624 24161885 := bstep (se 3 (by rfl) ⟨4530353, by rfl⟩ : syracuseStep 24161885 = 9060707) B9060707
theorem B8367947 : Blo 1100624 8367947 := bstep (se 1 (by rfl) ⟨6275960, by rfl⟩ : syracuseStep 8367947 = 12551921) B12551921
theorem B3715037 : Blo 1100624 3715037 := bstep (se 3 (by rfl) ⟨696569, by rfl⟩ : syracuseStep 3715037 = 1393139) B1393139
theorem B1912907 : Blo 1100624 1912907 := bstep (se 1 (by rfl) ⟨1434680, by rfl⟩ : syracuseStep 1912907 = 2869361) B2869361
theorem B3977419 : Blo 1100624 3977419 := bstep (se 1 (by rfl) ⟨2983064, by rfl⟩ : syracuseStep 3977419 = 5966129) B5966129
theorem B8925389 : Blo 1100624 8925389 := bstep (se 3 (by rfl) ⟨1673510, by rfl⟩ : syracuseStep 8925389 = 3347021) B3347021
theorem B1651019 : Blo 1100624 1651019 := bstep (se 1 (by rfl) ⟨1238264, by rfl⟩ : syracuseStep 1651019 = 2476529) B2476529
theorem B1651031 : Blo 1100624 1651031 := bstep (se 1 (by rfl) ⟨1238273, by rfl⟩ : syracuseStep 1651031 = 2476547) B2476547
theorem B1651097 : Blo 1100624 1651097 := bstep (se 2 (by rfl) ⟨619161, by rfl⟩ : syracuseStep 1651097 = 1238323) B1238323
theorem B1651211 : Blo 1100624 1651211 := bstep (se 1 (by rfl) ⟨1238408, by rfl⟩ : syracuseStep 1651211 = 2476817) B2476817
theorem B1651223 : Blo 1100624 1651223 := bstep (se 1 (by rfl) ⟨1238417, by rfl⟩ : syracuseStep 1651223 = 2476835) B2476835
theorem B1651289 : Blo 1100624 1651289 := bstep (se 2 (by rfl) ⟨619233, by rfl⟩ : syracuseStep 1651289 = 1238467) B1238467
theorem B5583491 : Blo 1100624 5583491 := bstep (se 1 (by rfl) ⟨4187618, by rfl⟩ : syracuseStep 5583491 = 8375237) B8375237
theorem B1651403 : Blo 1100624 1651403 := bstep (se 1 (by rfl) ⟨1238552, by rfl⟩ : syracuseStep 1651403 = 2477105) B2477105
theorem B1651415 : Blo 1100624 1651415 := bstep (se 1 (by rfl) ⟨1238561, by rfl⟩ : syracuseStep 1651415 = 2477123) B2477123
theorem B1487641 : Blo 1100624 1487641 := bstep (se 2 (by rfl) ⟨557865, by rfl⟩ : syracuseStep 1487641 = 1115731) B1115731
theorem B1651481 : Blo 1100624 1651481 := bstep (se 2 (by rfl) ⟨619305, by rfl⟩ : syracuseStep 1651481 = 1238611) B1238611
theorem B1651595 : Blo 1100624 1651595 := bstep (se 1 (by rfl) ⟨1238696, by rfl⟩ : syracuseStep 1651595 = 2477393) B2477393
theorem B1651607 : Blo 1100624 1651607 := bstep (se 1 (by rfl) ⟨1238705, by rfl⟩ : syracuseStep 1651607 = 2477411) B2477411
theorem B1651673 : Blo 1100624 1651673 := bstep (se 2 (by rfl) ⟨619377, by rfl⟩ : syracuseStep 1651673 = 1238755) B1238755
theorem B6370321 : Blo 1100624 6370321 := bstep (se 2 (by rfl) ⟨2388870, by rfl⟩ : syracuseStep 6370321 = 4777741) B4777741
theorem B3716171 : Blo 1100624 3716171 := bstep (se 1 (by rfl) ⟨2787128, by rfl⟩ : syracuseStep 3716171 = 5574257) B5574257
theorem B1651787 : Blo 1100624 1651787 := bstep (se 1 (by rfl) ⟨1238840, by rfl⟩ : syracuseStep 1651787 = 2477681) B2477681
theorem B3224651 : Blo 1100624 3224651 := bstep (se 1 (by rfl) ⟨2418488, by rfl⟩ : syracuseStep 3224651 = 4836977) B4836977
theorem B1651799 : Blo 1100624 1651799 := bstep (se 1 (by rfl) ⟨1238849, by rfl⟩ : syracuseStep 1651799 = 2477699) B2477699
theorem B1651865 : Blo 1100624 1651865 := bstep (se 2 (by rfl) ⟨619449, by rfl⟩ : syracuseStep 1651865 = 1238899) B1238899
theorem B1651979 : Blo 1100624 1651979 := bstep (se 1 (by rfl) ⟨1238984, by rfl⟩ : syracuseStep 1651979 = 2477969) B2477969
theorem B1651991 : Blo 1100624 1651991 := bstep (se 1 (by rfl) ⟨1238993, by rfl⟩ : syracuseStep 1651991 = 2477987) B2477987
theorem B3716441 : Blo 1100624 3716441 := bstep (se 2 (by rfl) ⟨1393665, by rfl⟩ : syracuseStep 3716441 = 2787331) B2787331
theorem B1652057 : Blo 1100624 1652057 := bstep (se 2 (by rfl) ⟨619521, by rfl⟩ : syracuseStep 1652057 = 1239043) B1239043
theorem B1652171 : Blo 1100624 1652171 := bstep (se 1 (by rfl) ⟨1239128, by rfl⟩ : syracuseStep 1652171 = 2478257) B2478257
theorem B1652183 : Blo 1100624 1652183 := bstep (se 1 (by rfl) ⟨1239137, by rfl⟩ : syracuseStep 1652183 = 2478275) B2478275
theorem B1652249 : Blo 1100624 1652249 := bstep (se 2 (by rfl) ⟨619593, by rfl⟩ : syracuseStep 1652249 = 1239187) B1239187
theorem B3978803 : Blo 1100624 3978803 := bstep (se 1 (by rfl) ⟨2984102, by rfl⟩ : syracuseStep 3978803 = 5968205) B5968205
theorem B9418315 : Blo 1100624 9418315 := bstep (se 1 (by rfl) ⟨7063736, by rfl⟩ : syracuseStep 9418315 = 14127473) B14127473
theorem B1652363 : Blo 1100624 1652363 := bstep (se 1 (by rfl) ⟨1239272, by rfl⟩ : syracuseStep 1652363 = 2478545) B2478545
theorem B1652375 : Blo 1100624 1652375 := bstep (se 1 (by rfl) ⟨1239281, by rfl⟩ : syracuseStep 1652375 = 2478563) B2478563
theorem B1652441 : Blo 1100624 1652441 := bstep (se 2 (by rfl) ⟨619665, by rfl⟩ : syracuseStep 1652441 = 1239331) B1239331
theorem B1652555 : Blo 1100624 1652555 := bstep (se 1 (by rfl) ⟨1239416, by rfl⟩ : syracuseStep 1652555 = 2478833) B2478833
theorem B1652567 : Blo 1100624 1652567 := bstep (se 1 (by rfl) ⟨1239425, by rfl⟩ : syracuseStep 1652567 = 2478851) B2478851
theorem B9418589 : Blo 1100624 9418589 := bstep (se 3 (by rfl) ⟨1765985, by rfl⟩ : syracuseStep 9418589 = 3531971) B3531971
theorem B13416293 : Blo 1100624 13416293 := bstep (se 4 (by rfl) ⟨1257777, by rfl⟩ : syracuseStep 13416293 = 2515555) B2515555
theorem B4470673 : Blo 1100624 4470673 := bstep (se 2 (by rfl) ⟨1676502, by rfl⟩ : syracuseStep 4470673 = 3353005) B3353005
theorem B1652633 : Blo 1100624 1652633 := bstep (se 2 (by rfl) ⟨619737, by rfl⟩ : syracuseStep 1652633 = 1239475) B1239475
theorem B1652747 : Blo 1100624 1652747 := bstep (se 1 (by rfl) ⟨1239560, by rfl⟩ : syracuseStep 1652747 = 2479121) B2479121
theorem B3717143 : Blo 1100624 3717143 := bstep (se 1 (by rfl) ⟨2787857, by rfl⟩ : syracuseStep 3717143 = 5575715) B5575715
theorem B1652759 : Blo 1100624 1652759 := bstep (se 1 (by rfl) ⟨1239569, by rfl⟩ : syracuseStep 1652759 = 2479139) B2479139
theorem B1325143 : Blo 1100624 1325143 := bstep (se 1 (by rfl) ⟨993857, by rfl⟩ : syracuseStep 1325143 = 1987715) B1987715
theorem B1652825 : Blo 1100624 1652825 := bstep (se 2 (by rfl) ⟨619809, by rfl⟩ : syracuseStep 1652825 = 1239619) B1239619
theorem B1652939 : Blo 1100624 1652939 := bstep (se 1 (by rfl) ⟨1239704, by rfl⟩ : syracuseStep 1652939 = 2479409) B2479409
theorem B14530765 : Blo 1100624 14530765 := bstep (se 3 (by rfl) ⟨2724518, by rfl⟩ : syracuseStep 14530765 = 5449037) B5449037
theorem B1652951 : Blo 1100624 1652951 := bstep (se 1 (by rfl) ⟨1239713, by rfl⟩ : syracuseStep 1652951 = 2479427) B2479427
theorem B1653017 : Blo 1100624 1653017 := bstep (se 2 (by rfl) ⟨619881, by rfl⟩ : syracuseStep 1653017 = 1239763) B1239763
theorem B1653131 : Blo 1100624 1653131 := bstep (se 1 (by rfl) ⟨1239848, by rfl⟩ : syracuseStep 1653131 = 2479697) B2479697
theorem B1653143 : Blo 1100624 1653143 := bstep (se 1 (by rfl) ⟨1239857, by rfl⟩ : syracuseStep 1653143 = 2479715) B2479715
theorem B1325527 : Blo 1100624 1325527 := bstep (se 1 (by rfl) ⟨994145, by rfl⟩ : syracuseStep 1325527 = 1988291) B1988291
theorem B1653209 : Blo 1100624 1653209 := bstep (se 2 (by rfl) ⟨619953, by rfl⟩ : syracuseStep 1653209 = 1239907) B1239907
theorem B4471319 : Blo 1100624 4471319 := bstep (se 1 (by rfl) ⟨3353489, by rfl⟩ : syracuseStep 4471319 = 6706979) B6706979
theorem B9812515 : Blo 1100624 9812515 := bstep (se 1 (by rfl) ⟨7359386, by rfl⟩ : syracuseStep 9812515 = 14718773) B14718773
theorem B3717683 : Blo 1100624 3717683 := bstep (se 1 (by rfl) ⟨2788262, by rfl⟩ : syracuseStep 3717683 = 5576525) B5576525
theorem B1653323 : Blo 1100624 1653323 := bstep (se 1 (by rfl) ⟨1239992, by rfl⟩ : syracuseStep 1653323 = 2479985) B2479985
theorem B1653335 : Blo 1100624 1653335 := bstep (se 1 (by rfl) ⟨1240001, by rfl⟩ : syracuseStep 1653335 = 2480003) B2480003
theorem B10074775 : Blo 1100624 10074775 := bstep (se 1 (by rfl) ⟨7556081, by rfl⟩ : syracuseStep 10074775 = 15112163) B15112163
theorem B1653401 : Blo 1100624 1653401 := bstep (se 2 (by rfl) ⟨620025, by rfl⟩ : syracuseStep 1653401 = 1240051) B1240051
theorem B10730189 : Blo 1100624 10730189 := bstep (se 3 (by rfl) ⟨2011910, by rfl⟩ : syracuseStep 10730189 = 4023821) B4023821
theorem B1653515 : Blo 1100624 1653515 := bstep (se 1 (by rfl) ⟨1240136, by rfl⟩ : syracuseStep 1653515 = 2480273) B2480273
theorem B1653527 : Blo 1100624 1653527 := bstep (se 1 (by rfl) ⟨1240145, by rfl⟩ : syracuseStep 1653527 = 2480291) B2480291
theorem B3717953 : Blo 1100624 3717953 := bstep (se 2 (by rfl) ⟨1394232, by rfl⟩ : syracuseStep 3717953 = 2788465) B2788465
theorem B1653593 : Blo 1100624 1653593 := bstep (se 2 (by rfl) ⟨620097, by rfl⟩ : syracuseStep 1653593 = 1240195) B1240195
theorem B7060355 : Blo 1100624 7060355 := bstep (se 1 (by rfl) ⟨5295266, by rfl⟩ : syracuseStep 7060355 = 10590533) B10590533
theorem B7945091 : Blo 1100624 7945091 := bstep (se 1 (by rfl) ⟨5958818, by rfl⟩ : syracuseStep 7945091 = 11917637) B11917637
theorem B9419651 : Blo 1100624 9419651 := bstep (se 1 (by rfl) ⟨7064738, by rfl⟩ : syracuseStep 9419651 = 14129477) B14129477
theorem B81476549 : Blo 1100624 81476549 := bstep (se 4 (by rfl) ⟨7638426, by rfl⟩ : syracuseStep 81476549 = 15276853) B15276853
theorem B1653707 : Blo 1100624 1653707 := bstep (se 1 (by rfl) ⟨1240280, by rfl⟩ : syracuseStep 1653707 = 2480561) B2480561
theorem B1653719 : Blo 1100624 1653719 := bstep (se 1 (by rfl) ⟨1240289, by rfl⟩ : syracuseStep 1653719 = 2480579) B2480579
theorem B1653785 : Blo 1100624 1653785 := bstep (se 2 (by rfl) ⟨620169, by rfl⟩ : syracuseStep 1653785 = 1240339) B1240339
theorem B1653899 : Blo 1100624 1653899 := bstep (se 1 (by rfl) ⟨1240424, by rfl⟩ : syracuseStep 1653899 = 2480849) B2480849
theorem B1653911 : Blo 1100624 1653911 := bstep (se 1 (by rfl) ⟨1240433, by rfl⟩ : syracuseStep 1653911 = 2480867) B2480867
theorem B5029067 : Blo 1100624 5029067 := bstep (se 1 (by rfl) ⟨3771800, by rfl⟩ : syracuseStep 5029067 = 7543601) B7543601
theorem B1653977 : Blo 1100624 1653977 := bstep (se 2 (by rfl) ⟨620241, by rfl⟩ : syracuseStep 1653977 = 1240483) B1240483
theorem B1654091 : Blo 1100624 1654091 := bstep (se 1 (by rfl) ⟨1240568, by rfl⟩ : syracuseStep 1654091 = 2481137) B2481137
theorem B1654103 : Blo 1100624 1654103 := bstep (se 1 (by rfl) ⟨1240577, by rfl⟩ : syracuseStep 1654103 = 2481155) B2481155
theorem B3718493 : Blo 1100624 3718493 := bstep (se 3 (by rfl) ⟨697217, by rfl⟩ : syracuseStep 3718493 = 1394435) B1394435
theorem B1654169 : Blo 1100624 1654169 := bstep (se 2 (by rfl) ⟨620313, by rfl⟩ : syracuseStep 1654169 = 1240627) B1240627
theorem B1654283 : Blo 1100624 1654283 := bstep (se 1 (by rfl) ⟨1240712, by rfl⟩ : syracuseStep 1654283 = 2481425) B2481425
theorem B1654295 : Blo 1100624 1654295 := bstep (se 1 (by rfl) ⟨1240721, by rfl⟩ : syracuseStep 1654295 = 2481443) B2481443
theorem B1654361 : Blo 1100624 1654361 := bstep (se 2 (by rfl) ⟨620385, by rfl⟩ : syracuseStep 1654361 = 1240771) B1240771
theorem B38125187 : Blo 1100624 38125187 := bstep (se 1 (by rfl) ⟨28593890, by rfl⟩ : syracuseStep 38125187 = 57187781) B57187781
theorem B1654475 : Blo 1100624 1654475 := bstep (se 1 (by rfl) ⟨1240856, by rfl⟩ : syracuseStep 1654475 = 2481713) B2481713
theorem B1654487 : Blo 1100624 1654487 := bstep (se 1 (by rfl) ⟨1240865, by rfl⟩ : syracuseStep 1654487 = 2481731) B2481731
theorem B1654553 : Blo 1100624 1654553 := bstep (se 2 (by rfl) ⟨620457, by rfl⟩ : syracuseStep 1654553 = 1240915) B1240915
theorem B1654667 : Blo 1100624 1654667 := bstep (se 1 (by rfl) ⟨1241000, by rfl⟩ : syracuseStep 1654667 = 2482001) B2482001
theorem B1654679 : Blo 1100624 1654679 := bstep (se 1 (by rfl) ⟨1241009, by rfl⟩ : syracuseStep 1654679 = 2482019) B2482019
theorem B1654745 : Blo 1100624 1654745 := bstep (se 2 (by rfl) ⟨620529, by rfl⟩ : syracuseStep 1654745 = 1241059) B1241059
theorem B1654859 : Blo 1100624 1654859 := bstep (se 1 (by rfl) ⟨1241144, by rfl⟩ : syracuseStep 1654859 = 2482289) B2482289
theorem B1654871 : Blo 1100624 1654871 := bstep (se 1 (by rfl) ⟨1241153, by rfl⟩ : syracuseStep 1654871 = 2482307) B2482307
theorem B1654937 : Blo 1100624 1654937 := bstep (se 2 (by rfl) ⟨620601, by rfl⟩ : syracuseStep 1654937 = 1241203) B1241203
theorem B11911373 : Blo 1100624 11911373 := bstep (se 3 (by rfl) ⟨2233382, by rfl⟩ : syracuseStep 11911373 = 4466765) B4466765
theorem B1655051 : Blo 1100624 1655051 := bstep (se 1 (by rfl) ⟨1241288, by rfl⟩ : syracuseStep 1655051 = 2482577) B2482577
theorem B5587217 : Blo 1100624 5587217 := bstep (se 2 (by rfl) ⟨2095206, by rfl⟩ : syracuseStep 5587217 = 4190413) B4190413
theorem B1655063 : Blo 1100624 1655063 := bstep (se 1 (by rfl) ⟨1241297, by rfl⟩ : syracuseStep 1655063 = 2482595) B2482595
theorem B4702529 : Blo 1100624 4702529 := bstep (se 2 (by rfl) ⟨1763448, by rfl⟩ : syracuseStep 4702529 = 3526897) B3526897
theorem B6275393 : Blo 1100624 6275393 := bstep (se 2 (by rfl) ⟨2353272, by rfl⟩ : syracuseStep 6275393 = 4706545) B4706545
theorem B1655129 : Blo 1100624 1655129 := bstep (se 2 (by rfl) ⟨620673, by rfl⟩ : syracuseStep 1655129 = 1241347) B1241347
theorem B5587379 : Blo 1100624 5587379 := bstep (se 1 (by rfl) ⟨4190534, by rfl⟩ : syracuseStep 5587379 = 8381069) B8381069
theorem B3719627 : Blo 1100624 3719627 := bstep (se 1 (by rfl) ⟨2789720, by rfl⟩ : syracuseStep 3719627 = 5579441) B5579441
theorem B1655243 : Blo 1100624 1655243 := bstep (se 1 (by rfl) ⟨1241432, by rfl⟩ : syracuseStep 1655243 = 2482865) B2482865
theorem B1655255 : Blo 1100624 1655255 := bstep (se 1 (by rfl) ⟨1241441, by rfl⟩ : syracuseStep 1655255 = 2482883) B2482883
theorem B1655321 : Blo 1100624 1655321 := bstep (se 2 (by rfl) ⟨620745, by rfl⟩ : syracuseStep 1655321 = 1241491) B1241491
theorem B4473395 : Blo 1100624 4473395 := bstep (se 1 (by rfl) ⟨3355046, by rfl⟩ : syracuseStep 4473395 = 6710093) B6710093
theorem B1393291 : Blo 1100624 1393291 := bstep (se 1 (by rfl) ⟨1044968, by rfl⟩ : syracuseStep 1393291 = 2089937) B2089937
theorem B1655435 : Blo 1100624 1655435 := bstep (se 1 (by rfl) ⟨1241576, by rfl⟩ : syracuseStep 1655435 = 2483153) B2483153
theorem B1655447 : Blo 1100624 1655447 := bstep (se 1 (by rfl) ⟨1241585, by rfl⟩ : syracuseStep 1655447 = 2483171) B2483171
theorem B3719897 : Blo 1100624 3719897 := bstep (se 2 (by rfl) ⟨1394961, by rfl⟩ : syracuseStep 3719897 = 2789923) B2789923
theorem B1655513 : Blo 1100624 1655513 := bstep (se 2 (by rfl) ⟨620817, by rfl⟩ : syracuseStep 1655513 = 1241635) B1241635
theorem B1655627 : Blo 1100624 1655627 := bstep (se 1 (by rfl) ⟨1241720, by rfl⟩ : syracuseStep 1655627 = 2483441) B2483441
theorem B1655639 : Blo 1100624 1655639 := bstep (se 1 (by rfl) ⟨1241729, by rfl⟩ : syracuseStep 1655639 = 2483459) B2483459
theorem B1655705 : Blo 1100624 1655705 := bstep (se 2 (by rfl) ⟨620889, by rfl⟩ : syracuseStep 1655705 = 1241779) B1241779
theorem B1655819 : Blo 1100624 1655819 := bstep (se 1 (by rfl) ⟨1241864, by rfl⟩ : syracuseStep 1655819 = 2483729) B2483729
theorem B1655831 : Blo 1100624 1655831 := bstep (se 1 (by rfl) ⟨1241873, by rfl⟩ : syracuseStep 1655831 = 2483747) B2483747
theorem B8373293 : Blo 1100624 8373293 := bstep (se 3 (by rfl) ⟨1569992, by rfl⟩ : syracuseStep 8373293 = 3139985) B3139985
theorem B1655897 : Blo 1100624 1655897 := bstep (se 2 (by rfl) ⟨620961, by rfl⟩ : syracuseStep 1655897 = 1241923) B1241923
theorem B5653597 : Blo 1100624 5653597 := bstep (se 3 (by rfl) ⟨1060049, by rfl⟩ : syracuseStep 5653597 = 2120099) B2120099
theorem B16794755 : Blo 1100624 16794755 := bstep (se 1 (by rfl) ⟨12596066, by rfl⟩ : syracuseStep 16794755 = 25192133) B25192133
theorem B1656011 : Blo 1100624 1656011 := bstep (se 1 (by rfl) ⟨1242008, by rfl⟩ : syracuseStep 1656011 = 2484017) B2484017
theorem B1656023 : Blo 1100624 1656023 := bstep (se 1 (by rfl) ⟨1242017, by rfl⟩ : syracuseStep 1656023 = 2484035) B2484035
theorem B4703453 : Blo 1100624 4703453 := bstep (se 3 (by rfl) ⟨881897, by rfl⟩ : syracuseStep 4703453 = 1763795) B1763795
theorem B1656089 : Blo 1100624 1656089 := bstep (se 2 (by rfl) ⟨621033, by rfl⟩ : syracuseStep 1656089 = 1242067) B1242067
theorem B1656203 : Blo 1100624 1656203 := bstep (se 1 (by rfl) ⟨1242152, by rfl⟩ : syracuseStep 1656203 = 2484305) B2484305
theorem B3720599 : Blo 1100624 3720599 := bstep (se 1 (by rfl) ⟨2790449, by rfl⟩ : syracuseStep 3720599 = 5580899) B5580899
theorem B1656215 : Blo 1100624 1656215 := bstep (se 1 (by rfl) ⟨1242161, by rfl⟩ : syracuseStep 1656215 = 2484323) B2484323
theorem B1656281 : Blo 1100624 1656281 := bstep (se 2 (by rfl) ⟨621105, by rfl⟩ : syracuseStep 1656281 = 1242211) B1242211
theorem B32261645 : Blo 1100624 32261645 := bstep (se 3 (by rfl) ⟨6049058, by rfl⟩ : syracuseStep 32261645 = 12098117) B12098117
theorem B1656395 : Blo 1100624 1656395 := bstep (se 1 (by rfl) ⟨1242296, by rfl⟩ : syracuseStep 1656395 = 2484593) B2484593
theorem B1394263 : Blo 1100624 1394263 := bstep (se 1 (by rfl) ⟨1045697, by rfl⟩ : syracuseStep 1394263 = 2091395) B2091395
theorem B1656407 : Blo 1100624 1656407 := bstep (se 1 (by rfl) ⟨1242305, by rfl⟩ : syracuseStep 1656407 = 2484611) B2484611
theorem B1656473 : Blo 1100624 1656473 := bstep (se 2 (by rfl) ⟨621177, by rfl⟩ : syracuseStep 1656473 = 1242355) B1242355
theorem B1656587 : Blo 1100624 1656587 := bstep (se 1 (by rfl) ⟨1242440, by rfl⟩ : syracuseStep 1656587 = 2484881) B2484881
theorem B1656599 : Blo 1100624 1656599 := bstep (se 1 (by rfl) ⟨1242449, by rfl⟩ : syracuseStep 1656599 = 2484899) B2484899
theorem B1656665 : Blo 1100624 1656665 := bstep (se 2 (by rfl) ⟨621249, by rfl⟩ : syracuseStep 1656665 = 1242499) B1242499
theorem B3721139 : Blo 1100624 3721139 := bstep (se 1 (by rfl) ⟨2790854, by rfl⟩ : syracuseStep 3721139 = 5581709) B5581709
theorem B1656779 : Blo 1100624 1656779 := bstep (se 1 (by rfl) ⟨1242584, by rfl⟩ : syracuseStep 1656779 = 2485169) B2485169
theorem B1656791 : Blo 1100624 1656791 := bstep (se 1 (by rfl) ⟨1242593, by rfl⟩ : syracuseStep 1656791 = 2485187) B2485187
theorem B23840729 : Blo 1100624 23840729 := bstep (se 2 (by rfl) ⟨8940273, by rfl⟩ : syracuseStep 23840729 = 17880547) B17880547
theorem B1722379 : Blo 1100624 1722379 := bstep (se 1 (by rfl) ⟨1291784, by rfl⟩ : syracuseStep 1722379 = 2583569) B2583569
theorem B1656857 : Blo 1100624 1656857 := bstep (se 2 (by rfl) ⟨621321, by rfl⟩ : syracuseStep 1656857 = 1242643) B1242643
theorem B3721409 : Blo 1100624 3721409 := bstep (se 2 (by rfl) ⟨1395528, by rfl⟩ : syracuseStep 3721409 = 2791057) B2791057
theorem B5589323 : Blo 1100624 5589323 := bstep (se 1 (by rfl) ⟨4191992, by rfl⟩ : syracuseStep 5589323 = 8383985) B8383985
theorem B1395083 : Blo 1100624 1395083 := bstep (se 1 (by rfl) ⟨1046312, by rfl⟩ : syracuseStep 1395083 = 2092625) B2092625
theorem B2476439 : Blo 1100624 2476439 := bstep (se 1 (by rfl) ⟨1857329, by rfl⟩ : syracuseStep 2476439 = 3714659) B3714659
theorem B2476619 : Blo 1100624 2476619 := bstep (se 1 (by rfl) ⟨1857464, by rfl⟩ : syracuseStep 2476619 = 3714929) B3714929
theorem B2476673 : Blo 1100624 2476673 := bstep (se 2 (by rfl) ⟨928752, by rfl⟩ : syracuseStep 2476673 = 1857505) B1857505
theorem B8931971 : Blo 1100624 8931971 := bstep (se 1 (by rfl) ⟨6698978, by rfl⟩ : syracuseStep 8931971 = 13397957) B13397957
theorem B6277783 : Blo 1100624 6277783 := bstep (se 1 (by rfl) ⟨4708337, by rfl⟩ : syracuseStep 6277783 = 9416675) B9416675
theorem B1886935 : Blo 1100624 1886935 := bstep (se 1 (by rfl) ⟨1415201, by rfl⟩ : syracuseStep 1886935 = 2830403) B2830403
theorem B3721949 : Blo 1100624 3721949 := bstep (se 3 (by rfl) ⟨697865, by rfl⟩ : syracuseStep 3721949 = 1395731) B1395731
theorem B1100631 : Blo 1100624 1100631 := bstep (se 1 (by rfl) ⟨825473, by rfl⟩ : syracuseStep 1100631 = 1650947) B1650947
theorem B2476889 : Blo 1100624 2476889 := bstep (se 2 (by rfl) ⟨928833, by rfl⟩ : syracuseStep 2476889 = 1857667) B1857667
theorem B1100651 : Blo 1100624 1100651 := bstep (se 1 (by rfl) ⟨825488, by rfl⟩ : syracuseStep 1100651 = 1650977) B1650977
theorem B1100663 : Blo 1100624 1100663 := bstep (se 1 (by rfl) ⟨825497, by rfl⟩ : syracuseStep 1100663 = 1650995) B1650995
theorem B1100683 : Blo 1100624 1100683 := bstep (se 1 (by rfl) ⟨825512, by rfl⟩ : syracuseStep 1100683 = 1651025) B1651025
theorem B1100695 : Blo 1100624 1100695 := bstep (se 1 (by rfl) ⟨825521, by rfl⟩ : syracuseStep 1100695 = 1651043) B1651043
theorem B1100715 : Blo 1100624 1100715 := bstep (se 1 (by rfl) ⟨825536, by rfl⟩ : syracuseStep 1100715 = 1651073) B1651073
theorem B2476979 : Blo 1100624 2476979 := bstep (se 1 (by rfl) ⟨1857734, by rfl⟩ : syracuseStep 2476979 = 3715469) B3715469
theorem B1100727 : Blo 1100624 1100727 := bstep (se 1 (by rfl) ⟨825545, by rfl⟩ : syracuseStep 1100727 = 1651091) B1651091
theorem B1100747 : Blo 1100624 1100747 := bstep (se 1 (by rfl) ⟨825560, by rfl⟩ : syracuseStep 1100747 = 1651121) B1651121
theorem B1100759 : Blo 1100624 1100759 := bstep (se 1 (by rfl) ⟨825569, by rfl⟩ : syracuseStep 1100759 = 1651139) B1651139
theorem B2477015 : Blo 1100624 2477015 := bstep (se 1 (by rfl) ⟨1857761, by rfl⟩ : syracuseStep 2477015 = 3715523) B3715523
theorem B1100779 : Blo 1100624 1100779 := bstep (se 1 (by rfl) ⟨825584, by rfl⟩ : syracuseStep 1100779 = 1651169) B1651169
theorem B1100791 : Blo 1100624 1100791 := bstep (se 1 (by rfl) ⟨825593, by rfl⟩ : syracuseStep 1100791 = 1651187) B1651187
theorem B1100811 : Blo 1100624 1100811 := bstep (se 1 (by rfl) ⟨825608, by rfl⟩ : syracuseStep 1100811 = 1651217) B1651217
theorem B1100823 : Blo 1100624 1100823 := bstep (se 1 (by rfl) ⟨825617, by rfl⟩ : syracuseStep 1100823 = 1651235) B1651235
theorem B1100843 : Blo 1100624 1100843 := bstep (se 1 (by rfl) ⟨825632, by rfl⟩ : syracuseStep 1100843 = 1651265) B1651265
theorem B1100855 : Blo 1100624 1100855 := bstep (se 1 (by rfl) ⟨825641, by rfl⟩ : syracuseStep 1100855 = 1651283) B1651283
theorem B1100875 : Blo 1100624 1100875 := bstep (se 1 (by rfl) ⟨825656, by rfl⟩ : syracuseStep 1100875 = 1651313) B1651313
theorem B1395787 : Blo 1100624 1395787 := bstep (se 1 (by rfl) ⟨1046840, by rfl⟩ : syracuseStep 1395787 = 2093681) B2093681
theorem B1100887 : Blo 1100624 1100887 := bstep (se 1 (by rfl) ⟨825665, by rfl⟩ : syracuseStep 1100887 = 1651331) B1651331
theorem B1100907 : Blo 1100624 1100907 := bstep (se 1 (by rfl) ⟨825680, by rfl⟩ : syracuseStep 1100907 = 1651361) B1651361
theorem B1100919 : Blo 1100624 1100919 := bstep (se 1 (by rfl) ⟨825689, by rfl⟩ : syracuseStep 1100919 = 1651379) B1651379
theorem B1100939 : Blo 1100624 1100939 := bstep (se 1 (by rfl) ⟨825704, by rfl⟩ : syracuseStep 1100939 = 1651409) B1651409
theorem B2477195 : Blo 1100624 2477195 := bstep (se 1 (by rfl) ⟨1857896, by rfl⟩ : syracuseStep 2477195 = 3715793) B3715793
theorem B1100951 : Blo 1100624 1100951 := bstep (se 1 (by rfl) ⟨825713, by rfl⟩ : syracuseStep 1100951 = 1651427) B1651427
theorem B1100971 : Blo 1100624 1100971 := bstep (se 1 (by rfl) ⟨825728, by rfl⟩ : syracuseStep 1100971 = 1651457) B1651457
theorem B4181165 : Blo 1100624 4181165 := bstep (se 3 (by rfl) ⟨783968, by rfl⟩ : syracuseStep 4181165 = 1567937) B1567937
theorem B1100983 : Blo 1100624 1100983 := bstep (se 1 (by rfl) ⟨825737, by rfl⟩ : syracuseStep 1100983 = 1651475) B1651475
theorem B2477249 : Blo 1100624 2477249 := bstep (se 2 (by rfl) ⟨928968, by rfl⟩ : syracuseStep 2477249 = 1857937) B1857937
theorem B1101003 : Blo 1100624 1101003 := bstep (se 1 (by rfl) ⟨825752, by rfl⟩ : syracuseStep 1101003 = 1651505) B1651505
theorem B1101015 : Blo 1100624 1101015 := bstep (se 1 (by rfl) ⟨825761, by rfl⟩ : syracuseStep 1101015 = 1651523) B1651523
theorem B1101035 : Blo 1100624 1101035 := bstep (se 1 (by rfl) ⟨825776, by rfl⟩ : syracuseStep 1101035 = 1651553) B1651553
theorem B1101047 : Blo 1100624 1101047 := bstep (se 1 (by rfl) ⟨825785, by rfl⟩ : syracuseStep 1101047 = 1651571) B1651571
theorem B1101067 : Blo 1100624 1101067 := bstep (se 1 (by rfl) ⟨825800, by rfl⟩ : syracuseStep 1101067 = 1651601) B1651601
theorem B1101079 : Blo 1100624 1101079 := bstep (se 1 (by rfl) ⟨825809, by rfl⟩ : syracuseStep 1101079 = 1651619) B1651619
theorem B1101099 : Blo 1100624 1101099 := bstep (se 1 (by rfl) ⟨825824, by rfl⟩ : syracuseStep 1101099 = 1651649) B1651649
theorem B1101111 : Blo 1100624 1101111 := bstep (se 1 (by rfl) ⟨825833, by rfl⟩ : syracuseStep 1101111 = 1651667) B1651667
theorem B1101131 : Blo 1100624 1101131 := bstep (se 1 (by rfl) ⟨825848, by rfl⟩ : syracuseStep 1101131 = 1651697) B1651697
theorem B1101143 : Blo 1100624 1101143 := bstep (se 1 (by rfl) ⟨825857, by rfl⟩ : syracuseStep 1101143 = 1651715) B1651715
theorem B1396055 : Blo 1100624 1396055 := bstep (se 1 (by rfl) ⟨1047041, by rfl⟩ : syracuseStep 1396055 = 2094083) B2094083
theorem B1101163 : Blo 1100624 1101163 := bstep (se 1 (by rfl) ⟨825872, by rfl⟩ : syracuseStep 1101163 = 1651745) B1651745
theorem B1101175 : Blo 1100624 1101175 := bstep (se 1 (by rfl) ⟨825881, by rfl⟩ : syracuseStep 1101175 = 1651763) B1651763
theorem B1101195 : Blo 1100624 1101195 := bstep (se 1 (by rfl) ⟨825896, by rfl⟩ : syracuseStep 1101195 = 1651793) B1651793
theorem B1101207 : Blo 1100624 1101207 := bstep (se 1 (by rfl) ⟨825905, by rfl⟩ : syracuseStep 1101207 = 1651811) B1651811
theorem B2477465 : Blo 1100624 2477465 := bstep (se 2 (by rfl) ⟨929049, by rfl⟩ : syracuseStep 2477465 = 1858099) B1858099
theorem B1101227 : Blo 1100624 1101227 := bstep (se 1 (by rfl) ⟨825920, by rfl⟩ : syracuseStep 1101227 = 1651841) B1651841
theorem B1101239 : Blo 1100624 1101239 := bstep (se 1 (by rfl) ⟨825929, by rfl⟩ : syracuseStep 1101239 = 1651859) B1651859
theorem B1101259 : Blo 1100624 1101259 := bstep (se 1 (by rfl) ⟨825944, by rfl⟩ : syracuseStep 1101259 = 1651889) B1651889
theorem B1101271 : Blo 1100624 1101271 := bstep (se 1 (by rfl) ⟨825953, by rfl⟩ : syracuseStep 1101271 = 1651907) B1651907
theorem B1101291 : Blo 1100624 1101291 := bstep (se 1 (by rfl) ⟨825968, by rfl⟩ : syracuseStep 1101291 = 1651937) B1651937
theorem B2477555 : Blo 1100624 2477555 := bstep (se 1 (by rfl) ⟨1858166, by rfl⟩ : syracuseStep 2477555 = 3716333) B3716333
theorem B1101303 : Blo 1100624 1101303 := bstep (se 1 (by rfl) ⟨825977, by rfl⟩ : syracuseStep 1101303 = 1651955) B1651955
theorem B4771331 : Blo 1100624 4771331 := bstep (se 1 (by rfl) ⟨3578498, by rfl⟩ : syracuseStep 4771331 = 7156997) B7156997
theorem B1101323 : Blo 1100624 1101323 := bstep (se 1 (by rfl) ⟨825992, by rfl⟩ : syracuseStep 1101323 = 1651985) B1651985
theorem B2477591 : Blo 1100624 2477591 := bstep (se 1 (by rfl) ⟨1858193, by rfl⟩ : syracuseStep 2477591 = 3716387) B3716387
theorem B1101335 : Blo 1100624 1101335 := bstep (se 1 (by rfl) ⟨826001, by rfl⟩ : syracuseStep 1101335 = 1652003) B1652003
theorem B1101355 : Blo 1100624 1101355 := bstep (se 1 (by rfl) ⟨826016, by rfl⟩ : syracuseStep 1101355 = 1652033) B1652033
theorem B1101367 : Blo 1100624 1101367 := bstep (se 1 (by rfl) ⟨826025, by rfl⟩ : syracuseStep 1101367 = 1652051) B1652051
theorem B1101387 : Blo 1100624 1101387 := bstep (se 1 (by rfl) ⟨826040, by rfl⟩ : syracuseStep 1101387 = 1652081) B1652081
theorem B1101399 : Blo 1100624 1101399 := bstep (se 1 (by rfl) ⟨826049, by rfl⟩ : syracuseStep 1101399 = 1652099) B1652099
theorem B1101419 : Blo 1100624 1101419 := bstep (se 1 (by rfl) ⟨826064, by rfl⟩ : syracuseStep 1101419 = 1652129) B1652129
theorem B1101431 : Blo 1100624 1101431 := bstep (se 1 (by rfl) ⟨826073, by rfl⟩ : syracuseStep 1101431 = 1652147) B1652147
theorem B1101451 : Blo 1100624 1101451 := bstep (se 1 (by rfl) ⟨826088, by rfl⟩ : syracuseStep 1101451 = 1652177) B1652177
theorem B1101463 : Blo 1100624 1101463 := bstep (se 1 (by rfl) ⟨826097, by rfl⟩ : syracuseStep 1101463 = 1652195) B1652195
theorem B1101483 : Blo 1100624 1101483 := bstep (se 1 (by rfl) ⟨826112, by rfl⟩ : syracuseStep 1101483 = 1652225) B1652225
theorem B6704819 : Blo 1100624 6704819 := bstep (se 1 (by rfl) ⟨5028614, by rfl⟩ : syracuseStep 6704819 = 10057229) B10057229
theorem B3985075 : Blo 1100624 3985075 := bstep (se 1 (by rfl) ⟨2988806, by rfl⟩ : syracuseStep 3985075 = 5977613) B5977613
theorem B1101495 : Blo 1100624 1101495 := bstep (se 1 (by rfl) ⟨826121, by rfl⟩ : syracuseStep 1101495 = 1652243) B1652243
theorem B2477771 : Blo 1100624 2477771 := bstep (se 1 (by rfl) ⟨1858328, by rfl⟩ : syracuseStep 2477771 = 3716657) B3716657
theorem B1101515 : Blo 1100624 1101515 := bstep (se 1 (by rfl) ⟨826136, by rfl⟩ : syracuseStep 1101515 = 1652273) B1652273
theorem B1101527 : Blo 1100624 1101527 := bstep (se 1 (by rfl) ⟨826145, by rfl⟩ : syracuseStep 1101527 = 1652291) B1652291
theorem B1101547 : Blo 1100624 1101547 := bstep (se 1 (by rfl) ⟨826160, by rfl⟩ : syracuseStep 1101547 = 1652321) B1652321
theorem B1101559 : Blo 1100624 1101559 := bstep (se 1 (by rfl) ⟨826169, by rfl⟩ : syracuseStep 1101559 = 1652339) B1652339
theorem B2477825 : Blo 1100624 2477825 := bstep (se 2 (by rfl) ⟨929184, by rfl⟩ : syracuseStep 2477825 = 1858369) B1858369
theorem B1101579 : Blo 1100624 1101579 := bstep (se 1 (by rfl) ⟨826184, by rfl⟩ : syracuseStep 1101579 = 1652369) B1652369
theorem B1101591 : Blo 1100624 1101591 := bstep (se 1 (by rfl) ⟨826193, by rfl⟩ : syracuseStep 1101591 = 1652387) B1652387
theorem B1101611 : Blo 1100624 1101611 := bstep (se 1 (by rfl) ⟨826208, by rfl⟩ : syracuseStep 1101611 = 1652417) B1652417
theorem B1101623 : Blo 1100624 1101623 := bstep (se 1 (by rfl) ⟨826217, by rfl⟩ : syracuseStep 1101623 = 1652435) B1652435
theorem B1101643 : Blo 1100624 1101643 := bstep (se 1 (by rfl) ⟨826232, by rfl⟩ : syracuseStep 1101643 = 1652465) B1652465
theorem B3723083 : Blo 1100624 3723083 := bstep (se 1 (by rfl) ⟨2792312, by rfl⟩ : syracuseStep 3723083 = 5584625) B5584625
theorem B1101655 : Blo 1100624 1101655 := bstep (se 1 (by rfl) ⟨826241, by rfl⟩ : syracuseStep 1101655 = 1652483) B1652483
theorem B1101675 : Blo 1100624 1101675 := bstep (se 1 (by rfl) ⟨826256, by rfl⟩ : syracuseStep 1101675 = 1652513) B1652513
theorem B1101687 : Blo 1100624 1101687 := bstep (se 1 (by rfl) ⟨826265, by rfl⟩ : syracuseStep 1101687 = 1652531) B1652531
theorem B1101707 : Blo 1100624 1101707 := bstep (se 1 (by rfl) ⟨826280, by rfl⟩ : syracuseStep 1101707 = 1652561) B1652561
theorem B1101719 : Blo 1100624 1101719 := bstep (se 1 (by rfl) ⟨826289, by rfl⟩ : syracuseStep 1101719 = 1652579) B1652579
theorem B1101739 : Blo 1100624 1101739 := bstep (se 1 (by rfl) ⟨826304, by rfl⟩ : syracuseStep 1101739 = 1652609) B1652609
theorem B4181939 : Blo 1100624 4181939 := bstep (se 1 (by rfl) ⟨3136454, by rfl⟩ : syracuseStep 4181939 = 6272909) B6272909
theorem B1101751 : Blo 1100624 1101751 := bstep (se 1 (by rfl) ⟨826313, by rfl⟩ : syracuseStep 1101751 = 1652627) B1652627
theorem B1101771 : Blo 1100624 1101771 := bstep (se 1 (by rfl) ⟨826328, by rfl⟩ : syracuseStep 1101771 = 1652657) B1652657
theorem B1101783 : Blo 1100624 1101783 := bstep (se 1 (by rfl) ⟨826337, by rfl⟩ : syracuseStep 1101783 = 1652675) B1652675
theorem B2478041 : Blo 1100624 2478041 := bstep (se 2 (by rfl) ⟨929265, by rfl⟩ : syracuseStep 2478041 = 1858531) B1858531
theorem B1101803 : Blo 1100624 1101803 := bstep (se 1 (by rfl) ⟨826352, by rfl⟩ : syracuseStep 1101803 = 1652705) B1652705
theorem B1101815 : Blo 1100624 1101815 := bstep (se 1 (by rfl) ⟨826361, by rfl⟩ : syracuseStep 1101815 = 1652723) B1652723
theorem B1101835 : Blo 1100624 1101835 := bstep (se 1 (by rfl) ⟨826376, by rfl⟩ : syracuseStep 1101835 = 1652753) B1652753
theorem B1101847 : Blo 1100624 1101847 := bstep (se 1 (by rfl) ⟨826385, by rfl⟩ : syracuseStep 1101847 = 1652771) B1652771
theorem B1396759 : Blo 1100624 1396759 := bstep (se 1 (by rfl) ⟨1047569, by rfl⟩ : syracuseStep 1396759 = 2095139) B2095139
theorem B1101867 : Blo 1100624 1101867 := bstep (se 1 (by rfl) ⟨826400, by rfl⟩ : syracuseStep 1101867 = 1652801) B1652801
theorem B2478131 : Blo 1100624 2478131 := bstep (se 1 (by rfl) ⟨1858598, by rfl⟩ : syracuseStep 2478131 = 3717197) B3717197
theorem B1101879 : Blo 1100624 1101879 := bstep (se 1 (by rfl) ⟨826409, by rfl⟩ : syracuseStep 1101879 = 1652819) B1652819
theorem B5591105 : Blo 1100624 5591105 := bstep (se 2 (by rfl) ⟨2096664, by rfl⟩ : syracuseStep 5591105 = 4193329) B4193329
theorem B1101899 : Blo 1100624 1101899 := bstep (se 1 (by rfl) ⟨826424, by rfl⟩ : syracuseStep 1101899 = 1652849) B1652849
theorem B2478167 : Blo 1100624 2478167 := bstep (se 1 (by rfl) ⟨1858625, by rfl⟩ : syracuseStep 2478167 = 3717251) B3717251
theorem B1101911 : Blo 1100624 1101911 := bstep (se 1 (by rfl) ⟨826433, by rfl⟩ : syracuseStep 1101911 = 1652867) B1652867
theorem B3723353 : Blo 1100624 3723353 := bstep (se 2 (by rfl) ⟨1396257, by rfl⟩ : syracuseStep 3723353 = 2792515) B2792515
theorem B1101931 : Blo 1100624 1101931 := bstep (se 1 (by rfl) ⟨826448, by rfl⟩ : syracuseStep 1101931 = 1652897) B1652897
theorem B1101943 : Blo 1100624 1101943 := bstep (se 1 (by rfl) ⟨826457, by rfl⟩ : syracuseStep 1101943 = 1652915) B1652915
theorem B1101963 : Blo 1100624 1101963 := bstep (se 1 (by rfl) ⟨826472, by rfl⟩ : syracuseStep 1101963 = 1652945) B1652945
theorem B1101975 : Blo 1100624 1101975 := bstep (se 1 (by rfl) ⟨826481, by rfl⟩ : syracuseStep 1101975 = 1652963) B1652963
theorem B1101995 : Blo 1100624 1101995 := bstep (se 1 (by rfl) ⟨826496, by rfl⟩ : syracuseStep 1101995 = 1652993) B1652993
theorem B1102007 : Blo 1100624 1102007 := bstep (se 1 (by rfl) ⟨826505, by rfl⟩ : syracuseStep 1102007 = 1653011) B1653011
theorem B1134775 : Blo 1100624 1134775 := bstep (se 1 (by rfl) ⟨851081, by rfl⟩ : syracuseStep 1134775 = 1702163) B1702163
theorem B1102027 : Blo 1100624 1102027 := bstep (se 1 (by rfl) ⟨826520, by rfl⟩ : syracuseStep 1102027 = 1653041) B1653041
theorem B1102039 : Blo 1100624 1102039 := bstep (se 1 (by rfl) ⟨826529, by rfl⟩ : syracuseStep 1102039 = 1653059) B1653059
theorem B1102059 : Blo 1100624 1102059 := bstep (se 1 (by rfl) ⟨826544, by rfl⟩ : syracuseStep 1102059 = 1653089) B1653089
theorem B1102071 : Blo 1100624 1102071 := bstep (se 1 (by rfl) ⟨826553, by rfl⟩ : syracuseStep 1102071 = 1653107) B1653107
theorem B2478347 : Blo 1100624 2478347 := bstep (se 1 (by rfl) ⟨1858760, by rfl⟩ : syracuseStep 2478347 = 3717521) B3717521
theorem B1102091 : Blo 1100624 1102091 := bstep (se 1 (by rfl) ⟨826568, by rfl⟩ : syracuseStep 1102091 = 1653137) B1653137
theorem B1102103 : Blo 1100624 1102103 := bstep (se 1 (by rfl) ⟨826577, by rfl⟩ : syracuseStep 1102103 = 1653155) B1653155
theorem B1102123 : Blo 1100624 1102123 := bstep (se 1 (by rfl) ⟨826592, by rfl⟩ : syracuseStep 1102123 = 1653185) B1653185
theorem B1102135 : Blo 1100624 1102135 := bstep (se 1 (by rfl) ⟨826601, by rfl⟩ : syracuseStep 1102135 = 1653203) B1653203
theorem B2478401 : Blo 1100624 2478401 := bstep (se 2 (by rfl) ⟨929400, by rfl⟩ : syracuseStep 2478401 = 1858801) B1858801
theorem B1102155 : Blo 1100624 1102155 := bstep (se 1 (by rfl) ⟨826616, by rfl⟩ : syracuseStep 1102155 = 1653233) B1653233
theorem B1102167 : Blo 1100624 1102167 := bstep (se 1 (by rfl) ⟨826625, by rfl⟩ : syracuseStep 1102167 = 1653251) B1653251
theorem B1593689 : Blo 1100624 1593689 := bstep (se 2 (by rfl) ⟨597633, by rfl⟩ : syracuseStep 1593689 = 1195267) B1195267
theorem B1102187 : Blo 1100624 1102187 := bstep (se 1 (by rfl) ⟨826640, by rfl⟩ : syracuseStep 1102187 = 1653281) B1653281
theorem B1102199 : Blo 1100624 1102199 := bstep (se 1 (by rfl) ⟨826649, by rfl⟩ : syracuseStep 1102199 = 1653299) B1653299
theorem B1102219 : Blo 1100624 1102219 := bstep (se 1 (by rfl) ⟨826664, by rfl⟩ : syracuseStep 1102219 = 1653329) B1653329
theorem B1102231 : Blo 1100624 1102231 := bstep (se 1 (by rfl) ⟨826673, by rfl⟩ : syracuseStep 1102231 = 1653347) B1653347
theorem B1102251 : Blo 1100624 1102251 := bstep (se 1 (by rfl) ⟨826688, by rfl⟩ : syracuseStep 1102251 = 1653377) B1653377
theorem B1102263 : Blo 1100624 1102263 := bstep (se 1 (by rfl) ⟨826697, by rfl⟩ : syracuseStep 1102263 = 1653395) B1653395
theorem B1102283 : Blo 1100624 1102283 := bstep (se 1 (by rfl) ⟨826712, by rfl⟩ : syracuseStep 1102283 = 1653425) B1653425
theorem B1102295 : Blo 1100624 1102295 := bstep (se 1 (by rfl) ⟨826721, by rfl⟩ : syracuseStep 1102295 = 1653443) B1653443
theorem B1593815 : Blo 1100624 1593815 := bstep (se 1 (by rfl) ⟨1195361, by rfl⟩ : syracuseStep 1593815 = 2390723) B2390723
theorem B1102315 : Blo 1100624 1102315 := bstep (se 1 (by rfl) ⟨826736, by rfl⟩ : syracuseStep 1102315 = 1653473) B1653473
theorem B1102327 : Blo 1100624 1102327 := bstep (se 1 (by rfl) ⟨826745, by rfl⟩ : syracuseStep 1102327 = 1653491) B1653491
theorem B4706819 : Blo 1100624 4706819 := bstep (se 1 (by rfl) ⟨3530114, by rfl⟩ : syracuseStep 4706819 = 7060229) B7060229
theorem B1102347 : Blo 1100624 1102347 := bstep (se 1 (by rfl) ⟨826760, by rfl⟩ : syracuseStep 1102347 = 1653521) B1653521
theorem B1102359 : Blo 1100624 1102359 := bstep (se 1 (by rfl) ⟨826769, by rfl⟩ : syracuseStep 1102359 = 1653539) B1653539
theorem B2478617 : Blo 1100624 2478617 := bstep (se 2 (by rfl) ⟨929481, by rfl⟩ : syracuseStep 2478617 = 1858963) B1858963
theorem B1102379 : Blo 1100624 1102379 := bstep (se 1 (by rfl) ⟨826784, by rfl⟩ : syracuseStep 1102379 = 1653569) B1653569
theorem B1102391 : Blo 1100624 1102391 := bstep (se 1 (by rfl) ⟨826793, by rfl⟩ : syracuseStep 1102391 = 1653587) B1653587
theorem B1102411 : Blo 1100624 1102411 := bstep (se 1 (by rfl) ⟨826808, by rfl⟩ : syracuseStep 1102411 = 1653617) B1653617
theorem B1102423 : Blo 1100624 1102423 := bstep (se 1 (by rfl) ⟨826817, by rfl⟩ : syracuseStep 1102423 = 1653635) B1653635
theorem B11915869 : Blo 1100624 11915869 := bstep (se 3 (by rfl) ⟨2234225, by rfl⟩ : syracuseStep 11915869 = 4468451) B4468451
theorem B1102443 : Blo 1100624 1102443 := bstep (se 1 (by rfl) ⟨826832, by rfl⟩ : syracuseStep 1102443 = 1653665) B1653665
theorem B2478707 : Blo 1100624 2478707 := bstep (se 1 (by rfl) ⟨1859030, by rfl⟩ : syracuseStep 2478707 = 3718061) B3718061
theorem B1102455 : Blo 1100624 1102455 := bstep (se 1 (by rfl) ⟨826841, by rfl⟩ : syracuseStep 1102455 = 1653683) B1653683
theorem B1102475 : Blo 1100624 1102475 := bstep (se 1 (by rfl) ⟨826856, by rfl⟩ : syracuseStep 1102475 = 1653713) B1653713
theorem B2478743 : Blo 1100624 2478743 := bstep (se 1 (by rfl) ⟨1859057, by rfl⟩ : syracuseStep 2478743 = 3718115) B3718115
theorem B1102487 : Blo 1100624 1102487 := bstep (se 1 (by rfl) ⟨826865, by rfl⟩ : syracuseStep 1102487 = 1653731) B1653731
theorem B1102507 : Blo 1100624 1102507 := bstep (se 1 (by rfl) ⟨826880, by rfl⟩ : syracuseStep 1102507 = 1653761) B1653761
theorem B3527347 : Blo 1100624 3527347 := bstep (se 1 (by rfl) ⟨2645510, by rfl⟩ : syracuseStep 3527347 = 5291021) B5291021
theorem B1102519 : Blo 1100624 1102519 := bstep (se 1 (by rfl) ⟨826889, by rfl⟩ : syracuseStep 1102519 = 1653779) B1653779
theorem B1102539 : Blo 1100624 1102539 := bstep (se 1 (by rfl) ⟨826904, by rfl⟩ : syracuseStep 1102539 = 1653809) B1653809
theorem B1102551 : Blo 1100624 1102551 := bstep (se 1 (by rfl) ⟨826913, by rfl⟩ : syracuseStep 1102551 = 1653827) B1653827
theorem B1102571 : Blo 1100624 1102571 := bstep (se 1 (by rfl) ⟨826928, by rfl⟩ : syracuseStep 1102571 = 1653857) B1653857
theorem B1102583 : Blo 1100624 1102583 := bstep (se 1 (by rfl) ⟨826937, by rfl⟩ : syracuseStep 1102583 = 1653875) B1653875
theorem B1102603 : Blo 1100624 1102603 := bstep (se 1 (by rfl) ⟨826952, by rfl⟩ : syracuseStep 1102603 = 1653905) B1653905
theorem B3724055 : Blo 1100624 3724055 := bstep (se 1 (by rfl) ⟨2793041, by rfl⟩ : syracuseStep 3724055 = 5586083) B5586083
theorem B1102615 : Blo 1100624 1102615 := bstep (se 1 (by rfl) ⟨826961, by rfl⟩ : syracuseStep 1102615 = 1653923) B1653923
theorem B1102635 : Blo 1100624 1102635 := bstep (se 1 (by rfl) ⟨826976, by rfl⟩ : syracuseStep 1102635 = 1653953) B1653953
theorem B1102647 : Blo 1100624 1102647 := bstep (se 1 (by rfl) ⟨826985, by rfl⟩ : syracuseStep 1102647 = 1653971) B1653971
theorem B2478923 : Blo 1100624 2478923 := bstep (se 1 (by rfl) ⟨1859192, by rfl⟩ : syracuseStep 2478923 = 3718385) B3718385
theorem B1102667 : Blo 1100624 1102667 := bstep (se 1 (by rfl) ⟨827000, by rfl⟩ : syracuseStep 1102667 = 1654001) B1654001
theorem B1102679 : Blo 1100624 1102679 := bstep (se 1 (by rfl) ⟨827009, by rfl⟩ : syracuseStep 1102679 = 1654019) B1654019
theorem B3527513 : Blo 1100624 3527513 := bstep (se 2 (by rfl) ⟨1322817, by rfl⟩ : syracuseStep 3527513 = 2645635) B2645635
theorem B8377181 : Blo 1100624 8377181 := bstep (se 3 (by rfl) ⟨1570721, by rfl⟩ : syracuseStep 8377181 = 3141443) B3141443
theorem B1102699 : Blo 1100624 1102699 := bstep (se 1 (by rfl) ⟨827024, by rfl⟩ : syracuseStep 1102699 = 1654049) B1654049
theorem B1102711 : Blo 1100624 1102711 := bstep (se 1 (by rfl) ⟨827033, by rfl⟩ : syracuseStep 1102711 = 1654067) B1654067
theorem B2478977 : Blo 1100624 2478977 := bstep (se 2 (by rfl) ⟨929616, by rfl⟩ : syracuseStep 2478977 = 1859233) B1859233
theorem B1102731 : Blo 1100624 1102731 := bstep (se 1 (by rfl) ⟨827048, by rfl⟩ : syracuseStep 1102731 = 1654097) B1654097
theorem B1102743 : Blo 1100624 1102743 := bstep (se 1 (by rfl) ⟨827057, by rfl⟩ : syracuseStep 1102743 = 1654115) B1654115
theorem B1102763 : Blo 1100624 1102763 := bstep (se 1 (by rfl) ⟨827072, by rfl⟩ : syracuseStep 1102763 = 1654145) B1654145
theorem B5297075 : Blo 1100624 5297075 := bstep (se 1 (by rfl) ⟨3972806, by rfl⟩ : syracuseStep 5297075 = 7945613) B7945613
theorem B1102775 : Blo 1100624 1102775 := bstep (se 1 (by rfl) ⟨827081, by rfl⟩ : syracuseStep 1102775 = 1654163) B1654163
theorem B1102795 : Blo 1100624 1102795 := bstep (se 1 (by rfl) ⟨827096, by rfl⟩ : syracuseStep 1102795 = 1654193) B1654193
theorem B1102807 : Blo 1100624 1102807 := bstep (se 1 (by rfl) ⟨827105, by rfl⟩ : syracuseStep 1102807 = 1654211) B1654211
theorem B1102827 : Blo 1100624 1102827 := bstep (se 1 (by rfl) ⟨827120, by rfl⟩ : syracuseStep 1102827 = 1654241) B1654241
theorem B1987571 : Blo 1100624 1987571 := bstep (se 1 (by rfl) ⟨1490678, by rfl⟩ : syracuseStep 1987571 = 2981357) B2981357
theorem B1102839 : Blo 1100624 1102839 := bstep (se 1 (by rfl) ⟨827129, by rfl⟩ : syracuseStep 1102839 = 1654259) B1654259
theorem B1102859 : Blo 1100624 1102859 := bstep (se 1 (by rfl) ⟨827144, by rfl⟩ : syracuseStep 1102859 = 1654289) B1654289
theorem B1102871 : Blo 1100624 1102871 := bstep (se 1 (by rfl) ⟨827153, by rfl⟩ : syracuseStep 1102871 = 1654307) B1654307
theorem B1102891 : Blo 1100624 1102891 := bstep (se 1 (by rfl) ⟨827168, by rfl⟩ : syracuseStep 1102891 = 1654337) B1654337
theorem B1102903 : Blo 1100624 1102903 := bstep (se 1 (by rfl) ⟨827177, by rfl⟩ : syracuseStep 1102903 = 1654355) B1654355
theorem B1102923 : Blo 1100624 1102923 := bstep (se 1 (by rfl) ⟨827192, by rfl⟩ : syracuseStep 1102923 = 1654385) B1654385
theorem B1102935 : Blo 1100624 1102935 := bstep (se 1 (by rfl) ⟨827201, by rfl⟩ : syracuseStep 1102935 = 1654403) B1654403
theorem B2479193 : Blo 1100624 2479193 := bstep (se 2 (by rfl) ⟨929697, by rfl⟩ : syracuseStep 2479193 = 1859395) B1859395
theorem B1102955 : Blo 1100624 1102955 := bstep (se 1 (by rfl) ⟨827216, by rfl⟩ : syracuseStep 1102955 = 1654433) B1654433
theorem B1102967 : Blo 1100624 1102967 := bstep (se 1 (by rfl) ⟨827225, by rfl⟩ : syracuseStep 1102967 = 1654451) B1654451
theorem B1102987 : Blo 1100624 1102987 := bstep (se 1 (by rfl) ⟨827240, by rfl⟩ : syracuseStep 1102987 = 1654481) B1654481
theorem B1102999 : Blo 1100624 1102999 := bstep (se 1 (by rfl) ⟨827249, by rfl⟩ : syracuseStep 1102999 = 1654499) B1654499
theorem B1103019 : Blo 1100624 1103019 := bstep (se 1 (by rfl) ⟨827264, by rfl⟩ : syracuseStep 1103019 = 1654529) B1654529
theorem B2479283 : Blo 1100624 2479283 := bstep (se 1 (by rfl) ⟨1859462, by rfl⟩ : syracuseStep 2479283 = 3718925) B3718925
theorem B1103031 : Blo 1100624 1103031 := bstep (se 1 (by rfl) ⟨827273, by rfl⟩ : syracuseStep 1103031 = 1654547) B1654547
theorem B1103051 : Blo 1100624 1103051 := bstep (se 1 (by rfl) ⟨827288, by rfl⟩ : syracuseStep 1103051 = 1654577) B1654577
theorem B1987787 : Blo 1100624 1987787 := bstep (se 1 (by rfl) ⟨1490840, by rfl⟩ : syracuseStep 1987787 = 2981681) B2981681
theorem B2479319 : Blo 1100624 2479319 := bstep (se 1 (by rfl) ⟨1859489, by rfl⟩ : syracuseStep 2479319 = 3718979) B3718979
theorem B1103063 : Blo 1100624 1103063 := bstep (se 1 (by rfl) ⟨827297, by rfl⟩ : syracuseStep 1103063 = 1654595) B1654595
theorem B1103083 : Blo 1100624 1103083 := bstep (se 1 (by rfl) ⟨827312, by rfl⟩ : syracuseStep 1103083 = 1654625) B1654625
theorem B1103095 : Blo 1100624 1103095 := bstep (se 1 (by rfl) ⟨827321, by rfl⟩ : syracuseStep 1103095 = 1654643) B1654643
theorem B1103115 : Blo 1100624 1103115 := bstep (se 1 (by rfl) ⟨827336, by rfl⟩ : syracuseStep 1103115 = 1654673) B1654673
theorem B1103127 : Blo 1100624 1103127 := bstep (se 1 (by rfl) ⟨827345, by rfl⟩ : syracuseStep 1103127 = 1654691) B1654691
theorem B1103147 : Blo 1100624 1103147 := bstep (se 1 (by rfl) ⟨827360, by rfl⟩ : syracuseStep 1103147 = 1654721) B1654721
theorem B3724595 : Blo 1100624 3724595 := bstep (se 1 (by rfl) ⟨2793446, by rfl⟩ : syracuseStep 3724595 = 5586893) B5586893
theorem B1103159 : Blo 1100624 1103159 := bstep (se 1 (by rfl) ⟨827369, by rfl⟩ : syracuseStep 1103159 = 1654739) B1654739
theorem B1103179 : Blo 1100624 1103179 := bstep (se 1 (by rfl) ⟨827384, by rfl⟩ : syracuseStep 1103179 = 1654769) B1654769
theorem B1103191 : Blo 1100624 1103191 := bstep (se 1 (by rfl) ⟨827393, by rfl⟩ : syracuseStep 1103191 = 1654787) B1654787
theorem B1103211 : Blo 1100624 1103211 := bstep (se 1 (by rfl) ⟨827408, by rfl⟩ : syracuseStep 1103211 = 1654817) B1654817
theorem B1103223 : Blo 1100624 1103223 := bstep (se 1 (by rfl) ⟨827417, by rfl⟩ : syracuseStep 1103223 = 1654835) B1654835
theorem B4183427 : Blo 1100624 4183427 := bstep (se 1 (by rfl) ⟨3137570, by rfl⟩ : syracuseStep 4183427 = 6275141) B6275141
theorem B2479499 : Blo 1100624 2479499 := bstep (se 1 (by rfl) ⟨1859624, by rfl⟩ : syracuseStep 2479499 = 3719249) B3719249
theorem B1103243 : Blo 1100624 1103243 := bstep (se 1 (by rfl) ⟨827432, by rfl⟩ : syracuseStep 1103243 = 1654865) B1654865
theorem B1103255 : Blo 1100624 1103255 := bstep (se 1 (by rfl) ⟨827441, by rfl⟩ : syracuseStep 1103255 = 1654883) B1654883
theorem B1103275 : Blo 1100624 1103275 := bstep (se 1 (by rfl) ⟨827456, by rfl⟩ : syracuseStep 1103275 = 1654913) B1654913
theorem B1103287 : Blo 1100624 1103287 := bstep (se 1 (by rfl) ⟨827465, by rfl⟩ : syracuseStep 1103287 = 1654931) B1654931
theorem B2479553 : Blo 1100624 2479553 := bstep (se 2 (by rfl) ⟨929832, by rfl⟩ : syracuseStep 2479553 = 1859665) B1859665
theorem B2119115 : Blo 1100624 2119115 := bstep (se 1 (by rfl) ⟨1589336, by rfl⟩ : syracuseStep 2119115 = 3178673) B3178673
theorem B1103307 : Blo 1100624 1103307 := bstep (se 1 (by rfl) ⟨827480, by rfl⟩ : syracuseStep 1103307 = 1654961) B1654961
theorem B1103319 : Blo 1100624 1103319 := bstep (se 1 (by rfl) ⟨827489, by rfl⟩ : syracuseStep 1103319 = 1654979) B1654979
theorem B1103339 : Blo 1100624 1103339 := bstep (se 1 (by rfl) ⟨827504, by rfl⟩ : syracuseStep 1103339 = 1655009) B1655009
theorem B1103351 : Blo 1100624 1103351 := bstep (se 1 (by rfl) ⟨827513, by rfl⟩ : syracuseStep 1103351 = 1655027) B1655027
theorem B1103371 : Blo 1100624 1103371 := bstep (se 1 (by rfl) ⟨827528, by rfl⟩ : syracuseStep 1103371 = 1655057) B1655057
theorem B1103383 : Blo 1100624 1103383 := bstep (se 1 (by rfl) ⟨827537, by rfl⟩ : syracuseStep 1103383 = 1655075) B1655075
theorem B1103403 : Blo 1100624 1103403 := bstep (se 1 (by rfl) ⟨827552, by rfl⟩ : syracuseStep 1103403 = 1655105) B1655105
theorem B1103415 : Blo 1100624 1103415 := bstep (se 1 (by rfl) ⟨827561, by rfl⟩ : syracuseStep 1103415 = 1655123) B1655123
theorem B3724865 : Blo 1100624 3724865 := bstep (se 2 (by rfl) ⟨1396824, by rfl⟩ : syracuseStep 3724865 = 2793649) B2793649
theorem B1103435 : Blo 1100624 1103435 := bstep (se 1 (by rfl) ⟨827576, by rfl⟩ : syracuseStep 1103435 = 1655153) B1655153
theorem B1103447 : Blo 1100624 1103447 := bstep (se 1 (by rfl) ⟨827585, by rfl⟩ : syracuseStep 1103447 = 1655171) B1655171
theorem B3528281 : Blo 1100624 3528281 := bstep (se 2 (by rfl) ⟨1323105, by rfl⟩ : syracuseStep 3528281 = 2646211) B2646211
theorem B1103467 : Blo 1100624 1103467 := bstep (se 1 (by rfl) ⟨827600, by rfl⟩ : syracuseStep 1103467 = 1655201) B1655201
theorem B1103479 : Blo 1100624 1103479 := bstep (se 1 (by rfl) ⟨827609, by rfl⟩ : syracuseStep 1103479 = 1655219) B1655219
theorem B1103499 : Blo 1100624 1103499 := bstep (se 1 (by rfl) ⟨827624, by rfl⟩ : syracuseStep 1103499 = 1655249) B1655249
theorem B1103511 : Blo 1100624 1103511 := bstep (se 1 (by rfl) ⟨827633, by rfl⟩ : syracuseStep 1103511 = 1655267) B1655267
theorem B2479769 : Blo 1100624 2479769 := bstep (se 2 (by rfl) ⟨929913, by rfl⟩ : syracuseStep 2479769 = 1859827) B1859827
theorem B1103531 : Blo 1100624 1103531 := bstep (se 1 (by rfl) ⟨827648, by rfl⟩ : syracuseStep 1103531 = 1655297) B1655297
theorem B1103543 : Blo 1100624 1103543 := bstep (se 1 (by rfl) ⟨827657, by rfl⟩ : syracuseStep 1103543 = 1655315) B1655315
theorem B3135179 : Blo 1100624 3135179 := bstep (se 1 (by rfl) ⟨2351384, by rfl⟩ : syracuseStep 3135179 = 4702769) B4702769
theorem B1103563 : Blo 1100624 1103563 := bstep (se 1 (by rfl) ⟨827672, by rfl⟩ : syracuseStep 1103563 = 1655345) B1655345
theorem B1103575 : Blo 1100624 1103575 := bstep (se 1 (by rfl) ⟨827681, by rfl⟩ : syracuseStep 1103575 = 1655363) B1655363
theorem B1103595 : Blo 1100624 1103595 := bstep (se 1 (by rfl) ⟨827696, by rfl⟩ : syracuseStep 1103595 = 1655393) B1655393
theorem B2479859 : Blo 1100624 2479859 := bstep (se 1 (by rfl) ⟨1859894, by rfl⟩ : syracuseStep 2479859 = 3719789) B3719789
theorem B1103607 : Blo 1100624 1103607 := bstep (se 1 (by rfl) ⟨827705, by rfl⟩ : syracuseStep 1103607 = 1655411) B1655411
theorem B1103627 : Blo 1100624 1103627 := bstep (se 1 (by rfl) ⟨827720, by rfl⟩ : syracuseStep 1103627 = 1655441) B1655441
theorem B2479895 : Blo 1100624 2479895 := bstep (se 1 (by rfl) ⟨1859921, by rfl⟩ : syracuseStep 2479895 = 3719843) B3719843
theorem B1103639 : Blo 1100624 1103639 := bstep (se 1 (by rfl) ⟨827729, by rfl⟩ : syracuseStep 1103639 = 1655459) B1655459
theorem B1103659 : Blo 1100624 1103659 := bstep (se 1 (by rfl) ⟨827744, by rfl⟩ : syracuseStep 1103659 = 1655489) B1655489
theorem B1103671 : Blo 1100624 1103671 := bstep (se 1 (by rfl) ⟨827753, by rfl⟩ : syracuseStep 1103671 = 1655507) B1655507
theorem B4183883 : Blo 1100624 4183883 := bstep (se 1 (by rfl) ⟨3137912, by rfl⟩ : syracuseStep 4183883 = 6275825) B6275825
theorem B1103691 : Blo 1100624 1103691 := bstep (se 1 (by rfl) ⟨827768, by rfl⟩ : syracuseStep 1103691 = 1655537) B1655537
theorem B1103703 : Blo 1100624 1103703 := bstep (se 1 (by rfl) ⟨827777, by rfl⟩ : syracuseStep 1103703 = 1655555) B1655555
theorem B1103723 : Blo 1100624 1103723 := bstep (se 1 (by rfl) ⟨827792, by rfl⟩ : syracuseStep 1103723 = 1655585) B1655585
theorem B1103735 : Blo 1100624 1103735 := bstep (se 1 (by rfl) ⟨827801, by rfl⟩ : syracuseStep 1103735 = 1655603) B1655603
theorem B1103755 : Blo 1100624 1103755 := bstep (se 1 (by rfl) ⟨827816, by rfl⟩ : syracuseStep 1103755 = 1655633) B1655633
theorem B1857431 : Blo 1100624 1857431 := bstep (se 1 (by rfl) ⟨1393073, by rfl⟩ : syracuseStep 1857431 = 2786147) B2786147
theorem B1103767 : Blo 1100624 1103767 := bstep (se 1 (by rfl) ⟨827825, by rfl⟩ : syracuseStep 1103767 = 1655651) B1655651
theorem B1103787 : Blo 1100624 1103787 := bstep (se 1 (by rfl) ⟨827840, by rfl⟩ : syracuseStep 1103787 = 1655681) B1655681
theorem B1103799 : Blo 1100624 1103799 := bstep (se 1 (by rfl) ⟨827849, by rfl⟩ : syracuseStep 1103799 = 1655699) B1655699
theorem B2480075 : Blo 1100624 2480075 := bstep (se 1 (by rfl) ⟨1860056, by rfl⟩ : syracuseStep 2480075 = 3720113) B3720113
theorem B1103819 : Blo 1100624 1103819 := bstep (se 1 (by rfl) ⟨827864, by rfl⟩ : syracuseStep 1103819 = 1655729) B1655729
theorem B1103831 : Blo 1100624 1103831 := bstep (se 1 (by rfl) ⟨827873, by rfl⟩ : syracuseStep 1103831 = 1655747) B1655747
theorem B1103851 : Blo 1100624 1103851 := bstep (se 1 (by rfl) ⟨827888, by rfl⟩ : syracuseStep 1103851 = 1655777) B1655777
theorem B1103863 : Blo 1100624 1103863 := bstep (se 1 (by rfl) ⟨827897, by rfl⟩ : syracuseStep 1103863 = 1655795) B1655795
theorem B2480129 : Blo 1100624 2480129 := bstep (se 2 (by rfl) ⟨930048, by rfl⟩ : syracuseStep 2480129 = 1860097) B1860097
theorem B1103883 : Blo 1100624 1103883 := bstep (se 1 (by rfl) ⟨827912, by rfl⟩ : syracuseStep 1103883 = 1655825) B1655825
theorem B4184081 : Blo 1100624 4184081 := bstep (se 2 (by rfl) ⟨1569030, by rfl⟩ : syracuseStep 4184081 = 3138061) B3138061
theorem B1857559 : Blo 1100624 1857559 := bstep (se 1 (by rfl) ⟨1393169, by rfl⟩ : syracuseStep 1857559 = 2786339) B2786339
theorem B1103895 : Blo 1100624 1103895 := bstep (se 1 (by rfl) ⟨827921, by rfl⟩ : syracuseStep 1103895 = 1655843) B1655843
theorem B1103915 : Blo 1100624 1103915 := bstep (se 1 (by rfl) ⟨827936, by rfl⟩ : syracuseStep 1103915 = 1655873) B1655873
theorem B1103927 : Blo 1100624 1103927 := bstep (se 1 (by rfl) ⟨827945, by rfl⟩ : syracuseStep 1103927 = 1655891) B1655891
theorem B1103947 : Blo 1100624 1103947 := bstep (se 1 (by rfl) ⟨827960, by rfl⟩ : syracuseStep 1103947 = 1655921) B1655921
theorem B1103959 : Blo 1100624 1103959 := bstep (se 1 (by rfl) ⟨827969, by rfl⟩ : syracuseStep 1103959 = 1655939) B1655939
theorem B3528793 : Blo 1100624 3528793 := bstep (se 2 (by rfl) ⟨1323297, by rfl⟩ : syracuseStep 3528793 = 2646595) B2646595
theorem B3725405 : Blo 1100624 3725405 := bstep (se 3 (by rfl) ⟨698513, by rfl⟩ : syracuseStep 3725405 = 1397027) B1397027
theorem B1103979 : Blo 1100624 1103979 := bstep (se 1 (by rfl) ⟨827984, by rfl⟩ : syracuseStep 1103979 = 1655969) B1655969
theorem B1103991 : Blo 1100624 1103991 := bstep (se 1 (by rfl) ⟨827993, by rfl⟩ : syracuseStep 1103991 = 1655987) B1655987
theorem B1104011 : Blo 1100624 1104011 := bstep (se 1 (by rfl) ⟨828008, by rfl⟩ : syracuseStep 1104011 = 1656017) B1656017
theorem B1104023 : Blo 1100624 1104023 := bstep (se 1 (by rfl) ⟨828017, by rfl⟩ : syracuseStep 1104023 = 1656035) B1656035
theorem B1104043 : Blo 1100624 1104043 := bstep (se 1 (by rfl) ⟨828032, by rfl⟩ : syracuseStep 1104043 = 1656065) B1656065
theorem B1104055 : Blo 1100624 1104055 := bstep (se 1 (by rfl) ⟨828041, by rfl⟩ : syracuseStep 1104055 = 1656083) B1656083
theorem B1104075 : Blo 1100624 1104075 := bstep (se 1 (by rfl) ⟨828056, by rfl⟩ : syracuseStep 1104075 = 1656113) B1656113
theorem B1104087 : Blo 1100624 1104087 := bstep (se 1 (by rfl) ⟨828065, by rfl⟩ : syracuseStep 1104087 = 1656131) B1656131
theorem B2480345 : Blo 1100624 2480345 := bstep (se 2 (by rfl) ⟨930129, by rfl⟩ : syracuseStep 2480345 = 1860259) B1860259
theorem B1104107 : Blo 1100624 1104107 := bstep (se 1 (by rfl) ⟨828080, by rfl⟩ : syracuseStep 1104107 = 1656161) B1656161
theorem B1104119 : Blo 1100624 1104119 := bstep (se 1 (by rfl) ⟨828089, by rfl⟩ : syracuseStep 1104119 = 1656179) B1656179
theorem B1104139 : Blo 1100624 1104139 := bstep (se 1 (by rfl) ⟨828104, by rfl⟩ : syracuseStep 1104139 = 1656209) B1656209
theorem B1104151 : Blo 1100624 1104151 := bstep (se 1 (by rfl) ⟨828113, by rfl⟩ : syracuseStep 1104151 = 1656227) B1656227
theorem B1104171 : Blo 1100624 1104171 := bstep (se 1 (by rfl) ⟨828128, by rfl⟩ : syracuseStep 1104171 = 1656257) B1656257
theorem B2480435 : Blo 1100624 2480435 := bstep (se 1 (by rfl) ⟨1860326, by rfl⟩ : syracuseStep 2480435 = 3720653) B3720653
theorem B1104183 : Blo 1100624 1104183 := bstep (se 1 (by rfl) ⟨828137, by rfl⟩ : syracuseStep 1104183 = 1656275) B1656275
theorem B1104203 : Blo 1100624 1104203 := bstep (se 1 (by rfl) ⟨828152, by rfl⟩ : syracuseStep 1104203 = 1656305) B1656305
theorem B2480471 : Blo 1100624 2480471 := bstep (se 1 (by rfl) ⟨1860353, by rfl⟩ : syracuseStep 2480471 = 3720707) B3720707
theorem B1104215 : Blo 1100624 1104215 := bstep (se 1 (by rfl) ⟨828161, by rfl⟩ : syracuseStep 1104215 = 1656323) B1656323
theorem B1104235 : Blo 1100624 1104235 := bstep (se 1 (by rfl) ⟨828176, by rfl⟩ : syracuseStep 1104235 = 1656353) B1656353
theorem B1104247 : Blo 1100624 1104247 := bstep (se 1 (by rfl) ⟨828185, by rfl⟩ : syracuseStep 1104247 = 1656371) B1656371
theorem B1104267 : Blo 1100624 1104267 := bstep (se 1 (by rfl) ⟨828200, by rfl⟩ : syracuseStep 1104267 = 1656401) B1656401
theorem B1104279 : Blo 1100624 1104279 := bstep (se 1 (by rfl) ⟨828209, by rfl⟩ : syracuseStep 1104279 = 1656419) B1656419
theorem B1104299 : Blo 1100624 1104299 := bstep (se 1 (by rfl) ⟨828224, by rfl⟩ : syracuseStep 1104299 = 1656449) B1656449
theorem B1104311 : Blo 1100624 1104311 := bstep (se 1 (by rfl) ⟨828233, by rfl⟩ : syracuseStep 1104311 = 1656467) B1656467
theorem B1104331 : Blo 1100624 1104331 := bstep (se 1 (by rfl) ⟨828248, by rfl⟩ : syracuseStep 1104331 = 1656497) B1656497
theorem B1104343 : Blo 1100624 1104343 := bstep (se 1 (by rfl) ⟨828257, by rfl⟩ : syracuseStep 1104343 = 1656515) B1656515
theorem B1104363 : Blo 1100624 1104363 := bstep (se 1 (by rfl) ⟨828272, by rfl⟩ : syracuseStep 1104363 = 1656545) B1656545
theorem B1104375 : Blo 1100624 1104375 := bstep (se 1 (by rfl) ⟨828281, by rfl⟩ : syracuseStep 1104375 = 1656563) B1656563
theorem B2480651 : Blo 1100624 2480651 := bstep (se 1 (by rfl) ⟨1860488, by rfl⟩ : syracuseStep 2480651 = 3720977) B3720977
theorem B1104395 : Blo 1100624 1104395 := bstep (se 1 (by rfl) ⟨828296, by rfl⟩ : syracuseStep 1104395 = 1656593) B1656593
theorem B1104407 : Blo 1100624 1104407 := bstep (se 1 (by rfl) ⟨828305, by rfl⟩ : syracuseStep 1104407 = 1656611) B1656611
theorem B1104427 : Blo 1100624 1104427 := bstep (se 1 (by rfl) ⟨828320, by rfl⟩ : syracuseStep 1104427 = 1656641) B1656641
theorem B1104439 : Blo 1100624 1104439 := bstep (se 1 (by rfl) ⟨828329, by rfl⟩ : syracuseStep 1104439 = 1656659) B1656659
theorem B2480705 : Blo 1100624 2480705 := bstep (se 2 (by rfl) ⟨930264, by rfl⟩ : syracuseStep 2480705 = 1860529) B1860529
theorem B1104459 : Blo 1100624 1104459 := bstep (se 1 (by rfl) ⟨828344, by rfl⟩ : syracuseStep 1104459 = 1656689) B1656689
theorem B1104471 : Blo 1100624 1104471 := bstep (se 1 (by rfl) ⟨828353, by rfl⟩ : syracuseStep 1104471 = 1656707) B1656707
theorem B1104491 : Blo 1100624 1104491 := bstep (se 1 (by rfl) ⟨828368, by rfl⟩ : syracuseStep 1104491 = 1656737) B1656737
theorem B1104503 : Blo 1100624 1104503 := bstep (se 1 (by rfl) ⟨828377, by rfl⟩ : syracuseStep 1104503 = 1656755) B1656755
theorem B1858187 : Blo 1100624 1858187 := bstep (se 1 (by rfl) ⟨1393640, by rfl⟩ : syracuseStep 1858187 = 2787281) B2787281
theorem B1104523 : Blo 1100624 1104523 := bstep (se 1 (by rfl) ⟨828392, by rfl⟩ : syracuseStep 1104523 = 1656785) B1656785
theorem B1104535 : Blo 1100624 1104535 := bstep (se 1 (by rfl) ⟨828401, by rfl⟩ : syracuseStep 1104535 = 1656803) B1656803
theorem B1104555 : Blo 1100624 1104555 := bstep (se 1 (by rfl) ⟨828416, by rfl⟩ : syracuseStep 1104555 = 1656833) B1656833
theorem B1104567 : Blo 1100624 1104567 := bstep (se 1 (by rfl) ⟨828425, by rfl⟩ : syracuseStep 1104567 = 1656851) B1656851
theorem B1104587 : Blo 1100624 1104587 := bstep (se 1 (by rfl) ⟨828440, by rfl⟩ : syracuseStep 1104587 = 1656881) B1656881
theorem B1104599 : Blo 1100624 1104599 := bstep (se 1 (by rfl) ⟨828449, by rfl⟩ : syracuseStep 1104599 = 1656899) B1656899
theorem B1104619 : Blo 1100624 1104619 := bstep (se 1 (by rfl) ⟨828464, by rfl⟩ : syracuseStep 1104619 = 1656929) B1656929
theorem B1858315 : Blo 1100624 1858315 := bstep (se 1 (by rfl) ⟨1393736, by rfl⟩ : syracuseStep 1858315 = 2787473) B2787473
theorem B4184855 : Blo 1100624 4184855 := bstep (se 1 (by rfl) ⟨3138641, by rfl⟩ : syracuseStep 4184855 = 6277283) B6277283
theorem B2480921 : Blo 1100624 2480921 := bstep (se 2 (by rfl) ⟨930345, by rfl⟩ : syracuseStep 2480921 = 1860691) B1860691
theorem B7166765 : Blo 1100624 7166765 := bstep (se 3 (by rfl) ⟨1343768, by rfl⟩ : syracuseStep 7166765 = 2687537) B2687537
theorem B2481011 : Blo 1100624 2481011 := bstep (se 1 (by rfl) ⟨1860758, by rfl⟩ : syracuseStep 2481011 = 3721517) B3721517
theorem B2481047 : Blo 1100624 2481047 := bstep (se 1 (by rfl) ⟨1860785, by rfl⟩ : syracuseStep 2481047 = 3721571) B3721571
theorem B1858457 : Blo 1100624 1858457 := bstep (se 2 (by rfl) ⟨696921, by rfl⟩ : syracuseStep 1858457 = 1393843) B1393843
theorem B3136477 : Blo 1100624 3136477 := bstep (se 3 (by rfl) ⟨588089, by rfl⟩ : syracuseStep 3136477 = 1176179) B1176179
theorem B4185053 : Blo 1100624 4185053 := bstep (se 3 (by rfl) ⟨784697, by rfl⟩ : syracuseStep 4185053 = 1569395) B1569395
theorem B1858585 : Blo 1100624 1858585 := bstep (se 2 (by rfl) ⟨696969, by rfl⟩ : syracuseStep 1858585 = 1393939) B1393939
theorem B2481227 : Blo 1100624 2481227 := bstep (se 1 (by rfl) ⟨1860920, by rfl⟩ : syracuseStep 2481227 = 3721841) B3721841
theorem B2481281 : Blo 1100624 2481281 := bstep (se 2 (by rfl) ⟨930480, by rfl⟩ : syracuseStep 2481281 = 1860961) B1860961
theorem B2514059 : Blo 1100624 2514059 := bstep (se 1 (by rfl) ⟨1885544, by rfl⟩ : syracuseStep 2514059 = 3771089) B3771089
theorem B3529921 : Blo 1100624 3529921 := bstep (se 2 (by rfl) ⟨1323720, by rfl⟩ : syracuseStep 3529921 = 2647441) B2647441
theorem B3726539 : Blo 1100624 3726539 := bstep (se 1 (by rfl) ⟨2794904, by rfl⟩ : syracuseStep 3726539 = 5589809) B5589809
theorem B3136819 : Blo 1100624 3136819 := bstep (se 1 (by rfl) ⟨2352614, by rfl⟩ : syracuseStep 3136819 = 4705229) B4705229
theorem B2481497 : Blo 1100624 2481497 := bstep (se 2 (by rfl) ⟨930561, by rfl⟩ : syracuseStep 2481497 = 1861123) B1861123
theorem B2481587 : Blo 1100624 2481587 := bstep (se 1 (by rfl) ⟨1861190, by rfl⟩ : syracuseStep 2481587 = 3722381) B3722381
theorem B2481623 : Blo 1100624 2481623 := bstep (se 1 (by rfl) ⟨1861217, by rfl⟩ : syracuseStep 2481623 = 3722435) B3722435
theorem B3726809 : Blo 1100624 3726809 := bstep (se 2 (by rfl) ⟨1397553, by rfl⟩ : syracuseStep 3726809 = 2795107) B2795107
theorem B1859159 : Blo 1100624 1859159 := bstep (se 1 (by rfl) ⟨1394369, by rfl⟩ : syracuseStep 1859159 = 2788739) B2788739
theorem B2481803 : Blo 1100624 2481803 := bstep (se 1 (by rfl) ⟨1861352, by rfl⟩ : syracuseStep 2481803 = 3722705) B3722705
theorem B2481857 : Blo 1100624 2481857 := bstep (se 2 (by rfl) ⟨930696, by rfl⟩ : syracuseStep 2481857 = 1861393) B1861393
theorem B1859287 : Blo 1100624 1859287 := bstep (se 1 (by rfl) ⟨1394465, by rfl⟩ : syracuseStep 1859287 = 2788931) B2788931
theorem B2482073 : Blo 1100624 2482073 := bstep (se 2 (by rfl) ⟨930777, by rfl⟩ : syracuseStep 2482073 = 1861555) B1861555
theorem B2482163 : Blo 1100624 2482163 := bstep (se 1 (by rfl) ⟨1861622, by rfl⟩ : syracuseStep 2482163 = 3723245) B3723245
theorem B2482199 : Blo 1100624 2482199 := bstep (se 1 (by rfl) ⟨1861649, by rfl⟩ : syracuseStep 2482199 = 3723299) B3723299
theorem B3727511 : Blo 1100624 3727511 := bstep (se 1 (by rfl) ⟨2795633, by rfl⟩ : syracuseStep 3727511 = 5591267) B5591267
theorem B2482379 : Blo 1100624 2482379 := bstep (se 1 (by rfl) ⟨1861784, by rfl⟩ : syracuseStep 2482379 = 3723569) B3723569
theorem B17883341 : Blo 1100624 17883341 := bstep (se 3 (by rfl) ⟨3353126, by rfl⟩ : syracuseStep 17883341 = 6706253) B6706253
theorem B3137753 : Blo 1100624 3137753 := bstep (se 2 (by rfl) ⟨1176657, by rfl⟩ : syracuseStep 3137753 = 2353315) B2353315
theorem B2482433 : Blo 1100624 2482433 := bstep (se 2 (by rfl) ⟨930912, by rfl⟩ : syracuseStep 2482433 = 1861825) B1861825
theorem B93184277 : Blo 1100624 93184277 := bstep (se 6 (by rfl) ⟨2184006, by rfl⟩ : syracuseStep 93184277 = 4368013) B4368013
theorem B2351435 : Blo 1100624 2351435 := bstep (se 1 (by rfl) ⟨1763576, by rfl⟩ : syracuseStep 2351435 = 3527153) B3527153
theorem B1859915 : Blo 1100624 1859915 := bstep (se 1 (by rfl) ⟨1394936, by rfl⟩ : syracuseStep 1859915 = 2789873) B2789873
theorem B1860043 : Blo 1100624 1860043 := bstep (se 1 (by rfl) ⟨1395032, by rfl⟩ : syracuseStep 1860043 = 2790065) B2790065
theorem B2482649 : Blo 1100624 2482649 := bstep (se 2 (by rfl) ⟨930993, by rfl⟩ : syracuseStep 2482649 = 1861987) B1861987
theorem B4088323 : Blo 1100624 4088323 := bstep (se 1 (by rfl) ⟨3066242, by rfl⟩ : syracuseStep 4088323 = 6132485) B6132485
theorem B12575249 : Blo 1100624 12575249 := bstep (se 2 (by rfl) ⟨4715718, by rfl⟩ : syracuseStep 12575249 = 9431437) B9431437
theorem B4710935 : Blo 1100624 4710935 := bstep (se 1 (by rfl) ⟨3533201, by rfl⟩ : syracuseStep 4710935 = 7066403) B7066403
theorem B2482739 : Blo 1100624 2482739 := bstep (se 1 (by rfl) ⟨1862054, by rfl⟩ : syracuseStep 2482739 = 3724109) B3724109
theorem B2482775 : Blo 1100624 2482775 := bstep (se 1 (by rfl) ⟨1862081, by rfl⟩ : syracuseStep 2482775 = 3724163) B3724163
theorem B1860185 : Blo 1100624 1860185 := bstep (se 2 (by rfl) ⟨697569, by rfl⟩ : syracuseStep 1860185 = 1395139) B1395139
theorem B3728051 : Blo 1100624 3728051 := bstep (se 1 (by rfl) ⟨2796038, by rfl⟩ : syracuseStep 3728051 = 5592077) B5592077
theorem B2122433 : Blo 1100624 2122433 := bstep (se 2 (by rfl) ⟨795912, by rfl⟩ : syracuseStep 2122433 = 1591825) B1591825
theorem B25420493 : Blo 1100624 25420493 := bstep (se 3 (by rfl) ⟨4766342, by rfl⟩ : syracuseStep 25420493 = 9532685) B9532685
theorem B1860313 : Blo 1100624 1860313 := bstep (se 2 (by rfl) ⟨697617, by rfl⟩ : syracuseStep 1860313 = 1395235) B1395235
theorem B2089739 : Blo 1100624 2089739 := bstep (se 1 (by rfl) ⟨1567304, by rfl⟩ : syracuseStep 2089739 = 3134609) B3134609
theorem B2482955 : Blo 1100624 2482955 := bstep (se 1 (by rfl) ⟨1862216, by rfl⟩ : syracuseStep 2482955 = 3724433) B3724433
theorem B2089793 : Blo 1100624 2089793 := bstep (se 2 (by rfl) ⟨783672, by rfl⟩ : syracuseStep 2089793 = 1567345) B1567345
theorem B2483009 : Blo 1100624 2483009 := bstep (se 2 (by rfl) ⟨931128, by rfl⟩ : syracuseStep 2483009 = 1862257) B1862257
theorem B4711243 : Blo 1100624 4711243 := bstep (se 1 (by rfl) ⟨3533432, by rfl⟩ : syracuseStep 4711243 = 7066865) B7066865
theorem B4088665 : Blo 1100624 4088665 := bstep (se 2 (by rfl) ⟨1533249, by rfl⟩ : syracuseStep 4088665 = 3066499) B3066499
theorem B3531613 : Blo 1100624 3531613 := bstep (se 3 (by rfl) ⟨662177, by rfl⟩ : syracuseStep 3531613 = 1324355) B1324355
theorem B4187011 : Blo 1100624 4187011 := bstep (se 1 (by rfl) ⟨3140258, by rfl⟩ : syracuseStep 4187011 = 6280517) B6280517
theorem B6710195 : Blo 1100624 6710195 := bstep (se 1 (by rfl) ⟨5032646, by rfl⟩ : syracuseStep 6710195 = 10065293) B10065293
theorem B2483225 : Blo 1100624 2483225 := bstep (se 2 (by rfl) ⟨931209, by rfl⟩ : syracuseStep 2483225 = 1862419) B1862419
theorem B2352179 : Blo 1100624 2352179 := bstep (se 1 (by rfl) ⟨1764134, by rfl⟩ : syracuseStep 2352179 = 3528269) B3528269
theorem B4711517 : Blo 1100624 4711517 := bstep (se 3 (by rfl) ⟨883409, by rfl⟩ : syracuseStep 4711517 = 1766819) B1766819
theorem B7070813 : Blo 1100624 7070813 := bstep (se 3 (by rfl) ⟨1325777, by rfl⟩ : syracuseStep 7070813 = 2651555) B2651555
theorem B2483315 : Blo 1100624 2483315 := bstep (se 1 (by rfl) ⟨1862486, by rfl⟩ : syracuseStep 2483315 = 3724973) B3724973
theorem B5301379 : Blo 1100624 5301379 := bstep (se 1 (by rfl) ⟨3976034, by rfl⟩ : syracuseStep 5301379 = 7952069) B7952069
theorem B14115991 : Blo 1100624 14115991 := bstep (se 1 (by rfl) ⟨10586993, by rfl⟩ : syracuseStep 14115991 = 21173987) B21173987
theorem B2483351 : Blo 1100624 2483351 := bstep (se 1 (by rfl) ⟨1862513, by rfl⟩ : syracuseStep 2483351 = 3725027) B3725027
theorem B4187315 : Blo 1100624 4187315 := bstep (se 1 (by rfl) ⟨3140486, by rfl⟩ : syracuseStep 4187315 = 6280973) B6280973
theorem B1238251 : Blo 1100624 1238251 := bstep (se 1 (by rfl) ⟨928688, by rfl⟩ : syracuseStep 1238251 = 1857377) B1857377
theorem B1860887 : Blo 1100624 1860887 := bstep (se 1 (by rfl) ⟨1395665, by rfl⟩ : syracuseStep 1860887 = 2791331) B2791331
theorem B2483531 : Blo 1100624 2483531 := bstep (se 1 (by rfl) ⟨1862648, by rfl⟩ : syracuseStep 2483531 = 3725297) B3725297
theorem B1238359 : Blo 1100624 1238359 := bstep (se 1 (by rfl) ⟨928769, by rfl⟩ : syracuseStep 1238359 = 1857539) B1857539
theorem B2483585 : Blo 1100624 2483585 := bstep (se 2 (by rfl) ⟨931344, by rfl⟩ : syracuseStep 2483585 = 1862689) B1862689
theorem B1861015 : Blo 1100624 1861015 := bstep (se 1 (by rfl) ⟨1395761, by rfl⟩ : syracuseStep 1861015 = 2791523) B2791523
theorem B1238539 : Blo 1100624 1238539 := bstep (se 1 (by rfl) ⟨928904, by rfl⟩ : syracuseStep 1238539 = 1857809) B1857809
theorem B2483801 : Blo 1100624 2483801 := bstep (se 2 (by rfl) ⟨931425, by rfl⟩ : syracuseStep 2483801 = 1862851) B1862851
theorem B3139165 : Blo 1100624 3139165 := bstep (se 3 (by rfl) ⟨588593, by rfl⟩ : syracuseStep 3139165 = 1177187) B1177187
theorem B13428317 : Blo 1100624 13428317 := bstep (se 3 (by rfl) ⟨2517809, by rfl⟩ : syracuseStep 13428317 = 5035619) B5035619
theorem B22668893 : Blo 1100624 22668893 := bstep (se 3 (by rfl) ⟨4250417, by rfl⟩ : syracuseStep 22668893 = 8500835) B8500835
theorem B1238647 : Blo 1100624 1238647 := bstep (se 1 (by rfl) ⟨928985, by rfl⟩ : syracuseStep 1238647 = 1857971) B1857971
theorem B2483891 : Blo 1100624 2483891 := bstep (se 1 (by rfl) ⟨1862918, by rfl⟩ : syracuseStep 2483891 = 3725837) B3725837
theorem B2090711 : Blo 1100624 2090711 := bstep (se 1 (by rfl) ⟨1568033, by rfl⟩ : syracuseStep 2090711 = 3136067) B3136067
theorem B2483927 : Blo 1100624 2483927 := bstep (se 1 (by rfl) ⟨1862945, by rfl⟩ : syracuseStep 2483927 = 3725891) B3725891
theorem B6285073 : Blo 1100624 6285073 := bstep (se 2 (by rfl) ⟨2356902, by rfl⟩ : syracuseStep 6285073 = 4713805) B4713805
theorem B1238827 : Blo 1100624 1238827 := bstep (se 1 (by rfl) ⟨929120, by rfl⟩ : syracuseStep 1238827 = 1858241) B1858241
theorem B3139393 : Blo 1100624 3139393 := bstep (se 2 (by rfl) ⟨1177272, by rfl⟩ : syracuseStep 3139393 = 2354545) B2354545
theorem B4187969 : Blo 1100624 4187969 := bstep (se 2 (by rfl) ⟨1570488, by rfl⟩ : syracuseStep 4187969 = 3140977) B3140977
theorem B11921269 : Blo 1100624 11921269 := bstep (se 5 (by rfl) ⟨558809, by rfl⟩ : syracuseStep 11921269 = 1117619) B1117619
theorem B2353025 : Blo 1100624 2353025 := bstep (se 2 (by rfl) ⟨882384, by rfl⟩ : syracuseStep 2353025 = 1764769) B1764769
theorem B2484107 : Blo 1100624 2484107 := bstep (se 1 (by rfl) ⟨1863080, by rfl⟩ : syracuseStep 2484107 = 3726161) B3726161
theorem B1238935 : Blo 1100624 1238935 := bstep (se 1 (by rfl) ⟨929201, by rfl⟩ : syracuseStep 1238935 = 1858403) B1858403
theorem B2484161 : Blo 1100624 2484161 := bstep (se 2 (by rfl) ⟨931560, by rfl⟩ : syracuseStep 2484161 = 1863121) B1863121
theorem B1861643 : Blo 1100624 1861643 := bstep (se 1 (by rfl) ⟨1396232, by rfl⟩ : syracuseStep 1861643 = 2792465) B2792465
theorem B1239115 : Blo 1100624 1239115 := bstep (se 1 (by rfl) ⟨929336, by rfl⟩ : syracuseStep 1239115 = 1858673) B1858673
theorem B1763417 : Blo 1100624 1763417 := bstep (se 2 (by rfl) ⟨661281, by rfl⟩ : syracuseStep 1763417 = 1322563) B1322563
theorem B2648153 : Blo 1100624 2648153 := bstep (se 2 (by rfl) ⟨993057, by rfl⟩ : syracuseStep 2648153 = 1986115) B1986115
theorem B1861771 : Blo 1100624 1861771 := bstep (se 1 (by rfl) ⟨1396328, by rfl⟩ : syracuseStep 1861771 = 2792657) B2792657
theorem B5957783 : Blo 1100624 5957783 := bstep (se 1 (by rfl) ⟨4468337, by rfl⟩ : syracuseStep 5957783 = 8936675) B8936675
theorem B3139735 : Blo 1100624 3139735 := bstep (se 1 (by rfl) ⟨2354801, by rfl⟩ : syracuseStep 3139735 = 4709603) B4709603
theorem B2484377 : Blo 1100624 2484377 := bstep (se 2 (by rfl) ⟨931641, by rfl⟩ : syracuseStep 2484377 = 1863283) B1863283
theorem B1239223 : Blo 1100624 1239223 := bstep (se 1 (by rfl) ⟨929417, by rfl⟩ : syracuseStep 1239223 = 1858835) B1858835
theorem B2353367 : Blo 1100624 2353367 := bstep (se 1 (by rfl) ⟨1765025, by rfl⟩ : syracuseStep 2353367 = 3530051) B3530051
theorem B2091251 : Blo 1100624 2091251 := bstep (se 1 (by rfl) ⟨1568438, by rfl⟩ : syracuseStep 2091251 = 3136877) B3136877
theorem B2484467 : Blo 1100624 2484467 := bstep (se 1 (by rfl) ⟨1863350, by rfl⟩ : syracuseStep 2484467 = 3726701) B3726701
theorem B2484503 : Blo 1100624 2484503 := bstep (se 1 (by rfl) ⟨1863377, by rfl⟩ : syracuseStep 2484503 = 3726755) B3726755
theorem B1861913 : Blo 1100624 1861913 := bstep (se 2 (by rfl) ⟨698217, by rfl⟩ : syracuseStep 1861913 = 1396435) B1396435
theorem B5368139 : Blo 1100624 5368139 := bstep (se 1 (by rfl) ⟨4026104, by rfl⟩ : syracuseStep 5368139 = 8052209) B8052209
theorem B1239403 : Blo 1100624 1239403 := bstep (se 1 (by rfl) ⟨929552, by rfl⟩ : syracuseStep 1239403 = 1859105) B1859105
theorem B4712849 : Blo 1100624 4712849 := bstep (se 2 (by rfl) ⟨1767318, by rfl⟩ : syracuseStep 4712849 = 3534637) B3534637
theorem B1862041 : Blo 1100624 1862041 := bstep (se 2 (by rfl) ⟨698265, by rfl⟩ : syracuseStep 1862041 = 1396531) B1396531
theorem B2484683 : Blo 1100624 2484683 := bstep (se 1 (by rfl) ⟨1863512, by rfl⟩ : syracuseStep 2484683 = 3727025) B3727025
theorem B1239511 : Blo 1100624 1239511 := bstep (se 1 (by rfl) ⟨929633, by rfl⟩ : syracuseStep 1239511 = 1859267) B1859267
theorem B2484737 : Blo 1100624 2484737 := bstep (se 2 (by rfl) ⟨931776, by rfl⟩ : syracuseStep 2484737 = 1863553) B1863553
theorem B1272407 : Blo 1100624 1272407 := bstep (se 1 (by rfl) ⟨954305, by rfl⟩ : syracuseStep 1272407 = 1908611) B1908611
theorem B20146781 : Blo 1100624 20146781 := bstep (se 3 (by rfl) ⟨3777521, by rfl⟩ : syracuseStep 20146781 = 7555043) B7555043
theorem B1239691 : Blo 1100624 1239691 := bstep (se 1 (by rfl) ⟨929768, by rfl⟩ : syracuseStep 1239691 = 1859537) B1859537
theorem B2091737 : Blo 1100624 2091737 := bstep (se 2 (by rfl) ⟨784401, by rfl⟩ : syracuseStep 2091737 = 1568803) B1568803
theorem B2484953 : Blo 1100624 2484953 := bstep (se 2 (by rfl) ⟨931857, by rfl⟩ : syracuseStep 2484953 = 1863715) B1863715
theorem B1239799 : Blo 1100624 1239799 := bstep (se 1 (by rfl) ⟨929849, by rfl⟩ : syracuseStep 1239799 = 1859699) B1859699
theorem B2485043 : Blo 1100624 2485043 := bstep (se 1 (by rfl) ⟨1863782, by rfl⟩ : syracuseStep 2485043 = 3727565) B3727565
theorem B2485079 : Blo 1100624 2485079 := bstep (se 1 (by rfl) ⟨1863809, by rfl⟩ : syracuseStep 2485079 = 3727619) B3727619
theorem B3140441 : Blo 1100624 3140441 := bstep (se 2 (by rfl) ⟨1177665, by rfl⟩ : syracuseStep 3140441 = 2355331) B2355331
theorem B1239979 : Blo 1100624 1239979 := bstep (se 1 (by rfl) ⟨929984, by rfl⟩ : syracuseStep 1239979 = 1859969) B1859969
theorem B1862615 : Blo 1100624 1862615 := bstep (se 1 (by rfl) ⟨1396961, by rfl⟩ : syracuseStep 1862615 = 2793923) B2793923
theorem B2485259 : Blo 1100624 2485259 := bstep (se 1 (by rfl) ⟨1863944, by rfl⟩ : syracuseStep 2485259 = 3727889) B3727889
theorem B1240087 : Blo 1100624 1240087 := bstep (se 1 (by rfl) ⟨930065, by rfl⟩ : syracuseStep 1240087 = 1860131) B1860131
theorem B4189229 : Blo 1100624 4189229 := bstep (se 3 (by rfl) ⟨785480, by rfl⟩ : syracuseStep 4189229 = 1570961) B1570961
theorem B2485313 : Blo 1100624 2485313 := bstep (se 2 (by rfl) ⟨931992, by rfl⟩ : syracuseStep 2485313 = 1863985) B1863985
theorem B4189259 : Blo 1100624 4189259 := bstep (se 1 (by rfl) ⟨3141944, by rfl⟩ : syracuseStep 4189259 = 6283889) B6283889
theorem B1862743 : Blo 1100624 1862743 := bstep (se 1 (by rfl) ⟨1397057, by rfl⟩ : syracuseStep 1862743 = 2794115) B2794115
theorem B52292789 : Blo 1100624 52292789 := bstep (se 5 (by rfl) ⟨2451224, by rfl⟩ : syracuseStep 52292789 = 4902449) B4902449
theorem B1240267 : Blo 1100624 1240267 := bstep (se 1 (by rfl) ⟨930200, by rfl⟩ : syracuseStep 1240267 = 1860401) B1860401
theorem B1568011 : Blo 1100624 1568011 := bstep (se 1 (by rfl) ⟨1176008, by rfl⟩ : syracuseStep 1568011 = 2352017) B2352017
theorem B1240375 : Blo 1100624 1240375 := bstep (se 1 (by rfl) ⟨930281, by rfl⟩ : syracuseStep 1240375 = 1860563) B1860563
theorem B9432395 : Blo 1100624 9432395 := bstep (se 1 (by rfl) ⟨7074296, by rfl⟩ : syracuseStep 9432395 = 14148593) B14148593
theorem B12578165 : Blo 1100624 12578165 := bstep (se 5 (by rfl) ⟨589601, by rfl⟩ : syracuseStep 12578165 = 1179203) B1179203
theorem B1240555 : Blo 1100624 1240555 := bstep (se 1 (by rfl) ⟨930416, by rfl⟩ : syracuseStep 1240555 = 1860833) B1860833
theorem B1240663 : Blo 1100624 1240663 := bstep (se 1 (by rfl) ⟨930497, by rfl⟩ : syracuseStep 1240663 = 1860995) B1860995
theorem B1863371 : Blo 1100624 1863371 := bstep (se 1 (by rfl) ⟨1397528, by rfl⟩ : syracuseStep 1863371 = 2795057) B2795057
theorem B4189913 : Blo 1100624 4189913 := bstep (se 2 (by rfl) ⟨1571217, by rfl⟩ : syracuseStep 4189913 = 3142435) B3142435
theorem B1240843 : Blo 1100624 1240843 := bstep (se 1 (by rfl) ⟨930632, by rfl⟩ : syracuseStep 1240843 = 1861265) B1861265
theorem B21163841 : Blo 1100624 21163841 := bstep (se 2 (by rfl) ⟨7936440, by rfl⟩ : syracuseStep 21163841 = 15872881) B15872881
theorem B1863499 : Blo 1100624 1863499 := bstep (se 1 (by rfl) ⟨1397624, by rfl⟩ : syracuseStep 1863499 = 2795249) B2795249
theorem B1240951 : Blo 1100624 1240951 := bstep (se 1 (by rfl) ⟨930713, by rfl⟩ : syracuseStep 1240951 = 1861427) B1861427
theorem B1863641 : Blo 1100624 1863641 := bstep (se 2 (by rfl) ⟨698865, by rfl⟩ : syracuseStep 1863641 = 1397731) B1397731
theorem B4190231 : Blo 1100624 4190231 := bstep (se 1 (by rfl) ⟨3142673, by rfl⟩ : syracuseStep 4190231 = 6285347) B6285347
theorem B1241131 : Blo 1100624 1241131 := bstep (se 1 (by rfl) ⟨930848, by rfl⟩ : syracuseStep 1241131 = 1861697) B1861697
theorem B7073837 : Blo 1100624 7073837 := bstep (se 3 (by rfl) ⟨1326344, by rfl⟩ : syracuseStep 7073837 = 2652689) B2652689
theorem B1863769 : Blo 1100624 1863769 := bstep (se 2 (by rfl) ⟨698913, by rfl⟩ : syracuseStep 1863769 = 1397827) B1397827
theorem B11300957 : Blo 1100624 11300957 := bstep (se 3 (by rfl) ⟨2118929, by rfl⟩ : syracuseStep 11300957 = 4237859) B4237859
theorem B2093195 : Blo 1100624 2093195 := bstep (se 1 (by rfl) ⟨1569896, by rfl⟩ : syracuseStep 2093195 = 3139793) B3139793
theorem B1241239 : Blo 1100624 1241239 := bstep (se 1 (by rfl) ⟨930929, by rfl⟩ : syracuseStep 1241239 = 1861859) B1861859
theorem B1175735 : Blo 1100624 1175735 := bstep (se 1 (by rfl) ⟨881801, by rfl⟩ : syracuseStep 1175735 = 1763603) B1763603
theorem B2093377 : Blo 1100624 2093377 := bstep (se 2 (by rfl) ⟨785016, by rfl⟩ : syracuseStep 2093377 = 1570033) B1570033
theorem B1241419 : Blo 1100624 1241419 := bstep (se 1 (by rfl) ⟨931064, by rfl⟩ : syracuseStep 1241419 = 1862129) B1862129
theorem B1241527 : Blo 1100624 1241527 := bstep (se 1 (by rfl) ⟨931145, by rfl⟩ : syracuseStep 1241527 = 1862291) B1862291
theorem B3142081 : Blo 1100624 3142081 := bstep (se 2 (by rfl) ⟨1178280, by rfl⟩ : syracuseStep 3142081 = 2356561) B2356561
theorem B1569241 : Blo 1100624 1569241 := bstep (se 2 (by rfl) ⟨588465, by rfl⟩ : syracuseStep 1569241 = 1176931) B1176931
theorem B1241707 : Blo 1100624 1241707 := bstep (se 1 (by rfl) ⟨931280, by rfl⟩ : syracuseStep 1241707 = 1862561) B1862561
theorem B4190899 : Blo 1100624 4190899 := bstep (se 1 (by rfl) ⟨3143174, by rfl⟩ : syracuseStep 4190899 = 6286349) B6286349
theorem B1241815 : Blo 1100624 1241815 := bstep (se 1 (by rfl) ⟨931361, by rfl⟩ : syracuseStep 1241815 = 1862723) B1862723
theorem B2093825 : Blo 1100624 2093825 := bstep (se 2 (by rfl) ⟨785184, by rfl⟩ : syracuseStep 2093825 = 1570369) B1570369
theorem B5960465 : Blo 1100624 5960465 := bstep (se 2 (by rfl) ⟨2235174, by rfl⟩ : syracuseStep 5960465 = 4470349) B4470349
theorem B4715309 : Blo 1100624 4715309 := bstep (se 3 (by rfl) ⟨884120, by rfl⟩ : syracuseStep 4715309 = 1768241) B1768241
theorem B1241995 : Blo 1100624 1241995 := bstep (se 1 (by rfl) ⟨931496, by rfl⟩ : syracuseStep 1241995 = 1862993) B1862993
theorem B1242103 : Blo 1100624 1242103 := bstep (se 1 (by rfl) ⟨931577, by rfl⟩ : syracuseStep 1242103 = 1863155) B1863155
theorem B2094167 : Blo 1100624 2094167 := bstep (se 1 (by rfl) ⟨1570625, by rfl⟩ : syracuseStep 2094167 = 3141251) B3141251
theorem B4715651 : Blo 1100624 4715651 := bstep (se 1 (by rfl) ⟨3536738, by rfl⟩ : syracuseStep 4715651 = 7073477) B7073477
theorem B6288515 : Blo 1100624 6288515 := bstep (se 1 (by rfl) ⟨4716386, by rfl⟩ : syracuseStep 6288515 = 9432773) B9432773
theorem B17855639 : Blo 1100624 17855639 := bstep (se 1 (by rfl) ⟨13391729, by rfl⟩ : syracuseStep 17855639 = 26783459) B26783459
theorem B1242283 : Blo 1100624 1242283 := bstep (se 1 (by rfl) ⟨931712, by rfl⟩ : syracuseStep 1242283 = 1863425) B1863425
theorem B51573941 : Blo 1100624 51573941 := bstep (se 5 (by rfl) ⟨2417528, by rfl⟩ : syracuseStep 51573941 = 4835057) B4835057
theorem B1176811 : Blo 1100624 1176811 := bstep (se 1 (by rfl) ⟨882608, by rfl⟩ : syracuseStep 1176811 = 1765217) B1765217
theorem B1242391 : Blo 1100624 1242391 := bstep (se 1 (by rfl) ⟨931793, by rfl⟩ : syracuseStep 1242391 = 1863587) B1863587
theorem B1242571 : Blo 1100624 1242571 := bstep (se 1 (by rfl) ⟨931928, by rfl⟩ : syracuseStep 1242571 = 1863857) B1863857
theorem B1242679 : Blo 1100624 1242679 := bstep (se 1 (by rfl) ⟨932009, by rfl⟩ : syracuseStep 1242679 = 1864019) B1864019
theorem B2094835 : Blo 1100624 2094835 := bstep (se 1 (by rfl) ⟨1571126, by rfl⟩ : syracuseStep 2094835 = 3142253) B3142253
theorem B6715153 : Blo 1100624 6715153 := bstep (se 2 (by rfl) ⟨2518182, by rfl⟩ : syracuseStep 6715153 = 5036365) B5036365
theorem B1570585 : Blo 1100624 1570585 := bstep (se 2 (by rfl) ⟨588969, by rfl⟩ : syracuseStep 1570585 = 1177939) B1177939
theorem B1570699 : Blo 1100624 1570699 := bstep (se 1 (by rfl) ⟨1178024, by rfl⟩ : syracuseStep 1570699 = 2356049) B2356049
theorem B4192145 : Blo 1100624 4192145 := bstep (se 2 (by rfl) ⟨1572054, by rfl⟩ : syracuseStep 4192145 = 3144109) B3144109
theorem B1275799 : Blo 1100624 1275799 := bstep (se 1 (by rfl) ⟨956849, by rfl⟩ : syracuseStep 1275799 = 1913699) B1913699
theorem B1177751 : Blo 1100624 1177751 := bstep (se 1 (by rfl) ⟨883313, by rfl⟩ : syracuseStep 1177751 = 1766627) B1766627
theorem B2357399 : Blo 1100624 2357399 := bstep (se 1 (by rfl) ⟨1768049, by rfl⟩ : syracuseStep 2357399 = 3536099) B3536099
theorem B3537047 : Blo 1100624 3537047 := bstep (se 1 (by rfl) ⟨2652785, by rfl⟩ : syracuseStep 3537047 = 5305571) B5305571
theorem B6715543 : Blo 1100624 6715543 := bstep (se 1 (by rfl) ⟨5036657, by rfl⟩ : syracuseStep 6715543 = 10073315) B10073315
theorem B2095283 : Blo 1100624 2095283 := bstep (se 1 (by rfl) ⟨1571462, by rfl⟩ : syracuseStep 2095283 = 3142925) B3142925
theorem B2652353 : Blo 1100624 2652353 := bstep (se 2 (by rfl) ⟨994632, by rfl⟩ : syracuseStep 2652353 = 1989265) B1989265
theorem B2095321 : Blo 1100624 2095321 := bstep (se 2 (by rfl) ⟨785745, by rfl⟩ : syracuseStep 2095321 = 1571491) B1571491
theorem B2652439 : Blo 1100624 2652439 := bstep (se 1 (by rfl) ⟨1989329, by rfl⟩ : syracuseStep 2652439 = 3978659) B3978659
theorem B2357579 : Blo 1100624 2357579 := bstep (se 1 (by rfl) ⟨1768184, by rfl⟩ : syracuseStep 2357579 = 3536369) B3536369
theorem B9402803 : Blo 1100624 9402803 := bstep (se 1 (by rfl) ⟨7052102, by rfl⟩ : syracuseStep 9402803 = 14104205) B14104205
theorem B4192843 : Blo 1100624 4192843 := bstep (se 1 (by rfl) ⟨3144632, by rfl⟩ : syracuseStep 4192843 = 6289265) B6289265
theorem B1768087 : Blo 1100624 1768087 := bstep (se 1 (by rfl) ⟨1326065, by rfl⟩ : syracuseStep 1768087 = 2652131) B2652131
theorem B2095769 : Blo 1100624 2095769 := bstep (se 2 (by rfl) ⟨785913, by rfl⟩ : syracuseStep 2095769 = 1571827) B1571827
theorem B1768139 : Blo 1100624 1768139 := bstep (se 1 (by rfl) ⟨1326104, by rfl⟩ : syracuseStep 1768139 = 2652209) B2652209
theorem B1768267 : Blo 1100624 1768267 := bstep (se 1 (by rfl) ⟨1326200, by rfl⟩ : syracuseStep 1768267 = 2652401) B2652401
theorem B4193117 : Blo 1100624 4193117 := bstep (se 3 (by rfl) ⟨786209, by rfl⟩ : syracuseStep 4193117 = 1572419) B1572419
theorem B10583075 : Blo 1100624 10583075 := bstep (se 1 (by rfl) ⟨7937306, by rfl⟩ : syracuseStep 10583075 = 15874613) B15874613
theorem B4586561 : Blo 1100624 4586561 := bstep (se 2 (by rfl) ⟨1719960, by rfl⟩ : syracuseStep 4586561 = 3439921) B3439921
theorem B28212299 : Blo 1100624 28212299 := bstep (se 1 (by rfl) ⟨21159224, by rfl⟩ : syracuseStep 28212299 = 42318449) B42318449
theorem B1572043 : Blo 1100624 1572043 := bstep (se 1 (by rfl) ⟨1179032, by rfl⟩ : syracuseStep 1572043 = 2358065) B2358065
theorem B2391383 : Blo 1100624 2391383 := bstep (se 1 (by rfl) ⟨1793537, by rfl⟩ : syracuseStep 2391383 = 3587075) B3587075
theorem B2096513 : Blo 1100624 2096513 := bstep (se 2 (by rfl) ⟨786192, by rfl⟩ : syracuseStep 2096513 = 1572385) B1572385
theorem B3538379 : Blo 1100624 3538379 := bstep (se 1 (by rfl) ⟨2653784, by rfl⟩ : syracuseStep 3538379 = 5307569) B5307569
theorem B4718027 : Blo 1100624 4718027 := bstep (se 1 (by rfl) ⟨3538520, by rfl⟩ : syracuseStep 4718027 = 7077041) B7077041
theorem B1572311 : Blo 1100624 1572311 := bstep (se 1 (by rfl) ⟨1179233, by rfl⟩ : syracuseStep 1572311 = 2358467) B2358467
theorem B6290905 : Blo 1100624 6290905 := bstep (se 2 (by rfl) ⟨2359089, by rfl⟩ : syracuseStep 6290905 = 4718179) B4718179
theorem B4193815 : Blo 1100624 4193815 := bstep (se 1 (by rfl) ⟨3145361, by rfl⟩ : syracuseStep 4193815 = 6290723) B6290723
theorem B2096779 : Blo 1100624 2096779 := bstep (se 1 (by rfl) ⟨1572584, by rfl⟩ : syracuseStep 2096779 = 3145169) B3145169
theorem B7077527 : Blo 1100624 7077527 := bstep (se 1 (by rfl) ⟨5308145, by rfl⟩ : syracuseStep 7077527 = 10616291) B10616291
theorem B1769177 : Blo 1100624 1769177 := bstep (se 2 (by rfl) ⟨663441, by rfl⟩ : syracuseStep 1769177 = 1326883) B1326883
theorem B2982263 : Blo 1100624 2982263 := bstep (se 1 (by rfl) ⟨2236697, by rfl⟩ : syracuseStep 2982263 = 4473395) B4473395
theorem B6357527 : Blo 1100624 6357527 := bstep (se 1 (by rfl) ⟨4768145, by rfl⟩ : syracuseStep 6357527 = 9536291) B9536291
theorem B4653883 : Blo 1100624 4653883 := bstep (se 1 (by rfl) ⟨3490412, by rfl⟩ : syracuseStep 4653883 = 6980825) B6980825
theorem B80413667 : Blo 1100624 80413667 := bstep (se 1 (by rfl) ⟨60310250, by rfl⟩ : syracuseStep 80413667 = 120620501) B120620501
theorem B15893819 : Blo 1100624 15893819 := bstep (se 1 (by rfl) ⟨11920364, by rfl⟩ : syracuseStep 15893819 = 23840729) B23840729
theorem B7538129 : Blo 1100624 7538129 := bstep (se 2 (by rfl) ⟨2826798, by rfl⟩ : syracuseStep 7538129 = 5653597) B5653597
theorem B5572637 : Blo 1100624 5572637 := bstep (se 3 (by rfl) ⟨1044869, by rfl⟩ : syracuseStep 5572637 = 2089739) B2089739
theorem B2787443 : Blo 1100624 2787443 := bstep (se 1 (by rfl) ⟨2090582, by rfl⟩ : syracuseStep 2787443 = 4181165) B4181165
theorem B3180887 : Blo 1100624 3180887 := bstep (se 1 (by rfl) ⟨2385665, by rfl⟩ : syracuseStep 3180887 = 4771331) B4771331
theorem B15895025 : Blo 1100624 15895025 := bstep (se 2 (by rfl) ⟨5960634, by rfl⟩ : syracuseStep 15895025 = 11921269) B11921269
theorem B5573123 : Blo 1100624 5573123 := bstep (se 1 (by rfl) ⟨4179842, by rfl⟩ : syracuseStep 5573123 = 8359685) B8359685
theorem B2787959 : Blo 1100624 2787959 := bstep (se 1 (by rfl) ⟨2090969, by rfl⟩ : syracuseStep 2787959 = 4181939) B4181939
theorem B2296505 : Blo 1100624 2296505 := bstep (se 2 (by rfl) ⟨861189, by rfl⟩ : syracuseStep 2296505 = 1722379) B1722379
theorem B2788951 : Blo 1100624 2788951 := bstep (se 1 (by rfl) ⟨2091713, by rfl⟩ : syracuseStep 2788951 = 4183427) B4183427
theorem B1412743 : Blo 1100624 1412743 := bstep (se 1 (by rfl) ⟨1059557, by rfl⟩ : syracuseStep 1412743 = 2119115) B2119115
theorem B2789255 : Blo 1100624 2789255 := bstep (se 1 (by rfl) ⟨2091941, by rfl⟩ : syracuseStep 2789255 = 4183883) B4183883
theorem B2789387 : Blo 1100624 2789387 := bstep (se 1 (by rfl) ⟨2092040, by rfl⟩ : syracuseStep 2789387 = 4184081) B4184081
theorem B5574743 : Blo 1100624 5574743 := bstep (se 1 (by rfl) ⟨4181057, by rfl⟩ : syracuseStep 5574743 = 8362115) B8362115
theorem B2789903 : Blo 1100624 2789903 := bstep (se 1 (by rfl) ⟨2092427, by rfl⟩ : syracuseStep 2789903 = 4184855) B4184855
theorem B5575229 : Blo 1100624 5575229 := bstep (se 3 (by rfl) ⟨1045355, by rfl⟩ : syracuseStep 5575229 = 2090711) B2090711
theorem B2790035 : Blo 1100624 2790035 := bstep (se 1 (by rfl) ⟨2092526, by rfl⟩ : syracuseStep 2790035 = 4185053) B4185053
theorem B5313433 : Blo 1100624 5313433 := bstep (se 2 (by rfl) ⟨1992537, by rfl⟩ : syracuseStep 5313433 = 3985075) B3985075
theorem B3347543 : Blo 1100624 3347543 := bstep (se 1 (by rfl) ⟨2510657, by rfl⟩ : syracuseStep 3347543 = 5021315) B5021315
theorem B3347773 : Blo 1100624 3347773 := bstep (se 3 (by rfl) ⟨627707, by rfl⟩ : syracuseStep 3347773 = 1255415) B1255415
theorem B1513033 : Blo 1100624 1513033 := bstep (se 2 (by rfl) ⟨567387, by rfl⟩ : syracuseStep 1513033 = 1134775) B1134775
theorem B2791169 : Blo 1100624 2791169 := bstep (se 2 (by rfl) ⟨1046688, by rfl⟩ : syracuseStep 2791169 = 2093377) B2093377
theorem B1414955 : Blo 1100624 1414955 := bstep (se 1 (by rfl) ⟨1061216, by rfl⟩ : syracuseStep 1414955 = 2122433) B2122433
theorem B16946995 : Blo 1100624 16946995 := bstep (se 1 (by rfl) ⟨12710246, by rfl⟩ : syracuseStep 16946995 = 25420493) B25420493
theorem B2791543 : Blo 1100624 2791543 := bstep (se 1 (by rfl) ⟨2093657, by rfl⟩ : syracuseStep 2791543 = 4187315) B4187315
theorem B5577011 : Blo 1100624 5577011 := bstep (se 1 (by rfl) ⟨4182758, by rfl⟩ : syracuseStep 5577011 = 8365517) B8365517
theorem B8952211 : Blo 1100624 8952211 := bstep (se 1 (by rfl) ⟨6714158, by rfl⟩ : syracuseStep 8952211 = 13428317) B13428317
theorem B5970323 : Blo 1100624 5970323 := bstep (se 1 (by rfl) ⟨4477742, by rfl⟩ : syracuseStep 5970323 = 8955485) B8955485
theorem B15112595 : Blo 1100624 15112595 := bstep (se 1 (by rfl) ⟨11334446, by rfl⟩ : syracuseStep 15112595 = 22668893) B22668893
theorem B6035915 : Blo 1100624 6035915 := bstep (se 1 (by rfl) ⟨4526936, by rfl⟩ : syracuseStep 6035915 = 9053873) B9053873
theorem B7936555 : Blo 1100624 7936555 := bstep (se 1 (by rfl) ⟨5952416, by rfl⟩ : syracuseStep 7936555 = 11904833) B11904833
theorem B2791979 : Blo 1100624 2791979 := bstep (se 1 (by rfl) ⟨2093984, by rfl⟩ : syracuseStep 2791979 = 4187969) B4187969
theorem B5577335 : Blo 1100624 5577335 := bstep (se 1 (by rfl) ⟨4183001, by rfl⟩ : syracuseStep 5577335 = 8366003) B8366003
theorem B8493761 : Blo 1100624 8493761 := bstep (se 2 (by rfl) ⟨3185160, by rfl⟩ : syracuseStep 8493761 = 6370321) B6370321
theorem B3971855 : Blo 1100624 3971855 := bstep (se 1 (by rfl) ⟨2978891, by rfl⟩ : syracuseStep 3971855 = 5957783) B5957783
theorem B3578759 : Blo 1100624 3578759 := bstep (se 1 (by rfl) ⟨2684069, by rfl⟩ : syracuseStep 3578759 = 5368139) B5368139
theorem B28613837 : Blo 1100624 28613837 := bstep (se 3 (by rfl) ⟨5365094, by rfl⟩ : syracuseStep 28613837 = 10730189) B10730189
theorem B2792819 : Blo 1100624 2792819 := bstep (se 1 (by rfl) ⟨2094614, by rfl⟩ : syracuseStep 2792819 = 4189229) B4189229
theorem B2792839 : Blo 1100624 2792839 := bstep (se 1 (by rfl) ⟨2094629, by rfl⟩ : syracuseStep 2792839 = 4189259) B4189259
theorem B12557753 : Blo 1100624 12557753 := bstep (se 2 (by rfl) ⟨4709157, by rfl⟩ : syracuseStep 12557753 = 9418315) B9418315
theorem B19111373 : Blo 1100624 19111373 := bstep (se 3 (by rfl) ⟨3583382, by rfl⟩ : syracuseStep 19111373 = 7166765) B7166765
theorem B5578307 : Blo 1100624 5578307 := bstep (se 1 (by rfl) ⟨4183730, by rfl⟩ : syracuseStep 5578307 = 8367461) B8367461
theorem B3350135 : Blo 1100624 3350135 := bstep (se 1 (by rfl) ⟨2512601, by rfl⟩ : syracuseStep 3350135 = 5025203) B5025203
theorem B2793113 : Blo 1100624 2793113 := bstep (se 2 (by rfl) ⟨1047417, by rfl⟩ : syracuseStep 2793113 = 2094835) B2094835
theorem B8953537 : Blo 1100624 8953537 := bstep (se 2 (by rfl) ⟨3357576, by rfl⟩ : syracuseStep 8953537 = 6715153) B6715153
theorem B2793275 : Blo 1100624 2793275 := bstep (se 1 (by rfl) ⟨2094956, by rfl⟩ : syracuseStep 2793275 = 4189913) B4189913
theorem B5578631 : Blo 1100624 5578631 := bstep (se 1 (by rfl) ⟨4183973, by rfl⟩ : syracuseStep 5578631 = 8367947) B8367947
theorem B2793487 : Blo 1100624 2793487 := bstep (se 1 (by rfl) ⟨2095115, by rfl⟩ : syracuseStep 2793487 = 4190231) B4190231
theorem B8954057 : Blo 1100624 8954057 := bstep (se 2 (by rfl) ⟨3357771, by rfl⟩ : syracuseStep 8954057 = 6715543) B6715543
theorem B19374353 : Blo 1100624 19374353 := bstep (se 2 (by rfl) ⟨7265382, by rfl⟩ : syracuseStep 19374353 = 14530765) B14530765
theorem B2793761 : Blo 1100624 2793761 := bstep (se 2 (by rfl) ⟨1047660, by rfl⟩ : syracuseStep 2793761 = 2095321) B2095321
theorem B3973643 : Blo 1100624 3973643 := bstep (se 1 (by rfl) ⟨2980232, by rfl⟩ : syracuseStep 3973643 = 5960465) B5960465
theorem B13410845 : Blo 1100624 13410845 := bstep (se 3 (by rfl) ⟨2514533, by rfl⟩ : syracuseStep 13410845 = 5029067) B5029067
theorem B13083353 : Blo 1100624 13083353 := bstep (se 2 (by rfl) ⟨4906257, by rfl⟩ : syracuseStep 13083353 = 9812515) B9812515
theorem B11903759 : Blo 1100624 11903759 := bstep (se 1 (by rfl) ⟨8927819, by rfl⟩ : syracuseStep 11903759 = 17855639) B17855639
theorem B34382627 : Blo 1100624 34382627 := bstep (se 1 (by rfl) ⟨25786970, by rfl⟩ : syracuseStep 34382627 = 51573941) B51573941
theorem B21767093 : Blo 1100624 21767093 := bstep (se 5 (by rfl) ⟨1020332, by rfl⟩ : syracuseStep 21767093 = 2040665) B2040665
theorem B2794763 : Blo 1100624 2794763 := bstep (se 1 (by rfl) ⟨2096072, by rfl⟩ : syracuseStep 2794763 = 4192145) B4192145
theorem B6268535 : Blo 1100624 6268535 := bstep (se 1 (by rfl) ⟨4701401, by rfl⟩ : syracuseStep 6268535 = 9402803) B9402803
theorem B2795411 : Blo 1100624 2795411 := bstep (se 1 (by rfl) ⟨2096558, by rfl⟩ : syracuseStep 2795411 = 4193117) B4193117
theorem B7055383 : Blo 1100624 7055383 := bstep (se 1 (by rfl) ⟨5291537, by rfl⟩ : syracuseStep 7055383 = 10583075) B10583075
theorem B3778589 : Blo 1100624 3778589 := bstep (se 3 (by rfl) ⟨708485, by rfl⟩ : syracuseStep 3778589 = 1416971) B1416971
theorem B3057707 : Blo 1100624 3057707 := bstep (se 1 (by rfl) ⟨2293280, by rfl⟩ : syracuseStep 3057707 = 4586561) B4586561
theorem B2795705 : Blo 1100624 2795705 := bstep (se 2 (by rfl) ⟨1048389, by rfl⟩ : syracuseStep 2795705 = 2096779) B2096779
theorem B7940915 : Blo 1100624 7940915 := bstep (se 1 (by rfl) ⟨5955686, by rfl⟩ : syracuseStep 7940915 = 11911373) B11911373
theorem B3976121 : Blo 1100624 3976121 := bstep (se 2 (by rfl) ⟨1491045, by rfl⟩ : syracuseStep 3976121 = 2982091) B2982091
theorem B15871265 : Blo 1100624 15871265 := bstep (se 2 (by rfl) ⟨5951724, by rfl⟩ : syracuseStep 15871265 = 11903449) B11903449
theorem B5582195 : Blo 1100624 5582195 := bstep (se 1 (by rfl) ⟨4186646, by rfl⟩ : syracuseStep 5582195 = 8373293) B8373293
theorem B248491405 : Blo 1100624 248491405 := bstep (se 3 (by rfl) ⟨46592138, by rfl⟩ : syracuseStep 248491405 = 93184277) B93184277
theorem B6270493 : Blo 1100624 6270493 := bstep (se 3 (by rfl) ⟨1175717, by rfl⟩ : syracuseStep 6270493 = 2351435) B2351435
theorem B21507763 : Blo 1100624 21507763 := bstep (se 1 (by rfl) ⟨16130822, by rfl⟩ : syracuseStep 21507763 = 32261645) B32261645
theorem B5451553 : Blo 1100624 5451553 := bstep (se 2 (by rfl) ⟨2044332, by rfl⟩ : syracuseStep 5451553 = 4088665) B4088665
theorem B3714875 : Blo 1100624 3714875 := bstep (se 1 (by rfl) ⟨2786156, by rfl⟩ : syracuseStep 3714875 = 5572313) B5572313
theorem B5582681 : Blo 1100624 5582681 := bstep (se 2 (by rfl) ⟨2093505, by rfl⟩ : syracuseStep 5582681 = 4187011) B4187011
theorem B6271019 : Blo 1100624 6271019 := bstep (se 1 (by rfl) ⟨4703264, by rfl⟩ : syracuseStep 6271019 = 9406529) B9406529
theorem B26816629 : Blo 1100624 26816629 := bstep (se 5 (by rfl) ⟨1257029, by rfl⟩ : syracuseStep 26816629 = 2514059) B2514059
theorem B18821321 : Blo 1100624 18821321 := bstep (se 2 (by rfl) ⟨7057995, by rfl⟩ : syracuseStep 18821321 = 14115991) B14115991
theorem B1650959 : Blo 1100624 1650959 := bstep (se 1 (by rfl) ⟨1238219, by rfl⟩ : syracuseStep 1650959 = 2476439) B2476439
theorem B3715361 : Blo 1100624 3715361 := bstep (se 2 (by rfl) ⟨1393260, by rfl⟩ : syracuseStep 3715361 = 2786521) B2786521
theorem B1651001 : Blo 1100624 1651001 := bstep (se 2 (by rfl) ⟨619125, by rfl⟩ : syracuseStep 1651001 = 1238251) B1238251
theorem B1651079 : Blo 1100624 1651079 := bstep (se 1 (by rfl) ⟨1238309, by rfl⟩ : syracuseStep 1651079 = 2476619) B2476619
theorem B1651115 : Blo 1100624 1651115 := bstep (se 1 (by rfl) ⟨1238336, by rfl⟩ : syracuseStep 1651115 = 2476673) B2476673
theorem B1651145 : Blo 1100624 1651145 := bstep (se 2 (by rfl) ⟨619179, by rfl⟩ : syracuseStep 1651145 = 1238359) B1238359
theorem B1651259 : Blo 1100624 1651259 := bstep (se 1 (by rfl) ⟨1238444, by rfl⟩ : syracuseStep 1651259 = 2476889) B2476889
theorem B1651319 : Blo 1100624 1651319 := bstep (se 1 (by rfl) ⟨1238489, by rfl⟩ : syracuseStep 1651319 = 2476979) B2476979
theorem B1651343 : Blo 1100624 1651343 := bstep (se 1 (by rfl) ⟨1238507, by rfl⟩ : syracuseStep 1651343 = 2477015) B2477015
theorem B1651385 : Blo 1100624 1651385 := bstep (se 2 (by rfl) ⟨619269, by rfl⟩ : syracuseStep 1651385 = 1238539) B1238539
theorem B1651463 : Blo 1100624 1651463 := bstep (se 1 (by rfl) ⟨1238597, by rfl⟩ : syracuseStep 1651463 = 2477195) B2477195
theorem B1651499 : Blo 1100624 1651499 := bstep (se 1 (by rfl) ⟨1238624, by rfl⟩ : syracuseStep 1651499 = 2477249) B2477249
theorem B1651529 : Blo 1100624 1651529 := bstep (se 2 (by rfl) ⟨619323, by rfl⟩ : syracuseStep 1651529 = 1238647) B1238647
theorem B3715955 : Blo 1100624 3715955 := bstep (se 1 (by rfl) ⟨2786966, by rfl⟩ : syracuseStep 3715955 = 5573933) B5573933
theorem B1651643 : Blo 1100624 1651643 := bstep (se 1 (by rfl) ⟨1238732, by rfl⟩ : syracuseStep 1651643 = 2477465) B2477465
theorem B1651703 : Blo 1100624 1651703 := bstep (se 1 (by rfl) ⟨1238777, by rfl⟩ : syracuseStep 1651703 = 2477555) B2477555
theorem B1651727 : Blo 1100624 1651727 := bstep (se 1 (by rfl) ⟨1238795, by rfl⟩ : syracuseStep 1651727 = 2477591) B2477591
theorem B1651769 : Blo 1100624 1651769 := bstep (se 2 (by rfl) ⟨619413, by rfl⟩ : syracuseStep 1651769 = 1238827) B1238827
theorem B2864243 : Blo 1100624 2864243 := bstep (se 1 (by rfl) ⟨2148182, by rfl⟩ : syracuseStep 2864243 = 4296365) B4296365
theorem B4469879 : Blo 1100624 4469879 := bstep (se 1 (by rfl) ⟨3352409, by rfl⟩ : syracuseStep 4469879 = 6704819) B6704819
theorem B1651847 : Blo 1100624 1651847 := bstep (se 1 (by rfl) ⟨1238885, by rfl⟩ : syracuseStep 1651847 = 2477771) B2477771
theorem B1651883 : Blo 1100624 1651883 := bstep (se 1 (by rfl) ⟨1238912, by rfl⟩ : syracuseStep 1651883 = 2477825) B2477825
theorem B1488073 : Blo 1100624 1488073 := bstep (se 2 (by rfl) ⟨558027, by rfl⟩ : syracuseStep 1488073 = 1116055) B1116055
theorem B1651913 : Blo 1100624 1651913 := bstep (se 2 (by rfl) ⟨619467, by rfl⟩ : syracuseStep 1651913 = 1238935) B1238935
theorem B1652027 : Blo 1100624 1652027 := bstep (se 1 (by rfl) ⟨1239020, by rfl⟩ : syracuseStep 1652027 = 2478041) B2478041
theorem B21804389 : Blo 1100624 21804389 := bstep (se 4 (by rfl) ⟨2044161, by rfl⟩ : syracuseStep 21804389 = 4088323) B4088323
theorem B1652087 : Blo 1100624 1652087 := bstep (se 1 (by rfl) ⟨1239065, by rfl⟩ : syracuseStep 1652087 = 2478131) B2478131
theorem B20428163 : Blo 1100624 20428163 := bstep (se 1 (by rfl) ⟨15321122, by rfl⟩ : syracuseStep 20428163 = 30642245) B30642245
theorem B1652111 : Blo 1100624 1652111 := bstep (se 1 (by rfl) ⟨1239083, by rfl⟩ : syracuseStep 1652111 = 2478167) B2478167
theorem B1652153 : Blo 1100624 1652153 := bstep (se 2 (by rfl) ⟨619557, by rfl⟩ : syracuseStep 1652153 = 1239115) B1239115
theorem B10597837 : Blo 1100624 10597837 := bstep (se 3 (by rfl) ⟨1987094, by rfl⟩ : syracuseStep 10597837 = 3974189) B3974189
theorem B6272477 : Blo 1100624 6272477 := bstep (se 3 (by rfl) ⟨1176089, by rfl⟩ : syracuseStep 6272477 = 2352179) B2352179
theorem B1652231 : Blo 1100624 1652231 := bstep (se 1 (by rfl) ⟨1239173, by rfl⟩ : syracuseStep 1652231 = 2478347) B2478347
theorem B8599069 : Blo 1100624 8599069 := bstep (se 3 (by rfl) ⟨1612325, by rfl⟩ : syracuseStep 8599069 = 3224651) B3224651
theorem B1652267 : Blo 1100624 1652267 := bstep (se 1 (by rfl) ⟨1239200, by rfl⟩ : syracuseStep 1652267 = 2478401) B2478401
theorem B1652297 : Blo 1100624 1652297 := bstep (se 2 (by rfl) ⟨619611, by rfl⟩ : syracuseStep 1652297 = 1239223) B1239223
theorem B1652411 : Blo 1100624 1652411 := bstep (se 1 (by rfl) ⟨1239308, by rfl⟩ : syracuseStep 1652411 = 2478617) B2478617
theorem B1652471 : Blo 1100624 1652471 := bstep (se 1 (by rfl) ⟨1239353, by rfl⟩ : syracuseStep 1652471 = 2478707) B2478707
theorem B1652495 : Blo 1100624 1652495 := bstep (se 1 (by rfl) ⟨1239371, by rfl⟩ : syracuseStep 1652495 = 2478743) B2478743
theorem B1652537 : Blo 1100624 1652537 := bstep (se 2 (by rfl) ⟨619701, by rfl⟩ : syracuseStep 1652537 = 1239403) B1239403
theorem B1488775 : Blo 1100624 1488775 := bstep (se 1 (by rfl) ⟨1116581, by rfl⟩ : syracuseStep 1488775 = 2233163) B2233163
theorem B1652615 : Blo 1100624 1652615 := bstep (se 1 (by rfl) ⟨1239461, by rfl⟩ : syracuseStep 1652615 = 2478923) B2478923
theorem B5584787 : Blo 1100624 5584787 := bstep (se 1 (by rfl) ⟨4188590, by rfl⟩ : syracuseStep 5584787 = 8377181) B8377181
theorem B1652651 : Blo 1100624 1652651 := bstep (se 1 (by rfl) ⟨1239488, by rfl⟩ : syracuseStep 1652651 = 2478977) B2478977
theorem B1652681 : Blo 1100624 1652681 := bstep (se 2 (by rfl) ⟨619755, by rfl⟩ : syracuseStep 1652681 = 1239511) B1239511
theorem B1325047 : Blo 1100624 1325047 := bstep (se 1 (by rfl) ⟨993785, by rfl⟩ : syracuseStep 1325047 = 1987571) B1987571
theorem B1652795 : Blo 1100624 1652795 := bstep (se 1 (by rfl) ⟨1239596, by rfl⟩ : syracuseStep 1652795 = 2479193) B2479193
theorem B1652855 : Blo 1100624 1652855 := bstep (se 1 (by rfl) ⟨1239641, by rfl⟩ : syracuseStep 1652855 = 2479283) B2479283
theorem B1652879 : Blo 1100624 1652879 := bstep (se 1 (by rfl) ⟨1239659, by rfl⟩ : syracuseStep 1652879 = 2479319) B2479319
theorem B1652921 : Blo 1100624 1652921 := bstep (se 2 (by rfl) ⟨619845, by rfl⟩ : syracuseStep 1652921 = 1239691) B1239691
theorem B8370377 : Blo 1100624 8370377 := bstep (se 2 (by rfl) ⟨3138891, by rfl⟩ : syracuseStep 8370377 = 6277783) B6277783
theorem B1652999 : Blo 1100624 1652999 := bstep (se 1 (by rfl) ⟨1239749, by rfl⟩ : syracuseStep 1652999 = 2479499) B2479499
theorem B1653035 : Blo 1100624 1653035 := bstep (se 1 (by rfl) ⟨1239776, by rfl⟩ : syracuseStep 1653035 = 2479553) B2479553
theorem B1653065 : Blo 1100624 1653065 := bstep (se 2 (by rfl) ⟨619899, by rfl⟩ : syracuseStep 1653065 = 1239799) B1239799
theorem B1653179 : Blo 1100624 1653179 := bstep (se 1 (by rfl) ⟨1239884, by rfl⟩ : syracuseStep 1653179 = 2479769) B2479769
theorem B1653239 : Blo 1100624 1653239 := bstep (se 1 (by rfl) ⟨1239929, by rfl⟩ : syracuseStep 1653239 = 2479859) B2479859
theorem B1653263 : Blo 1100624 1653263 := bstep (se 1 (by rfl) ⟨1239947, by rfl⟩ : syracuseStep 1653263 = 2479895) B2479895
theorem B1653305 : Blo 1100624 1653305 := bstep (se 2 (by rfl) ⟨619989, by rfl⟩ : syracuseStep 1653305 = 1239979) B1239979
theorem B1653383 : Blo 1100624 1653383 := bstep (se 1 (by rfl) ⟨1240037, by rfl⟩ : syracuseStep 1653383 = 2480075) B2480075
theorem B1653419 : Blo 1100624 1653419 := bstep (se 1 (by rfl) ⟨1240064, by rfl⟩ : syracuseStep 1653419 = 2480129) B2480129
theorem B1653449 : Blo 1100624 1653449 := bstep (se 2 (by rfl) ⟨620043, by rfl⟩ : syracuseStep 1653449 = 1240087) B1240087
theorem B1653563 : Blo 1100624 1653563 := bstep (se 1 (by rfl) ⟨1240172, by rfl⟩ : syracuseStep 1653563 = 2480345) B2480345
theorem B1653623 : Blo 1100624 1653623 := bstep (se 1 (by rfl) ⟨1240217, by rfl⟩ : syracuseStep 1653623 = 2480435) B2480435
theorem B1653647 : Blo 1100624 1653647 := bstep (se 1 (by rfl) ⟨1240235, by rfl⟩ : syracuseStep 1653647 = 2480471) B2480471
theorem B1653689 : Blo 1100624 1653689 := bstep (se 2 (by rfl) ⟨620133, by rfl⟩ : syracuseStep 1653689 = 1240267) B1240267
theorem B1653767 : Blo 1100624 1653767 := bstep (se 1 (by rfl) ⟨1240325, by rfl⟩ : syracuseStep 1653767 = 2480651) B2480651
theorem B1653803 : Blo 1100624 1653803 := bstep (se 1 (by rfl) ⟨1240352, by rfl⟩ : syracuseStep 1653803 = 2480705) B2480705
theorem B1653833 : Blo 1100624 1653833 := bstep (se 2 (by rfl) ⟨620187, by rfl⟩ : syracuseStep 1653833 = 1240375) B1240375
theorem B1653947 : Blo 1100624 1653947 := bstep (se 1 (by rfl) ⟨1240460, by rfl⟩ : syracuseStep 1653947 = 2480921) B2480921
theorem B1654007 : Blo 1100624 1654007 := bstep (se 1 (by rfl) ⟨1240505, by rfl⟩ : syracuseStep 1654007 = 2481011) B2481011
theorem B1654031 : Blo 1100624 1654031 := bstep (se 1 (by rfl) ⟨1240523, by rfl⟩ : syracuseStep 1654031 = 2481047) B2481047
theorem B1654073 : Blo 1100624 1654073 := bstep (se 2 (by rfl) ⟨620277, by rfl⟩ : syracuseStep 1654073 = 1240555) B1240555
theorem B1654151 : Blo 1100624 1654151 := bstep (se 1 (by rfl) ⟨1240613, by rfl⟩ : syracuseStep 1654151 = 2481227) B2481227
theorem B3718547 : Blo 1100624 3718547 := bstep (se 1 (by rfl) ⟨2788910, by rfl⟩ : syracuseStep 3718547 = 5577821) B5577821
theorem B1654187 : Blo 1100624 1654187 := bstep (se 1 (by rfl) ⟨1240640, by rfl⟩ : syracuseStep 1654187 = 2481281) B2481281
theorem B1654217 : Blo 1100624 1654217 := bstep (se 2 (by rfl) ⟨620331, by rfl⟩ : syracuseStep 1654217 = 1240663) B1240663
theorem B1654331 : Blo 1100624 1654331 := bstep (se 1 (by rfl) ⟨1240748, by rfl⟩ : syracuseStep 1654331 = 2481497) B2481497
theorem B1654391 : Blo 1100624 1654391 := bstep (se 1 (by rfl) ⟨1240793, by rfl⟩ : syracuseStep 1654391 = 2481587) B2481587
theorem B1654415 : Blo 1100624 1654415 := bstep (se 1 (by rfl) ⟨1240811, by rfl⟩ : syracuseStep 1654415 = 2481623) B2481623
theorem B1654457 : Blo 1100624 1654457 := bstep (se 2 (by rfl) ⟨620421, by rfl⟩ : syracuseStep 1654457 = 1240843) B1240843
theorem B1654535 : Blo 1100624 1654535 := bstep (se 1 (by rfl) ⟨1240901, by rfl⟩ : syracuseStep 1654535 = 2481803) B2481803
theorem B1654571 : Blo 1100624 1654571 := bstep (se 1 (by rfl) ⟨1240928, by rfl⟩ : syracuseStep 1654571 = 2481857) B2481857
theorem B6274867 : Blo 1100624 6274867 := bstep (se 1 (by rfl) ⟨4706150, by rfl⟩ : syracuseStep 6274867 = 9412301) B9412301
theorem B1654601 : Blo 1100624 1654601 := bstep (se 2 (by rfl) ⟨620475, by rfl⟩ : syracuseStep 1654601 = 1240951) B1240951
theorem B1654715 : Blo 1100624 1654715 := bstep (se 1 (by rfl) ⟨1241036, by rfl⟩ : syracuseStep 1654715 = 2482073) B2482073
theorem B1654775 : Blo 1100624 1654775 := bstep (se 1 (by rfl) ⟨1241081, by rfl⟩ : syracuseStep 1654775 = 2482163) B2482163
theorem B1654799 : Blo 1100624 1654799 := bstep (se 1 (by rfl) ⟨1241099, by rfl⟩ : syracuseStep 1654799 = 2482199) B2482199
theorem B1654841 : Blo 1100624 1654841 := bstep (se 2 (by rfl) ⟨620565, by rfl⟩ : syracuseStep 1654841 = 1241131) B1241131
theorem B1654919 : Blo 1100624 1654919 := bstep (se 1 (by rfl) ⟨1241189, by rfl⟩ : syracuseStep 1654919 = 2482379) B2482379
theorem B1654955 : Blo 1100624 1654955 := bstep (se 1 (by rfl) ⟨1241216, by rfl⟩ : syracuseStep 1654955 = 2482433) B2482433
theorem B1654985 : Blo 1100624 1654985 := bstep (se 2 (by rfl) ⟨620619, by rfl⟩ : syracuseStep 1654985 = 1241239) B1241239
theorem B4702445 : Blo 1100624 4702445 := bstep (se 3 (by rfl) ⟨881708, by rfl⟩ : syracuseStep 4702445 = 1763417) B1763417
theorem B7061741 : Blo 1100624 7061741 := bstep (se 3 (by rfl) ⟨1324076, by rfl⟩ : syracuseStep 7061741 = 2648153) B2648153
theorem B1491257 : Blo 1100624 1491257 := bstep (se 2 (by rfl) ⟨559221, by rfl⟩ : syracuseStep 1491257 = 1118443) B1118443
theorem B1655099 : Blo 1100624 1655099 := bstep (se 1 (by rfl) ⟨1241324, by rfl⟩ : syracuseStep 1655099 = 2482649) B2482649
theorem B1655159 : Blo 1100624 1655159 := bstep (se 1 (by rfl) ⟨1241369, by rfl⟩ : syracuseStep 1655159 = 2482739) B2482739
theorem B1655183 : Blo 1100624 1655183 := bstep (se 1 (by rfl) ⟨1241387, by rfl⟩ : syracuseStep 1655183 = 2482775) B2482775
theorem B1655225 : Blo 1100624 1655225 := bstep (se 2 (by rfl) ⟨620709, by rfl⟩ : syracuseStep 1655225 = 1241419) B1241419
theorem B1655303 : Blo 1100624 1655303 := bstep (se 1 (by rfl) ⟨1241477, by rfl⟩ : syracuseStep 1655303 = 2482955) B2482955
theorem B1393195 : Blo 1100624 1393195 := bstep (se 1 (by rfl) ⟨1044896, by rfl⟩ : syracuseStep 1393195 = 2089793) B2089793
theorem B1655339 : Blo 1100624 1655339 := bstep (se 1 (by rfl) ⟨1241504, by rfl⟩ : syracuseStep 1655339 = 2483009) B2483009
theorem B1655369 : Blo 1100624 1655369 := bstep (se 2 (by rfl) ⟨620763, by rfl⟩ : syracuseStep 1655369 = 1241527) B1241527
theorem B4473463 : Blo 1100624 4473463 := bstep (se 1 (by rfl) ⟨3355097, by rfl⟩ : syracuseStep 4473463 = 6710195) B6710195
theorem B1655483 : Blo 1100624 1655483 := bstep (se 1 (by rfl) ⟨1241612, by rfl⟩ : syracuseStep 1655483 = 2483225) B2483225
theorem B1655543 : Blo 1100624 1655543 := bstep (se 1 (by rfl) ⟨1241657, by rfl⟩ : syracuseStep 1655543 = 2483315) B2483315
theorem B5030657 : Blo 1100624 5030657 := bstep (se 2 (by rfl) ⟨1886496, by rfl⟩ : syracuseStep 5030657 = 3772993) B3772993
theorem B3719951 : Blo 1100624 3719951 := bstep (se 1 (by rfl) ⟨2789963, by rfl⟩ : syracuseStep 3719951 = 5579927) B5579927
theorem B1655567 : Blo 1100624 1655567 := bstep (se 1 (by rfl) ⟨1241675, by rfl⟩ : syracuseStep 1655567 = 2483351) B2483351
theorem B1655609 : Blo 1100624 1655609 := bstep (se 2 (by rfl) ⟨620853, by rfl⟩ : syracuseStep 1655609 = 1241707) B1241707
theorem B1655687 : Blo 1100624 1655687 := bstep (se 1 (by rfl) ⟨1241765, by rfl⟩ : syracuseStep 1655687 = 2483531) B2483531
theorem B4703129 : Blo 1100624 4703129 := bstep (se 2 (by rfl) ⟨1763673, by rfl⟩ : syracuseStep 4703129 = 3527347) B3527347
theorem B5587865 : Blo 1100624 5587865 := bstep (se 2 (by rfl) ⟨2095449, by rfl⟩ : syracuseStep 5587865 = 4190899) B4190899
theorem B1655723 : Blo 1100624 1655723 := bstep (se 1 (by rfl) ⟨1241792, by rfl⟩ : syracuseStep 1655723 = 2483585) B2483585
theorem B1655753 : Blo 1100624 1655753 := bstep (se 2 (by rfl) ⟨620907, by rfl⟩ : syracuseStep 1655753 = 1241815) B1241815
theorem B3720221 : Blo 1100624 3720221 := bstep (se 3 (by rfl) ⟨697541, by rfl⟩ : syracuseStep 3720221 = 1395083) B1395083
theorem B1983521 : Blo 1100624 1983521 := bstep (se 2 (by rfl) ⟨743820, by rfl⟩ : syracuseStep 1983521 = 1487641) B1487641
theorem B1655867 : Blo 1100624 1655867 := bstep (se 1 (by rfl) ⟨1241900, by rfl⟩ : syracuseStep 1655867 = 2483801) B2483801
theorem B1655927 : Blo 1100624 1655927 := bstep (se 1 (by rfl) ⟨1241945, by rfl⟩ : syracuseStep 1655927 = 2483891) B2483891
theorem B1655951 : Blo 1100624 1655951 := bstep (se 1 (by rfl) ⟨1241963, by rfl⟩ : syracuseStep 1655951 = 2483927) B2483927
theorem B1655993 : Blo 1100624 1655993 := bstep (se 2 (by rfl) ⟨620997, by rfl⟩ : syracuseStep 1655993 = 1241995) B1241995
theorem B6276325 : Blo 1100624 6276325 := bstep (se 4 (by rfl) ⟨588405, by rfl⟩ : syracuseStep 6276325 = 1176811) B1176811
theorem B1656071 : Blo 1100624 1656071 := bstep (se 1 (by rfl) ⟨1242053, by rfl⟩ : syracuseStep 1656071 = 2484107) B2484107
theorem B1656107 : Blo 1100624 1656107 := bstep (se 1 (by rfl) ⟨1242080, by rfl⟩ : syracuseStep 1656107 = 2484161) B2484161
theorem B1656137 : Blo 1100624 1656137 := bstep (se 2 (by rfl) ⟨621051, by rfl⟩ : syracuseStep 1656137 = 1242103) B1242103
theorem B1656251 : Blo 1100624 1656251 := bstep (se 1 (by rfl) ⟨1242188, by rfl⟩ : syracuseStep 1656251 = 2484377) B2484377
theorem B1394167 : Blo 1100624 1394167 := bstep (se 1 (by rfl) ⟨1045625, by rfl⟩ : syracuseStep 1394167 = 2091251) B2091251
theorem B1656311 : Blo 1100624 1656311 := bstep (se 1 (by rfl) ⟨1242233, by rfl⟩ : syracuseStep 1656311 = 2484467) B2484467
theorem B1656335 : Blo 1100624 1656335 := bstep (se 1 (by rfl) ⟨1242251, by rfl⟩ : syracuseStep 1656335 = 2484503) B2484503
theorem B1656377 : Blo 1100624 1656377 := bstep (se 2 (by rfl) ⟨621141, by rfl⟩ : syracuseStep 1656377 = 1242283) B1242283
theorem B3393085 : Blo 1100624 3393085 := bstep (se 3 (by rfl) ⟨636203, by rfl⟩ : syracuseStep 3393085 = 1272407) B1272407
theorem B1656455 : Blo 1100624 1656455 := bstep (se 1 (by rfl) ⟨1242341, by rfl⟩ : syracuseStep 1656455 = 2484683) B2484683
theorem B1656491 : Blo 1100624 1656491 := bstep (se 1 (by rfl) ⟨1242368, by rfl⟩ : syracuseStep 1656491 = 2484737) B2484737
theorem B1656521 : Blo 1100624 1656521 := bstep (se 2 (by rfl) ⟨621195, by rfl⟩ : syracuseStep 1656521 = 1242391) B1242391
theorem B5031695 : Blo 1100624 5031695 := bstep (se 1 (by rfl) ⟨3773771, by rfl⟩ : syracuseStep 5031695 = 7547543) B7547543
theorem B1394491 : Blo 1100624 1394491 := bstep (se 1 (by rfl) ⟨1045868, by rfl⟩ : syracuseStep 1394491 = 2091737) B2091737
theorem B1656635 : Blo 1100624 1656635 := bstep (se 1 (by rfl) ⟨1242476, by rfl⟩ : syracuseStep 1656635 = 2484953) B2484953
theorem B1656695 : Blo 1100624 1656695 := bstep (se 1 (by rfl) ⟨1242521, by rfl⟩ : syracuseStep 1656695 = 2485043) B2485043
theorem B1656719 : Blo 1100624 1656719 := bstep (se 1 (by rfl) ⟨1242539, by rfl⟩ : syracuseStep 1656719 = 2485079) B2485079
theorem B1656761 : Blo 1100624 1656761 := bstep (se 2 (by rfl) ⟨621285, by rfl⟩ : syracuseStep 1656761 = 1242571) B1242571
theorem B1656839 : Blo 1100624 1656839 := bstep (se 1 (by rfl) ⟨1242629, by rfl⟩ : syracuseStep 1656839 = 2485259) B2485259
theorem B1656875 : Blo 1100624 1656875 := bstep (se 1 (by rfl) ⟨1242656, by rfl⟩ : syracuseStep 1656875 = 2485313) B2485313
theorem B1656905 : Blo 1100624 1656905 := bstep (se 2 (by rfl) ⟨621339, by rfl⟩ : syracuseStep 1656905 = 1242679) B1242679
theorem B16107923 : Blo 1100624 16107923 := bstep (se 1 (by rfl) ⟨12080942, by rfl⟩ : syracuseStep 16107923 = 24161885) B24161885
theorem B3721625 : Blo 1100624 3721625 := bstep (se 2 (by rfl) ⟨1395609, by rfl⟩ : syracuseStep 3721625 = 2791219) B2791219
theorem B14109227 : Blo 1100624 14109227 := bstep (se 1 (by rfl) ⟨10581920, by rfl⟩ : syracuseStep 14109227 = 21163841) B21163841
theorem B2476691 : Blo 1100624 2476691 := bstep (se 1 (by rfl) ⟨1857518, by rfl⟩ : syracuseStep 2476691 = 3715037) B3715037
theorem B2476745 : Blo 1100624 2476745 := bstep (se 2 (by rfl) ⟨928779, by rfl⟩ : syracuseStep 2476745 = 1857559) B1857559
theorem B1395463 : Blo 1100624 1395463 := bstep (se 1 (by rfl) ⟨1046597, by rfl⟩ : syracuseStep 1395463 = 2093195) B2093195
theorem B4705057 : Blo 1100624 4705057 := bstep (se 2 (by rfl) ⟨1764396, by rfl⟩ : syracuseStep 4705057 = 3528793) B3528793
theorem B5950259 : Blo 1100624 5950259 := bstep (se 1 (by rfl) ⟨4462694, by rfl⟩ : syracuseStep 5950259 = 8925389) B8925389
theorem B1100679 : Blo 1100624 1100679 := bstep (se 1 (by rfl) ⟨825509, by rfl⟩ : syracuseStep 1100679 = 1651019) B1651019
theorem B1100687 : Blo 1100624 1100687 := bstep (se 1 (by rfl) ⟨825515, by rfl⟩ : syracuseStep 1100687 = 1651031) B1651031
theorem B1100731 : Blo 1100624 1100731 := bstep (se 1 (by rfl) ⟨825548, by rfl⟩ : syracuseStep 1100731 = 1651097) B1651097
theorem B1100807 : Blo 1100624 1100807 := bstep (se 1 (by rfl) ⟨825605, by rfl⟩ : syracuseStep 1100807 = 1651211) B1651211
theorem B1100815 : Blo 1100624 1100815 := bstep (se 1 (by rfl) ⟨825611, by rfl⟩ : syracuseStep 1100815 = 1651223) B1651223
theorem B1100859 : Blo 1100624 1100859 := bstep (se 1 (by rfl) ⟨825644, by rfl⟩ : syracuseStep 1100859 = 1651289) B1651289
theorem B3722327 : Blo 1100624 3722327 := bstep (se 1 (by rfl) ⟨2791745, by rfl⟩ : syracuseStep 3722327 = 5583491) B5583491
theorem B1100935 : Blo 1100624 1100935 := bstep (se 1 (by rfl) ⟨825701, by rfl⟩ : syracuseStep 1100935 = 1651403) B1651403
theorem B1100943 : Blo 1100624 1100943 := bstep (se 1 (by rfl) ⟨825707, by rfl⟩ : syracuseStep 1100943 = 1651415) B1651415
theorem B1395883 : Blo 1100624 1395883 := bstep (se 1 (by rfl) ⟨1046912, by rfl⟩ : syracuseStep 1395883 = 2093825) B2093825
theorem B1100987 : Blo 1100624 1100987 := bstep (se 1 (by rfl) ⟨825740, by rfl⟩ : syracuseStep 1100987 = 1651481) B1651481
theorem B1101063 : Blo 1100624 1101063 := bstep (se 1 (by rfl) ⟨825797, by rfl⟩ : syracuseStep 1101063 = 1651595) B1651595
theorem B1101071 : Blo 1100624 1101071 := bstep (se 1 (by rfl) ⟨825803, by rfl⟩ : syracuseStep 1101071 = 1651607) B1651607
theorem B1101115 : Blo 1100624 1101115 := bstep (se 1 (by rfl) ⟨825836, by rfl⟩ : syracuseStep 1101115 = 1651673) B1651673
theorem B2477447 : Blo 1100624 2477447 := bstep (se 1 (by rfl) ⟨1858085, by rfl⟩ : syracuseStep 2477447 = 3716171) B3716171
theorem B1101191 : Blo 1100624 1101191 := bstep (se 1 (by rfl) ⟨825893, by rfl⟩ : syracuseStep 1101191 = 1651787) B1651787
theorem B1101199 : Blo 1100624 1101199 := bstep (se 1 (by rfl) ⟨825899, by rfl⟩ : syracuseStep 1101199 = 1651799) B1651799
theorem B1396111 : Blo 1100624 1396111 := bstep (se 1 (by rfl) ⟨1047083, by rfl⟩ : syracuseStep 1396111 = 2094167) B2094167
theorem B5590457 : Blo 1100624 5590457 := bstep (se 2 (by rfl) ⟨2096421, by rfl⟩ : syracuseStep 5590457 = 4192843) B4192843
theorem B1101243 : Blo 1100624 1101243 := bstep (se 1 (by rfl) ⟨825932, by rfl⟩ : syracuseStep 1101243 = 1651865) B1651865
theorem B1101319 : Blo 1100624 1101319 := bstep (se 1 (by rfl) ⟨825989, by rfl⟩ : syracuseStep 1101319 = 1651979) B1651979
theorem B1101327 : Blo 1100624 1101327 := bstep (se 1 (by rfl) ⟨825995, by rfl⟩ : syracuseStep 1101327 = 1651991) B1651991
theorem B2477627 : Blo 1100624 2477627 := bstep (se 1 (by rfl) ⟨1858220, by rfl⟩ : syracuseStep 2477627 = 3716441) B3716441
theorem B1101371 : Blo 1100624 1101371 := bstep (se 1 (by rfl) ⟨826028, by rfl⟩ : syracuseStep 1101371 = 1652057) B1652057
theorem B3722813 : Blo 1100624 3722813 := bstep (se 3 (by rfl) ⟨698027, by rfl⟩ : syracuseStep 3722813 = 1396055) B1396055
theorem B1101447 : Blo 1100624 1101447 := bstep (se 1 (by rfl) ⟨826085, by rfl⟩ : syracuseStep 1101447 = 1652171) B1652171
theorem B1101455 : Blo 1100624 1101455 := bstep (se 1 (by rfl) ⟨826091, by rfl⟩ : syracuseStep 1101455 = 1652183) B1652183
theorem B2477753 : Blo 1100624 2477753 := bstep (se 2 (by rfl) ⟨929157, by rfl⟩ : syracuseStep 2477753 = 1858315) B1858315
theorem B1101499 : Blo 1100624 1101499 := bstep (se 1 (by rfl) ⟨826124, by rfl⟩ : syracuseStep 1101499 = 1652249) B1652249
theorem B1101575 : Blo 1100624 1101575 := bstep (se 1 (by rfl) ⟨826181, by rfl⟩ : syracuseStep 1101575 = 1652363) B1652363
theorem B1101583 : Blo 1100624 1101583 := bstep (se 1 (by rfl) ⟨826187, by rfl⟩ : syracuseStep 1101583 = 1652375) B1652375
theorem B1101627 : Blo 1100624 1101627 := bstep (se 1 (by rfl) ⟨826220, by rfl⟩ : syracuseStep 1101627 = 1652441) B1652441
theorem B1101703 : Blo 1100624 1101703 := bstep (se 1 (by rfl) ⟨826277, by rfl⟩ : syracuseStep 1101703 = 1652555) B1652555
theorem B1101711 : Blo 1100624 1101711 := bstep (se 1 (by rfl) ⟨826283, by rfl⟩ : syracuseStep 1101711 = 1652567) B1652567
theorem B6279059 : Blo 1100624 6279059 := bstep (se 1 (by rfl) ⟨4709294, by rfl⟩ : syracuseStep 6279059 = 9418589) B9418589
theorem B1101755 : Blo 1100624 1101755 := bstep (se 1 (by rfl) ⟨826316, by rfl⟩ : syracuseStep 1101755 = 1652633) B1652633
theorem B4181969 : Blo 1100624 4181969 := bstep (se 2 (by rfl) ⟨1568238, by rfl⟩ : syracuseStep 4181969 = 3136477) B3136477
theorem B1101831 : Blo 1100624 1101831 := bstep (se 1 (by rfl) ⟨826373, by rfl⟩ : syracuseStep 1101831 = 1652747) B1652747
theorem B2478095 : Blo 1100624 2478095 := bstep (se 1 (by rfl) ⟨1858571, by rfl⟩ : syracuseStep 2478095 = 3717143) B3717143
theorem B1101839 : Blo 1100624 1101839 := bstep (se 1 (by rfl) ⟨826379, by rfl⟩ : syracuseStep 1101839 = 1652759) B1652759
theorem B2478113 : Blo 1100624 2478113 := bstep (se 2 (by rfl) ⟨929292, by rfl⟩ : syracuseStep 2478113 = 1858585) B1858585
theorem B1101883 : Blo 1100624 1101883 := bstep (se 1 (by rfl) ⟨826412, by rfl⟩ : syracuseStep 1101883 = 1652825) B1652825
theorem B1396855 : Blo 1100624 1396855 := bstep (se 1 (by rfl) ⟨1047641, by rfl⟩ : syracuseStep 1396855 = 2095283) B2095283
theorem B1101959 : Blo 1100624 1101959 := bstep (se 1 (by rfl) ⟨826469, by rfl⟩ : syracuseStep 1101959 = 1652939) B1652939
theorem B1101967 : Blo 1100624 1101967 := bstep (se 1 (by rfl) ⟨826475, by rfl⟩ : syracuseStep 1101967 = 1652951) B1652951
theorem B1102011 : Blo 1100624 1102011 := bstep (se 1 (by rfl) ⟨826508, by rfl⟩ : syracuseStep 1102011 = 1653017) B1653017
theorem B4706561 : Blo 1100624 4706561 := bstep (se 2 (by rfl) ⟨1764960, by rfl⟩ : syracuseStep 4706561 = 3529921) B3529921
theorem B1102087 : Blo 1100624 1102087 := bstep (se 1 (by rfl) ⟨826565, by rfl⟩ : syracuseStep 1102087 = 1653131) B1653131
theorem B1102095 : Blo 1100624 1102095 := bstep (se 1 (by rfl) ⟨826571, by rfl⟩ : syracuseStep 1102095 = 1653143) B1653143
theorem B1102139 : Blo 1100624 1102139 := bstep (se 1 (by rfl) ⟨826604, by rfl⟩ : syracuseStep 1102139 = 1653209) B1653209
theorem B2478455 : Blo 1100624 2478455 := bstep (se 1 (by rfl) ⟨1858841, by rfl⟩ : syracuseStep 2478455 = 3717683) B3717683
theorem B1102215 : Blo 1100624 1102215 := bstep (se 1 (by rfl) ⟨826661, by rfl⟩ : syracuseStep 1102215 = 1653323) B1653323
theorem B1102223 : Blo 1100624 1102223 := bstep (se 1 (by rfl) ⟨826667, by rfl⟩ : syracuseStep 1102223 = 1653335) B1653335
theorem B4182425 : Blo 1100624 4182425 := bstep (se 2 (by rfl) ⟨1568409, by rfl⟩ : syracuseStep 4182425 = 3136819) B3136819
theorem B1102267 : Blo 1100624 1102267 := bstep (se 1 (by rfl) ⟨826700, by rfl⟩ : syracuseStep 1102267 = 1653401) B1653401
theorem B1397179 : Blo 1100624 1397179 := bstep (se 1 (by rfl) ⟨1047884, by rfl⟩ : syracuseStep 1397179 = 2095769) B2095769
theorem B1102343 : Blo 1100624 1102343 := bstep (se 1 (by rfl) ⟨826757, by rfl⟩ : syracuseStep 1102343 = 1653515) B1653515
theorem B1102351 : Blo 1100624 1102351 := bstep (se 1 (by rfl) ⟨826763, by rfl⟩ : syracuseStep 1102351 = 1653527) B1653527
theorem B2478635 : Blo 1100624 2478635 := bstep (se 1 (by rfl) ⟨1858976, by rfl⟩ : syracuseStep 2478635 = 3717953) B3717953
theorem B1102395 : Blo 1100624 1102395 := bstep (se 1 (by rfl) ⟨826796, by rfl⟩ : syracuseStep 1102395 = 1653593) B1653593
theorem B4706903 : Blo 1100624 4706903 := bstep (se 1 (by rfl) ⟨3530177, by rfl⟩ : syracuseStep 4706903 = 7060355) B7060355
theorem B5296727 : Blo 1100624 5296727 := bstep (se 1 (by rfl) ⟨3972545, by rfl⟩ : syracuseStep 5296727 = 7945091) B7945091
theorem B6279767 : Blo 1100624 6279767 := bstep (se 1 (by rfl) ⟨4709825, by rfl⟩ : syracuseStep 6279767 = 9419651) B9419651
theorem B54317699 : Blo 1100624 54317699 := bstep (se 1 (by rfl) ⟨40738274, by rfl⟩ : syracuseStep 54317699 = 81476549) B81476549
theorem B1102471 : Blo 1100624 1102471 := bstep (se 1 (by rfl) ⟨826853, by rfl⟩ : syracuseStep 1102471 = 1653707) B1653707
theorem B1102479 : Blo 1100624 1102479 := bstep (se 1 (by rfl) ⟨826859, by rfl⟩ : syracuseStep 1102479 = 1653719) B1653719
theorem B1102523 : Blo 1100624 1102523 := bstep (se 1 (by rfl) ⟨826892, by rfl⟩ : syracuseStep 1102523 = 1653785) B1653785
theorem B5591753 : Blo 1100624 5591753 := bstep (se 2 (by rfl) ⟨2096907, by rfl⟩ : syracuseStep 5591753 = 4193815) B4193815
theorem B1102599 : Blo 1100624 1102599 := bstep (se 1 (by rfl) ⟨826949, by rfl⟩ : syracuseStep 1102599 = 1653899) B1653899
theorem B1102607 : Blo 1100624 1102607 := bstep (se 1 (by rfl) ⟨826955, by rfl⟩ : syracuseStep 1102607 = 1653911) B1653911
theorem B1102651 : Blo 1100624 1102651 := bstep (se 1 (by rfl) ⟨826988, by rfl⟩ : syracuseStep 1102651 = 1653977) B1653977
theorem B1102727 : Blo 1100624 1102727 := bstep (se 1 (by rfl) ⟨827045, by rfl⟩ : syracuseStep 1102727 = 1654091) B1654091
theorem B1102735 : Blo 1100624 1102735 := bstep (se 1 (by rfl) ⟨827051, by rfl⟩ : syracuseStep 1102735 = 1654103) B1654103
theorem B1594255 : Blo 1100624 1594255 := bstep (se 1 (by rfl) ⟨1195691, by rfl⟩ : syracuseStep 1594255 = 2391383) B2391383
theorem B2478995 : Blo 1100624 2478995 := bstep (se 1 (by rfl) ⟨1859246, by rfl⟩ : syracuseStep 2478995 = 3718493) B3718493
theorem B1397675 : Blo 1100624 1397675 := bstep (se 1 (by rfl) ⟨1048256, by rfl⟩ : syracuseStep 1397675 = 2096513) B2096513
theorem B3724217 : Blo 1100624 3724217 := bstep (se 2 (by rfl) ⟨1396581, by rfl⟩ : syracuseStep 3724217 = 2793163) B2793163
theorem B1102779 : Blo 1100624 1102779 := bstep (se 1 (by rfl) ⟨827084, by rfl⟩ : syracuseStep 1102779 = 1654169) B1654169
theorem B2479049 : Blo 1100624 2479049 := bstep (se 2 (by rfl) ⟨929643, by rfl⟩ : syracuseStep 2479049 = 1859287) B1859287
theorem B1102855 : Blo 1100624 1102855 := bstep (se 1 (by rfl) ⟨827141, by rfl⟩ : syracuseStep 1102855 = 1654283) B1654283
theorem B1102863 : Blo 1100624 1102863 := bstep (se 1 (by rfl) ⟨827147, by rfl⟩ : syracuseStep 1102863 = 1654295) B1654295
theorem B1102907 : Blo 1100624 1102907 := bstep (se 1 (by rfl) ⟨827180, by rfl⟩ : syracuseStep 1102907 = 1654361) B1654361
theorem B25416791 : Blo 1100624 25416791 := bstep (se 1 (by rfl) ⟨19062593, by rfl⟩ : syracuseStep 25416791 = 38125187) B38125187
theorem B1102983 : Blo 1100624 1102983 := bstep (se 1 (by rfl) ⟨827237, by rfl⟩ : syracuseStep 1102983 = 1654475) B1654475
theorem B1102991 : Blo 1100624 1102991 := bstep (se 1 (by rfl) ⟨827243, by rfl⟩ : syracuseStep 1102991 = 1654487) B1654487
theorem B1103035 : Blo 1100624 1103035 := bstep (se 1 (by rfl) ⟨827276, by rfl⟩ : syracuseStep 1103035 = 1654553) B1654553
theorem B1103111 : Blo 1100624 1103111 := bstep (se 1 (by rfl) ⟨827333, by rfl⟩ : syracuseStep 1103111 = 1654667) B1654667
theorem B1103119 : Blo 1100624 1103119 := bstep (se 1 (by rfl) ⟨827339, by rfl⟩ : syracuseStep 1103119 = 1654679) B1654679
theorem B1103163 : Blo 1100624 1103163 := bstep (se 1 (by rfl) ⟨827372, by rfl⟩ : syracuseStep 1103163 = 1654745) B1654745
theorem B1103239 : Blo 1100624 1103239 := bstep (se 1 (by rfl) ⟨827429, by rfl⟩ : syracuseStep 1103239 = 1654859) B1654859
theorem B1103247 : Blo 1100624 1103247 := bstep (se 1 (by rfl) ⟨827435, by rfl⟩ : syracuseStep 1103247 = 1654871) B1654871
theorem B1103291 : Blo 1100624 1103291 := bstep (se 1 (by rfl) ⟨827468, by rfl⟩ : syracuseStep 1103291 = 1654937) B1654937
theorem B1103367 : Blo 1100624 1103367 := bstep (se 1 (by rfl) ⟨827525, by rfl⟩ : syracuseStep 1103367 = 1655051) B1655051
theorem B3724811 : Blo 1100624 3724811 := bstep (se 1 (by rfl) ⟨2793608, by rfl⟩ : syracuseStep 3724811 = 5587217) B5587217
theorem B1103375 : Blo 1100624 1103375 := bstep (se 1 (by rfl) ⟨827531, by rfl⟩ : syracuseStep 1103375 = 1655063) B1655063
theorem B3135019 : Blo 1100624 3135019 := bstep (se 1 (by rfl) ⟨2351264, by rfl⟩ : syracuseStep 3135019 = 4702529) B4702529
theorem B4183595 : Blo 1100624 4183595 := bstep (se 1 (by rfl) ⟨3137696, by rfl⟩ : syracuseStep 4183595 = 6275393) B6275393
theorem B1103419 : Blo 1100624 1103419 := bstep (se 1 (by rfl) ⟨827564, by rfl⟩ : syracuseStep 1103419 = 1655129) B1655129
theorem B3724919 : Blo 1100624 3724919 := bstep (se 1 (by rfl) ⟨2793689, by rfl⟩ : syracuseStep 3724919 = 5587379) B5587379
theorem B2479751 : Blo 1100624 2479751 := bstep (se 1 (by rfl) ⟨1859813, by rfl⟩ : syracuseStep 2479751 = 3719627) B3719627
theorem B1103495 : Blo 1100624 1103495 := bstep (se 1 (by rfl) ⟨827621, by rfl⟩ : syracuseStep 1103495 = 1655243) B1655243
theorem B1103503 : Blo 1100624 1103503 := bstep (se 1 (by rfl) ⟨827627, by rfl⟩ : syracuseStep 1103503 = 1655255) B1655255
theorem B40195763 : Blo 1100624 40195763 := bstep (se 1 (by rfl) ⟨30146822, by rfl⟩ : syracuseStep 40195763 = 60293645) B60293645
theorem B1103547 : Blo 1100624 1103547 := bstep (se 1 (by rfl) ⟨827660, by rfl⟩ : syracuseStep 1103547 = 1655321) B1655321
theorem B1103623 : Blo 1100624 1103623 := bstep (se 1 (by rfl) ⟨827717, by rfl⟩ : syracuseStep 1103623 = 1655435) B1655435
theorem B1103631 : Blo 1100624 1103631 := bstep (se 1 (by rfl) ⟨827723, by rfl⟩ : syracuseStep 1103631 = 1655447) B1655447
theorem B12736291 : Blo 1100624 12736291 := bstep (se 1 (by rfl) ⟨9552218, by rfl⟩ : syracuseStep 12736291 = 19104437) B19104437
theorem B1857323 : Blo 1100624 1857323 := bstep (se 1 (by rfl) ⟨1392992, by rfl⟩ : syracuseStep 1857323 = 2785985) B2785985
theorem B2479931 : Blo 1100624 2479931 := bstep (se 1 (by rfl) ⟨1859948, by rfl⟩ : syracuseStep 2479931 = 3719897) B3719897
theorem B1103675 : Blo 1100624 1103675 := bstep (se 1 (by rfl) ⟨827756, by rfl⟩ : syracuseStep 1103675 = 1655513) B1655513
theorem B3135293 : Blo 1100624 3135293 := bstep (se 3 (by rfl) ⟨587867, by rfl⟩ : syracuseStep 3135293 = 1175735) B1175735
theorem B1103751 : Blo 1100624 1103751 := bstep (se 1 (by rfl) ⟨827813, by rfl⟩ : syracuseStep 1103751 = 1655627) B1655627
theorem B1103759 : Blo 1100624 1103759 := bstep (se 1 (by rfl) ⟨827819, by rfl⟩ : syracuseStep 1103759 = 1655639) B1655639
theorem B2480057 : Blo 1100624 2480057 := bstep (se 2 (by rfl) ⟨930021, by rfl⟩ : syracuseStep 2480057 = 1860043) B1860043
theorem B1103803 : Blo 1100624 1103803 := bstep (se 1 (by rfl) ⟨827852, by rfl⟩ : syracuseStep 1103803 = 1655705) B1655705
theorem B1103879 : Blo 1100624 1103879 := bstep (se 1 (by rfl) ⟨827909, by rfl⟩ : syracuseStep 1103879 = 1655819) B1655819
theorem B1103887 : Blo 1100624 1103887 := bstep (se 1 (by rfl) ⟨827915, by rfl⟩ : syracuseStep 1103887 = 1655831) B1655831
theorem B1103931 : Blo 1100624 1103931 := bstep (se 1 (by rfl) ⟨827948, by rfl⟩ : syracuseStep 1103931 = 1655897) B1655897
theorem B11196503 : Blo 1100624 11196503 := bstep (se 1 (by rfl) ⟨8397377, by rfl⟩ : syracuseStep 11196503 = 16794755) B16794755
theorem B1104007 : Blo 1100624 1104007 := bstep (se 1 (by rfl) ⟨828005, by rfl⟩ : syracuseStep 1104007 = 1656011) B1656011
theorem B1104015 : Blo 1100624 1104015 := bstep (se 1 (by rfl) ⟨828011, by rfl⟩ : syracuseStep 1104015 = 1656023) B1656023
theorem B3135635 : Blo 1100624 3135635 := bstep (se 1 (by rfl) ⟨2351726, by rfl⟩ : syracuseStep 3135635 = 4703453) B4703453
theorem B1857721 : Blo 1100624 1857721 := bstep (se 2 (by rfl) ⟨696645, by rfl⟩ : syracuseStep 1857721 = 1393291) B1393291
theorem B1104059 : Blo 1100624 1104059 := bstep (se 1 (by rfl) ⟨828044, by rfl⟩ : syracuseStep 1104059 = 1656089) B1656089
theorem B3725513 : Blo 1100624 3725513 := bstep (se 2 (by rfl) ⟨1397067, by rfl⟩ : syracuseStep 3725513 = 2794135) B2794135
theorem B4249837 : Blo 1100624 4249837 := bstep (se 3 (by rfl) ⟨796844, by rfl⟩ : syracuseStep 4249837 = 1593689) B1593689
theorem B1104135 : Blo 1100624 1104135 := bstep (se 1 (by rfl) ⟨828101, by rfl⟩ : syracuseStep 1104135 = 1656203) B1656203
theorem B2480399 : Blo 1100624 2480399 := bstep (se 1 (by rfl) ⟨1860299, by rfl⟩ : syracuseStep 2480399 = 3720599) B3720599
theorem B1104143 : Blo 1100624 1104143 := bstep (se 1 (by rfl) ⟨828107, by rfl⟩ : syracuseStep 1104143 = 1656215) B1656215
theorem B2480417 : Blo 1100624 2480417 := bstep (se 2 (by rfl) ⟨930156, by rfl⟩ : syracuseStep 2480417 = 1860313) B1860313
theorem B1104187 : Blo 1100624 1104187 := bstep (se 1 (by rfl) ⟨828140, by rfl⟩ : syracuseStep 1104187 = 1656281) B1656281
theorem B1988983 : Blo 1100624 1988983 := bstep (se 1 (by rfl) ⟨1491737, by rfl⟩ : syracuseStep 1988983 = 2983475) B2983475
theorem B1104263 : Blo 1100624 1104263 := bstep (se 1 (by rfl) ⟨828197, by rfl⟩ : syracuseStep 1104263 = 1656395) B1656395
theorem B1104271 : Blo 1100624 1104271 := bstep (se 1 (by rfl) ⟨828203, by rfl⟩ : syracuseStep 1104271 = 1656407) B1656407
theorem B6281657 : Blo 1100624 6281657 := bstep (se 2 (by rfl) ⟨2355621, by rfl⟩ : syracuseStep 6281657 = 4711243) B4711243
theorem B1104315 : Blo 1100624 1104315 := bstep (se 1 (by rfl) ⟨828236, by rfl⟩ : syracuseStep 1104315 = 1656473) B1656473
theorem B4708817 : Blo 1100624 4708817 := bstep (se 2 (by rfl) ⟨1765806, by rfl⟩ : syracuseStep 4708817 = 3531613) B3531613
theorem B1104391 : Blo 1100624 1104391 := bstep (se 1 (by rfl) ⟨828293, by rfl⟩ : syracuseStep 1104391 = 1656587) B1656587
theorem B1104399 : Blo 1100624 1104399 := bstep (se 1 (by rfl) ⟨828299, by rfl⟩ : syracuseStep 1104399 = 1656599) B1656599
theorem B1104443 : Blo 1100624 1104443 := bstep (se 1 (by rfl) ⟨828332, by rfl⟩ : syracuseStep 1104443 = 1656665) B1656665
theorem B4250173 : Blo 1100624 4250173 := bstep (se 3 (by rfl) ⟨796907, by rfl⟩ : syracuseStep 4250173 = 1593815) B1593815
theorem B2480759 : Blo 1100624 2480759 := bstep (se 1 (by rfl) ⟨1860569, by rfl⟩ : syracuseStep 2480759 = 3721139) B3721139
theorem B1104519 : Blo 1100624 1104519 := bstep (se 1 (by rfl) ⟨828389, by rfl⟩ : syracuseStep 1104519 = 1656779) B1656779
theorem B1104527 : Blo 1100624 1104527 := bstep (se 1 (by rfl) ⟨828395, by rfl⟩ : syracuseStep 1104527 = 1656791) B1656791
theorem B1104571 : Blo 1100624 1104571 := bstep (se 1 (by rfl) ⟨828428, by rfl⟩ : syracuseStep 1104571 = 1656857) B1656857
theorem B2480939 : Blo 1100624 2480939 := bstep (se 1 (by rfl) ⟨1860704, by rfl⟩ : syracuseStep 2480939 = 3721409) B3721409
theorem B5299033 : Blo 1100624 5299033 := bstep (se 2 (by rfl) ⟨1987137, by rfl⟩ : syracuseStep 5299033 = 3974275) B3974275
theorem B7068505 : Blo 1100624 7068505 := bstep (se 2 (by rfl) ⟨2650689, by rfl⟩ : syracuseStep 7068505 = 5301379) B5301379
theorem B1858423 : Blo 1100624 1858423 := bstep (se 1 (by rfl) ⟨1393817, by rfl⟩ : syracuseStep 1858423 = 2787635) B2787635
theorem B3726215 : Blo 1100624 3726215 := bstep (se 1 (by rfl) ⟨2794661, by rfl⟩ : syracuseStep 3726215 = 5589323) B5589323
theorem B1858619 : Blo 1100624 1858619 := bstep (se 1 (by rfl) ⟨1393964, by rfl⟩ : syracuseStep 1858619 = 2787929) B2787929
theorem B5954647 : Blo 1100624 5954647 := bstep (se 1 (by rfl) ⟨4465985, by rfl⟩ : syracuseStep 5954647 = 8931971) B8931971
theorem B2481299 : Blo 1100624 2481299 := bstep (se 1 (by rfl) ⟨1860974, by rfl⟩ : syracuseStep 2481299 = 3721949) B3721949
theorem B2481353 : Blo 1100624 2481353 := bstep (se 2 (by rfl) ⟨930507, by rfl⟩ : syracuseStep 2481353 = 1861015) B1861015
theorem B3726593 : Blo 1100624 3726593 := bstep (se 2 (by rfl) ⟨1397472, by rfl⟩ : syracuseStep 3726593 = 2794945) B2794945
theorem B1859017 : Blo 1100624 1859017 := bstep (se 2 (by rfl) ⟨697131, by rfl⟩ : syracuseStep 1859017 = 1394263) B1394263
theorem B4185553 : Blo 1100624 4185553 := bstep (se 2 (by rfl) ⟨1569582, by rfl⟩ : syracuseStep 4185553 = 3139165) B3139165
theorem B8380097 : Blo 1100624 8380097 := bstep (se 2 (by rfl) ⟨3142536, by rfl⟩ : syracuseStep 8380097 = 6285073) B6285073
theorem B4185857 : Blo 1100624 4185857 := bstep (se 2 (by rfl) ⟨1569696, by rfl⟩ : syracuseStep 4185857 = 3139393) B3139393
theorem B2482055 : Blo 1100624 2482055 := bstep (se 1 (by rfl) ⟨1861541, by rfl⟩ : syracuseStep 2482055 = 3723083) B3723083
theorem B3727403 : Blo 1100624 3727403 := bstep (se 1 (by rfl) ⟨2795552, by rfl⟩ : syracuseStep 3727403 = 5591105) B5591105
theorem B2482235 : Blo 1100624 2482235 := bstep (se 1 (by rfl) ⟨1861676, by rfl⟩ : syracuseStep 2482235 = 3723353) B3723353
theorem B6709367 : Blo 1100624 6709367 := bstep (se 1 (by rfl) ⟨5032025, by rfl⟩ : syracuseStep 6709367 = 10064051) B10064051
theorem B1859719 : Blo 1100624 1859719 := bstep (se 1 (by rfl) ⟨1394789, by rfl⟩ : syracuseStep 1859719 = 2789579) B2789579
theorem B2482361 : Blo 1100624 2482361 := bstep (se 2 (by rfl) ⟨930885, by rfl⟩ : syracuseStep 2482361 = 1861771) B1861771
theorem B5300417 : Blo 1100624 5300417 := bstep (se 2 (by rfl) ⟨1987656, by rfl⟩ : syracuseStep 5300417 = 3975313) B3975313
theorem B4186313 : Blo 1100624 4186313 := bstep (se 2 (by rfl) ⟨1569867, by rfl⟩ : syracuseStep 4186313 = 3139735) B3139735
theorem B3137879 : Blo 1100624 3137879 := bstep (se 1 (by rfl) ⟨2353409, by rfl⟩ : syracuseStep 3137879 = 4706819) B4706819
theorem B2646539 : Blo 1100624 2646539 := bstep (se 1 (by rfl) ⟨1984904, by rfl⟩ : syracuseStep 2646539 = 3969809) B3969809
theorem B2482703 : Blo 1100624 2482703 := bstep (se 1 (by rfl) ⟨1862027, by rfl⟩ : syracuseStep 2482703 = 3724055) B3724055
theorem B5300765 : Blo 1100624 5300765 := bstep (se 3 (by rfl) ⟨993893, by rfl⟩ : syracuseStep 5300765 = 1987787) B1987787
theorem B2482721 : Blo 1100624 2482721 := bstep (se 2 (by rfl) ⟨931020, by rfl⟩ : syracuseStep 2482721 = 1862041) B1862041
theorem B2351675 : Blo 1100624 2351675 := bstep (se 1 (by rfl) ⟨1763756, by rfl⟩ : syracuseStep 2351675 = 3527513) B3527513
theorem B3531383 : Blo 1100624 3531383 := bstep (se 1 (by rfl) ⟨2648537, by rfl⟩ : syracuseStep 3531383 = 5297075) B5297075
theorem B1860367 : Blo 1100624 1860367 := bstep (se 1 (by rfl) ⟨1395275, by rfl⟩ : syracuseStep 1860367 = 2790551) B2790551
theorem B9429797 : Blo 1100624 9429797 := bstep (se 4 (by rfl) ⟨884043, by rfl⟩ : syracuseStep 9429797 = 1768087) B1768087
theorem B2646827 : Blo 1100624 2646827 := bstep (se 1 (by rfl) ⟨1985120, by rfl⟩ : syracuseStep 2646827 = 3970241) B3970241
theorem B2483063 : Blo 1100624 2483063 := bstep (se 1 (by rfl) ⟨1862297, by rfl⟩ : syracuseStep 2483063 = 3724595) B3724595
theorem B2515913 : Blo 1100624 2515913 := bstep (se 2 (by rfl) ⟨943467, by rfl⟩ : syracuseStep 2515913 = 1886935) B1886935
theorem B18834443 : Blo 1100624 18834443 := bstep (se 1 (by rfl) ⟨14125832, by rfl⟩ : syracuseStep 18834443 = 28251665) B28251665
theorem B2483243 : Blo 1100624 2483243 := bstep (se 1 (by rfl) ⟨1862432, by rfl⟩ : syracuseStep 2483243 = 3724865) B3724865
theorem B2352187 : Blo 1100624 2352187 := bstep (se 1 (by rfl) ⟨1764140, by rfl⟩ : syracuseStep 2352187 = 3528281) B3528281
theorem B2090119 : Blo 1100624 2090119 := bstep (se 1 (by rfl) ⟨1567589, by rfl⟩ : syracuseStep 2090119 = 3135179) B3135179
theorem B1238287 : Blo 1100624 1238287 := bstep (se 1 (by rfl) ⟨928715, by rfl⟩ : syracuseStep 1238287 = 1857431) B1857431
theorem B1860907 : Blo 1100624 1860907 := bstep (se 1 (by rfl) ⟨1395680, by rfl⟩ : syracuseStep 1860907 = 2791361) B2791361
theorem B2483603 : Blo 1100624 2483603 := bstep (se 1 (by rfl) ⟨1862702, by rfl⟩ : syracuseStep 2483603 = 3725405) B3725405
theorem B1861049 : Blo 1100624 1861049 := bstep (se 2 (by rfl) ⟨697893, by rfl⟩ : syracuseStep 1861049 = 1395787) B1395787
theorem B2483657 : Blo 1100624 2483657 := bstep (se 2 (by rfl) ⟨931371, by rfl⟩ : syracuseStep 2483657 = 1862743) B1862743
theorem B14116355 : Blo 1100624 14116355 := bstep (se 1 (by rfl) ⟨10587266, by rfl⟩ : syracuseStep 14116355 = 21174533) B21174533
theorem B2090681 : Blo 1100624 2090681 := bstep (se 2 (by rfl) ⟨784005, by rfl⟩ : syracuseStep 2090681 = 1568011) B1568011
theorem B1238791 : Blo 1100624 1238791 := bstep (se 1 (by rfl) ⟨929093, by rfl⟩ : syracuseStep 1238791 = 1858187) B1858187
theorem B1238971 : Blo 1100624 1238971 := bstep (se 1 (by rfl) ⟨929228, by rfl⟩ : syracuseStep 1238971 = 1858457) B1858457
theorem B1861751 : Blo 1100624 1861751 := bstep (se 1 (by rfl) ⟨1396313, by rfl⟩ : syracuseStep 1861751 = 2792627) B2792627
theorem B2484359 : Blo 1100624 2484359 := bstep (se 1 (by rfl) ⟨1863269, by rfl⟩ : syracuseStep 2484359 = 3726539) B3726539
theorem B2484539 : Blo 1100624 2484539 := bstep (se 1 (by rfl) ⟨1863404, by rfl⟩ : syracuseStep 2484539 = 3726809) B3726809
theorem B1239439 : Blo 1100624 1239439 := bstep (se 1 (by rfl) ⟨929579, by rfl⟩ : syracuseStep 1239439 = 1859159) B1859159
theorem B2484665 : Blo 1100624 2484665 := bstep (se 2 (by rfl) ⟨931749, by rfl⟩ : syracuseStep 2484665 = 1863499) B1863499
theorem B1862203 : Blo 1100624 1862203 := bstep (se 1 (by rfl) ⟨1396652, by rfl⟩ : syracuseStep 1862203 = 2793305) B2793305
theorem B2648663 : Blo 1100624 2648663 := bstep (se 1 (by rfl) ⟨1986497, by rfl⟩ : syracuseStep 2648663 = 3972995) B3972995
theorem B12544631 : Blo 1100624 12544631 := bstep (se 1 (by rfl) ⟨9408473, by rfl⟩ : syracuseStep 12544631 = 18816947) B18816947
theorem B1862345 : Blo 1100624 1862345 := bstep (se 2 (by rfl) ⟨698379, by rfl⟩ : syracuseStep 1862345 = 1396759) B1396759
theorem B2485007 : Blo 1100624 2485007 := bstep (se 1 (by rfl) ⟨1863755, by rfl⟩ : syracuseStep 2485007 = 3727511) B3727511
theorem B2485025 : Blo 1100624 2485025 := bstep (se 2 (by rfl) ⟨931884, by rfl⟩ : syracuseStep 2485025 = 1863769) B1863769
theorem B11922227 : Blo 1100624 11922227 := bstep (se 1 (by rfl) ⟨8941670, by rfl⟩ : syracuseStep 11922227 = 17883341) B17883341
theorem B2091835 : Blo 1100624 2091835 := bstep (se 1 (by rfl) ⟨1568876, by rfl⟩ : syracuseStep 2091835 = 3137753) B3137753
theorem B1239943 : Blo 1100624 1239943 := bstep (se 1 (by rfl) ⟨929957, by rfl⟩ : syracuseStep 1239943 = 1859915) B1859915
theorem B6712211 : Blo 1100624 6712211 := bstep (se 1 (by rfl) ⟨5034158, by rfl⟩ : syracuseStep 6712211 = 10068317) B10068317
theorem B5303225 : Blo 1100624 5303225 := bstep (se 2 (by rfl) ⟨1988709, by rfl⟩ : syracuseStep 5303225 = 3977419) B3977419
theorem B8383499 : Blo 1100624 8383499 := bstep (se 1 (by rfl) ⟨6287624, by rfl⟩ : syracuseStep 8383499 = 12575249) B12575249
theorem B3140623 : Blo 1100624 3140623 := bstep (se 1 (by rfl) ⟨2355467, by rfl⟩ : syracuseStep 3140623 = 4710935) B4710935
theorem B1240123 : Blo 1100624 1240123 := bstep (se 1 (by rfl) ⟨930092, by rfl⟩ : syracuseStep 1240123 = 1860185) B1860185
theorem B3140669 : Blo 1100624 3140669 := bstep (se 3 (by rfl) ⟨588875, by rfl⟩ : syracuseStep 3140669 = 1177751) B1177751
theorem B2485367 : Blo 1100624 2485367 := bstep (se 1 (by rfl) ⟨1864025, by rfl⟩ : syracuseStep 2485367 = 3728051) B3728051
theorem B4189441 : Blo 1100624 4189441 := bstep (se 2 (by rfl) ⟨1571040, by rfl⟩ : syracuseStep 4189441 = 3142081) B3142081
theorem B2092321 : Blo 1100624 2092321 := bstep (se 2 (by rfl) ⟨784620, by rfl⟩ : syracuseStep 2092321 = 1569241) B1569241
theorem B1863047 : Blo 1100624 1863047 := bstep (se 1 (by rfl) ⟨1397285, by rfl⟩ : syracuseStep 1863047 = 2794571) B2794571
theorem B3141011 : Blo 1100624 3141011 := bstep (se 1 (by rfl) ⟨2355758, by rfl⟩ : syracuseStep 3141011 = 4711517) B4711517
theorem B4713875 : Blo 1100624 4713875 := bstep (se 1 (by rfl) ⟨3535406, by rfl⟩ : syracuseStep 4713875 = 7070813) B7070813
theorem B6712723 : Blo 1100624 6712723 := bstep (se 1 (by rfl) ⟨5034542, by rfl⟩ : syracuseStep 6712723 = 10069085) B10069085
theorem B15887825 : Blo 1100624 15887825 := bstep (se 2 (by rfl) ⟨5957934, by rfl⟩ : syracuseStep 15887825 = 11915869) B11915869
theorem B1240591 : Blo 1100624 1240591 := bstep (se 1 (by rfl) ⟨930443, by rfl⟩ : syracuseStep 1240591 = 1860887) B1860887
theorem B1568683 : Blo 1100624 1568683 := bstep (se 1 (by rfl) ⟨1176512, by rfl⟩ : syracuseStep 1568683 = 2353025) B2353025
theorem B1241095 : Blo 1100624 1241095 := bstep (se 1 (by rfl) ⟨930821, by rfl⟩ : syracuseStep 1241095 = 1861643) B1861643
theorem B1863695 : Blo 1100624 1863695 := bstep (se 1 (by rfl) ⟨1397771, by rfl⟩ : syracuseStep 1863695 = 2795543) B2795543
theorem B11923517 : Blo 1100624 11923517 := bstep (se 3 (by rfl) ⟨2235659, by rfl⟩ : syracuseStep 11923517 = 4471319) B4471319
theorem B1568911 : Blo 1100624 1568911 := bstep (se 1 (by rfl) ⟨1176683, by rfl⟩ : syracuseStep 1568911 = 2353367) B2353367
theorem B1241275 : Blo 1100624 1241275 := bstep (se 1 (by rfl) ⟨930956, by rfl⟩ : syracuseStep 1241275 = 1861913) B1861913
theorem B3141899 : Blo 1100624 3141899 := bstep (se 1 (by rfl) ⟨2356424, by rfl⟩ : syracuseStep 3141899 = 4712849) B4712849
theorem B13431187 : Blo 1100624 13431187 := bstep (se 1 (by rfl) ⟨10073390, by rfl⟩ : syracuseStep 13431187 = 20146781) B20146781
theorem B2093627 : Blo 1100624 2093627 := bstep (se 1 (by rfl) ⟨1570220, by rfl⟩ : syracuseStep 2093627 = 3140441) B3140441
theorem B1241743 : Blo 1100624 1241743 := bstep (se 1 (by rfl) ⟨931307, by rfl⟩ : syracuseStep 1241743 = 1862615) B1862615
theorem B34861859 : Blo 1100624 34861859 := bstep (se 1 (by rfl) ⟨26146394, by rfl⟩ : syracuseStep 34861859 = 52292789) B52292789
theorem B20083571 : Blo 1100624 20083571 := bstep (se 1 (by rfl) ⟨15062678, by rfl⟩ : syracuseStep 20083571 = 30125357) B30125357
theorem B6288263 : Blo 1100624 6288263 := bstep (se 1 (by rfl) ⟨4716197, by rfl⟩ : syracuseStep 6288263 = 9432395) B9432395
theorem B8385443 : Blo 1100624 8385443 := bstep (se 1 (by rfl) ⟨6289082, by rfl⟩ : syracuseStep 8385443 = 12578165) B12578165
theorem B2978849 : Blo 1100624 2978849 := bstep (se 2 (by rfl) ⟨1117068, by rfl⟩ : syracuseStep 2978849 = 2234137) B2234137
theorem B2094113 : Blo 1100624 2094113 := bstep (se 2 (by rfl) ⟨785292, by rfl⟩ : syracuseStep 2094113 = 1570585) B1570585
theorem B1242247 : Blo 1100624 1242247 := bstep (se 1 (by rfl) ⟨931685, by rfl⟩ : syracuseStep 1242247 = 1863371) B1863371
theorem B2094265 : Blo 1100624 2094265 := bstep (se 2 (by rfl) ⟨785349, by rfl⟩ : syracuseStep 2094265 = 1570699) B1570699
theorem B5960897 : Blo 1100624 5960897 := bstep (se 2 (by rfl) ⟨2235336, by rfl⟩ : syracuseStep 5960897 = 4470673) B4470673
theorem B1701065 : Blo 1100624 1701065 := bstep (se 2 (by rfl) ⟨637899, by rfl⟩ : syracuseStep 1701065 = 1275799) B1275799
theorem B18838817 : Blo 1100624 18838817 := bstep (se 2 (by rfl) ⟨7064556, by rfl⟩ : syracuseStep 18838817 = 14129113) B14129113
theorem B1242427 : Blo 1100624 1242427 := bstep (se 1 (by rfl) ⟨931820, by rfl⟩ : syracuseStep 1242427 = 1863641) B1863641
theorem B4715891 : Blo 1100624 4715891 := bstep (se 1 (by rfl) ⟨3536918, by rfl⟩ : syracuseStep 4715891 = 7073837) B7073837
theorem B1275271 : Blo 1100624 1275271 := bstep (se 1 (by rfl) ⟨956453, by rfl⟩ : syracuseStep 1275271 = 1912907) B1912907
theorem B7533971 : Blo 1100624 7533971 := bstep (se 1 (by rfl) ⟨5650478, by rfl⟩ : syracuseStep 7533971 = 11300957) B11300957
theorem B1766857 : Blo 1100624 1766857 := bstep (se 2 (by rfl) ⟨662571, by rfl⟩ : syracuseStep 1766857 = 1325143) B1325143
theorem B3536585 : Blo 1100624 3536585 := bstep (se 2 (by rfl) ⟨1326219, by rfl⟩ : syracuseStep 3536585 = 2652439) B2652439
theorem B3143539 : Blo 1100624 3143539 := bstep (se 1 (by rfl) ⟨2357654, by rfl⟩ : syracuseStep 3143539 = 4715309) B4715309
theorem B3143767 : Blo 1100624 3143767 := bstep (se 1 (by rfl) ⟨2357825, by rfl⟩ : syracuseStep 3143767 = 4715651) B4715651
theorem B4192343 : Blo 1100624 4192343 := bstep (se 1 (by rfl) ⟨3144257, by rfl⟩ : syracuseStep 4192343 = 6288515) B6288515
theorem B13433033 : Blo 1100624 13433033 := bstep (se 2 (by rfl) ⟨5037387, by rfl⟩ : syracuseStep 13433033 = 10074775) B10074775
theorem B2652535 : Blo 1100624 2652535 := bstep (se 1 (by rfl) ⟨1989401, by rfl⟩ : syracuseStep 2652535 = 3978803) B3978803
theorem B2357689 : Blo 1100624 2357689 := bstep (se 2 (by rfl) ⟨884133, by rfl⟩ : syracuseStep 2357689 = 1768267) B1768267
theorem B4192829 : Blo 1100624 4192829 := bstep (se 3 (by rfl) ⟨786155, by rfl⟩ : syracuseStep 4192829 = 1572311) B1572311
theorem B8944195 : Blo 1100624 8944195 := bstep (se 1 (by rfl) ⟨6708146, by rfl⟩ : syracuseStep 8944195 = 13416293) B13416293
theorem B1571599 : Blo 1100624 1571599 := bstep (se 1 (by rfl) ⟨1178699, by rfl⟩ : syracuseStep 1571599 = 2357399) B2357399
theorem B2358031 : Blo 1100624 2358031 := bstep (se 1 (by rfl) ⟨1768523, by rfl⟩ : syracuseStep 2358031 = 3537047) B3537047
theorem B1768235 : Blo 1100624 1768235 := bstep (se 1 (by rfl) ⟨1326176, by rfl⟩ : syracuseStep 1768235 = 2652353) B2652353
theorem B1571719 : Blo 1100624 1571719 := bstep (se 1 (by rfl) ⟨1178789, by rfl⟩ : syracuseStep 1571719 = 2357579) B2357579
theorem B2096057 : Blo 1100624 2096057 := bstep (se 2 (by rfl) ⟨786021, by rfl⟩ : syracuseStep 2096057 = 1572043) B1572043
theorem B1178759 : Blo 1100624 1178759 := bstep (se 1 (by rfl) ⟨884069, by rfl⟩ : syracuseStep 1178759 = 1768139) B1768139
theorem B28277909 : Blo 1100624 28277909 := bstep (se 6 (by rfl) ⟨662763, by rfl⟩ : syracuseStep 28277909 = 1325527) B1325527
theorem B8387873 : Blo 1100624 8387873 := bstep (se 2 (by rfl) ⟨3145452, by rfl⟩ : syracuseStep 8387873 = 6290905) B6290905
theorem B18808199 : Blo 1100624 18808199 := bstep (se 1 (by rfl) ⟨14106149, by rfl⟩ : syracuseStep 18808199 = 28212299) B28212299
theorem B2358919 : Blo 1100624 2358919 := bstep (se 1 (by rfl) ⟨1769189, by rfl⟩ : syracuseStep 2358919 = 3538379) B3538379
theorem B3145351 : Blo 1100624 3145351 := bstep (se 1 (by rfl) ⟨2359013, by rfl⟩ : syracuseStep 3145351 = 4718027) B4718027
theorem B4718351 : Blo 1100624 4718351 := bstep (se 1 (by rfl) ⟨3538763, by rfl⟩ : syracuseStep 4718351 = 7077527) B7077527
theorem B1179451 : Blo 1100624 1179451 := bstep (se 1 (by rfl) ⟨884588, by rfl⟩ : syracuseStep 1179451 = 1769177) B1769177
theorem B53609111 : Blo 1100624 53609111 := bstep (se 1 (by rfl) ⟨40206833, by rfl⟩ : syracuseStep 53609111 = 80413667) B80413667
theorem B5964617 : Blo 1100624 5964617 := bstep (se 2 (by rfl) ⟨2236731, by rfl⟩ : syracuseStep 5964617 = 4473463) B4473463
theorem B2786825 : Blo 1100624 2786825 := bstep (se 2 (by rfl) ⟨1045059, by rfl⟩ : syracuseStep 2786825 = 2090119) B2090119
theorem B9406151 : Blo 1100624 9406151 := bstep (se 1 (by rfl) ⟨7054613, by rfl⟩ : syracuseStep 9406151 = 14109227) B14109227
theorem B3966839 : Blo 1100624 3966839 := bstep (se 1 (by rfl) ⟨2975129, by rfl⟩ : syracuseStep 3966839 = 5950259) B5950259
theorem B4524113 : Blo 1100624 4524113 := bstep (se 2 (by rfl) ⟨1696542, by rfl⟩ : syracuseStep 4524113 = 3393085) B3393085
theorem B2787979 : Blo 1100624 2787979 := bstep (se 1 (by rfl) ⟨2090984, by rfl⟩ : syracuseStep 2787979 = 4181969) B4181969
theorem B9407177 : Blo 1100624 9407177 := bstep (se 2 (by rfl) ⟨3527691, by rfl⟩ : syracuseStep 9407177 = 7055383) B7055383
theorem B2788283 : Blo 1100624 2788283 := bstep (se 1 (by rfl) ⟨2091212, by rfl⟩ : syracuseStep 2788283 = 4182425) B4182425
theorem B36211799 : Blo 1100624 36211799 := bstep (se 1 (by rfl) ⟨27158849, by rfl⟩ : syracuseStep 36211799 = 54317699) B54317699
theorem B2231695 : Blo 1100624 2231695 := bstep (se 1 (by rfl) ⟨1673771, by rfl⟩ : syracuseStep 2231695 = 3347543) B3347543
theorem B16944527 : Blo 1100624 16944527 := bstep (se 1 (by rfl) ⟨12708395, by rfl⟩ : syracuseStep 16944527 = 25416791) B25416791
theorem B2789063 : Blo 1100624 2789063 := bstep (se 1 (by rfl) ⟨2091797, by rfl⟩ : syracuseStep 2789063 = 4183595) B4183595
theorem B2789113 : Blo 1100624 2789113 := bstep (se 2 (by rfl) ⟨1045917, by rfl⟩ : syracuseStep 2789113 = 2091835) B2091835
theorem B2789761 : Blo 1100624 2789761 := bstep (se 2 (by rfl) ⟨1046160, by rfl⟩ : syracuseStep 2789761 = 2092321) B2092321
theorem B331321873 : Blo 1100624 331321873 := bstep (se 2 (by rfl) ⟨124245702, by rfl⟩ : syracuseStep 331321873 = 248491405) B248491405
theorem B8950297 : Blo 1100624 8950297 := bstep (se 2 (by rfl) ⟨3356361, by rfl⟩ : syracuseStep 8950297 = 6712723) B6712723
theorem B8360657 : Blo 1100624 8360657 := bstep (se 2 (by rfl) ⟨3135246, by rfl⟩ : syracuseStep 8360657 = 6270493) B6270493
theorem B3773213 : Blo 1100624 3773213 := bstep (se 3 (by rfl) ⟨707477, by rfl⟩ : syracuseStep 3773213 = 1414955) B1414955
theorem B28677017 : Blo 1100624 28677017 := bstep (se 2 (by rfl) ⟨10753881, by rfl⟩ : syracuseStep 28677017 = 21507763) B21507763
theorem B2233423 : Blo 1100624 2233423 := bstep (se 1 (by rfl) ⟨1675067, by rfl⟩ : syracuseStep 2233423 = 3350135) B3350135
theorem B2790571 : Blo 1100624 2790571 := bstep (se 1 (by rfl) ⟨2092928, by rfl⟩ : syracuseStep 2790571 = 4185857) B4185857
theorem B2790875 : Blo 1100624 2790875 := bstep (se 1 (by rfl) ⟨2093156, by rfl⟩ : syracuseStep 2790875 = 4186313) B4186313
theorem B5969371 : Blo 1100624 5969371 := bstep (se 1 (by rfl) ⟨4477028, by rfl⟩ : syracuseStep 5969371 = 8954057) B8954057
theorem B35755505 : Blo 1100624 35755505 := bstep (se 2 (by rfl) ⟨13408314, by rfl⟩ : syracuseStep 35755505 = 26816629) B26816629
theorem B12916235 : Blo 1100624 12916235 := bstep (se 1 (by rfl) ⟨9687176, by rfl⟩ : syracuseStep 12916235 = 19374353) B19374353
theorem B8722235 : Blo 1100624 8722235 := bstep (se 1 (by rfl) ⟨6541676, by rfl⟩ : syracuseStep 8722235 = 13083353) B13083353
theorem B7935839 : Blo 1100624 7935839 := bstep (se 1 (by rfl) ⟨5951879, by rfl⟩ : syracuseStep 7935839 = 11903759) B11903759
theorem B1677275 : Blo 1100624 1677275 := bstep (se 1 (by rfl) ⟨1257956, by rfl⟩ : syracuseStep 1677275 = 2515913) B2515913
theorem B12556295 : Blo 1100624 12556295 := bstep (se 1 (by rfl) ⟨9417221, by rfl⟩ : syracuseStep 12556295 = 18834443) B18834443
theorem B9410903 : Blo 1100624 9410903 := bstep (se 1 (by rfl) ⟨7058177, by rfl⟩ : syracuseStep 9410903 = 14116355) B14116355
theorem B16095773 : Blo 1100624 16095773 := bstep (se 3 (by rfl) ⟨3017957, by rfl⟩ : syracuseStep 16095773 = 6035915) B6035915
theorem B7084577 : Blo 1100624 7084577 := bstep (se 2 (by rfl) ⟨2656716, by rfl⟩ : syracuseStep 7084577 = 5313433) B5313433
theorem B2038471 : Blo 1100624 2038471 := bstep (se 1 (by rfl) ⟨1528853, by rfl⟩ : syracuseStep 2038471 = 3057707) B3057707
theorem B2792353 : Blo 1100624 2792353 := bstep (se 2 (by rfl) ⟨1047132, by rfl⟩ : syracuseStep 2792353 = 2094265) B2094265
theorem B8363087 : Blo 1100624 8363087 := bstep (se 1 (by rfl) ⟨6272315, by rfl⟩ : syracuseStep 8363087 = 12544631) B12544631
theorem B22650029 : Blo 1100624 22650029 := bstep (se 3 (by rfl) ⟨4246880, by rfl⟩ : syracuseStep 22650029 = 8493761) B8493761
theorem B14130449 : Blo 1100624 14130449 := bstep (se 2 (by rfl) ⟨5298918, by rfl⟩ : syracuseStep 14130449 = 10597837) B10597837
theorem B10591883 : Blo 1100624 10591883 := bstep (se 1 (by rfl) ⟨7943912, by rfl⟩ : syracuseStep 10591883 = 15887825) B15887825
theorem B16981721 : Blo 1100624 16981721 := bstep (se 2 (by rfl) ⟨6368145, by rfl⟩ : syracuseStep 16981721 = 12736291) B12736291
theorem B8069509 : Blo 1100624 8069509 := bstep (se 4 (by rfl) ⟨756516, by rfl⟩ : syracuseStep 8069509 = 1513033) B1513033
theorem B23241239 : Blo 1100624 23241239 := bstep (se 1 (by rfl) ⟨17430929, by rfl⟩ : syracuseStep 23241239 = 34861859) B34861859
theorem B11936281 : Blo 1100624 11936281 := bstep (se 2 (by rfl) ⟨4476105, by rfl⟩ : syracuseStep 11936281 = 8952211) B8952211
theorem B1909495 : Blo 1100624 1909495 := bstep (se 1 (by rfl) ⟨1432121, by rfl⟩ : syracuseStep 1909495 = 2864243) B2864243
theorem B3973931 : Blo 1100624 3973931 := bstep (se 1 (by rfl) ⟨2980448, by rfl⟩ : syracuseStep 3973931 = 5960897) B5960897
theorem B12559211 : Blo 1100624 12559211 := bstep (se 1 (by rfl) ⟨9419408, by rfl⟩ : syracuseStep 12559211 = 18838817) B18838817
theorem B5022647 : Blo 1100624 5022647 := bstep (se 1 (by rfl) ⟨3766985, by rfl⟩ : syracuseStep 5022647 = 7533971) B7533971
theorem B2794895 : Blo 1100624 2794895 := bstep (se 1 (by rfl) ⟨2096171, by rfl⟩ : syracuseStep 2794895 = 4192343) B4192343
theorem B7939529 : Blo 1100624 7939529 := bstep (se 2 (by rfl) ⟨2977323, by rfl⟩ : syracuseStep 7939529 = 5954647) B5954647
theorem B5580251 : Blo 1100624 5580251 := bstep (se 1 (by rfl) ⟨4185188, by rfl⟩ : syracuseStep 5580251 = 8370377) B8370377
theorem B8955355 : Blo 1100624 8955355 := bstep (se 1 (by rfl) ⟨6716516, by rfl⟩ : syracuseStep 8955355 = 13433033) B13433033
theorem B2795219 : Blo 1100624 2795219 := bstep (se 1 (by rfl) ⟨2096414, by rfl⟩ : syracuseStep 2795219 = 4192829) B4192829
theorem B5580737 : Blo 1100624 5580737 := bstep (se 2 (by rfl) ⟨2092776, by rfl⟩ : syracuseStep 5580737 = 4185553) B4185553
theorem B18851939 : Blo 1100624 18851939 := bstep (se 1 (by rfl) ⟨14138954, by rfl⟩ : syracuseStep 18851939 = 28277909) B28277909
theorem B11938049 : Blo 1100624 11938049 := bstep (se 2 (by rfl) ⟨4476768, by rfl⟩ : syracuseStep 11938049 = 8953537) B8953537
theorem B8366489 : Blo 1100624 8366489 := bstep (se 2 (by rfl) ⟨3137433, by rfl⟩ : syracuseStep 8366489 = 6274867) B6274867
theorem B4238351 : Blo 1100624 4238351 := bstep (se 1 (by rfl) ⟨3178763, by rfl⟩ : syracuseStep 4238351 = 6357527) B6357527
theorem B3353771 : Blo 1100624 3353771 := bstep (se 1 (by rfl) ⟨2515328, by rfl⟩ : syracuseStep 3353771 = 5030657) B5030657
theorem B14134445 : Blo 1100624 14134445 := bstep (se 3 (by rfl) ⟨2650208, by rfl⟩ : syracuseStep 14134445 = 5300417) B5300417
theorem B1322347 : Blo 1100624 1322347 := bstep (se 1 (by rfl) ⟨991760, by rfl⟩ : syracuseStep 1322347 = 1983521) B1983521
theorem B3976685 : Blo 1100624 3976685 := bstep (se 3 (by rfl) ⟨745628, by rfl⟩ : syracuseStep 3976685 = 1491257) B1491257
theorem B10595879 : Blo 1100624 10595879 := bstep (se 1 (by rfl) ⟨7946909, by rfl⟩ : syracuseStep 10595879 = 15893819) B15893819
theorem B5025419 : Blo 1100624 5025419 := bstep (se 1 (by rfl) ⟨3769064, by rfl⟩ : syracuseStep 5025419 = 7538129) B7538129
theorem B6205177 : Blo 1100624 6205177 := bstep (se 2 (by rfl) ⟨2326941, by rfl⟩ : syracuseStep 6205177 = 4653883) B4653883
theorem B3354463 : Blo 1100624 3354463 := bstep (se 1 (by rfl) ⟨2515847, by rfl⟩ : syracuseStep 3354463 = 5031695) B5031695
theorem B3715091 : Blo 1100624 3715091 := bstep (se 1 (by rfl) ⟨2786318, by rfl⟩ : syracuseStep 3715091 = 5572637) B5572637
theorem B5583005 : Blo 1100624 5583005 := bstep (se 3 (by rfl) ⟨1046813, by rfl⟩ : syracuseStep 5583005 = 2093627) B2093627
theorem B8368433 : Blo 1100624 8368433 := bstep (se 2 (by rfl) ⟨3138162, by rfl⟩ : syracuseStep 8368433 = 6276325) B6276325
theorem B10596683 : Blo 1100624 10596683 := bstep (se 1 (by rfl) ⟨7947512, by rfl⟩ : syracuseStep 10596683 = 15895025) B15895025
theorem B3715415 : Blo 1100624 3715415 := bstep (se 1 (by rfl) ⟨2786561, by rfl⟩ : syracuseStep 3715415 = 5573123) B5573123
theorem B1651049 : Blo 1100624 1651049 := bstep (se 2 (by rfl) ⟨619143, by rfl⟩ : syracuseStep 1651049 = 1238287) B1238287
theorem B1651127 : Blo 1100624 1651127 := bstep (se 1 (by rfl) ⟨1238345, by rfl⟩ : syracuseStep 1651127 = 2476691) B2476691
theorem B1651163 : Blo 1100624 1651163 := bstep (se 1 (by rfl) ⟨1238372, by rfl⟩ : syracuseStep 1651163 = 2476745) B2476745
theorem B1651631 : Blo 1100624 1651631 := bstep (se 1 (by rfl) ⟨1238723, by rfl⟩ : syracuseStep 1651631 = 2477447) B2477447
theorem B1651721 : Blo 1100624 1651721 := bstep (se 2 (by rfl) ⟨619395, by rfl⟩ : syracuseStep 1651721 = 1238791) B1238791
theorem B1651751 : Blo 1100624 1651751 := bstep (se 1 (by rfl) ⟨1238813, by rfl⟩ : syracuseStep 1651751 = 2477627) B2477627
theorem B1651835 : Blo 1100624 1651835 := bstep (se 1 (by rfl) ⟨1238876, by rfl⟩ : syracuseStep 1651835 = 2477753) B2477753
theorem B1651961 : Blo 1100624 1651961 := bstep (se 2 (by rfl) ⟨619485, by rfl⟩ : syracuseStep 1651961 = 1238971) B1238971
theorem B1652063 : Blo 1100624 1652063 := bstep (se 1 (by rfl) ⟨1239047, by rfl⟩ : syracuseStep 1652063 = 2478095) B2478095
theorem B1652075 : Blo 1100624 1652075 := bstep (se 1 (by rfl) ⟨1239056, by rfl⟩ : syracuseStep 1652075 = 2478113) B2478113
theorem B3716495 : Blo 1100624 3716495 := bstep (se 1 (by rfl) ⟨2787371, by rfl⟩ : syracuseStep 3716495 = 5574743) B5574743
theorem B5584301 : Blo 1100624 5584301 := bstep (se 3 (by rfl) ⟨1047056, by rfl⟩ : syracuseStep 5584301 = 2094113) B2094113
theorem B1652303 : Blo 1100624 1652303 := bstep (se 1 (by rfl) ⟨1239227, by rfl⟩ : syracuseStep 1652303 = 2478455) B2478455
theorem B1652423 : Blo 1100624 1652423 := bstep (se 1 (by rfl) ⟨1239317, by rfl⟩ : syracuseStep 1652423 = 2478635) B2478635
theorem B3716819 : Blo 1100624 3716819 := bstep (se 1 (by rfl) ⟨2787614, by rfl⟩ : syracuseStep 3716819 = 5575229) B5575229
theorem B1652585 : Blo 1100624 1652585 := bstep (se 2 (by rfl) ⟨619719, by rfl⟩ : syracuseStep 1652585 = 1239439) B1239439
theorem B1652663 : Blo 1100624 1652663 := bstep (se 1 (by rfl) ⟨1239497, by rfl⟩ : syracuseStep 1652663 = 2478995) B2478995
theorem B1652699 : Blo 1100624 1652699 := bstep (se 1 (by rfl) ⟨1239524, by rfl⟩ : syracuseStep 1652699 = 2479049) B2479049
theorem B6273409 : Blo 1100624 6273409 := bstep (se 2 (by rfl) ⟨2352528, by rfl⟩ : syracuseStep 6273409 = 4705057) B4705057
theorem B1653167 : Blo 1100624 1653167 := bstep (se 1 (by rfl) ⟨1239875, by rfl⟩ : syracuseStep 1653167 = 2479751) B2479751
theorem B1653257 : Blo 1100624 1653257 := bstep (se 2 (by rfl) ⟨619971, by rfl⟩ : syracuseStep 1653257 = 1239943) B1239943
theorem B1653287 : Blo 1100624 1653287 := bstep (se 1 (by rfl) ⟨1239965, by rfl⟩ : syracuseStep 1653287 = 2479931) B2479931
theorem B1653371 : Blo 1100624 1653371 := bstep (se 1 (by rfl) ⟨1240028, by rfl⟩ : syracuseStep 1653371 = 2480057) B2480057
theorem B1653497 : Blo 1100624 1653497 := bstep (se 2 (by rfl) ⟨620061, by rfl⟩ : syracuseStep 1653497 = 1240123) B1240123
theorem B1653599 : Blo 1100624 1653599 := bstep (se 1 (by rfl) ⟨1240199, by rfl⟩ : syracuseStep 1653599 = 2480399) B2480399
theorem B1653611 : Blo 1100624 1653611 := bstep (se 1 (by rfl) ⟨1240208, by rfl⟩ : syracuseStep 1653611 = 2480417) B2480417
theorem B3718007 : Blo 1100624 3718007 := bstep (se 1 (by rfl) ⟨2788505, by rfl⟩ : syracuseStep 3718007 = 5577011) B5577011
theorem B3980215 : Blo 1100624 3980215 := bstep (se 1 (by rfl) ⟨2985161, by rfl⟩ : syracuseStep 3980215 = 5970323) B5970323
theorem B5585921 : Blo 1100624 5585921 := bstep (se 2 (by rfl) ⟨2094720, by rfl⟩ : syracuseStep 5585921 = 4189441) B4189441
theorem B3718223 : Blo 1100624 3718223 := bstep (se 1 (by rfl) ⟨2788667, by rfl⟩ : syracuseStep 3718223 = 5577335) B5577335
theorem B1653839 : Blo 1100624 1653839 := bstep (se 1 (by rfl) ⟨1240379, by rfl⟩ : syracuseStep 1653839 = 2480759) B2480759
theorem B1653959 : Blo 1100624 1653959 := bstep (se 1 (by rfl) ⟨1240469, by rfl⟩ : syracuseStep 1653959 = 2480939) B2480939
theorem B1654121 : Blo 1100624 1654121 := bstep (se 2 (by rfl) ⟨620295, by rfl⟩ : syracuseStep 1654121 = 1240591) B1240591
theorem B1654199 : Blo 1100624 1654199 := bstep (se 1 (by rfl) ⟨1240649, by rfl⟩ : syracuseStep 1654199 = 2481299) B2481299
theorem B3718601 : Blo 1100624 3718601 := bstep (se 2 (by rfl) ⟨1394475, by rfl⟩ : syracuseStep 3718601 = 2788951) B2788951
theorem B1654235 : Blo 1100624 1654235 := bstep (se 1 (by rfl) ⟨1240676, by rfl⟩ : syracuseStep 1654235 = 2481353) B2481353
theorem B1883657 : Blo 1100624 1883657 := bstep (se 2 (by rfl) ⟨706371, by rfl⟩ : syracuseStep 1883657 = 1412743) B1412743
theorem B8371835 : Blo 1100624 8371835 := bstep (se 1 (by rfl) ⟨6278876, by rfl⟩ : syracuseStep 8371835 = 12557753) B12557753
theorem B3718871 : Blo 1100624 3718871 := bstep (se 1 (by rfl) ⟨2789153, by rfl⟩ : syracuseStep 3718871 = 5578307) B5578307
theorem B5586731 : Blo 1100624 5586731 := bstep (se 1 (by rfl) ⟨4190048, by rfl⟩ : syracuseStep 5586731 = 8380097) B8380097
theorem B3719087 : Blo 1100624 3719087 := bstep (se 1 (by rfl) ⟨2789315, by rfl⟩ : syracuseStep 3719087 = 5578631) B5578631
theorem B1654703 : Blo 1100624 1654703 := bstep (se 1 (by rfl) ⟨1241027, by rfl⟩ : syracuseStep 1654703 = 2482055) B2482055
theorem B1654793 : Blo 1100624 1654793 := bstep (se 2 (by rfl) ⟨620547, by rfl⟩ : syracuseStep 1654793 = 1241095) B1241095
theorem B1654823 : Blo 1100624 1654823 := bstep (se 1 (by rfl) ⟨1241117, by rfl⟩ : syracuseStep 1654823 = 2482235) B2482235
theorem B10076237 : Blo 1100624 10076237 := bstep (se 3 (by rfl) ⟨1889294, by rfl⟩ : syracuseStep 10076237 = 3778589) B3778589
theorem B4472911 : Blo 1100624 4472911 := bstep (se 1 (by rfl) ⟨3354683, by rfl⟩ : syracuseStep 4472911 = 6709367) B6709367
theorem B1654907 : Blo 1100624 1654907 := bstep (se 1 (by rfl) ⟨1241180, by rfl⟩ : syracuseStep 1654907 = 2482361) B2482361
theorem B1655033 : Blo 1100624 1655033 := bstep (se 2 (by rfl) ⟨620637, by rfl⟩ : syracuseStep 1655033 = 1241275) B1241275
theorem B1655135 : Blo 1100624 1655135 := bstep (se 1 (by rfl) ⟨1241351, by rfl⟩ : syracuseStep 1655135 = 2482703) B2482703
theorem B1655147 : Blo 1100624 1655147 := bstep (se 1 (by rfl) ⟨1241360, by rfl⟩ : syracuseStep 1655147 = 2482721) B2482721
theorem B22921751 : Blo 1100624 22921751 := bstep (se 1 (by rfl) ⟨17191313, by rfl⟩ : syracuseStep 22921751 = 34382627) B34382627
theorem B17908249 : Blo 1100624 17908249 := bstep (se 2 (by rfl) ⟨6715593, by rfl⟩ : syracuseStep 17908249 = 13431187) B13431187
theorem B1655375 : Blo 1100624 1655375 := bstep (se 1 (by rfl) ⟨1241531, by rfl⟩ : syracuseStep 1655375 = 2483063) B2483063
theorem B1655495 : Blo 1100624 1655495 := bstep (se 1 (by rfl) ⟨1241621, by rfl⟩ : syracuseStep 1655495 = 2483243) B2483243
theorem B1655657 : Blo 1100624 1655657 := bstep (se 2 (by rfl) ⟨620871, by rfl⟩ : syracuseStep 1655657 = 1241743) B1241743
theorem B1655735 : Blo 1100624 1655735 := bstep (se 1 (by rfl) ⟨1241801, by rfl⟩ : syracuseStep 1655735 = 2483603) B2483603
theorem B1655771 : Blo 1100624 1655771 := bstep (se 1 (by rfl) ⟨1241828, by rfl⟩ : syracuseStep 1655771 = 2483657) B2483657
theorem B4179023 : Blo 1100624 4179023 := bstep (se 1 (by rfl) ⟨3134267, by rfl⟩ : syracuseStep 4179023 = 6268535) B6268535
theorem B1393787 : Blo 1100624 1393787 := bstep (se 1 (by rfl) ⟨1045340, by rfl⟩ : syracuseStep 1393787 = 2090681) B2090681
theorem B1656239 : Blo 1100624 1656239 := bstep (se 1 (by rfl) ⟨1242179, by rfl⟩ : syracuseStep 1656239 = 2484359) B2484359
theorem B1656329 : Blo 1100624 1656329 := bstep (se 2 (by rfl) ⟨621123, by rfl⟩ : syracuseStep 1656329 = 1242247) B1242247
theorem B1656359 : Blo 1100624 1656359 := bstep (se 1 (by rfl) ⟨1242269, by rfl⟩ : syracuseStep 1656359 = 2484539) B2484539
theorem B1984097 : Blo 1100624 1984097 := bstep (se 2 (by rfl) ⟨744036, by rfl⟩ : syracuseStep 1984097 = 1488073) B1488073
theorem B1656443 : Blo 1100624 1656443 := bstep (se 1 (by rfl) ⟨1242332, by rfl⟩ : syracuseStep 1656443 = 2484665) B2484665
theorem B1656569 : Blo 1100624 1656569 := bstep (se 2 (by rfl) ⟨621213, by rfl⟩ : syracuseStep 1656569 = 1242427) B1242427
theorem B1656671 : Blo 1100624 1656671 := bstep (se 1 (by rfl) ⟨1242503, by rfl⟩ : syracuseStep 1656671 = 2485007) B2485007
theorem B1656683 : Blo 1100624 1656683 := bstep (se 1 (by rfl) ⟨1242512, by rfl⟩ : syracuseStep 1656683 = 2485025) B2485025
theorem B5293943 : Blo 1100624 5293943 := bstep (se 1 (by rfl) ⟨3970457, by rfl⟩ : syracuseStep 5293943 = 7940915) B7940915
theorem B7948151 : Blo 1100624 7948151 := bstep (se 1 (by rfl) ⟨5961113, by rfl⟩ : syracuseStep 7948151 = 11922227) B11922227
theorem B4474807 : Blo 1100624 4474807 := bstep (se 1 (by rfl) ⟨3356105, by rfl⟩ : syracuseStep 4474807 = 6712211) B6712211
theorem B5588999 : Blo 1100624 5588999 := bstep (se 1 (by rfl) ⟨4191749, by rfl⟩ : syracuseStep 5588999 = 8383499) B8383499
theorem B6801445 : Blo 1100624 6801445 := bstep (se 4 (by rfl) ⟨637635, by rfl⟩ : syracuseStep 6801445 = 1275271) B1275271
theorem B4180025 : Blo 1100624 4180025 := bstep (se 2 (by rfl) ⟨1567509, by rfl⟩ : syracuseStep 4180025 = 3135019) B3135019
theorem B1656911 : Blo 1100624 1656911 := bstep (se 1 (by rfl) ⟨1242683, by rfl⟩ : syracuseStep 1656911 = 2485367) B2485367
theorem B3721463 : Blo 1100624 3721463 := bstep (se 1 (by rfl) ⟨2791097, by rfl⟩ : syracuseStep 3721463 = 5582195) B5582195
theorem B22595993 : Blo 1100624 22595993 := bstep (se 2 (by rfl) ⟨8473497, by rfl⟩ : syracuseStep 22595993 = 16946995) B16946995
theorem B5589485 : Blo 1100624 5589485 := bstep (se 3 (by rfl) ⟨1048028, by rfl⟩ : syracuseStep 5589485 = 2096057) B2096057
theorem B1985033 : Blo 1100624 1985033 := bstep (se 2 (by rfl) ⟨744387, by rfl⟩ : syracuseStep 1985033 = 1488775) B1488775
theorem B2476583 : Blo 1100624 2476583 := bstep (se 1 (by rfl) ⟨1857437, by rfl⟩ : syracuseStep 2476583 = 3714875) B3714875
theorem B3721787 : Blo 1100624 3721787 := bstep (se 1 (by rfl) ⟨2791340, by rfl⟩ : syracuseStep 3721787 = 5582681) B5582681
theorem B4180679 : Blo 1100624 4180679 := bstep (se 1 (by rfl) ⟨3135509, by rfl⟩ : syracuseStep 4180679 = 6271019) B6271019
theorem B7949011 : Blo 1100624 7949011 := bstep (se 1 (by rfl) ⟨5961758, by rfl⟩ : syracuseStep 7949011 = 11923517) B11923517
theorem B3722057 : Blo 1100624 3722057 := bstep (se 2 (by rfl) ⟨1395771, by rfl⟩ : syracuseStep 3722057 = 2791543) B2791543
theorem B1100639 : Blo 1100624 1100639 := bstep (se 1 (by rfl) ⟨825479, by rfl⟩ : syracuseStep 1100639 = 1650959) B1650959
theorem B2476907 : Blo 1100624 2476907 := bstep (se 1 (by rfl) ⟨1857680, by rfl⟩ : syracuseStep 2476907 = 3715361) B3715361
theorem B1100667 : Blo 1100624 1100667 := bstep (se 1 (by rfl) ⟨825500, by rfl⟩ : syracuseStep 1100667 = 1651001) B1651001
theorem B2476961 : Blo 1100624 2476961 := bstep (se 2 (by rfl) ⟨928860, by rfl⟩ : syracuseStep 2476961 = 1857721) B1857721
theorem B1100719 : Blo 1100624 1100719 := bstep (se 1 (by rfl) ⟨825539, by rfl⟩ : syracuseStep 1100719 = 1651079) B1651079
theorem B1100743 : Blo 1100624 1100743 := bstep (se 1 (by rfl) ⟨825557, by rfl⟩ : syracuseStep 1100743 = 1651115) B1651115
theorem B1100763 : Blo 1100624 1100763 := bstep (se 1 (by rfl) ⟨825572, by rfl⟩ : syracuseStep 1100763 = 1651145) B1651145
theorem B1100839 : Blo 1100624 1100839 := bstep (se 1 (by rfl) ⟨825629, by rfl⟩ : syracuseStep 1100839 = 1651259) B1651259
theorem B1100879 : Blo 1100624 1100879 := bstep (se 1 (by rfl) ⟨825659, by rfl⟩ : syracuseStep 1100879 = 1651319) B1651319
theorem B1100895 : Blo 1100624 1100895 := bstep (se 1 (by rfl) ⟨825671, by rfl⟩ : syracuseStep 1100895 = 1651343) B1651343
theorem B1100923 : Blo 1100624 1100923 := bstep (se 1 (by rfl) ⟨825692, by rfl⟩ : syracuseStep 1100923 = 1651385) B1651385
theorem B1100975 : Blo 1100624 1100975 := bstep (se 1 (by rfl) ⟨825731, by rfl⟩ : syracuseStep 1100975 = 1651463) B1651463
theorem B1100999 : Blo 1100624 1100999 := bstep (se 1 (by rfl) ⟨825749, by rfl⟩ : syracuseStep 1100999 = 1651499) B1651499
theorem B76303565 : Blo 1100624 76303565 := bstep (se 3 (by rfl) ⟨14306918, by rfl⟩ : syracuseStep 76303565 = 28613837) B28613837
theorem B1101019 : Blo 1100624 1101019 := bstep (se 1 (by rfl) ⟨825764, by rfl⟩ : syracuseStep 1101019 = 1651529) B1651529
theorem B13389047 : Blo 1100624 13389047 := bstep (se 1 (by rfl) ⟨10041785, by rfl⟩ : syracuseStep 13389047 = 20083571) B20083571
theorem B2477303 : Blo 1100624 2477303 := bstep (se 1 (by rfl) ⟨1857977, by rfl⟩ : syracuseStep 2477303 = 3715955) B3715955
theorem B5590295 : Blo 1100624 5590295 := bstep (se 1 (by rfl) ⟨4192721, by rfl⟩ : syracuseStep 5590295 = 8385443) B8385443
theorem B1101095 : Blo 1100624 1101095 := bstep (se 1 (by rfl) ⟨825821, by rfl⟩ : syracuseStep 1101095 = 1651643) B1651643
theorem B1101135 : Blo 1100624 1101135 := bstep (se 1 (by rfl) ⟨825851, by rfl⟩ : syracuseStep 1101135 = 1651703) B1651703
theorem B1101151 : Blo 1100624 1101151 := bstep (se 1 (by rfl) ⟨825863, by rfl⟩ : syracuseStep 1101151 = 1651727) B1651727
theorem B1985899 : Blo 1100624 1985899 := bstep (se 1 (by rfl) ⟨1489424, by rfl⟩ : syracuseStep 1985899 = 2978849) B2978849
theorem B1101179 : Blo 1100624 1101179 := bstep (se 1 (by rfl) ⟨825884, by rfl⟩ : syracuseStep 1101179 = 1651769) B1651769
theorem B1101231 : Blo 1100624 1101231 := bstep (se 1 (by rfl) ⟨825923, by rfl⟩ : syracuseStep 1101231 = 1651847) B1651847
theorem B1101255 : Blo 1100624 1101255 := bstep (se 1 (by rfl) ⟨825941, by rfl⟩ : syracuseStep 1101255 = 1651883) B1651883
theorem B1101275 : Blo 1100624 1101275 := bstep (se 1 (by rfl) ⟨825956, by rfl⟩ : syracuseStep 1101275 = 1651913) B1651913
theorem B1134043 : Blo 1100624 1134043 := bstep (se 1 (by rfl) ⟨850532, by rfl⟩ : syracuseStep 1134043 = 1701065) B1701065
theorem B1101351 : Blo 1100624 1101351 := bstep (se 1 (by rfl) ⟨826013, by rfl⟩ : syracuseStep 1101351 = 1652027) B1652027
theorem B14536259 : Blo 1100624 14536259 := bstep (se 1 (by rfl) ⟨10902194, by rfl⟩ : syracuseStep 14536259 = 21804389) B21804389
theorem B1101391 : Blo 1100624 1101391 := bstep (se 1 (by rfl) ⟨826043, by rfl⟩ : syracuseStep 1101391 = 1652087) B1652087
theorem B13618775 : Blo 1100624 13618775 := bstep (se 1 (by rfl) ⟨10214081, by rfl⟩ : syracuseStep 13618775 = 20428163) B20428163
theorem B1101407 : Blo 1100624 1101407 := bstep (se 1 (by rfl) ⟨826055, by rfl⟩ : syracuseStep 1101407 = 1652111) B1652111
theorem B1101435 : Blo 1100624 1101435 := bstep (se 1 (by rfl) ⟨826076, by rfl⟩ : syracuseStep 1101435 = 1652153) B1652153
theorem B4181651 : Blo 1100624 4181651 := bstep (se 1 (by rfl) ⟨3136238, by rfl⟩ : syracuseStep 4181651 = 6272477) B6272477
theorem B1101487 : Blo 1100624 1101487 := bstep (se 1 (by rfl) ⟨826115, by rfl⟩ : syracuseStep 1101487 = 1652231) B1652231
theorem B1101511 : Blo 1100624 1101511 := bstep (se 1 (by rfl) ⟨826133, by rfl⟩ : syracuseStep 1101511 = 1652267) B1652267
theorem B1101531 : Blo 1100624 1101531 := bstep (se 1 (by rfl) ⟨826148, by rfl⟩ : syracuseStep 1101531 = 1652297) B1652297
theorem B7065377 : Blo 1100624 7065377 := bstep (se 2 (by rfl) ⟨2649516, by rfl⟩ : syracuseStep 7065377 = 5299033) B5299033
theorem B9424673 : Blo 1100624 9424673 := bstep (se 2 (by rfl) ⟨3534252, by rfl⟩ : syracuseStep 9424673 = 7068505) B7068505
theorem B1101607 : Blo 1100624 1101607 := bstep (se 1 (by rfl) ⟨826205, by rfl⟩ : syracuseStep 1101607 = 1652411) B1652411
theorem B2477897 : Blo 1100624 2477897 := bstep (se 2 (by rfl) ⟨929211, by rfl⟩ : syracuseStep 2477897 = 1858423) B1858423
theorem B1101647 : Blo 1100624 1101647 := bstep (se 1 (by rfl) ⟨826235, by rfl⟩ : syracuseStep 1101647 = 1652471) B1652471
theorem B1101663 : Blo 1100624 1101663 := bstep (se 1 (by rfl) ⟨826247, by rfl⟩ : syracuseStep 1101663 = 1652495) B1652495
theorem B1101691 : Blo 1100624 1101691 := bstep (se 1 (by rfl) ⟨826268, by rfl⟩ : syracuseStep 1101691 = 1652537) B1652537
theorem B1101743 : Blo 1100624 1101743 := bstep (se 1 (by rfl) ⟨826307, by rfl⟩ : syracuseStep 1101743 = 1652615) B1652615
theorem B3723191 : Blo 1100624 3723191 := bstep (se 1 (by rfl) ⟨2792393, by rfl⟩ : syracuseStep 3723191 = 5584787) B5584787
theorem B1101767 : Blo 1100624 1101767 := bstep (se 1 (by rfl) ⟨826325, by rfl⟩ : syracuseStep 1101767 = 1652651) B1652651
theorem B1101787 : Blo 1100624 1101787 := bstep (se 1 (by rfl) ⟨826340, by rfl⟩ : syracuseStep 1101787 = 1652681) B1652681
theorem B1101863 : Blo 1100624 1101863 := bstep (se 1 (by rfl) ⟨826397, by rfl⟩ : syracuseStep 1101863 = 1652795) B1652795
theorem B1101903 : Blo 1100624 1101903 := bstep (se 1 (by rfl) ⟨826427, by rfl⟩ : syracuseStep 1101903 = 1652855) B1652855
theorem B1101919 : Blo 1100624 1101919 := bstep (se 1 (by rfl) ⟨826439, by rfl⟩ : syracuseStep 1101919 = 1652879) B1652879
theorem B1101947 : Blo 1100624 1101947 := bstep (se 1 (by rfl) ⟨826460, by rfl⟩ : syracuseStep 1101947 = 1652921) B1652921
theorem B1101999 : Blo 1100624 1101999 := bstep (se 1 (by rfl) ⟨826499, by rfl⟩ : syracuseStep 1101999 = 1652999) B1652999
theorem B1102023 : Blo 1100624 1102023 := bstep (se 1 (by rfl) ⟨826517, by rfl⟩ : syracuseStep 1102023 = 1653035) B1653035
theorem B1102043 : Blo 1100624 1102043 := bstep (se 1 (by rfl) ⟨826532, by rfl⟩ : syracuseStep 1102043 = 1653065) B1653065
theorem B1102119 : Blo 1100624 1102119 := bstep (se 1 (by rfl) ⟨826589, by rfl⟩ : syracuseStep 1102119 = 1653179) B1653179
theorem B1102159 : Blo 1100624 1102159 := bstep (se 1 (by rfl) ⟨826619, by rfl⟩ : syracuseStep 1102159 = 1653239) B1653239
theorem B1102175 : Blo 1100624 1102175 := bstep (se 1 (by rfl) ⟨826631, by rfl⟩ : syracuseStep 1102175 = 1653263) B1653263
theorem B1102203 : Blo 1100624 1102203 := bstep (se 1 (by rfl) ⟨826652, by rfl⟩ : syracuseStep 1102203 = 1653305) B1653305
theorem B1102255 : Blo 1100624 1102255 := bstep (se 1 (by rfl) ⟨826691, by rfl⟩ : syracuseStep 1102255 = 1653383) B1653383
theorem B1102279 : Blo 1100624 1102279 := bstep (se 1 (by rfl) ⟨826709, by rfl⟩ : syracuseStep 1102279 = 1653419) B1653419
theorem B1102299 : Blo 1100624 1102299 := bstep (se 1 (by rfl) ⟨826724, by rfl⟩ : syracuseStep 1102299 = 1653449) B1653449
theorem B3723785 : Blo 1100624 3723785 := bstep (se 2 (by rfl) ⟨1396419, by rfl⟩ : syracuseStep 3723785 = 2792839) B2792839
theorem B1102375 : Blo 1100624 1102375 := bstep (se 1 (by rfl) ⟨826781, by rfl⟩ : syracuseStep 1102375 = 1653563) B1653563
theorem B1102415 : Blo 1100624 1102415 := bstep (se 1 (by rfl) ⟨826811, by rfl⟩ : syracuseStep 1102415 = 1653623) B1653623
theorem B1102431 : Blo 1100624 1102431 := bstep (se 1 (by rfl) ⟨826823, by rfl⟩ : syracuseStep 1102431 = 1653647) B1653647
theorem B2478689 : Blo 1100624 2478689 := bstep (se 2 (by rfl) ⟨929508, by rfl⟩ : syracuseStep 2478689 = 1859017) B1859017
theorem B1102459 : Blo 1100624 1102459 := bstep (se 1 (by rfl) ⟨826844, by rfl⟩ : syracuseStep 1102459 = 1653689) B1653689
theorem B1102511 : Blo 1100624 1102511 := bstep (se 1 (by rfl) ⟨826883, by rfl⟩ : syracuseStep 1102511 = 1653767) B1653767
theorem B1102535 : Blo 1100624 1102535 := bstep (se 1 (by rfl) ⟨826901, by rfl⟩ : syracuseStep 1102535 = 1653803) B1653803
theorem B1102555 : Blo 1100624 1102555 := bstep (se 1 (by rfl) ⟨826916, by rfl⟩ : syracuseStep 1102555 = 1653833) B1653833
theorem B1102631 : Blo 1100624 1102631 := bstep (se 1 (by rfl) ⟨826973, by rfl⟩ : syracuseStep 1102631 = 1653947) B1653947
theorem B1102671 : Blo 1100624 1102671 := bstep (se 1 (by rfl) ⟨827003, by rfl⟩ : syracuseStep 1102671 = 1654007) B1654007
theorem B1102687 : Blo 1100624 1102687 := bstep (se 1 (by rfl) ⟨827015, by rfl⟩ : syracuseStep 1102687 = 1654031) B1654031
theorem B5591915 : Blo 1100624 5591915 := bstep (se 1 (by rfl) ⟨4193936, by rfl⟩ : syracuseStep 5591915 = 8387873) B8387873
theorem B1102715 : Blo 1100624 1102715 := bstep (se 1 (by rfl) ⟨827036, by rfl⟩ : syracuseStep 1102715 = 1654073) B1654073
theorem B12538799 : Blo 1100624 12538799 := bstep (se 1 (by rfl) ⟨9404099, by rfl⟩ : syracuseStep 12538799 = 18808199) B18808199
theorem B1102767 : Blo 1100624 1102767 := bstep (se 1 (by rfl) ⟨827075, by rfl⟩ : syracuseStep 1102767 = 1654151) B1654151
theorem B2479031 : Blo 1100624 2479031 := bstep (se 1 (by rfl) ⟨1859273, by rfl⟩ : syracuseStep 2479031 = 3718547) B3718547
theorem B1102791 : Blo 1100624 1102791 := bstep (se 1 (by rfl) ⟨827093, by rfl⟩ : syracuseStep 1102791 = 1654187) B1654187
theorem B1102811 : Blo 1100624 1102811 := bstep (se 1 (by rfl) ⟨827108, by rfl⟩ : syracuseStep 1102811 = 1654217) B1654217
theorem B1102887 : Blo 1100624 1102887 := bstep (se 1 (by rfl) ⟨827165, by rfl⟩ : syracuseStep 1102887 = 1654331) B1654331
theorem B1102927 : Blo 1100624 1102927 := bstep (se 1 (by rfl) ⟨827195, by rfl⟩ : syracuseStep 1102927 = 1654391) B1654391
theorem B1102943 : Blo 1100624 1102943 := bstep (se 1 (by rfl) ⟨827207, by rfl⟩ : syracuseStep 1102943 = 1654415) B1654415
theorem B1102971 : Blo 1100624 1102971 := bstep (se 1 (by rfl) ⟨827228, by rfl⟩ : syracuseStep 1102971 = 1654457) B1654457
theorem B1103023 : Blo 1100624 1103023 := bstep (se 1 (by rfl) ⟨827267, by rfl⟩ : syracuseStep 1103023 = 1654535) B1654535
theorem B1103047 : Blo 1100624 1103047 := bstep (se 1 (by rfl) ⟨827285, by rfl⟩ : syracuseStep 1103047 = 1654571) B1654571
theorem B1103067 : Blo 1100624 1103067 := bstep (se 1 (by rfl) ⟨827300, by rfl⟩ : syracuseStep 1103067 = 1654601) B1654601
theorem B1103143 : Blo 1100624 1103143 := bstep (se 1 (by rfl) ⟨827357, by rfl⟩ : syracuseStep 1103143 = 1654715) B1654715
theorem B1103183 : Blo 1100624 1103183 := bstep (se 1 (by rfl) ⟨827387, by rfl⟩ : syracuseStep 1103183 = 1654775) B1654775
theorem B1103199 : Blo 1100624 1103199 := bstep (se 1 (by rfl) ⟨827399, by rfl⟩ : syracuseStep 1103199 = 1654799) B1654799
theorem B3724649 : Blo 1100624 3724649 := bstep (se 2 (by rfl) ⟨1396743, by rfl⟩ : syracuseStep 3724649 = 2793487) B2793487
theorem B1103227 : Blo 1100624 1103227 := bstep (se 1 (by rfl) ⟨827420, by rfl⟩ : syracuseStep 1103227 = 1654841) B1654841
theorem B1103279 : Blo 1100624 1103279 := bstep (se 1 (by rfl) ⟨827459, by rfl⟩ : syracuseStep 1103279 = 1654919) B1654919
theorem B1103303 : Blo 1100624 1103303 := bstep (se 1 (by rfl) ⟨827477, by rfl⟩ : syracuseStep 1103303 = 1654955) B1654955
theorem B1103323 : Blo 1100624 1103323 := bstep (se 1 (by rfl) ⟨827492, by rfl⟩ : syracuseStep 1103323 = 1654985) B1654985
theorem B3134963 : Blo 1100624 3134963 := bstep (se 1 (by rfl) ⟨2351222, by rfl⟩ : syracuseStep 3134963 = 4702445) B4702445
theorem B4707827 : Blo 1100624 4707827 := bstep (se 1 (by rfl) ⟨3530870, by rfl⟩ : syracuseStep 4707827 = 7061741) B7061741
theorem B2479625 : Blo 1100624 2479625 := bstep (se 2 (by rfl) ⟨929859, by rfl⟩ : syracuseStep 2479625 = 1859719) B1859719
theorem B1103399 : Blo 1100624 1103399 := bstep (se 1 (by rfl) ⟨827549, by rfl⟩ : syracuseStep 1103399 = 1655099) B1655099
theorem B1103439 : Blo 1100624 1103439 := bstep (se 1 (by rfl) ⟨827579, by rfl⟩ : syracuseStep 1103439 = 1655159) B1655159
theorem B1103455 : Blo 1100624 1103455 := bstep (se 1 (by rfl) ⟨827591, by rfl⟩ : syracuseStep 1103455 = 1655183) B1655183
theorem B1103483 : Blo 1100624 1103483 := bstep (se 1 (by rfl) ⟨827612, by rfl⟩ : syracuseStep 1103483 = 1655225) B1655225
theorem B1103535 : Blo 1100624 1103535 := bstep (se 1 (by rfl) ⟨827651, by rfl⟩ : syracuseStep 1103535 = 1655303) B1655303
theorem B1103559 : Blo 1100624 1103559 := bstep (se 1 (by rfl) ⟨827669, by rfl⟩ : syracuseStep 1103559 = 1655339) B1655339
theorem B1103579 : Blo 1100624 1103579 := bstep (se 1 (by rfl) ⟨827684, by rfl⟩ : syracuseStep 1103579 = 1655369) B1655369
theorem B1103655 : Blo 1100624 1103655 := bstep (se 1 (by rfl) ⟨827741, by rfl⟩ : syracuseStep 1103655 = 1655483) B1655483
theorem B1103695 : Blo 1100624 1103695 := bstep (se 1 (by rfl) ⟨827771, by rfl⟩ : syracuseStep 1103695 = 1655543) B1655543
theorem B2479967 : Blo 1100624 2479967 := bstep (se 1 (by rfl) ⟨1859975, by rfl⟩ : syracuseStep 2479967 = 3719951) B3719951
theorem B1103711 : Blo 1100624 1103711 := bstep (se 1 (by rfl) ⟨827783, by rfl⟩ : syracuseStep 1103711 = 1655567) B1655567
theorem B1103739 : Blo 1100624 1103739 := bstep (se 1 (by rfl) ⟨827804, by rfl⟩ : syracuseStep 1103739 = 1655609) B1655609
theorem B1103791 : Blo 1100624 1103791 := bstep (se 1 (by rfl) ⟨827843, by rfl⟩ : syracuseStep 1103791 = 1655687) B1655687
theorem B3135419 : Blo 1100624 3135419 := bstep (se 1 (by rfl) ⟨2351564, by rfl⟩ : syracuseStep 3135419 = 4703129) B4703129
theorem B3725243 : Blo 1100624 3725243 := bstep (se 1 (by rfl) ⟨2793932, by rfl⟩ : syracuseStep 3725243 = 5587865) B5587865
theorem B1103815 : Blo 1100624 1103815 := bstep (se 1 (by rfl) ⟨827861, by rfl⟩ : syracuseStep 1103815 = 1655723) B1655723
theorem B1103835 : Blo 1100624 1103835 := bstep (se 1 (by rfl) ⟨827876, by rfl⟩ : syracuseStep 1103835 = 1655753) B1655753
theorem B2480147 : Blo 1100624 2480147 := bstep (se 1 (by rfl) ⟨1860110, by rfl⟩ : syracuseStep 2480147 = 3720221) B3720221
theorem B1103911 : Blo 1100624 1103911 := bstep (se 1 (by rfl) ⟨827933, by rfl⟩ : syracuseStep 1103911 = 1655867) B1655867
theorem B1857593 : Blo 1100624 1857593 := bstep (se 2 (by rfl) ⟨696597, by rfl⟩ : syracuseStep 1857593 = 1393195) B1393195
theorem B1103951 : Blo 1100624 1103951 := bstep (se 1 (by rfl) ⟨827963, by rfl⟩ : syracuseStep 1103951 = 1655927) B1655927
theorem B1103967 : Blo 1100624 1103967 := bstep (se 1 (by rfl) ⟨827975, by rfl⟩ : syracuseStep 1103967 = 1655951) B1655951
theorem B1103995 : Blo 1100624 1103995 := bstep (se 1 (by rfl) ⟨827996, by rfl⟩ : syracuseStep 1103995 = 1655993) B1655993
theorem B1104047 : Blo 1100624 1104047 := bstep (se 1 (by rfl) ⟨828035, by rfl⟩ : syracuseStep 1104047 = 1656071) B1656071
theorem B1104071 : Blo 1100624 1104071 := bstep (se 1 (by rfl) ⟨828053, by rfl⟩ : syracuseStep 1104071 = 1656107) B1656107
theorem B1104091 : Blo 1100624 1104091 := bstep (se 1 (by rfl) ⟨828068, by rfl⟩ : syracuseStep 1104091 = 1656137) B1656137
theorem B1104167 : Blo 1100624 1104167 := bstep (se 1 (by rfl) ⟨828125, by rfl⟩ : syracuseStep 1104167 = 1656251) B1656251
theorem B1104207 : Blo 1100624 1104207 := bstep (se 1 (by rfl) ⟨828155, by rfl⟩ : syracuseStep 1104207 = 1656311) B1656311
theorem B1104223 : Blo 1100624 1104223 := bstep (se 1 (by rfl) ⟨828167, by rfl⟩ : syracuseStep 1104223 = 1656335) B1656335
theorem B2480489 : Blo 1100624 2480489 := bstep (se 2 (by rfl) ⟨930183, by rfl⟩ : syracuseStep 2480489 = 1860367) B1860367
theorem B1104251 : Blo 1100624 1104251 := bstep (se 1 (by rfl) ⟨828188, by rfl⟩ : syracuseStep 1104251 = 1656377) B1656377
theorem B1104303 : Blo 1100624 1104303 := bstep (se 1 (by rfl) ⟨828227, by rfl⟩ : syracuseStep 1104303 = 1656455) B1656455
theorem B1104327 : Blo 1100624 1104327 := bstep (se 1 (by rfl) ⟨828245, by rfl⟩ : syracuseStep 1104327 = 1656491) B1656491
theorem B1104347 : Blo 1100624 1104347 := bstep (se 1 (by rfl) ⟨828260, by rfl⟩ : syracuseStep 1104347 = 1656521) B1656521
theorem B1104423 : Blo 1100624 1104423 := bstep (se 1 (by rfl) ⟨828317, by rfl⟩ : syracuseStep 1104423 = 1656635) B1656635
theorem B1104463 : Blo 1100624 1104463 := bstep (se 1 (by rfl) ⟨828347, by rfl⟩ : syracuseStep 1104463 = 1656695) B1656695
theorem B1104479 : Blo 1100624 1104479 := bstep (se 1 (by rfl) ⟨828359, by rfl⟩ : syracuseStep 1104479 = 1656719) B1656719
theorem B1104507 : Blo 1100624 1104507 := bstep (se 1 (by rfl) ⟨828380, by rfl⟩ : syracuseStep 1104507 = 1656761) B1656761
theorem B1104559 : Blo 1100624 1104559 := bstep (se 1 (by rfl) ⟨828419, by rfl⟩ : syracuseStep 1104559 = 1656839) B1656839
theorem B1104583 : Blo 1100624 1104583 := bstep (se 1 (by rfl) ⟨828437, by rfl⟩ : syracuseStep 1104583 = 1656875) B1656875
theorem B1104603 : Blo 1100624 1104603 := bstep (se 1 (by rfl) ⟨828452, by rfl⟩ : syracuseStep 1104603 = 1656905) B1656905
theorem B1858295 : Blo 1100624 1858295 := bstep (se 1 (by rfl) ⟨1393721, by rfl⟩ : syracuseStep 1858295 = 2787443) B2787443
theorem B3136249 : Blo 1100624 3136249 := bstep (se 2 (by rfl) ⟨1176093, by rfl⟩ : syracuseStep 3136249 = 2352187) B2352187
theorem B2120591 : Blo 1100624 2120591 := bstep (se 1 (by rfl) ⟨1590443, by rfl⟩ : syracuseStep 2120591 = 3180887) B3180887
theorem B10738615 : Blo 1100624 10738615 := bstep (se 1 (by rfl) ⟨8053961, by rfl⟩ : syracuseStep 10738615 = 16107923) B16107923
theorem B2481083 : Blo 1100624 2481083 := bstep (se 1 (by rfl) ⟨1860812, by rfl⟩ : syracuseStep 2481083 = 3721625) B3721625
theorem B2481209 : Blo 1100624 2481209 := bstep (se 2 (by rfl) ⟨930453, by rfl⟩ : syracuseStep 2481209 = 1860907) B1860907
theorem B1858639 : Blo 1100624 1858639 := bstep (se 1 (by rfl) ⟨1393979, by rfl⟩ : syracuseStep 1858639 = 2787959) B2787959
theorem B1531003 : Blo 1100624 1531003 := bstep (se 1 (by rfl) ⟨1148252, by rfl⟩ : syracuseStep 1531003 = 2296505) B2296505
theorem B1858889 : Blo 1100624 1858889 := bstep (se 2 (by rfl) ⟨697083, by rfl⟩ : syracuseStep 1858889 = 1394167) B1394167
theorem B2481551 : Blo 1100624 2481551 := bstep (se 1 (by rfl) ⟨1861163, by rfl⟩ : syracuseStep 2481551 = 3722327) B3722327
theorem B3726971 : Blo 1100624 3726971 := bstep (se 1 (by rfl) ⟨2795228, by rfl⟩ : syracuseStep 3726971 = 5590457) B5590457
theorem B2481875 : Blo 1100624 2481875 := bstep (se 1 (by rfl) ⟨1861406, by rfl⟩ : syracuseStep 2481875 = 3722813) B3722813
theorem B1859321 : Blo 1100624 1859321 := bstep (se 2 (by rfl) ⟨697245, by rfl⟩ : syracuseStep 1859321 = 1394491) B1394491
theorem B3727133 : Blo 1100624 3727133 := bstep (se 3 (by rfl) ⟨698837, by rfl⟩ : syracuseStep 3727133 = 1397675) B1397675
theorem B1859503 : Blo 1100624 1859503 := bstep (se 1 (by rfl) ⟨1394627, by rfl⟩ : syracuseStep 1859503 = 2789255) B2789255
theorem B4186039 : Blo 1100624 4186039 := bstep (se 1 (by rfl) ⟨3139529, by rfl⟩ : syracuseStep 4186039 = 6279059) B6279059
theorem B1859591 : Blo 1100624 1859591 := bstep (se 1 (by rfl) ⟨1394693, by rfl⟩ : syracuseStep 1859591 = 2789387) B2789387
theorem B3137707 : Blo 1100624 3137707 := bstep (se 1 (by rfl) ⟨2353280, by rfl⟩ : syracuseStep 3137707 = 4706561) B4706561
theorem B1859935 : Blo 1100624 1859935 := bstep (se 1 (by rfl) ⟨1394951, by rfl⟩ : syracuseStep 1859935 = 2789903) B2789903
theorem B3137935 : Blo 1100624 3137935 := bstep (se 1 (by rfl) ⟨2353451, by rfl⟩ : syracuseStep 3137935 = 4706903) B4706903
theorem B3531151 : Blo 1100624 3531151 := bstep (se 1 (by rfl) ⟨2648363, by rfl⟩ : syracuseStep 3531151 = 5296727) B5296727
theorem B4186511 : Blo 1100624 4186511 := bstep (se 1 (by rfl) ⟨3139883, by rfl⟩ : syracuseStep 4186511 = 6279767) B6279767
theorem B1860023 : Blo 1100624 1860023 := bstep (se 1 (by rfl) ⟨1395017, by rfl⟩ : syracuseStep 1860023 = 2790035) B2790035
theorem B3727835 : Blo 1100624 3727835 := bstep (se 1 (by rfl) ⟨2795876, by rfl⟩ : syracuseStep 3727835 = 5591753) B5591753
theorem B2482811 : Blo 1100624 2482811 := bstep (se 1 (by rfl) ⟨1862108, by rfl⟩ : syracuseStep 2482811 = 3724217) B3724217
theorem B2482937 : Blo 1100624 2482937 := bstep (se 2 (by rfl) ⟨931101, by rfl⟩ : syracuseStep 2482937 = 1862203) B1862203
theorem B2483207 : Blo 1100624 2483207 := bstep (se 1 (by rfl) ⟨1862405, by rfl⟩ : syracuseStep 2483207 = 3724811) B3724811
theorem B1860617 : Blo 1100624 1860617 := bstep (se 2 (by rfl) ⟨697731, by rfl⟩ : syracuseStep 1860617 = 1395463) B1395463
theorem B2483279 : Blo 1100624 2483279 := bstep (se 1 (by rfl) ⟨1862459, by rfl⟩ : syracuseStep 2483279 = 3724919) B3724919
theorem B26797175 : Blo 1100624 26797175 := bstep (se 1 (by rfl) ⟨20097881, by rfl⟩ : syracuseStep 26797175 = 40195763) B40195763
theorem B1860779 : Blo 1100624 1860779 := bstep (se 1 (by rfl) ⟨1395584, by rfl⟩ : syracuseStep 1860779 = 2791169) B2791169
theorem B1238215 : Blo 1100624 1238215 := bstep (se 1 (by rfl) ⟨928661, by rfl⟩ : syracuseStep 1238215 = 1857323) B1857323
theorem B2090195 : Blo 1100624 2090195 := bstep (se 1 (by rfl) ⟨1567646, by rfl⟩ : syracuseStep 2090195 = 3135293) B3135293
theorem B31810805 : Blo 1100624 31810805 := bstep (se 5 (by rfl) ⟨1491131, by rfl⟩ : syracuseStep 31810805 = 2982263) B2982263
theorem B4187497 : Blo 1100624 4187497 := bstep (se 2 (by rfl) ⟨1570311, by rfl⟩ : syracuseStep 4187497 = 3140623) B3140623
theorem B7464335 : Blo 1100624 7464335 := bstep (se 1 (by rfl) ⟨5598251, by rfl⟩ : syracuseStep 7464335 = 11196503) B11196503
theorem B2090423 : Blo 1100624 2090423 := bstep (se 1 (by rfl) ⟨1567817, by rfl⟩ : syracuseStep 2090423 = 3135635) B3135635
theorem B2483675 : Blo 1100624 2483675 := bstep (se 1 (by rfl) ⟨1862756, by rfl⟩ : syracuseStep 2483675 = 3725513) B3725513
theorem B1861177 : Blo 1100624 1861177 := bstep (se 2 (by rfl) ⟨697941, by rfl⟩ : syracuseStep 1861177 = 1395883) B1395883
theorem B4187771 : Blo 1100624 4187771 := bstep (se 1 (by rfl) ⟨3140828, by rfl⟩ : syracuseStep 4187771 = 6281657) B6281657
theorem B3139211 : Blo 1100624 3139211 := bstep (se 1 (by rfl) ⟨2354408, by rfl⟩ : syracuseStep 3139211 = 4708817) B4708817
theorem B1861319 : Blo 1100624 1861319 := bstep (se 1 (by rfl) ⟨1395989, by rfl⟩ : syracuseStep 1861319 = 2791979) B2791979
theorem B2647903 : Blo 1100624 2647903 := bstep (se 1 (by rfl) ⟨1985927, by rfl⟩ : syracuseStep 2647903 = 3971855) B3971855
theorem B1861481 : Blo 1100624 1861481 := bstep (se 2 (by rfl) ⟨698055, by rfl⟩ : syracuseStep 1861481 = 1396111) B1396111
theorem B2385839 : Blo 1100624 2385839 := bstep (se 1 (by rfl) ⟨1789379, by rfl⟩ : syracuseStep 2385839 = 3578759) B3578759
theorem B2484143 : Blo 1100624 2484143 := bstep (se 1 (by rfl) ⟨1863107, by rfl⟩ : syracuseStep 2484143 = 3726215) B3726215
theorem B1239079 : Blo 1100624 1239079 := bstep (se 1 (by rfl) ⟨929309, by rfl⟩ : syracuseStep 1239079 = 1858619) B1858619
theorem B2484395 : Blo 1100624 2484395 := bstep (se 1 (by rfl) ⟨1863296, by rfl⟩ : syracuseStep 2484395 = 3726593) B3726593
theorem B1861879 : Blo 1100624 1861879 := bstep (se 1 (by rfl) ⟨1396409, by rfl⟩ : syracuseStep 1861879 = 2792819) B2792819
theorem B12740915 : Blo 1100624 12740915 := bstep (se 1 (by rfl) ⟨9555686, by rfl⟩ : syracuseStep 12740915 = 19111373) B19111373
theorem B7268737 : Blo 1100624 7268737 := bstep (se 2 (by rfl) ⟨2725776, by rfl⟩ : syracuseStep 7268737 = 5451553) B5451553
theorem B1862075 : Blo 1100624 1862075 := bstep (se 1 (by rfl) ⟨1396556, by rfl⟩ : syracuseStep 1862075 = 2793113) B2793113
theorem B1862183 : Blo 1100624 1862183 := bstep (se 1 (by rfl) ⟨1396637, by rfl⟩ : syracuseStep 1862183 = 2793275) B2793275
theorem B2091577 : Blo 1100624 2091577 := bstep (se 2 (by rfl) ⟨784341, by rfl⟩ : syracuseStep 2091577 = 1568683) B1568683
theorem B2484935 : Blo 1100624 2484935 := bstep (se 1 (by rfl) ⟨1863701, by rfl⟩ : syracuseStep 2484935 = 3727403) B3727403
theorem B1862473 : Blo 1100624 1862473 := bstep (se 2 (by rfl) ⟨698427, by rfl⟩ : syracuseStep 1862473 = 1396855) B1396855
theorem B2091881 : Blo 1100624 2091881 := bstep (se 2 (by rfl) ⟨784455, by rfl⟩ : syracuseStep 2091881 = 1568911) B1568911
theorem B1862507 : Blo 1100624 1862507 := bstep (se 1 (by rfl) ⟨1396880, by rfl⟩ : syracuseStep 1862507 = 2793761) B2793761
theorem B2091919 : Blo 1100624 2091919 := bstep (se 1 (by rfl) ⟨1568939, by rfl⟩ : syracuseStep 2091919 = 3137879) B3137879
theorem B1764359 : Blo 1100624 1764359 := bstep (se 1 (by rfl) ⟨1323269, by rfl⟩ : syracuseStep 1764359 = 2646539) B2646539
theorem B2649095 : Blo 1100624 2649095 := bstep (se 1 (by rfl) ⟨1986821, by rfl⟩ : syracuseStep 2649095 = 3973643) B3973643
theorem B8940563 : Blo 1100624 8940563 := bstep (se 1 (by rfl) ⟨6705422, by rfl⟩ : syracuseStep 8940563 = 13410845) B13410845
theorem B3533843 : Blo 1100624 3533843 := bstep (se 1 (by rfl) ⟨2650382, by rfl⟩ : syracuseStep 3533843 = 5300765) B5300765
theorem B1567783 : Blo 1100624 1567783 := bstep (se 1 (by rfl) ⟨1175837, by rfl⟩ : syracuseStep 1567783 = 2351675) B2351675
theorem B2354255 : Blo 1100624 2354255 := bstep (se 1 (by rfl) ⟨1765691, by rfl⟩ : syracuseStep 2354255 = 3531383) B3531383
theorem B6286531 : Blo 1100624 6286531 := bstep (se 1 (by rfl) ⟨4714898, by rfl⟩ : syracuseStep 6286531 = 9429797) B9429797
theorem B1764551 : Blo 1100624 1764551 := bstep (se 1 (by rfl) ⟨1323413, by rfl⟩ : syracuseStep 1764551 = 2646827) B2646827
theorem B1862905 : Blo 1100624 1862905 := bstep (se 2 (by rfl) ⟨698589, by rfl⟩ : syracuseStep 1862905 = 1397179) B1397179
theorem B14511395 : Blo 1100624 14511395 := bstep (se 1 (by rfl) ⟨10883546, by rfl⟩ : syracuseStep 14511395 = 21767093) B21767093
theorem B1863175 : Blo 1100624 1863175 := bstep (se 1 (by rfl) ⟨1397381, by rfl⟩ : syracuseStep 1863175 = 2794763) B2794763
theorem B1240699 : Blo 1100624 1240699 := bstep (se 1 (by rfl) ⟨930524, by rfl⟩ : syracuseStep 1240699 = 1861049) B1861049
theorem B40300253 : Blo 1100624 40300253 := bstep (se 3 (by rfl) ⟨7556297, by rfl⟩ : syracuseStep 40300253 = 15112595) B15112595
theorem B2125673 : Blo 1100624 2125673 := bstep (se 2 (by rfl) ⟨797127, by rfl⟩ : syracuseStep 2125673 = 1594255) B1594255
theorem B1863607 : Blo 1100624 1863607 := bstep (se 1 (by rfl) ⟨1397705, by rfl⟩ : syracuseStep 1863607 = 2795411) B2795411
theorem B1241167 : Blo 1100624 1241167 := bstep (se 1 (by rfl) ⟨930875, by rfl⟩ : syracuseStep 1241167 = 1861751) B1861751
theorem B1863803 : Blo 1100624 1863803 := bstep (se 1 (by rfl) ⟨1397852, by rfl⟩ : syracuseStep 1863803 = 2795705) B2795705
theorem B17854789 : Blo 1100624 17854789 := bstep (se 4 (by rfl) ⟨1673886, by rfl⟩ : syracuseStep 17854789 = 3347773) B3347773
theorem B1765775 : Blo 1100624 1765775 := bstep (se 1 (by rfl) ⟨1324331, by rfl⟩ : syracuseStep 1765775 = 2648663) B2648663
theorem B1241563 : Blo 1100624 1241563 := bstep (se 1 (by rfl) ⟨931172, by rfl⟩ : syracuseStep 1241563 = 1862345) B1862345
theorem B2355809 : Blo 1100624 2355809 := bstep (se 2 (by rfl) ⟨883428, by rfl⟩ : syracuseStep 2355809 = 1766857) B1766857
theorem B2650747 : Blo 1100624 2650747 := bstep (se 1 (by rfl) ⟨1988060, by rfl⟩ : syracuseStep 2650747 = 3976121) B3976121
theorem B3535483 : Blo 1100624 3535483 := bstep (se 1 (by rfl) ⟨2651612, by rfl⟩ : syracuseStep 3535483 = 5303225) B5303225
theorem B11465425 : Blo 1100624 11465425 := bstep (se 2 (by rfl) ⟨4299534, by rfl⟩ : syracuseStep 11465425 = 8599069) B8599069
theorem B2093779 : Blo 1100624 2093779 := bstep (se 1 (by rfl) ⟨1570334, by rfl⟩ : syracuseStep 2093779 = 3140669) B3140669
theorem B4715293 : Blo 1100624 4715293 := bstep (se 3 (by rfl) ⟨884117, by rfl⟩ : syracuseStep 4715293 = 1768235) B1768235
theorem B10580843 : Blo 1100624 10580843 := bstep (se 1 (by rfl) ⟨7935632, by rfl⟩ : syracuseStep 10580843 = 15871265) B15871265
theorem B1242031 : Blo 1100624 1242031 := bstep (se 1 (by rfl) ⟨931523, by rfl⟩ : syracuseStep 1242031 = 1863047) B1863047
theorem B2094007 : Blo 1100624 2094007 := bstep (se 1 (by rfl) ⟨1570505, by rfl⟩ : syracuseStep 2094007 = 3141011) B3141011
theorem B3142583 : Blo 1100624 3142583 := bstep (se 1 (by rfl) ⟨2356937, by rfl⟩ : syracuseStep 3142583 = 4713875) B4713875
theorem B4191385 : Blo 1100624 4191385 := bstep (se 2 (by rfl) ⟨1571769, by rfl⟩ : syracuseStep 4191385 = 3143539) B3143539
theorem B1766729 : Blo 1100624 1766729 := bstep (se 2 (by rfl) ⟨662523, by rfl⟩ : syracuseStep 1766729 = 1325047) B1325047
theorem B1242463 : Blo 1100624 1242463 := bstep (se 1 (by rfl) ⟨931847, by rfl⟩ : syracuseStep 1242463 = 1863695) B1863695
theorem B4191689 : Blo 1100624 4191689 := bstep (se 2 (by rfl) ⟨1571883, by rfl⟩ : syracuseStep 4191689 = 3143767) B3143767
theorem B12547547 : Blo 1100624 12547547 := bstep (se 1 (by rfl) ⟨9410660, by rfl⟩ : syracuseStep 12547547 = 18821321) B18821321
theorem B2094599 : Blo 1100624 2094599 := bstep (se 1 (by rfl) ⟨1570949, by rfl⟩ : syracuseStep 2094599 = 3141899) B3141899
theorem B5666449 : Blo 1100624 5666449 := bstep (se 2 (by rfl) ⟨2124918, by rfl⟩ : syracuseStep 5666449 = 4249837) B4249837
theorem B3143357 : Blo 1100624 3143357 := bstep (se 3 (by rfl) ⟨589379, by rfl⟩ : syracuseStep 3143357 = 1178759) B1178759
theorem B2651977 : Blo 1100624 2651977 := bstep (se 2 (by rfl) ⟨994491, by rfl⟩ : syracuseStep 2651977 = 1988983) B1988983
theorem B3536713 : Blo 1100624 3536713 := bstep (se 2 (by rfl) ⟨1326267, by rfl⟩ : syracuseStep 3536713 = 2652535) B2652535
theorem B3143585 : Blo 1100624 3143585 := bstep (se 2 (by rfl) ⟨1178844, by rfl⟩ : syracuseStep 3143585 = 2357689) B2357689
theorem B4192175 : Blo 1100624 4192175 := bstep (se 1 (by rfl) ⟨3144131, by rfl⟩ : syracuseStep 4192175 = 6288263) B6288263
theorem B10582073 : Blo 1100624 10582073 := bstep (se 2 (by rfl) ⟨3968277, by rfl⟩ : syracuseStep 10582073 = 7936555) B7936555
theorem B2979919 : Blo 1100624 2979919 := bstep (se 1 (by rfl) ⟨2234939, by rfl⟩ : syracuseStep 2979919 = 4469879) B4469879
theorem B5666897 : Blo 1100624 5666897 := bstep (se 2 (by rfl) ⟨2125086, by rfl⟩ : syracuseStep 5666897 = 4250173) B4250173
theorem B11925593 : Blo 1100624 11925593 := bstep (se 2 (by rfl) ⟨4472097, by rfl⟩ : syracuseStep 11925593 = 8944195) B8944195
theorem B3143927 : Blo 1100624 3143927 := bstep (se 1 (by rfl) ⟨2357945, by rfl⟩ : syracuseStep 3143927 = 4715891) B4715891
theorem B2095465 : Blo 1100624 2095465 := bstep (se 2 (by rfl) ⟨785799, by rfl⟩ : syracuseStep 2095465 = 1571599) B1571599
theorem B3144041 : Blo 1100624 3144041 := bstep (se 2 (by rfl) ⟨1179015, by rfl⟩ : syracuseStep 3144041 = 2358031) B2358031
theorem B2357723 : Blo 1100624 2357723 := bstep (se 1 (by rfl) ⟨1768292, by rfl⟩ : syracuseStep 2357723 = 3536585) B3536585
theorem B2095625 : Blo 1100624 2095625 := bstep (se 2 (by rfl) ⟨785859, by rfl⟩ : syracuseStep 2095625 = 1571719) B1571719
theorem B6290405 : Blo 1100624 6290405 := bstep (se 4 (by rfl) ⟨589725, by rfl⟩ : syracuseStep 6290405 = 1179451) B1179451
theorem B3145225 : Blo 1100624 3145225 := bstep (se 2 (by rfl) ⟨1179459, by rfl⟩ : syracuseStep 3145225 = 2358919) B2358919
theorem B4193801 : Blo 1100624 4193801 := bstep (se 2 (by rfl) ⟨1572675, by rfl⟩ : syracuseStep 4193801 = 3145351) B3145351
theorem B3145567 : Blo 1100624 3145567 := bstep (se 1 (by rfl) ⟨2359175, by rfl⟩ : syracuseStep 3145567 = 4718351) B4718351
theorem B6717491 : Blo 1100624 6717491 := bstep (se 1 (by rfl) ⟨5038118, by rfl⟩ : syracuseStep 6717491 = 10076237) B10076237
theorem B5963881 : Blo 1100624 5963881 := bstep (se 2 (by rfl) ⟨2236455, by rfl⟩ : syracuseStep 5963881 = 4472911) B4472911
theorem B2786015 : Blo 1100624 2786015 := bstep (se 1 (by rfl) ⟨2089511, by rfl⟩ : syracuseStep 2786015 = 4179023) B4179023
theorem B2786683 : Blo 1100624 2786683 := bstep (se 1 (by rfl) ⟨2090012, by rfl⟩ : syracuseStep 2786683 = 4180025) B4180025
theorem B3016075 : Blo 1100624 3016075 := bstep (se 1 (by rfl) ⟨2262056, by rfl⟩ : syracuseStep 3016075 = 4524113) B4524113
theorem B2787119 : Blo 1100624 2787119 := bstep (se 1 (by rfl) ⟨2090339, by rfl⟩ : syracuseStep 2787119 = 4180679) B4180679
theorem B9079183 : Blo 1100624 9079183 := bstep (se 1 (by rfl) ⟨6809387, by rfl⟩ : syracuseStep 9079183 = 13618775) B13618775
theorem B2787767 : Blo 1100624 2787767 := bstep (se 1 (by rfl) ⟨2090825, by rfl⟩ : syracuseStep 2787767 = 4181651) B4181651
theorem B5573771 : Blo 1100624 5573771 := bstep (se 1 (by rfl) ⟨4180328, by rfl⟩ : syracuseStep 5573771 = 8360657) B8360657
theorem B8359199 : Blo 1100624 8359199 := bstep (se 1 (by rfl) ⟨6269399, by rfl⟩ : syracuseStep 8359199 = 12538799) B12538799
theorem B2788769 : Blo 1100624 2788769 := bstep (se 2 (by rfl) ⟨1045788, by rfl⟩ : syracuseStep 2788769 = 2091577) B2091577
theorem B2789225 : Blo 1100624 2789225 := bstep (se 2 (by rfl) ⟨1045959, by rfl⟩ : syracuseStep 2789225 = 2091919) B2091919
theorem B1118183 : Blo 1100624 1118183 := bstep (se 1 (by rfl) ⟨838637, by rfl⟩ : syracuseStep 1118183 = 1677275) B1677275
theorem B43487381 : Blo 1100624 43487381 := bstep (se 6 (by rfl) ⟨1019235, by rfl⟩ : syracuseStep 43487381 = 2038471) B2038471
theorem B4723051 : Blo 1100624 4723051 := bstep (se 1 (by rfl) ⟨3542288, by rfl⟩ : syracuseStep 4723051 = 7084577) B7084577
theorem B5575391 : Blo 1100624 5575391 := bstep (se 1 (by rfl) ⟨4181543, by rfl⟩ : syracuseStep 5575391 = 8363087) B8363087
theorem B2791007 : Blo 1100624 2791007 := bstep (se 1 (by rfl) ⟨2093255, by rfl⟩ : syracuseStep 2791007 = 4186511) B4186511
theorem B3348431 : Blo 1100624 3348431 := bstep (se 1 (by rfl) ⟨2511323, by rfl⟩ : syracuseStep 3348431 = 5022647) B5022647
theorem B11933729 : Blo 1100624 11933729 := bstep (se 2 (by rfl) ⟨4475148, by rfl⟩ : syracuseStep 11933729 = 8950297) B8950297
theorem B17864783 : Blo 1100624 17864783 := bstep (se 1 (by rfl) ⟨13398587, by rfl⟩ : syracuseStep 17864783 = 26797175) B26797175
theorem B21207203 : Blo 1100624 21207203 := bstep (se 1 (by rfl) ⟨15905402, by rfl⟩ : syracuseStep 21207203 = 31810805) B31810805
theorem B2791705 : Blo 1100624 2791705 := bstep (se 2 (by rfl) ⟨1046889, by rfl⟩ : syracuseStep 2791705 = 2093779) B2093779
theorem B2791847 : Blo 1100624 2791847 := bstep (se 1 (by rfl) ⟨2093885, by rfl⟩ : syracuseStep 2791847 = 4187771) B4187771
theorem B2792009 : Blo 1100624 2792009 := bstep (se 2 (by rfl) ⟨1047003, by rfl⟩ : syracuseStep 2792009 = 2094007) B2094007
theorem B8493943 : Blo 1100624 8493943 := bstep (se 1 (by rfl) ⟨6370457, by rfl⟩ : syracuseStep 8493943 = 12740915) B12740915
theorem B5577659 : Blo 1100624 5577659 := bstep (se 1 (by rfl) ⟨4183244, by rfl⟩ : syracuseStep 5577659 = 8366489) B8366489
theorem B2825567 : Blo 1100624 2825567 := bstep (se 1 (by rfl) ⟨2119175, by rfl⟩ : syracuseStep 2825567 = 4238351) B4238351
theorem B11902373 : Blo 1100624 11902373 := bstep (se 4 (by rfl) ⟨1115847, by rfl⟩ : syracuseStep 11902373 = 2231695) B2231695
theorem B2235847 : Blo 1100624 2235847 := bstep (se 1 (by rfl) ⟨1676885, by rfl⟩ : syracuseStep 2235847 = 3353771) B3353771
theorem B9674263 : Blo 1100624 9674263 := bstep (se 1 (by rfl) ⟨7255697, by rfl⟩ : syracuseStep 9674263 = 14511395) B14511395
theorem B3350279 : Blo 1100624 3350279 := bstep (se 1 (by rfl) ⟨2512709, by rfl⟩ : syracuseStep 3350279 = 5025419) B5025419
theorem B1417115 : Blo 1100624 1417115 := bstep (se 1 (by rfl) ⟨1062836, by rfl⟩ : syracuseStep 1417115 = 2125673) B2125673
theorem B3973225 : Blo 1100624 3973225 := bstep (se 2 (by rfl) ⟨1489959, by rfl⟩ : syracuseStep 3973225 = 2979919) B2979919
theorem B5578955 : Blo 1100624 5578955 := bstep (se 1 (by rfl) ⟨4184216, by rfl⟩ : syracuseStep 5578955 = 8368433) B8368433
theorem B2793953 : Blo 1100624 2793953 := bstep (se 2 (by rfl) ⟨1047732, by rfl⟩ : syracuseStep 2793953 = 2095465) B2095465
theorem B8364545 : Blo 1100624 8364545 := bstep (se 2 (by rfl) ⟨3136704, by rfl⟩ : syracuseStep 8364545 = 6273409) B6273409
theorem B7053895 : Blo 1100624 7053895 := bstep (se 1 (by rfl) ⟨5290421, by rfl⟩ : syracuseStep 7053895 = 10580843) B10580843
theorem B2794459 : Blo 1100624 2794459 := bstep (se 1 (by rfl) ⟨2095844, by rfl⟩ : syracuseStep 2794459 = 4191689) B4191689
theorem B8365031 : Blo 1100624 8365031 := bstep (se 1 (by rfl) ⟨6273773, by rfl⟩ : syracuseStep 8365031 = 12547547) B12547547
theorem B2794783 : Blo 1100624 2794783 := bstep (se 1 (by rfl) ⟨2096087, by rfl⟩ : syracuseStep 2794783 = 4192175) B4192175
theorem B7054715 : Blo 1100624 7054715 := bstep (se 1 (by rfl) ⟨5291036, by rfl⟩ : syracuseStep 7054715 = 10582073) B10582073
theorem B3777931 : Blo 1100624 3777931 := bstep (se 1 (by rfl) ⟨2833448, by rfl⟩ : syracuseStep 3777931 = 5666897) B5666897
theorem B2041337 : Blo 1100624 2041337 := bstep (se 2 (by rfl) ⟨765501, by rfl⟩ : syracuseStep 2041337 = 1531003) B1531003
theorem B23865637 : Blo 1100624 23865637 := bstep (se 4 (by rfl) ⟨2237403, by rfl⟩ : syracuseStep 23865637 = 4474807) B4474807
theorem B1255771 : Blo 1100624 1255771 := bstep (se 1 (by rfl) ⟨941828, by rfl⟩ : syracuseStep 1255771 = 1883657) B1883657
theorem B2795867 : Blo 1100624 2795867 := bstep (se 1 (by rfl) ⟨2096900, by rfl⟩ : syracuseStep 2795867 = 4193801) B4193801
theorem B5581223 : Blo 1100624 5581223 := bstep (se 1 (by rfl) ⟨4185917, by rfl⟩ : syracuseStep 5581223 = 8371835) B8371835
theorem B5581385 : Blo 1100624 5581385 := bstep (se 2 (by rfl) ⟨2093019, by rfl⟩ : syracuseStep 5581385 = 4186039) B4186039
theorem B15281167 : Blo 1100624 15281167 := bstep (se 1 (by rfl) ⟨11460875, by rfl⟩ : syracuseStep 15281167 = 22921751) B22921751
theorem B3976411 : Blo 1100624 3976411 := bstep (se 1 (by rfl) ⟨2982308, by rfl⟩ : syracuseStep 3976411 = 5964617) B5964617
theorem B1322731 : Blo 1100624 1322731 := bstep (se 1 (by rfl) ⟨992048, by rfl⟩ : syracuseStep 1322731 = 1984097) B1984097
theorem B6270767 : Blo 1100624 6270767 := bstep (se 1 (by rfl) ⟨4703075, by rfl⟩ : syracuseStep 6270767 = 9406151) B9406151
theorem B1650953 : Blo 1100624 1650953 := bstep (se 2 (by rfl) ⟨619107, by rfl⟩ : syracuseStep 1650953 = 1238215) B1238215
theorem B1651055 : Blo 1100624 1651055 := bstep (se 1 (by rfl) ⟨1238291, by rfl⟩ : syracuseStep 1651055 = 2476583) B2476583
theorem B6271451 : Blo 1100624 6271451 := bstep (se 1 (by rfl) ⟨4703588, by rfl⟩ : syracuseStep 6271451 = 9407177) B9407177
theorem B5583329 : Blo 1100624 5583329 := bstep (se 2 (by rfl) ⟨2093748, by rfl⟩ : syracuseStep 5583329 = 4187497) B4187497
theorem B1651271 : Blo 1100624 1651271 := bstep (se 1 (by rfl) ⟨1238453, by rfl⟩ : syracuseStep 1651271 = 2476907) B2476907
theorem B1651307 : Blo 1100624 1651307 := bstep (se 1 (by rfl) ⟨1238480, by rfl⟩ : syracuseStep 1651307 = 2476961) B2476961
theorem B11940473 : Blo 1100624 11940473 := bstep (se 2 (by rfl) ⟨4477677, by rfl⟩ : syracuseStep 11940473 = 8955355) B8955355
theorem B43037381 : Blo 1100624 43037381 := bstep (se 4 (by rfl) ⟨4034754, by rfl⟩ : syracuseStep 43037381 = 8069509) B8069509
theorem B50869043 : Blo 1100624 50869043 := bstep (se 1 (by rfl) ⟨38151782, by rfl⟩ : syracuseStep 50869043 = 76303565) B76303565
theorem B8926031 : Blo 1100624 8926031 := bstep (se 1 (by rfl) ⟨6694523, by rfl⟩ : syracuseStep 8926031 = 13389047) B13389047
theorem B1651535 : Blo 1100624 1651535 := bstep (se 1 (by rfl) ⟨1238651, by rfl⟩ : syracuseStep 1651535 = 2477303) B2477303
theorem B1651931 : Blo 1100624 1651931 := bstep (se 1 (by rfl) ⟨1238948, by rfl⟩ : syracuseStep 1651931 = 2477897) B2477897
theorem B1652105 : Blo 1100624 1652105 := bstep (se 2 (by rfl) ⟨619539, by rfl⟩ : syracuseStep 1652105 = 1239079) B1239079
theorem B3716765 : Blo 1100624 3716765 := bstep (se 3 (by rfl) ⟨696893, by rfl⟩ : syracuseStep 3716765 = 1393787) B1393787
theorem B1652459 : Blo 1100624 1652459 := bstep (se 1 (by rfl) ⟨1239344, by rfl⟩ : syracuseStep 1652459 = 2478689) B2478689
theorem B1652687 : Blo 1100624 1652687 := bstep (se 1 (by rfl) ⟨1239515, by rfl⟩ : syracuseStep 1652687 = 2479031) B2479031
theorem B3717305 : Blo 1100624 3717305 := bstep (se 2 (by rfl) ⟨1393989, by rfl⟩ : syracuseStep 3717305 = 2787979) B2787979
theorem B10598681 : Blo 1100624 10598681 := bstep (se 2 (by rfl) ⟨3974505, by rfl⟩ : syracuseStep 10598681 = 7949011) B7949011
theorem B23837003 : Blo 1100624 23837003 := bstep (se 1 (by rfl) ⟨17877752, by rfl⟩ : syracuseStep 23837003 = 35755505) B35755505
theorem B1653083 : Blo 1100624 1653083 := bstep (se 1 (by rfl) ⟨1239812, by rfl⟩ : syracuseStep 1653083 = 2479625) B2479625
theorem B5814823 : Blo 1100624 5814823 := bstep (se 1 (by rfl) ⟨4361117, by rfl⟩ : syracuseStep 5814823 = 8722235) B8722235
theorem B5290559 : Blo 1100624 5290559 := bstep (se 1 (by rfl) ⟨3967919, by rfl⟩ : syracuseStep 5290559 = 7935839) B7935839
theorem B1653311 : Blo 1100624 1653311 := bstep (se 1 (by rfl) ⟨1239983, by rfl⟩ : syracuseStep 1653311 = 2479967) B2479967
theorem B8370863 : Blo 1100624 8370863 := bstep (se 1 (by rfl) ⟨6278147, by rfl⟩ : syracuseStep 8370863 = 12556295) B12556295
theorem B1653431 : Blo 1100624 1653431 := bstep (se 1 (by rfl) ⟨1240073, by rfl⟩ : syracuseStep 1653431 = 2480147) B2480147
theorem B5585597 : Blo 1100624 5585597 := bstep (se 3 (by rfl) ⟨1047299, by rfl⟩ : syracuseStep 5585597 = 2094599) B2094599
theorem B6273935 : Blo 1100624 6273935 := bstep (se 1 (by rfl) ⟨4705451, by rfl⟩ : syracuseStep 6273935 = 9410903) B9410903
theorem B1653659 : Blo 1100624 1653659 := bstep (se 1 (by rfl) ⟨1240244, by rfl⟩ : syracuseStep 1653659 = 2480489) B2480489
theorem B1654055 : Blo 1100624 1654055 := bstep (se 1 (by rfl) ⟨1240541, by rfl⟩ : syracuseStep 1654055 = 2481083) B2481083
theorem B1654139 : Blo 1100624 1654139 := bstep (se 1 (by rfl) ⟨1240604, by rfl⟩ : syracuseStep 1654139 = 2481209) B2481209
theorem B1654265 : Blo 1100624 1654265 := bstep (se 2 (by rfl) ⟨620349, by rfl⟩ : syracuseStep 1654265 = 1240699) B1240699
theorem B9420299 : Blo 1100624 9420299 := bstep (se 1 (by rfl) ⟨7065224, by rfl⟩ : syracuseStep 9420299 = 14130449) B14130449
theorem B1654367 : Blo 1100624 1654367 := bstep (se 1 (by rfl) ⟨1240775, by rfl⟩ : syracuseStep 1654367 = 2481551) B2481551
theorem B3718817 : Blo 1100624 3718817 := bstep (se 2 (by rfl) ⟨1394556, by rfl⟩ : syracuseStep 3718817 = 2789113) B2789113
theorem B7061255 : Blo 1100624 7061255 := bstep (se 1 (by rfl) ⟨5295941, by rfl⟩ : syracuseStep 7061255 = 10591883) B10591883
theorem B4472617 : Blo 1100624 4472617 := bstep (se 2 (by rfl) ⟨1677231, by rfl⟩ : syracuseStep 4472617 = 3354463) B3354463
theorem B1654583 : Blo 1100624 1654583 := bstep (se 1 (by rfl) ⟨1240937, by rfl⟩ : syracuseStep 1654583 = 2481875) B2481875
theorem B11321147 : Blo 1100624 11321147 := bstep (se 1 (by rfl) ⟨8490860, by rfl⟩ : syracuseStep 11321147 = 16981721) B16981721
theorem B1654889 : Blo 1100624 1654889 := bstep (se 2 (by rfl) ⟨620583, by rfl⟩ : syracuseStep 1654889 = 1241167) B1241167
theorem B1655207 : Blo 1100624 1655207 := bstep (se 1 (by rfl) ⟨1241405, by rfl⟩ : syracuseStep 1655207 = 2482811) B2482811
theorem B23806385 : Blo 1100624 23806385 := bstep (se 2 (by rfl) ⟨8927394, by rfl⟩ : syracuseStep 23806385 = 17854789) B17854789
theorem B1655291 : Blo 1100624 1655291 := bstep (se 1 (by rfl) ⟨1241468, by rfl⟩ : syracuseStep 1655291 = 2482937) B2482937
theorem B3719681 : Blo 1100624 3719681 := bstep (se 2 (by rfl) ⟨1394880, by rfl⟩ : syracuseStep 3719681 = 2789761) B2789761
theorem B8372807 : Blo 1100624 8372807 := bstep (se 1 (by rfl) ⟨6279605, by rfl⟩ : syracuseStep 8372807 = 12559211) B12559211
theorem B1655417 : Blo 1100624 1655417 := bstep (se 2 (by rfl) ⟨620781, by rfl⟩ : syracuseStep 1655417 = 1241563) B1241563
theorem B1655471 : Blo 1100624 1655471 := bstep (se 1 (by rfl) ⟨1241603, by rfl⟩ : syracuseStep 1655471 = 2483207) B2483207
theorem B441762497 : Blo 1100624 441762497 := bstep (se 2 (by rfl) ⟨165660936, by rfl⟩ : syracuseStep 441762497 = 331321873) B331321873
theorem B1655519 : Blo 1100624 1655519 := bstep (se 1 (by rfl) ⟨1241639, by rfl⟩ : syracuseStep 1655519 = 2483279) B2483279
theorem B1393463 : Blo 1100624 1393463 := bstep (se 1 (by rfl) ⟨1045097, by rfl⟩ : syracuseStep 1393463 = 2090195) B2090195
theorem B15287233 : Blo 1100624 15287233 := bstep (se 2 (by rfl) ⟨5732712, by rfl⟩ : syracuseStep 15287233 = 11465425) B11465425
theorem B1393615 : Blo 1100624 1393615 := bstep (se 1 (by rfl) ⟨1045211, by rfl⟩ : syracuseStep 1393615 = 2090423) B2090423
theorem B5293019 : Blo 1100624 5293019 := bstep (se 1 (by rfl) ⟨3969764, by rfl⟩ : syracuseStep 5293019 = 7939529) B7939529
theorem B3720167 : Blo 1100624 3720167 := bstep (se 1 (by rfl) ⟨2790125, by rfl⟩ : syracuseStep 3720167 = 5580251) B5580251
theorem B1655783 : Blo 1100624 1655783 := bstep (se 1 (by rfl) ⟨1241837, by rfl⟩ : syracuseStep 1655783 = 2483675) B2483675
theorem B1656041 : Blo 1100624 1656041 := bstep (se 2 (by rfl) ⟨621015, by rfl⟩ : syracuseStep 1656041 = 1242031) B1242031
theorem B1590559 : Blo 1100624 1590559 := bstep (se 1 (by rfl) ⟨1192919, by rfl⟩ : syracuseStep 1590559 = 2385839) B2385839
theorem B1656095 : Blo 1100624 1656095 := bstep (se 1 (by rfl) ⟨1242071, by rfl⟩ : syracuseStep 1656095 = 2484143) B2484143
theorem B3720491 : Blo 1100624 3720491 := bstep (se 1 (by rfl) ⟨2790368, by rfl⟩ : syracuseStep 3720491 = 5580737) B5580737
theorem B5293421 : Blo 1100624 5293421 := bstep (se 3 (by rfl) ⟨992516, by rfl⟩ : syracuseStep 5293421 = 1985033) B1985033
theorem B12567959 : Blo 1100624 12567959 := bstep (se 1 (by rfl) ⟨9425969, by rfl⟩ : syracuseStep 12567959 = 18851939) B18851939
theorem B1656263 : Blo 1100624 1656263 := bstep (se 1 (by rfl) ⟨1242197, by rfl⟩ : syracuseStep 1656263 = 2484395) B2484395
theorem B5588513 : Blo 1100624 5588513 := bstep (se 2 (by rfl) ⟨2095692, by rfl⟩ : syracuseStep 5588513 = 4191385) B4191385
theorem B3720761 : Blo 1100624 3720761 := bstep (se 2 (by rfl) ⟨1395285, by rfl⟩ : syracuseStep 3720761 = 2790571) B2790571
theorem B1656617 : Blo 1100624 1656617 := bstep (se 2 (by rfl) ⟨621231, by rfl⟩ : syracuseStep 1656617 = 1242463) B1242463
theorem B1656623 : Blo 1100624 1656623 := bstep (se 1 (by rfl) ⟨1242467, by rfl⟩ : syracuseStep 1656623 = 2484935) B2484935
theorem B1394587 : Blo 1100624 1394587 := bstep (se 1 (by rfl) ⟨1045940, by rfl⟩ : syracuseStep 1394587 = 2091881) B2091881
theorem B9422963 : Blo 1100624 9422963 := bstep (se 1 (by rfl) ⟨7067222, by rfl⟩ : syracuseStep 9422963 = 14134445) B14134445
theorem B7555265 : Blo 1100624 7555265 := bstep (se 2 (by rfl) ⟨2833224, by rfl⟩ : syracuseStep 7555265 = 5666449) B5666449
theorem B7063919 : Blo 1100624 7063919 := bstep (se 1 (by rfl) ⟨5297939, by rfl⟩ : syracuseStep 7063919 = 10595879) B10595879
theorem B5654909 : Blo 1100624 5654909 := bstep (se 3 (by rfl) ⟨1060295, by rfl⟩ : syracuseStep 5654909 = 2120591) B2120591
theorem B6048229 : Blo 1100624 6048229 := bstep (se 4 (by rfl) ⟨567021, by rfl⟩ : syracuseStep 6048229 = 1134043) B1134043
theorem B2476727 : Blo 1100624 2476727 := bstep (se 1 (by rfl) ⟨1857545, by rfl⟩ : syracuseStep 2476727 = 3715091) B3715091
theorem B3722003 : Blo 1100624 3722003 := bstep (se 1 (by rfl) ⟨2791502, by rfl⟩ : syracuseStep 3722003 = 5583005) B5583005
theorem B7064455 : Blo 1100624 7064455 := bstep (se 1 (by rfl) ⟨5298341, by rfl⟩ : syracuseStep 7064455 = 10596683) B10596683
theorem B2476943 : Blo 1100624 2476943 := bstep (se 1 (by rfl) ⟨1857707, by rfl⟩ : syracuseStep 2476943 = 3715415) B3715415
theorem B1100699 : Blo 1100624 1100699 := bstep (se 1 (by rfl) ⟨825524, by rfl⟩ : syracuseStep 1100699 = 1651049) B1651049
theorem B1100751 : Blo 1100624 1100751 := bstep (se 1 (by rfl) ⟨825563, by rfl⟩ : syracuseStep 1100751 = 1651127) B1651127
theorem B1100775 : Blo 1100624 1100775 := bstep (se 1 (by rfl) ⟨825581, by rfl⟩ : syracuseStep 1100775 = 1651163) B1651163
theorem B1101087 : Blo 1100624 1101087 := bstep (se 1 (by rfl) ⟨825815, by rfl⟩ : syracuseStep 1101087 = 1651631) B1651631
theorem B1101147 : Blo 1100624 1101147 := bstep (se 1 (by rfl) ⟨825860, by rfl⟩ : syracuseStep 1101147 = 1651721) B1651721
theorem B1101167 : Blo 1100624 1101167 := bstep (se 1 (by rfl) ⟨825875, by rfl⟩ : syracuseStep 1101167 = 1651751) B1651751
theorem B1101223 : Blo 1100624 1101223 := bstep (se 1 (by rfl) ⟨825917, by rfl⟩ : syracuseStep 1101223 = 1651835) B1651835
theorem B1101307 : Blo 1100624 1101307 := bstep (se 1 (by rfl) ⟨825980, by rfl⟩ : syracuseStep 1101307 = 1651961) B1651961
theorem B1101375 : Blo 1100624 1101375 := bstep (se 1 (by rfl) ⟨826031, by rfl⟩ : syracuseStep 1101375 = 1652063) B1652063
theorem B1101383 : Blo 1100624 1101383 := bstep (se 1 (by rfl) ⟨826037, by rfl⟩ : syracuseStep 1101383 = 1652075) B1652075
theorem B2477663 : Blo 1100624 2477663 := bstep (se 1 (by rfl) ⟨1858247, by rfl⟩ : syracuseStep 2477663 = 3716495) B3716495
theorem B3722867 : Blo 1100624 3722867 := bstep (se 1 (by rfl) ⟨2792150, by rfl⟩ : syracuseStep 3722867 = 5584301) B5584301
theorem B4181665 : Blo 1100624 4181665 := bstep (se 2 (by rfl) ⟨1568124, by rfl⟩ : syracuseStep 4181665 = 3136249) B3136249
theorem B1101535 : Blo 1100624 1101535 := bstep (se 1 (by rfl) ⟨826151, by rfl⟩ : syracuseStep 1101535 = 1652303) B1652303
theorem B1101615 : Blo 1100624 1101615 := bstep (se 1 (by rfl) ⟨826211, by rfl⟩ : syracuseStep 1101615 = 1652423) B1652423
theorem B2477879 : Blo 1100624 2477879 := bstep (se 1 (by rfl) ⟨1858409, by rfl⟩ : syracuseStep 2477879 = 3716819) B3716819
theorem B3723137 : Blo 1100624 3723137 := bstep (se 2 (by rfl) ⟨1396176, by rfl⟩ : syracuseStep 3723137 = 2792353) B2792353
theorem B1101723 : Blo 1100624 1101723 := bstep (se 1 (by rfl) ⟨826292, by rfl⟩ : syracuseStep 1101723 = 1652585) B1652585
theorem B1101775 : Blo 1100624 1101775 := bstep (se 1 (by rfl) ⟨826331, by rfl⟩ : syracuseStep 1101775 = 1652663) B1652663
theorem B1101799 : Blo 1100624 1101799 := bstep (se 1 (by rfl) ⟨826349, by rfl⟩ : syracuseStep 1101799 = 1652699) B1652699
theorem B7950395 : Blo 1100624 7950395 := bstep (se 1 (by rfl) ⟨5962796, by rfl⟩ : syracuseStep 7950395 = 11925593) B11925593
theorem B2478185 : Blo 1100624 2478185 := bstep (se 2 (by rfl) ⟨929319, by rfl⟩ : syracuseStep 2478185 = 1858639) B1858639
theorem B1102111 : Blo 1100624 1102111 := bstep (se 1 (by rfl) ⟨826583, by rfl⟩ : syracuseStep 1102111 = 1653167) B1653167
theorem B1102171 : Blo 1100624 1102171 := bstep (se 1 (by rfl) ⟨826628, by rfl⟩ : syracuseStep 1102171 = 1653257) B1653257
theorem B1397083 : Blo 1100624 1397083 := bstep (se 1 (by rfl) ⟨1047812, by rfl⟩ : syracuseStep 1397083 = 2095625) B2095625
theorem B1102191 : Blo 1100624 1102191 := bstep (se 1 (by rfl) ⟨826643, by rfl⟩ : syracuseStep 1102191 = 1653287) B1653287
theorem B1102247 : Blo 1100624 1102247 := bstep (se 1 (by rfl) ⟨826685, by rfl⟩ : syracuseStep 1102247 = 1653371) B1653371
theorem B1102331 : Blo 1100624 1102331 := bstep (se 1 (by rfl) ⟨826748, by rfl⟩ : syracuseStep 1102331 = 1653497) B1653497
theorem B1102399 : Blo 1100624 1102399 := bstep (se 1 (by rfl) ⟨826799, by rfl⟩ : syracuseStep 1102399 = 1653599) B1653599
theorem B1102407 : Blo 1100624 1102407 := bstep (se 1 (by rfl) ⟨826805, by rfl⟩ : syracuseStep 1102407 = 1653611) B1653611
theorem B2478671 : Blo 1100624 2478671 := bstep (se 1 (by rfl) ⟨1859003, by rfl⟩ : syracuseStep 2478671 = 3718007) B3718007
theorem B3723947 : Blo 1100624 3723947 := bstep (se 1 (by rfl) ⟨2792960, by rfl⟩ : syracuseStep 3723947 = 5585921) B5585921
theorem B2478815 : Blo 1100624 2478815 := bstep (se 1 (by rfl) ⟨1859111, by rfl⟩ : syracuseStep 2478815 = 3718223) B3718223
theorem B1102559 : Blo 1100624 1102559 := bstep (se 1 (by rfl) ⟨826919, by rfl⟩ : syracuseStep 1102559 = 1653839) B1653839
theorem B1102639 : Blo 1100624 1102639 := bstep (se 1 (by rfl) ⟨826979, by rfl⟩ : syracuseStep 1102639 = 1653959) B1653959
theorem B1102747 : Blo 1100624 1102747 := bstep (se 1 (by rfl) ⟨827060, by rfl⟩ : syracuseStep 1102747 = 1654121) B1654121
theorem B1102799 : Blo 1100624 1102799 := bstep (se 1 (by rfl) ⟨827099, by rfl⟩ : syracuseStep 1102799 = 1654199) B1654199
theorem B2479067 : Blo 1100624 2479067 := bstep (se 1 (by rfl) ⟨1859300, by rfl⟩ : syracuseStep 2479067 = 3718601) B3718601
theorem B1102823 : Blo 1100624 1102823 := bstep (se 1 (by rfl) ⟨827117, by rfl⟩ : syracuseStep 1102823 = 1654235) B1654235
theorem B2479247 : Blo 1100624 2479247 := bstep (se 1 (by rfl) ⟨1859435, by rfl⟩ : syracuseStep 2479247 = 3718871) B3718871
theorem B3724487 : Blo 1100624 3724487 := bstep (se 1 (by rfl) ⟨2793365, by rfl⟩ : syracuseStep 3724487 = 5586731) B5586731
theorem B2479337 : Blo 1100624 2479337 := bstep (se 2 (by rfl) ⟨929751, by rfl⟩ : syracuseStep 2479337 = 1859503) B1859503
theorem B2479391 : Blo 1100624 2479391 := bstep (se 1 (by rfl) ⟨1859543, by rfl⟩ : syracuseStep 2479391 = 3719087) B3719087
theorem B1103135 : Blo 1100624 1103135 := bstep (se 1 (by rfl) ⟨827351, by rfl⟩ : syracuseStep 1103135 = 1654703) B1654703
theorem B1103195 : Blo 1100624 1103195 := bstep (se 1 (by rfl) ⟨827396, by rfl⟩ : syracuseStep 1103195 = 1654793) B1654793
theorem B1103215 : Blo 1100624 1103215 := bstep (se 1 (by rfl) ⟨827411, by rfl⟩ : syracuseStep 1103215 = 1654823) B1654823
theorem B1103271 : Blo 1100624 1103271 := bstep (se 1 (by rfl) ⟨827453, by rfl⟩ : syracuseStep 1103271 = 1654907) B1654907
theorem B1103355 : Blo 1100624 1103355 := bstep (se 1 (by rfl) ⟨827516, by rfl⟩ : syracuseStep 1103355 = 1655033) B1655033
theorem B4183609 : Blo 1100624 4183609 := bstep (se 2 (by rfl) ⟨1568853, by rfl⟩ : syracuseStep 4183609 = 3137707) B3137707
theorem B1103423 : Blo 1100624 1103423 := bstep (se 1 (by rfl) ⟨827567, by rfl⟩ : syracuseStep 1103423 = 1655135) B1655135
theorem B1103431 : Blo 1100624 1103431 := bstep (se 1 (by rfl) ⟨827573, by rfl⟩ : syracuseStep 1103431 = 1655147) B1655147
theorem B1103583 : Blo 1100624 1103583 := bstep (se 1 (by rfl) ⟨827687, by rfl⟩ : syracuseStep 1103583 = 1655375) B1655375
theorem B35739407 : Blo 1100624 35739407 := bstep (se 1 (by rfl) ⟨26804555, by rfl⟩ : syracuseStep 35739407 = 53609111) B53609111
theorem B2479913 : Blo 1100624 2479913 := bstep (se 2 (by rfl) ⟨929967, by rfl⟩ : syracuseStep 2479913 = 1859935) B1859935
theorem B1103663 : Blo 1100624 1103663 := bstep (se 1 (by rfl) ⟨827747, by rfl⟩ : syracuseStep 1103663 = 1655495) B1655495
theorem B4183913 : Blo 1100624 4183913 := bstep (se 2 (by rfl) ⟨1568967, by rfl⟩ : syracuseStep 4183913 = 3137935) B3137935
theorem B4708201 : Blo 1100624 4708201 := bstep (se 2 (by rfl) ⟨1765575, by rfl⟩ : syracuseStep 4708201 = 3531151) B3531151
theorem B1103771 : Blo 1100624 1103771 := bstep (se 1 (by rfl) ⟨827828, by rfl⟩ : syracuseStep 1103771 = 1655657) B1655657
theorem B1103823 : Blo 1100624 1103823 := bstep (se 1 (by rfl) ⟨827867, by rfl⟩ : syracuseStep 1103823 = 1655735) B1655735
theorem B1103847 : Blo 1100624 1103847 := bstep (se 1 (by rfl) ⟨827885, by rfl⟩ : syracuseStep 1103847 = 1655771) B1655771
theorem B15915041 : Blo 1100624 15915041 := bstep (se 2 (by rfl) ⟨5968140, by rfl⟩ : syracuseStep 15915041 = 11936281) B11936281
theorem B23877665 : Blo 1100624 23877665 := bstep (se 2 (by rfl) ⟨8954124, by rfl⟩ : syracuseStep 23877665 = 17908249) B17908249
theorem B1104159 : Blo 1100624 1104159 := bstep (se 1 (by rfl) ⟨828119, by rfl⟩ : syracuseStep 1104159 = 1656239) B1656239
theorem B2545993 : Blo 1100624 2545993 := bstep (se 2 (by rfl) ⟨954747, by rfl⟩ : syracuseStep 2545993 = 1909495) B1909495
theorem B1857883 : Blo 1100624 1857883 := bstep (se 1 (by rfl) ⟨1393412, by rfl⟩ : syracuseStep 1857883 = 2786825) B2786825
theorem B1104219 : Blo 1100624 1104219 := bstep (se 1 (by rfl) ⟨828164, by rfl⟩ : syracuseStep 1104219 = 1656329) B1656329
theorem B1104239 : Blo 1100624 1104239 := bstep (se 1 (by rfl) ⟨828179, by rfl⟩ : syracuseStep 1104239 = 1656359) B1656359
theorem B1104295 : Blo 1100624 1104295 := bstep (se 1 (by rfl) ⟨828221, by rfl⟩ : syracuseStep 1104295 = 1656443) B1656443
theorem B1104379 : Blo 1100624 1104379 := bstep (se 1 (by rfl) ⟨828284, by rfl⟩ : syracuseStep 1104379 = 1656569) B1656569
theorem B1104447 : Blo 1100624 1104447 := bstep (se 1 (by rfl) ⟨828335, by rfl⟩ : syracuseStep 1104447 = 1656671) B1656671
theorem B1104455 : Blo 1100624 1104455 := bstep (se 1 (by rfl) ⟨828341, by rfl⟩ : syracuseStep 1104455 = 1656683) B1656683
theorem B2644559 : Blo 1100624 2644559 := bstep (se 1 (by rfl) ⟨1983419, by rfl⟩ : syracuseStep 2644559 = 3966839) B3966839
theorem B3529295 : Blo 1100624 3529295 := bstep (se 1 (by rfl) ⟨2646971, by rfl⟩ : syracuseStep 3529295 = 5293943) B5293943
theorem B5298767 : Blo 1100624 5298767 := bstep (se 1 (by rfl) ⟨3974075, by rfl⟩ : syracuseStep 5298767 = 7948151) B7948151
theorem B3725999 : Blo 1100624 3725999 := bstep (se 1 (by rfl) ⟨2794499, by rfl⟩ : syracuseStep 3725999 = 5588999) B5588999
theorem B1104607 : Blo 1100624 1104607 := bstep (se 1 (by rfl) ⟨828455, by rfl⟩ : syracuseStep 1104607 = 1656911) B1656911
theorem B2480975 : Blo 1100624 2480975 := bstep (se 1 (by rfl) ⟨1860731, by rfl⟩ : syracuseStep 2480975 = 3721463) B3721463
theorem B6282157 : Blo 1100624 6282157 := bstep (se 3 (by rfl) ⟨1177904, by rfl⟩ : syracuseStep 6282157 = 2355809) B2355809
theorem B15063995 : Blo 1100624 15063995 := bstep (se 1 (by rfl) ⟨11297996, by rfl⟩ : syracuseStep 15063995 = 22595993) B22595993
theorem B3726323 : Blo 1100624 3726323 := bstep (se 1 (by rfl) ⟨2794742, by rfl⟩ : syracuseStep 3726323 = 5589485) B5589485
theorem B2481191 : Blo 1100624 2481191 := bstep (se 1 (by rfl) ⟨1860893, by rfl⟩ : syracuseStep 2481191 = 3721787) B3721787
theorem B2481371 : Blo 1100624 2481371 := bstep (se 1 (by rfl) ⟨1861028, by rfl⟩ : syracuseStep 2481371 = 3722057) B3722057
theorem B1858855 : Blo 1100624 1858855 := bstep (se 1 (by rfl) ⟨1394141, by rfl⟩ : syracuseStep 1858855 = 2788283) B2788283
theorem B24141199 : Blo 1100624 24141199 := bstep (se 1 (by rfl) ⟨18105899, by rfl⟩ : syracuseStep 24141199 = 36211799) B36211799
theorem B2481569 : Blo 1100624 2481569 := bstep (se 2 (by rfl) ⟨930588, by rfl⟩ : syracuseStep 2481569 = 1861177) B1861177
theorem B3726863 : Blo 1100624 3726863 := bstep (se 1 (by rfl) ⟨2795147, by rfl⟩ : syracuseStep 3726863 = 5590295) B5590295
theorem B11296351 : Blo 1100624 11296351 := bstep (se 1 (by rfl) ⟨8472263, by rfl⟩ : syracuseStep 11296351 = 16944527) B16944527
theorem B9690839 : Blo 1100624 9690839 := bstep (se 1 (by rfl) ⟨7268129, by rfl⟩ : syracuseStep 9690839 = 14536259) B14536259
theorem B76472045 : Blo 1100624 76472045 := bstep (se 3 (by rfl) ⟨14338508, by rfl⟩ : syracuseStep 76472045 = 28677017) B28677017
theorem B3530537 : Blo 1100624 3530537 := bstep (se 2 (by rfl) ⟨1323951, by rfl⟩ : syracuseStep 3530537 = 2647903) B2647903
theorem B1859375 : Blo 1100624 1859375 := bstep (se 1 (by rfl) ⟨1394531, by rfl⟩ : syracuseStep 1859375 = 2789063) B2789063
theorem B4710251 : Blo 1100624 4710251 := bstep (se 1 (by rfl) ⟨3532688, by rfl⟩ : syracuseStep 4710251 = 7065377) B7065377
theorem B6283115 : Blo 1100624 6283115 := bstep (se 1 (by rfl) ⟨4712336, by rfl⟩ : syracuseStep 6283115 = 9424673) B9424673
theorem B2482127 : Blo 1100624 2482127 := bstep (se 1 (by rfl) ⟨1861595, by rfl⟩ : syracuseStep 2482127 = 3723191) B3723191
theorem B9068593 : Blo 1100624 9068593 := bstep (se 2 (by rfl) ⟨3400722, by rfl⟩ : syracuseStep 9068593 = 6801445) B6801445
theorem B2482505 : Blo 1100624 2482505 := bstep (se 2 (by rfl) ⟨930939, by rfl⟩ : syracuseStep 2482505 = 1861879) B1861879
theorem B2482523 : Blo 1100624 2482523 := bstep (se 1 (by rfl) ⟨1861892, by rfl⟩ : syracuseStep 2482523 = 3723785) B3723785
theorem B9691649 : Blo 1100624 9691649 := bstep (se 2 (by rfl) ⟨3634368, by rfl⟩ : syracuseStep 9691649 = 7268737) B7268737
theorem B2515475 : Blo 1100624 2515475 := bstep (se 1 (by rfl) ⟨1886606, by rfl⟩ : syracuseStep 2515475 = 3773213) B3773213
theorem B3727943 : Blo 1100624 3727943 := bstep (se 1 (by rfl) ⟨2795957, by rfl⟩ : syracuseStep 3727943 = 5591915) B5591915
theorem B4711277 : Blo 1100624 4711277 := bstep (se 3 (by rfl) ⟨883364, by rfl⟩ : syracuseStep 4711277 = 1766729) B1766729
theorem B2483099 : Blo 1100624 2483099 := bstep (se 1 (by rfl) ⟨1862324, by rfl⟩ : syracuseStep 2483099 = 3724649) B3724649
theorem B1860583 : Blo 1100624 1860583 := bstep (se 1 (by rfl) ⟨1395437, by rfl⟩ : syracuseStep 1860583 = 2790875) B2790875
theorem B2089975 : Blo 1100624 2089975 := bstep (se 1 (by rfl) ⟨1567481, by rfl⟩ : syracuseStep 2089975 = 3134963) B3134963
theorem B3138551 : Blo 1100624 3138551 := bstep (se 1 (by rfl) ⟨2353913, by rfl⟩ : syracuseStep 3138551 = 4707827) B4707827
theorem B8610823 : Blo 1100624 8610823 := bstep (se 1 (by rfl) ⟨6458117, by rfl⟩ : syracuseStep 8610823 = 12916235) B12916235
theorem B2483297 : Blo 1100624 2483297 := bstep (se 2 (by rfl) ⟨931236, by rfl⟩ : syracuseStep 2483297 = 1862473) B1862473
theorem B2090279 : Blo 1100624 2090279 := bstep (se 1 (by rfl) ⟨1567709, by rfl⟩ : syracuseStep 2090279 = 3135419) B3135419
theorem B2483495 : Blo 1100624 2483495 := bstep (se 1 (by rfl) ⟨1862621, by rfl⟩ : syracuseStep 2483495 = 3725243) B3725243
theorem B1238395 : Blo 1100624 1238395 := bstep (se 1 (by rfl) ⟨928796, by rfl⟩ : syracuseStep 1238395 = 1857593) B1857593
theorem B2090377 : Blo 1100624 2090377 := bstep (se 2 (by rfl) ⟨783891, by rfl⟩ : syracuseStep 2090377 = 1567783) B1567783
theorem B79619573 : Blo 1100624 79619573 := bstep (se 5 (by rfl) ⟨3732167, by rfl⟩ : syracuseStep 79619573 = 7464335) B7464335
theorem B8382041 : Blo 1100624 8382041 := bstep (se 2 (by rfl) ⟨3143265, by rfl⟩ : syracuseStep 8382041 = 6286531) B6286531
theorem B2483873 : Blo 1100624 2483873 := bstep (se 2 (by rfl) ⟨931452, by rfl⟩ : syracuseStep 2483873 = 1862905) B1862905
theorem B1763129 : Blo 1100624 1763129 := bstep (se 2 (by rfl) ⟨661173, by rfl⟩ : syracuseStep 1763129 = 1322347) B1322347
theorem B2647865 : Blo 1100624 2647865 := bstep (se 2 (by rfl) ⟨992949, by rfl⟩ : syracuseStep 2647865 = 1985899) B1985899
theorem B1238863 : Blo 1100624 1238863 := bstep (se 1 (by rfl) ⟨929147, by rfl⟩ : syracuseStep 1238863 = 1858295) B1858295
theorem B2484233 : Blo 1100624 2484233 := bstep (se 2 (by rfl) ⟨931587, by rfl⟩ : syracuseStep 2484233 = 1863175) B1863175
theorem B15100019 : Blo 1100624 15100019 := bstep (se 1 (by rfl) ⟨11325014, by rfl⟩ : syracuseStep 15100019 = 22650029) B22650029
theorem B1239259 : Blo 1100624 1239259 := bstep (se 1 (by rfl) ⟨929444, by rfl⟩ : syracuseStep 1239259 = 1858889) B1858889
theorem B2484647 : Blo 1100624 2484647 := bstep (se 1 (by rfl) ⟨1863485, by rfl⟩ : syracuseStep 2484647 = 3726971) B3726971
theorem B1239547 : Blo 1100624 1239547 := bstep (se 1 (by rfl) ⟨929660, by rfl⟩ : syracuseStep 1239547 = 1859321) B1859321
theorem B2484755 : Blo 1100624 2484755 := bstep (se 1 (by rfl) ⟨1863566, by rfl⟩ : syracuseStep 2484755 = 3727133) B3727133
theorem B2484809 : Blo 1100624 2484809 := bstep (se 2 (by rfl) ⟨931803, by rfl⟩ : syracuseStep 2484809 = 1863607) B1863607
theorem B1239727 : Blo 1100624 1239727 := bstep (se 1 (by rfl) ⟨929795, by rfl⟩ : syracuseStep 1239727 = 1859591) B1859591
theorem B1240015 : Blo 1100624 1240015 := bstep (se 1 (by rfl) ⟨930011, by rfl⟩ : syracuseStep 1240015 = 1860023) B1860023
theorem B2485223 : Blo 1100624 2485223 := bstep (se 1 (by rfl) ⟨1863917, by rfl⟩ : syracuseStep 2485223 = 3727835) B3727835
theorem B15494159 : Blo 1100624 15494159 := bstep (se 1 (by rfl) ⟨11620619, by rfl⟩ : syracuseStep 15494159 = 23241239) B23241239
theorem B2649287 : Blo 1100624 2649287 := bstep (se 1 (by rfl) ⟨1986965, by rfl⟩ : syracuseStep 2649287 = 3973931) B3973931
theorem B1240411 : Blo 1100624 1240411 := bstep (se 1 (by rfl) ⟨930308, by rfl⟩ : syracuseStep 1240411 = 1860617) B1860617
theorem B1240519 : Blo 1100624 1240519 := bstep (se 1 (by rfl) ⟨930389, by rfl⟩ : syracuseStep 1240519 = 1860779) B1860779
theorem B3534329 : Blo 1100624 3534329 := bstep (se 2 (by rfl) ⟨1325373, by rfl⟩ : syracuseStep 3534329 = 2650747) B2650747
theorem B4713977 : Blo 1100624 4713977 := bstep (se 2 (by rfl) ⟨1767741, by rfl⟩ : syracuseStep 4713977 = 3535483) B3535483
theorem B1863263 : Blo 1100624 1863263 := bstep (se 1 (by rfl) ⟨1397447, by rfl⟩ : syracuseStep 1863263 = 2794895) B2794895
theorem B6287057 : Blo 1100624 6287057 := bstep (se 2 (by rfl) ⟨2357646, by rfl⟩ : syracuseStep 6287057 = 4715293) B4715293
theorem B2092807 : Blo 1100624 2092807 := bstep (se 1 (by rfl) ⟨1569605, by rfl⟩ : syracuseStep 2092807 = 3139211) B3139211
theorem B1240879 : Blo 1100624 1240879 := bstep (se 1 (by rfl) ⟨930659, by rfl⟩ : syracuseStep 1240879 = 1861319) B1861319
theorem B1863479 : Blo 1100624 1863479 := bstep (se 1 (by rfl) ⟨1397609, by rfl⟩ : syracuseStep 1863479 = 2795219) B2795219
theorem B1240987 : Blo 1100624 1240987 := bstep (se 1 (by rfl) ⟨930740, by rfl⟩ : syracuseStep 1240987 = 1861481) B1861481
theorem B42922061 : Blo 1100624 42922061 := bstep (se 3 (by rfl) ⟨8047886, by rfl⟩ : syracuseStep 42922061 = 16095773) B16095773
theorem B2977897 : Blo 1100624 2977897 := bstep (se 2 (by rfl) ⟨1116711, by rfl⟩ : syracuseStep 2977897 = 2233423) B2233423
theorem B7958699 : Blo 1100624 7958699 := bstep (se 1 (by rfl) ⟨5969024, by rfl⟩ : syracuseStep 7958699 = 11938049) B11938049
theorem B1241383 : Blo 1100624 1241383 := bstep (se 1 (by rfl) ⟨931037, by rfl⟩ : syracuseStep 1241383 = 1862075) B1862075
theorem B1241455 : Blo 1100624 1241455 := bstep (se 1 (by rfl) ⟨931091, by rfl⟩ : syracuseStep 1241455 = 1862183) B1862183
theorem B1241671 : Blo 1100624 1241671 := bstep (se 1 (by rfl) ⟨931253, by rfl⟩ : syracuseStep 1241671 = 1862507) B1862507
theorem B7959161 : Blo 1100624 7959161 := bstep (se 2 (by rfl) ⟨2984685, by rfl⟩ : syracuseStep 7959161 = 5969371) B5969371
theorem B1176239 : Blo 1100624 1176239 := bstep (se 1 (by rfl) ⟨882179, by rfl⟩ : syracuseStep 1176239 = 1764359) B1764359
theorem B1766063 : Blo 1100624 1766063 := bstep (se 1 (by rfl) ⟨1324547, by rfl⟩ : syracuseStep 1766063 = 2649095) B2649095
theorem B5960375 : Blo 1100624 5960375 := bstep (se 1 (by rfl) ⟨4470281, by rfl⟩ : syracuseStep 5960375 = 8940563) B8940563
theorem B2355895 : Blo 1100624 2355895 := bstep (se 1 (by rfl) ⟨1766921, by rfl⟩ : syracuseStep 2355895 = 3533843) B3533843
theorem B1569503 : Blo 1100624 1569503 := bstep (se 1 (by rfl) ⟨1177127, by rfl⟩ : syracuseStep 1569503 = 2354255) B2354255
theorem B1176367 : Blo 1100624 1176367 := bstep (se 1 (by rfl) ⟨882275, by rfl⟩ : syracuseStep 1176367 = 1764551) B1764551
theorem B2651123 : Blo 1100624 2651123 := bstep (se 1 (by rfl) ⟨1988342, by rfl⟩ : syracuseStep 2651123 = 3976685) B3976685
theorem B3535969 : Blo 1100624 3535969 := bstep (se 2 (by rfl) ⟨1325988, by rfl⟩ : syracuseStep 3535969 = 2651977) B2651977
theorem B4715617 : Blo 1100624 4715617 := bstep (se 2 (by rfl) ⟨1768356, by rfl⟩ : syracuseStep 4715617 = 3536713) B3536713
theorem B26866835 : Blo 1100624 26866835 := bstep (se 1 (by rfl) ⟨20150126, by rfl⟩ : syracuseStep 26866835 = 40300253) B40300253
theorem B1242535 : Blo 1100624 1242535 := bstep (se 1 (by rfl) ⟨931901, by rfl⟩ : syracuseStep 1242535 = 1863803) B1863803
theorem B1177183 : Blo 1100624 1177183 := bstep (se 1 (by rfl) ⟨882887, by rfl⟩ : syracuseStep 1177183 = 1765775) B1765775
theorem B2095055 : Blo 1100624 2095055 := bstep (se 1 (by rfl) ⟨1571291, by rfl⟩ : syracuseStep 2095055 = 3142583) B3142583
theorem B2095571 : Blo 1100624 2095571 := bstep (se 1 (by rfl) ⟨1571678, by rfl⟩ : syracuseStep 2095571 = 3143357) B3143357
theorem B14318153 : Blo 1100624 14318153 := bstep (se 2 (by rfl) ⟨5369307, by rfl⟩ : syracuseStep 14318153 = 10738615) B10738615
theorem B5306953 : Blo 1100624 5306953 := bstep (se 2 (by rfl) ⟨1990107, by rfl⟩ : syracuseStep 5306953 = 3980215) B3980215
theorem B2095723 : Blo 1100624 2095723 := bstep (se 1 (by rfl) ⟨1571792, by rfl⟩ : syracuseStep 2095723 = 3143585) B3143585
theorem B33094277 : Blo 1100624 33094277 := bstep (se 4 (by rfl) ⟨3102588, by rfl⟩ : syracuseStep 33094277 = 6205177) B6205177
theorem B2095951 : Blo 1100624 2095951 := bstep (se 1 (by rfl) ⟨1571963, by rfl⟩ : syracuseStep 2095951 = 3143927) B3143927
theorem B2096027 : Blo 1100624 2096027 := bstep (se 1 (by rfl) ⟨1572020, by rfl⟩ : syracuseStep 2096027 = 3144041) B3144041
theorem B1571815 : Blo 1100624 1571815 := bstep (se 1 (by rfl) ⟨1178861, by rfl⟩ : syracuseStep 1571815 = 2357723) B2357723
theorem B4193603 : Blo 1100624 4193603 := bstep (se 1 (by rfl) ⟨3145202, by rfl⟩ : syracuseStep 4193603 = 6290405) B6290405
theorem B4193633 : Blo 1100624 4193633 := bstep (se 2 (by rfl) ⟨1572612, by rfl⟩ : syracuseStep 4193633 = 3145225) B3145225
theorem B4194089 : Blo 1100624 4194089 := bstep (se 2 (by rfl) ⟨1572783, by rfl⟩ : syracuseStep 4194089 = 3145567) B3145567
theorem B12091457 : Blo 1100624 12091457 := bstep (se 2 (by rfl) ⟨4534296, by rfl⟩ : syracuseStep 12091457 = 9068593) B9068593
theorem B9405193 : Blo 1100624 9405193 := bstep (se 2 (by rfl) ⟨3526947, by rfl⟩ : syracuseStep 9405193 = 7053895) B7053895
theorem B20382977 : Blo 1100624 20382977 := bstep (se 2 (by rfl) ⟨7643616, by rfl⟩ : syracuseStep 20382977 = 15287233) B15287233
theorem B2786633 : Blo 1100624 2786633 := bstep (se 2 (by rfl) ⟨1044987, by rfl⟩ : syracuseStep 2786633 = 2089975) B2089975
theorem B3769939 : Blo 1100624 3769939 := bstep (se 1 (by rfl) ⟨2827454, by rfl⟩ : syracuseStep 3769939 = 5654909) B5654909
theorem B2787169 : Blo 1100624 2787169 := bstep (se 2 (by rfl) ⟨1045188, by rfl⟩ : syracuseStep 2787169 = 2090377) B2090377
theorem B5572799 : Blo 1100624 5572799 := bstep (se 1 (by rfl) ⟨4179599, by rfl⟩ : syracuseStep 5572799 = 8359199) B8359199
theorem B31820849 : Blo 1100624 31820849 := bstep (se 2 (by rfl) ⟨11932818, by rfl⟩ : syracuseStep 31820849 = 23865637) B23865637
theorem B1674361 : Blo 1100624 1674361 := bstep (se 2 (by rfl) ⟨627885, by rfl⟩ : syracuseStep 1674361 = 1255771) B1255771
theorem B8064305 : Blo 1100624 8064305 := bstep (se 2 (by rfl) ⟨3024114, by rfl⟩ : syracuseStep 8064305 = 6048229) B6048229
theorem B18812573 : Blo 1100624 18812573 := bstep (se 3 (by rfl) ⟨3527357, by rfl⟩ : syracuseStep 18812573 = 7054715) B7054715
theorem B2789275 : Blo 1100624 2789275 := bstep (se 1 (by rfl) ⟨2091956, by rfl⟩ : syracuseStep 2789275 = 4183913) B4183913
theorem B2232287 : Blo 1100624 2232287 := bstep (se 1 (by rfl) ⟨1674215, by rfl⟩ : syracuseStep 2232287 = 3348431) B3348431
theorem B5575553 : Blo 1100624 5575553 := bstep (se 2 (by rfl) ⟨2090832, by rfl⟩ : syracuseStep 5575553 = 4181665) B4181665
theorem B7934915 : Blo 1100624 7934915 := bstep (se 1 (by rfl) ⟨5951186, by rfl⟩ : syracuseStep 7934915 = 11902373) B11902373
theorem B2790409 : Blo 1100624 2790409 := bstep (se 2 (by rfl) ⟨1046403, by rfl⟩ : syracuseStep 2790409 = 2092807) B2092807
theorem B6460559 : Blo 1100624 6460559 := bstep (se 1 (by rfl) ⟨4845419, by rfl⟩ : syracuseStep 6460559 = 9690839) B9690839
theorem B3970529 : Blo 1100624 3970529 := bstep (se 2 (by rfl) ⟨1488948, by rfl⟩ : syracuseStep 3970529 = 2977897) B2977897
theorem B5576363 : Blo 1100624 5576363 := bstep (se 1 (by rfl) ⟨4182272, by rfl⟩ : syracuseStep 5576363 = 8364545) B8364545
theorem B6461099 : Blo 1100624 6461099 := bstep (se 1 (by rfl) ⟨4845824, by rfl⟩ : syracuseStep 6461099 = 9691649) B9691649
theorem B6297401 : Blo 1100624 6297401 := bstep (se 2 (by rfl) ⟨2361525, by rfl⟩ : syracuseStep 6297401 = 4723051) B4723051
theorem B5576687 : Blo 1100624 5576687 := bstep (se 1 (by rfl) ⟨4182515, by rfl⟩ : syracuseStep 5576687 = 8365031) B8365031
theorem B10066679 : Blo 1100624 10066679 := bstep (se 1 (by rfl) ⟨7550009, by rfl⟩ : syracuseStep 10066679 = 15100019) B15100019
theorem B10329439 : Blo 1100624 10329439 := bstep (se 1 (by rfl) ⟨7747079, by rfl⟩ : syracuseStep 10329439 = 15494159) B15494159
theorem B5578145 : Blo 1100624 5578145 := bstep (se 2 (by rfl) ⟨2091804, by rfl⟩ : syracuseStep 5578145 = 4183609) B4183609
theorem B28614707 : Blo 1100624 28614707 := bstep (se 1 (by rfl) ⟨21461030, by rfl⟩ : syracuseStep 28614707 = 42922061) B42922061
theorem B3973583 : Blo 1100624 3973583 := bstep (se 1 (by rfl) ⟨2980187, by rfl⟩ : syracuseStep 3973583 = 5960375) B5960375
theorem B2794297 : Blo 1100624 2794297 := bstep (se 2 (by rfl) ⟨1047861, by rfl⟩ : syracuseStep 2794297 = 2095723) B2095723
theorem B2794601 : Blo 1100624 2794601 := bstep (se 2 (by rfl) ⟨1047975, by rfl⟩ : syracuseStep 2794601 = 2095951) B2095951
theorem B9545435 : Blo 1100624 9545435 := bstep (se 1 (by rfl) ⟨7159076, by rfl⟩ : syracuseStep 9545435 = 14318153) B14318153
theorem B22062851 : Blo 1100624 22062851 := bstep (se 1 (by rfl) ⟨16547138, by rfl⟩ : syracuseStep 22062851 = 33094277) B33094277
theorem B5580575 : Blo 1100624 5580575 := bstep (se 1 (by rfl) ⟨4185431, by rfl⟩ : syracuseStep 5580575 = 8370863) B8370863
theorem B32188265 : Blo 1100624 32188265 := bstep (se 2 (by rfl) ⟨12070599, by rfl⟩ : syracuseStep 32188265 = 24141199) B24141199
theorem B30189725 : Blo 1100624 30189725 := bstep (se 3 (by rfl) ⟨5660573, by rfl⟩ : syracuseStep 30189725 = 11321147) B11321147
theorem B2795735 : Blo 1100624 2795735 := bstep (se 1 (by rfl) ⟨2096801, by rfl⟩ : syracuseStep 2795735 = 4193603) B4193603
theorem B2795755 : Blo 1100624 2795755 := bstep (se 1 (by rfl) ⟨2096816, by rfl⟩ : syracuseStep 2795755 = 4193633) B4193633
theorem B12560669 : Blo 1100624 12560669 := bstep (se 3 (by rfl) ⟨2355125, by rfl⟩ : syracuseStep 12560669 = 4710251) B4710251
theorem B3778973 : Blo 1100624 3778973 := bstep (se 3 (by rfl) ⟨708557, by rfl⟩ : syracuseStep 3778973 = 1417115) B1417115
theorem B2796059 : Blo 1100624 2796059 := bstep (se 1 (by rfl) ⟨2097044, by rfl⟩ : syracuseStep 2796059 = 4194089) B4194089
theorem B15870923 : Blo 1100624 15870923 := bstep (se 1 (by rfl) ⟨11903192, by rfl⟩ : syracuseStep 15870923 = 23806385) B23806385
theorem B5581871 : Blo 1100624 5581871 := bstep (se 1 (by rfl) ⟨4186403, by rfl⟩ : syracuseStep 5581871 = 8372807) B8372807
theorem B11481097 : Blo 1100624 11481097 := bstep (se 2 (by rfl) ⟨4305411, by rfl⟩ : syracuseStep 11481097 = 8610823) B8610823
theorem B1651151 : Blo 1100624 1651151 := bstep (se 1 (by rfl) ⟨1238363, by rfl⟩ : syracuseStep 1651151 = 2476727) B2476727
theorem B1651193 : Blo 1100624 1651193 := bstep (se 2 (by rfl) ⟨619197, by rfl⟩ : syracuseStep 1651193 = 1238395) B1238395
theorem B3715577 : Blo 1100624 3715577 := bstep (se 2 (by rfl) ⟨1393341, by rfl⟩ : syracuseStep 3715577 = 2786683) B2786683
theorem B1651295 : Blo 1100624 1651295 := bstep (se 1 (by rfl) ⟨1238471, by rfl⟩ : syracuseStep 1651295 = 2476943) B2476943
theorem B3715847 : Blo 1100624 3715847 := bstep (se 1 (by rfl) ⟨2786885, by rfl⟩ : syracuseStep 3715847 = 5573771) B5573771
theorem B3715901 : Blo 1100624 3715901 := bstep (se 3 (by rfl) ⟨696731, by rfl⟩ : syracuseStep 3715901 = 1393463) B1393463
theorem B1651775 : Blo 1100624 1651775 := bstep (se 1 (by rfl) ⟨1238831, by rfl⟩ : syracuseStep 1651775 = 2477663) B2477663
theorem B1651817 : Blo 1100624 1651817 := bstep (se 2 (by rfl) ⟨619431, by rfl⟩ : syracuseStep 1651817 = 1238863) B1238863
theorem B1651919 : Blo 1100624 1651919 := bstep (se 1 (by rfl) ⟨1238939, by rfl⟩ : syracuseStep 1651919 = 2477879) B2477879
theorem B1652123 : Blo 1100624 1652123 := bstep (se 1 (by rfl) ⟨1239092, by rfl⟩ : syracuseStep 1652123 = 2478185) B2478185
theorem B1652345 : Blo 1100624 1652345 := bstep (se 2 (by rfl) ⟨619629, by rfl⟩ : syracuseStep 1652345 = 1239259) B1239259
theorem B1652447 : Blo 1100624 1652447 := bstep (se 1 (by rfl) ⟨1239335, by rfl⟩ : syracuseStep 1652447 = 2478671) B2478671
theorem B3716927 : Blo 1100624 3716927 := bstep (se 1 (by rfl) ⟨2787695, by rfl⟩ : syracuseStep 3716927 = 5575391) B5575391
theorem B1652543 : Blo 1100624 1652543 := bstep (se 1 (by rfl) ⟨1239407, by rfl⟩ : syracuseStep 1652543 = 2478815) B2478815
theorem B12105577 : Blo 1100624 12105577 := bstep (se 2 (by rfl) ⟨4539591, by rfl⟩ : syracuseStep 12105577 = 9079183) B9079183
theorem B1652711 : Blo 1100624 1652711 := bstep (se 1 (by rfl) ⟨1239533, by rfl⟩ : syracuseStep 1652711 = 2479067) B2479067
theorem B1652729 : Blo 1100624 1652729 := bstep (se 2 (by rfl) ⟨619773, by rfl⟩ : syracuseStep 1652729 = 1239547) B1239547
theorem B1652831 : Blo 1100624 1652831 := bstep (se 1 (by rfl) ⟨1239623, by rfl⟩ : syracuseStep 1652831 = 2479247) B2479247
theorem B1652891 : Blo 1100624 1652891 := bstep (se 1 (by rfl) ⟨1239668, by rfl⟩ : syracuseStep 1652891 = 2479337) B2479337
theorem B1652927 : Blo 1100624 1652927 := bstep (se 1 (by rfl) ⟨1239695, by rfl⟩ : syracuseStep 1652927 = 2479391) B2479391
theorem B1652969 : Blo 1100624 1652969 := bstep (se 2 (by rfl) ⟨619863, by rfl⟩ : syracuseStep 1652969 = 1239727) B1239727
theorem B9419273 : Blo 1100624 9419273 := bstep (se 2 (by rfl) ⟨3532227, by rfl⟩ : syracuseStep 9419273 = 7064455) B7064455
theorem B1653275 : Blo 1100624 1653275 := bstep (se 1 (by rfl) ⟨1239956, by rfl⟩ : syracuseStep 1653275 = 2479913) B2479913
theorem B1653353 : Blo 1100624 1653353 := bstep (se 2 (by rfl) ⟨620007, by rfl⟩ : syracuseStep 1653353 = 1240015) B1240015
theorem B11909855 : Blo 1100624 11909855 := bstep (se 1 (by rfl) ⟨8932391, by rfl⟩ : syracuseStep 11909855 = 17864783) B17864783
theorem B14138135 : Blo 1100624 14138135 := bstep (se 1 (by rfl) ⟨10603601, by rfl⟩ : syracuseStep 14138135 = 21207203) B21207203
theorem B1653881 : Blo 1100624 1653881 := bstep (se 2 (by rfl) ⟨620205, by rfl⟩ : syracuseStep 1653881 = 1240411) B1240411
theorem B1653983 : Blo 1100624 1653983 := bstep (se 1 (by rfl) ⟨1240487, by rfl⟩ : syracuseStep 1653983 = 2480975) B2480975
theorem B1654025 : Blo 1100624 1654025 := bstep (se 2 (by rfl) ⟨620259, by rfl⟩ : syracuseStep 1654025 = 1240519) B1240519
theorem B10042663 : Blo 1100624 10042663 := bstep (se 1 (by rfl) ⟨7531997, by rfl⟩ : syracuseStep 10042663 = 15063995) B15063995
theorem B3718439 : Blo 1100624 3718439 := bstep (se 1 (by rfl) ⟨2788829, by rfl⟩ : syracuseStep 3718439 = 5577659) B5577659
theorem B1654127 : Blo 1100624 1654127 := bstep (se 1 (by rfl) ⟨1240595, by rfl⟩ : syracuseStep 1654127 = 2481191) B2481191
theorem B95305085 : Blo 1100624 95305085 := bstep (se 3 (by rfl) ⟨17869703, by rfl⟩ : syracuseStep 95305085 = 35739407) B35739407
theorem B1654247 : Blo 1100624 1654247 := bstep (se 1 (by rfl) ⟨1240685, by rfl⟩ : syracuseStep 1654247 = 2481371) B2481371
theorem B1883711 : Blo 1100624 1883711 := bstep (se 1 (by rfl) ⟨1412783, by rfl⟩ : syracuseStep 1883711 = 2825567) B2825567
theorem B1654379 : Blo 1100624 1654379 := bstep (se 1 (by rfl) ⟨1240784, by rfl⟩ : syracuseStep 1654379 = 2481569) B2481569
theorem B1654505 : Blo 1100624 1654505 := bstep (se 2 (by rfl) ⟨620439, by rfl⟩ : syracuseStep 1654505 = 1240879) B1240879
theorem B1654649 : Blo 1100624 1654649 := bstep (se 2 (by rfl) ⟨620493, by rfl⟩ : syracuseStep 1654649 = 1240987) B1240987
theorem B1654751 : Blo 1100624 1654751 := bstep (se 1 (by rfl) ⟨1241063, by rfl⟩ : syracuseStep 1654751 = 2482127) B2482127
theorem B3719303 : Blo 1100624 3719303 := bstep (se 1 (by rfl) ⟨2789477, by rfl⟩ : syracuseStep 3719303 = 5578955) B5578955
theorem B1655003 : Blo 1100624 1655003 := bstep (se 1 (by rfl) ⟨1241252, by rfl⟩ : syracuseStep 1655003 = 2482505) B2482505
theorem B1655015 : Blo 1100624 1655015 := bstep (se 1 (by rfl) ⟨1241261, by rfl⟩ : syracuseStep 1655015 = 2482523) B2482523
theorem B1655177 : Blo 1100624 1655177 := bstep (se 2 (by rfl) ⟨620691, by rfl⟩ : syracuseStep 1655177 = 1241383) B1241383
theorem B1655273 : Blo 1100624 1655273 := bstep (se 2 (by rfl) ⟨620727, by rfl⟩ : syracuseStep 1655273 = 1241455) B1241455
theorem B1655399 : Blo 1100624 1655399 := bstep (se 1 (by rfl) ⟨1241549, by rfl⟩ : syracuseStep 1655399 = 2483099) B2483099
theorem B1655531 : Blo 1100624 1655531 := bstep (se 1 (by rfl) ⟨1241648, by rfl⟩ : syracuseStep 1655531 = 2483297) B2483297
theorem B1655561 : Blo 1100624 1655561 := bstep (se 2 (by rfl) ⟨620835, by rfl⟩ : syracuseStep 1655561 = 1241671) B1241671
theorem B1393519 : Blo 1100624 1393519 := bstep (se 1 (by rfl) ⟨1045139, by rfl⟩ : syracuseStep 1393519 = 2090279) B2090279
theorem B1655663 : Blo 1100624 1655663 := bstep (se 1 (by rfl) ⟨1241747, by rfl⟩ : syracuseStep 1655663 = 2483495) B2483495
theorem B1360891 : Blo 1100624 1360891 := bstep (se 1 (by rfl) ⟨1020668, by rfl⟩ : syracuseStep 1360891 = 2041337) B2041337
theorem B5588027 : Blo 1100624 5588027 := bstep (se 1 (by rfl) ⟨4191020, by rfl⟩ : syracuseStep 5588027 = 8382041) B8382041
theorem B1655915 : Blo 1100624 1655915 := bstep (se 1 (by rfl) ⟨1241936, by rfl⟩ : syracuseStep 1655915 = 2483873) B2483873
theorem B5588189 : Blo 1100624 5588189 := bstep (se 3 (by rfl) ⟨1047785, by rfl⟩ : syracuseStep 5588189 = 2095571) B2095571
theorem B1656155 : Blo 1100624 1656155 := bstep (se 1 (by rfl) ⟨1242116, by rfl⟩ : syracuseStep 1656155 = 2484233) B2484233
theorem B3720815 : Blo 1100624 3720815 := bstep (se 1 (by rfl) ⟨2790611, by rfl⟩ : syracuseStep 3720815 = 5581223) B5581223
theorem B1656431 : Blo 1100624 1656431 := bstep (se 1 (by rfl) ⟨1242323, by rfl⟩ : syracuseStep 1656431 = 2484647) B2484647
theorem B1656503 : Blo 1100624 1656503 := bstep (se 1 (by rfl) ⟨1242377, by rfl⟩ : syracuseStep 1656503 = 2484755) B2484755
theorem B3720923 : Blo 1100624 3720923 := bstep (se 1 (by rfl) ⟨2790692, by rfl⟩ : syracuseStep 3720923 = 5581385) B5581385
theorem B1656539 : Blo 1100624 1656539 := bstep (se 1 (by rfl) ⟨1242404, by rfl⟩ : syracuseStep 1656539 = 2484809) B2484809
theorem B1656713 : Blo 1100624 1656713 := bstep (se 2 (by rfl) ⟨621267, by rfl⟩ : syracuseStep 1656713 = 1242535) B1242535
theorem B1656815 : Blo 1100624 1656815 := bstep (se 1 (by rfl) ⟨1242611, by rfl⟩ : syracuseStep 1656815 = 2485223) B2485223
theorem B6277601 : Blo 1100624 6277601 := bstep (se 2 (by rfl) ⟨2354100, by rfl⟩ : syracuseStep 6277601 = 4708201) B4708201
theorem B4180511 : Blo 1100624 4180511 := bstep (se 1 (by rfl) ⟨3135383, by rfl⟩ : syracuseStep 4180511 = 6270767) B6270767
theorem B1100635 : Blo 1100624 1100635 := bstep (se 1 (by rfl) ⟨825476, by rfl⟩ : syracuseStep 1100635 = 1650953) B1650953
theorem B1100703 : Blo 1100624 1100703 := bstep (se 1 (by rfl) ⟨825527, by rfl⟩ : syracuseStep 1100703 = 1651055) B1651055
theorem B4180967 : Blo 1100624 4180967 := bstep (se 1 (by rfl) ⟨3135725, by rfl⟩ : syracuseStep 4180967 = 6271451) B6271451
theorem B3722219 : Blo 1100624 3722219 := bstep (se 1 (by rfl) ⟨2791664, by rfl⟩ : syracuseStep 3722219 = 5583329) B5583329
theorem B3722273 : Blo 1100624 3722273 := bstep (se 2 (by rfl) ⟨1395852, by rfl⟩ : syracuseStep 3722273 = 2791705) B2791705
theorem B1100847 : Blo 1100624 1100847 := bstep (se 1 (by rfl) ⟨825635, by rfl⟩ : syracuseStep 1100847 = 1651271) B1651271
theorem B1100871 : Blo 1100624 1100871 := bstep (se 1 (by rfl) ⟨825653, by rfl⟩ : syracuseStep 1100871 = 1651307) B1651307
theorem B3394657 : Blo 1100624 3394657 := bstep (se 2 (by rfl) ⟨1272996, by rfl⟩ : syracuseStep 3394657 = 2545993) B2545993
theorem B2477177 : Blo 1100624 2477177 := bstep (se 2 (by rfl) ⟨928941, by rfl⟩ : syracuseStep 2477177 = 1857883) B1857883
theorem B28691587 : Blo 1100624 28691587 := bstep (se 1 (by rfl) ⟨21518690, by rfl⟩ : syracuseStep 28691587 = 43037381) B43037381
theorem B6278309 : Blo 1100624 6278309 := bstep (se 4 (by rfl) ⟨588591, by rfl⟩ : syracuseStep 6278309 = 1177183) B1177183
theorem B5950687 : Blo 1100624 5950687 := bstep (se 1 (by rfl) ⟨4463015, by rfl⟩ : syracuseStep 5950687 = 8926031) B8926031
theorem B1101023 : Blo 1100624 1101023 := bstep (se 1 (by rfl) ⟨825767, by rfl⟩ : syracuseStep 1101023 = 1651535) B1651535
theorem B7753097 : Blo 1100624 7753097 := bstep (se 2 (by rfl) ⟨2907411, by rfl⟩ : syracuseStep 7753097 = 5814823) B5814823
theorem B17911223 : Blo 1100624 17911223 := bstep (se 1 (by rfl) ⟨13433417, by rfl⟩ : syracuseStep 17911223 = 26866835) B26866835
theorem B1101287 : Blo 1100624 1101287 := bstep (se 1 (by rfl) ⟨825965, by rfl⟩ : syracuseStep 1101287 = 1651931) B1651931
theorem B1101403 : Blo 1100624 1101403 := bstep (se 1 (by rfl) ⟨826052, by rfl⟩ : syracuseStep 1101403 = 1652105) B1652105
theorem B2477843 : Blo 1100624 2477843 := bstep (se 1 (by rfl) ⟨1858382, by rfl⟩ : syracuseStep 2477843 = 3716765) B3716765
theorem B1101639 : Blo 1100624 1101639 := bstep (se 1 (by rfl) ⟨826229, by rfl⟩ : syracuseStep 1101639 = 1652459) B1652459
theorem B11325257 : Blo 1100624 11325257 := bstep (se 2 (by rfl) ⟨4246971, by rfl⟩ : syracuseStep 11325257 = 8493943) B8493943
theorem B8376209 : Blo 1100624 8376209 := bstep (se 2 (by rfl) ⟨3141078, by rfl⟩ : syracuseStep 8376209 = 6282157) B6282157
theorem B1101791 : Blo 1100624 1101791 := bstep (se 1 (by rfl) ⟨826343, by rfl⟩ : syracuseStep 1101791 = 1652687) B1652687
theorem B1396703 : Blo 1100624 1396703 := bstep (se 1 (by rfl) ⟨1047527, by rfl⟩ : syracuseStep 1396703 = 2095055) B2095055
theorem B2478203 : Blo 1100624 2478203 := bstep (se 1 (by rfl) ⟨1858652, by rfl⟩ : syracuseStep 2478203 = 3717305) B3717305
theorem B7065787 : Blo 1100624 7065787 := bstep (se 1 (by rfl) ⟨5299340, by rfl⟩ : syracuseStep 7065787 = 10598681) B10598681
theorem B1102055 : Blo 1100624 1102055 := bstep (se 1 (by rfl) ⟨826541, by rfl⟩ : syracuseStep 1102055 = 1653083) B1653083
theorem B3527039 : Blo 1100624 3527039 := bstep (se 1 (by rfl) ⟨2645279, by rfl⟩ : syracuseStep 3527039 = 5290559) B5290559
theorem B1102207 : Blo 1100624 1102207 := bstep (se 1 (by rfl) ⟨826655, by rfl⟩ : syracuseStep 1102207 = 1653311) B1653311
theorem B2478473 : Blo 1100624 2478473 := bstep (se 2 (by rfl) ⟨929427, by rfl⟩ : syracuseStep 2478473 = 1858855) B1858855
theorem B1102287 : Blo 1100624 1102287 := bstep (se 1 (by rfl) ⟨826715, by rfl⟩ : syracuseStep 1102287 = 1653431) B1653431
theorem B3723731 : Blo 1100624 3723731 := bstep (se 1 (by rfl) ⟨2792798, by rfl⟩ : syracuseStep 3723731 = 5585597) B5585597
theorem B4182623 : Blo 1100624 4182623 := bstep (se 1 (by rfl) ⟨3136967, by rfl⟩ : syracuseStep 4182623 = 6273935) B6273935
theorem B1102439 : Blo 1100624 1102439 := bstep (se 1 (by rfl) ⟨826829, by rfl⟩ : syracuseStep 1102439 = 1653659) B1653659
theorem B1397351 : Blo 1100624 1397351 := bstep (se 1 (by rfl) ⟨1048013, by rfl⟩ : syracuseStep 1397351 = 2096027) B2096027
theorem B8934077 : Blo 1100624 8934077 := bstep (se 3 (by rfl) ⟨1675139, by rfl⟩ : syracuseStep 8934077 = 3350279) B3350279
theorem B12899017 : Blo 1100624 12899017 := bstep (se 2 (by rfl) ⟨4837131, by rfl⟩ : syracuseStep 12899017 = 9674263) B9674263
theorem B15061801 : Blo 1100624 15061801 := bstep (se 2 (by rfl) ⟨5648175, by rfl⟩ : syracuseStep 15061801 = 11296351) B11296351
theorem B1102703 : Blo 1100624 1102703 := bstep (se 1 (by rfl) ⟨827027, by rfl⟩ : syracuseStep 1102703 = 1654055) B1654055
theorem B1102759 : Blo 1100624 1102759 := bstep (se 1 (by rfl) ⟨827069, by rfl⟩ : syracuseStep 1102759 = 1654139) B1654139
theorem B1102843 : Blo 1100624 1102843 := bstep (se 1 (by rfl) ⟨827132, by rfl⟩ : syracuseStep 1102843 = 1654265) B1654265
theorem B6280199 : Blo 1100624 6280199 := bstep (se 1 (by rfl) ⟨4710149, by rfl⟩ : syracuseStep 6280199 = 9420299) B9420299
theorem B1102911 : Blo 1100624 1102911 := bstep (se 1 (by rfl) ⟨827183, by rfl⟩ : syracuseStep 1102911 = 1654367) B1654367
theorem B2479211 : Blo 1100624 2479211 := bstep (se 1 (by rfl) ⟨1859408, by rfl⟩ : syracuseStep 2479211 = 3718817) B3718817
theorem B4707503 : Blo 1100624 4707503 := bstep (se 1 (by rfl) ⟨3530627, by rfl⟩ : syracuseStep 4707503 = 7061255) B7061255
theorem B1103055 : Blo 1100624 1103055 := bstep (se 1 (by rfl) ⟨827291, by rfl⟩ : syracuseStep 1103055 = 1654583) B1654583
theorem B4478327 : Blo 1100624 4478327 := bstep (se 1 (by rfl) ⟨3358745, by rfl⟩ : syracuseStep 4478327 = 6717491) B6717491
theorem B1103259 : Blo 1100624 1103259 := bstep (se 1 (by rfl) ⟨827444, by rfl⟩ : syracuseStep 1103259 = 1654889) B1654889
theorem B5297633 : Blo 1100624 5297633 := bstep (se 2 (by rfl) ⟨1986612, by rfl⟩ : syracuseStep 5297633 = 3973225) B3973225
theorem B7951841 : Blo 1100624 7951841 := bstep (se 2 (by rfl) ⟨2981940, by rfl⟩ : syracuseStep 7951841 = 5963881) B5963881
theorem B1103471 : Blo 1100624 1103471 := bstep (se 1 (by rfl) ⟨827603, by rfl⟩ : syracuseStep 1103471 = 1655207) B1655207
theorem B325998229 : Blo 1100624 325998229 := bstep (se 6 (by rfl) ⟨7640583, by rfl⟩ : syracuseStep 325998229 = 15281167) B15281167
theorem B1103527 : Blo 1100624 1103527 := bstep (se 1 (by rfl) ⟨827645, by rfl⟩ : syracuseStep 1103527 = 1655291) B1655291
theorem B2479787 : Blo 1100624 2479787 := bstep (se 1 (by rfl) ⟨1859840, by rfl⟩ : syracuseStep 2479787 = 3719681) B3719681
theorem B1103611 : Blo 1100624 1103611 := bstep (se 1 (by rfl) ⟨827708, by rfl⟩ : syracuseStep 1103611 = 1655417) B1655417
theorem B1103647 : Blo 1100624 1103647 := bstep (se 1 (by rfl) ⟨827735, by rfl⟩ : syracuseStep 1103647 = 1655471) B1655471
theorem B294508331 : Blo 1100624 294508331 := bstep (se 1 (by rfl) ⟨220881248, by rfl⟩ : syracuseStep 294508331 = 441762497) B441762497
theorem B1857343 : Blo 1100624 1857343 := bstep (se 1 (by rfl) ⟨1393007, by rfl⟩ : syracuseStep 1857343 = 2786015) B2786015
theorem B1103679 : Blo 1100624 1103679 := bstep (se 1 (by rfl) ⟨827759, by rfl⟩ : syracuseStep 1103679 = 1655519) B1655519
theorem B3528679 : Blo 1100624 3528679 := bstep (se 1 (by rfl) ⟨2646509, by rfl⟩ : syracuseStep 3528679 = 5293019) B5293019
theorem B2480111 : Blo 1100624 2480111 := bstep (se 1 (by rfl) ⟨1860083, by rfl⟩ : syracuseStep 2480111 = 3720167) B3720167
theorem B1103855 : Blo 1100624 1103855 := bstep (se 1 (by rfl) ⟨827891, by rfl⟩ : syracuseStep 1103855 = 1655783) B1655783
theorem B1104027 : Blo 1100624 1104027 := bstep (se 1 (by rfl) ⟨828020, by rfl⟩ : syracuseStep 1104027 = 1656041) B1656041
theorem B1104063 : Blo 1100624 1104063 := bstep (se 1 (by rfl) ⟨828047, by rfl⟩ : syracuseStep 1104063 = 1656095) B1656095
theorem B2480327 : Blo 1100624 2480327 := bstep (se 1 (by rfl) ⟨1860245, by rfl⟩ : syracuseStep 2480327 = 3720491) B3720491
theorem B3528947 : Blo 1100624 3528947 := bstep (se 1 (by rfl) ⟨2646710, by rfl⟩ : syracuseStep 3528947 = 5293421) B5293421
theorem B8378639 : Blo 1100624 8378639 := bstep (se 1 (by rfl) ⟨6283979, by rfl⟩ : syracuseStep 8378639 = 12567959) B12567959
theorem B1104175 : Blo 1100624 1104175 := bstep (se 1 (by rfl) ⟨828131, by rfl⟩ : syracuseStep 1104175 = 1656263) B1656263
theorem B3725675 : Blo 1100624 3725675 := bstep (se 1 (by rfl) ⟨2794256, by rfl⟩ : syracuseStep 3725675 = 5588513) B5588513
theorem B2480507 : Blo 1100624 2480507 := bstep (se 1 (by rfl) ⟨1860380, by rfl⟩ : syracuseStep 2480507 = 3720761) B3720761
theorem B1104411 : Blo 1100624 1104411 := bstep (se 1 (by rfl) ⟨828308, by rfl⟩ : syracuseStep 1104411 = 1656617) B1656617
theorem B1858079 : Blo 1100624 1858079 := bstep (se 1 (by rfl) ⟨1393559, by rfl⟩ : syracuseStep 1858079 = 2787119) B2787119
theorem B1104415 : Blo 1100624 1104415 := bstep (se 1 (by rfl) ⟨828311, by rfl⟩ : syracuseStep 1104415 = 1656623) B1656623
theorem B1858153 : Blo 1100624 1858153 := bstep (se 2 (by rfl) ⟨696807, by rfl⟩ : syracuseStep 1858153 = 1393615) B1393615
theorem B3725945 : Blo 1100624 3725945 := bstep (se 2 (by rfl) ⟨1397229, by rfl⟩ : syracuseStep 3725945 = 2794459) B2794459
theorem B2480777 : Blo 1100624 2480777 := bstep (se 2 (by rfl) ⟨930291, by rfl⟩ : syracuseStep 2480777 = 1860583) B1860583
theorem B6707933 : Blo 1100624 6707933 := bstep (se 3 (by rfl) ⟨1257737, by rfl⟩ : syracuseStep 6707933 = 2515475) B2515475
theorem B6281975 : Blo 1100624 6281975 := bstep (se 1 (by rfl) ⟨4711481, by rfl⟩ : syracuseStep 6281975 = 9422963) B9422963
theorem B5036843 : Blo 1100624 5036843 := bstep (se 1 (by rfl) ⟨3777632, by rfl⟩ : syracuseStep 5036843 = 7555265) B7555265
theorem B4709279 : Blo 1100624 4709279 := bstep (se 1 (by rfl) ⟨3531959, by rfl⟩ : syracuseStep 4709279 = 7063919) B7063919
theorem B1858511 : Blo 1100624 1858511 := bstep (se 1 (by rfl) ⟨1393883, by rfl⟩ : syracuseStep 1858511 = 2787767) B2787767
theorem B3726377 : Blo 1100624 3726377 := bstep (se 2 (by rfl) ⟨1397391, by rfl⟩ : syracuseStep 3726377 = 2794783) B2794783
theorem B3136637 : Blo 1100624 3136637 := bstep (se 3 (by rfl) ⟨588119, by rfl⟩ : syracuseStep 3136637 = 1176239) B1176239
theorem B4709501 : Blo 1100624 4709501 := bstep (se 3 (by rfl) ⟨883031, by rfl⟩ : syracuseStep 4709501 = 1766063) B1766063
theorem B2481335 : Blo 1100624 2481335 := bstep (se 1 (by rfl) ⟨1861001, by rfl⟩ : syracuseStep 2481335 = 3722003) B3722003
theorem B4021433 : Blo 1100624 4021433 := bstep (se 2 (by rfl) ⟨1508037, by rfl⟩ : syracuseStep 4021433 = 3016075) B3016075
theorem B5037241 : Blo 1100624 5037241 := bstep (se 2 (by rfl) ⟨1888965, by rfl⟩ : syracuseStep 5037241 = 3777931) B3777931
theorem B4185341 : Blo 1100624 4185341 := bstep (se 3 (by rfl) ⟨784751, by rfl⟩ : syracuseStep 4185341 = 1569503) B1569503
theorem B1859179 : Blo 1100624 1859179 := bstep (se 1 (by rfl) ⟨1394384, by rfl⟩ : syracuseStep 1859179 = 2788769) B2788769
theorem B2481911 : Blo 1100624 2481911 := bstep (se 1 (by rfl) ⟨1861433, by rfl⟩ : syracuseStep 2481911 = 3722867) B3722867
theorem B1859449 : Blo 1100624 1859449 := bstep (se 2 (by rfl) ⟨697293, by rfl⟩ : syracuseStep 1859449 = 1394587) B1394587
theorem B1859483 : Blo 1100624 1859483 := bstep (se 1 (by rfl) ⟨1394612, by rfl⟩ : syracuseStep 1859483 = 2789225) B2789225
theorem B2482091 : Blo 1100624 2482091 := bstep (se 1 (by rfl) ⟨1861568, by rfl⟩ : syracuseStep 2482091 = 3723137) B3723137
theorem B5300263 : Blo 1100624 5300263 := bstep (se 1 (by rfl) ⟨3975197, by rfl⟩ : syracuseStep 5300263 = 7950395) B7950395
theorem B28991587 : Blo 1100624 28991587 := bstep (se 1 (by rfl) ⟨21743690, by rfl⟩ : syracuseStep 28991587 = 43487381) B43487381
theorem B2482631 : Blo 1100624 2482631 := bstep (se 1 (by rfl) ⟨1861973, by rfl⟩ : syracuseStep 2482631 = 3723947) B3723947
theorem B2482991 : Blo 1100624 2482991 := bstep (se 1 (by rfl) ⟨1862243, by rfl⟩ : syracuseStep 2482991 = 3724487) B3724487
theorem B1860671 : Blo 1100624 1860671 := bstep (se 1 (by rfl) ⟨1395503, by rfl⟩ : syracuseStep 1860671 = 2791007) B2791007
theorem B7955819 : Blo 1100624 7955819 := bstep (se 1 (by rfl) ⟨5966864, by rfl⟩ : syracuseStep 7955819 = 11933729) B11933729
theorem B10610027 : Blo 1100624 10610027 := bstep (se 1 (by rfl) ⟨7957520, by rfl⟩ : syracuseStep 10610027 = 15915041) B15915041
theorem B15918443 : Blo 1100624 15918443 := bstep (se 1 (by rfl) ⟨11938832, by rfl⟩ : syracuseStep 15918443 = 23877665) B23877665
theorem B1861231 : Blo 1100624 1861231 := bstep (se 1 (by rfl) ⟨1395923, by rfl⟩ : syracuseStep 1861231 = 2791847) B2791847
theorem B5301881 : Blo 1100624 5301881 := bstep (se 2 (by rfl) ⟨1988205, by rfl⟩ : syracuseStep 5301881 = 3976411) B3976411
theorem B1861339 : Blo 1100624 1861339 := bstep (se 1 (by rfl) ⟨1396004, by rfl⟩ : syracuseStep 1861339 = 2792009) B2792009
theorem B1763039 : Blo 1100624 1763039 := bstep (se 1 (by rfl) ⟨1322279, by rfl⟩ : syracuseStep 1763039 = 2644559) B2644559
theorem B2352863 : Blo 1100624 2352863 := bstep (se 1 (by rfl) ⟨1764647, by rfl⟩ : syracuseStep 2352863 = 3529295) B3529295
theorem B3532511 : Blo 1100624 3532511 := bstep (se 1 (by rfl) ⟨2649383, by rfl⟩ : syracuseStep 3532511 = 5298767) B5298767
theorem B2483999 : Blo 1100624 2483999 := bstep (se 1 (by rfl) ⟨1862999, by rfl⟩ : syracuseStep 2483999 = 3725999) B3725999
theorem B2484215 : Blo 1100624 2484215 := bstep (se 1 (by rfl) ⟨1863161, by rfl⟩ : syracuseStep 2484215 = 3726323) B3726323
theorem B1763641 : Blo 1100624 1763641 := bstep (se 2 (by rfl) ⟨661365, by rfl⟩ : syracuseStep 1763641 = 1322731) B1322731
theorem B2484575 : Blo 1100624 2484575 := bstep (se 1 (by rfl) ⟨1863431, by rfl⟩ : syracuseStep 2484575 = 3726863) B3726863
theorem B50981363 : Blo 1100624 50981363 := bstep (se 1 (by rfl) ⟨38236022, by rfl⟩ : syracuseStep 50981363 = 76472045) B76472045
theorem B2353691 : Blo 1100624 2353691 := bstep (se 1 (by rfl) ⟨1765268, by rfl⟩ : syracuseStep 2353691 = 3530537) B3530537
theorem B1239583 : Blo 1100624 1239583 := bstep (se 1 (by rfl) ⟨929687, by rfl⟩ : syracuseStep 1239583 = 1859375) B1859375
theorem B8383013 : Blo 1100624 8383013 := bstep (se 4 (by rfl) ⟨785907, by rfl⟩ : syracuseStep 8383013 = 1571815) B1571815
theorem B4188743 : Blo 1100624 4188743 := bstep (se 1 (by rfl) ⟨3141557, by rfl⟩ : syracuseStep 4188743 = 6283115) B6283115
theorem B1862635 : Blo 1100624 1862635 := bstep (se 1 (by rfl) ⟨1396976, by rfl⟩ : syracuseStep 1862635 = 2793953) B2793953
theorem B2485295 : Blo 1100624 2485295 := bstep (se 1 (by rfl) ⟨1863971, by rfl⟩ : syracuseStep 2485295 = 3727943) B3727943
theorem B1862777 : Blo 1100624 1862777 := bstep (se 2 (by rfl) ⟨698541, by rfl⟩ : syracuseStep 1862777 = 1397083) B1397083
theorem B3140851 : Blo 1100624 3140851 := bstep (se 1 (by rfl) ⟨2355638, by rfl⟩ : syracuseStep 3140851 = 4711277) B4711277
theorem B2092367 : Blo 1100624 2092367 := bstep (se 1 (by rfl) ⟨1569275, by rfl⟩ : syracuseStep 2092367 = 3138551) B3138551
theorem B3141193 : Blo 1100624 3141193 := bstep (se 2 (by rfl) ⟨1177947, by rfl⟩ : syracuseStep 3141193 = 2355895) B2355895
theorem B53079715 : Blo 1100624 53079715 := bstep (se 1 (by rfl) ⟨39809786, by rfl⟩ : syracuseStep 53079715 = 79619573) B79619573
theorem B1568489 : Blo 1100624 1568489 := bstep (se 2 (by rfl) ⟨588183, by rfl⟩ : syracuseStep 1568489 = 1176367) B1176367
theorem B1175419 : Blo 1100624 1175419 := bstep (se 1 (by rfl) ⟨881564, by rfl⟩ : syracuseStep 1175419 = 1763129) B1763129
theorem B1765243 : Blo 1100624 1765243 := bstep (se 1 (by rfl) ⟨1323932, by rfl⟩ : syracuseStep 1765243 = 2647865) B2647865
theorem B4714625 : Blo 1100624 4714625 := bstep (se 2 (by rfl) ⟨1767984, by rfl⟩ : syracuseStep 4714625 = 3535969) B3535969
theorem B6287489 : Blo 1100624 6287489 := bstep (se 2 (by rfl) ⟨2357808, by rfl⟩ : syracuseStep 6287489 = 4715617) B4715617
theorem B8482981 : Blo 1100624 8482981 := bstep (se 4 (by rfl) ⟨795279, by rfl⟩ : syracuseStep 8482981 = 1590559) B1590559
theorem B1863911 : Blo 1100624 1863911 := bstep (se 1 (by rfl) ⟨1397933, by rfl⟩ : syracuseStep 1863911 = 2795867) B2795867
theorem B1766191 : Blo 1100624 1766191 := bstep (se 1 (by rfl) ⟨1324643, by rfl⟩ : syracuseStep 1766191 = 2649287) B2649287
theorem B2356219 : Blo 1100624 2356219 := bstep (se 1 (by rfl) ⟨1767164, by rfl⟩ : syracuseStep 2356219 = 3534329) B3534329
theorem B3142651 : Blo 1100624 3142651 := bstep (se 1 (by rfl) ⟨2356988, by rfl⟩ : syracuseStep 3142651 = 4713977) B4713977
theorem B1242175 : Blo 1100624 1242175 := bstep (se 1 (by rfl) ⟨931631, by rfl⟩ : syracuseStep 1242175 = 1863263) B1863263
theorem B4191371 : Blo 1100624 4191371 := bstep (se 1 (by rfl) ⟨3143528, by rfl⟩ : syracuseStep 4191371 = 6287057) B6287057
theorem B1242319 : Blo 1100624 1242319 := bstep (se 1 (by rfl) ⟨931739, by rfl⟩ : syracuseStep 1242319 = 1863479) B1863479
theorem B5305799 : Blo 1100624 5305799 := bstep (se 1 (by rfl) ⟨3979349, by rfl⟩ : syracuseStep 5305799 = 7958699) B7958699
theorem B5306107 : Blo 1100624 5306107 := bstep (se 1 (by rfl) ⟨3979580, by rfl⟩ : syracuseStep 5306107 = 7959161) B7959161
theorem B7960315 : Blo 1100624 7960315 := bstep (se 1 (by rfl) ⟨5970236, by rfl⟩ : syracuseStep 7960315 = 11940473) B11940473
theorem B33912695 : Blo 1100624 33912695 := bstep (se 1 (by rfl) ⟨25434521, by rfl⟩ : syracuseStep 33912695 = 50869043) B50869043
theorem B1767415 : Blo 1100624 1767415 := bstep (se 1 (by rfl) ⟨1325561, by rfl⟩ : syracuseStep 1767415 = 2651123) B2651123
theorem B7075937 : Blo 1100624 7075937 := bstep (se 2 (by rfl) ⟨2653476, by rfl⟩ : syracuseStep 7075937 = 5306953) B5306953
theorem B15891335 : Blo 1100624 15891335 := bstep (se 1 (by rfl) ⟨11918501, by rfl⟩ : syracuseStep 15891335 = 23837003) B23837003
theorem B2981129 : Blo 1100624 2981129 := bstep (se 2 (by rfl) ⟨1117923, by rfl⟩ : syracuseStep 2981129 = 2235847) B2235847
theorem B5963489 : Blo 1100624 5963489 := bstep (se 2 (by rfl) ⟨2236308, by rfl⟩ : syracuseStep 5963489 = 4472617) B4472617
theorem B2981821 : Blo 1100624 2981821 := bstep (se 3 (by rfl) ⟨559091, by rfl⟩ : syracuseStep 2981821 = 1118183) B1118183
theorem B8060971 : Blo 1100624 8060971 := bstep (se 1 (by rfl) ⟨6045728, by rfl⟩ : syracuseStep 8060971 = 12091457) B12091457
theorem B2787007 : Blo 1100624 2787007 := bstep (se 1 (by rfl) ⟨2090255, by rfl⟩ : syracuseStep 2787007 = 4180511) B4180511
theorem B2787311 : Blo 1100624 2787311 := bstep (se 1 (by rfl) ⟨2090483, by rfl⟩ : syracuseStep 2787311 = 4180967) B4180967
theorem B5376203 : Blo 1100624 5376203 := bstep (se 1 (by rfl) ⟨4032152, by rfl⟩ : syracuseStep 5376203 = 8064305) B8064305
theorem B2788415 : Blo 1100624 2788415 := bstep (se 1 (by rfl) ⟨2091311, by rfl⟩ : syracuseStep 2788415 = 4182623) B4182623
theorem B2985551 : Blo 1100624 2985551 := bstep (se 1 (by rfl) ⟨2239163, by rfl⟩ : syracuseStep 2985551 = 4478327) B4478327
theorem B4198267 : Blo 1100624 4198267 := bstep (se 1 (by rfl) ⟨3148700, by rfl⟩ : syracuseStep 4198267 = 6297401) B6297401
theorem B4526209 : Blo 1100624 4526209 := bstep (se 2 (by rfl) ⟨1697328, by rfl⟩ : syracuseStep 4526209 = 3394657) B3394657
theorem B7934249 : Blo 1100624 7934249 := bstep (se 2 (by rfl) ⟨2975343, by rfl⟩ : syracuseStep 7934249 = 5950687) B5950687
theorem B2790227 : Blo 1100624 2790227 := bstep (se 1 (by rfl) ⟨2092670, by rfl⟩ : syracuseStep 2790227 = 4185341) B4185341
theorem B15308129 : Blo 1100624 15308129 := bstep (se 2 (by rfl) ⟨5740548, by rfl⟩ : syracuseStep 15308129 = 11481097) B11481097
theorem B19076471 : Blo 1100624 19076471 := bstep (se 1 (by rfl) ⟨14307353, by rfl⟩ : syracuseStep 19076471 = 28614707) B28614707
theorem B11310641 : Blo 1100624 11310641 := bstep (se 2 (by rfl) ⟨4241490, by rfl⟩ : syracuseStep 11310641 = 8482981) B8482981
theorem B9410525 : Blo 1100624 9410525 := bstep (se 3 (by rfl) ⟨1764473, by rfl⟩ : syracuseStep 9410525 = 3528947) B3528947
theorem B6363623 : Blo 1100624 6363623 := bstep (se 1 (by rfl) ⟨4772717, by rfl⟩ : syracuseStep 6363623 = 9545435) B9545435
theorem B20126483 : Blo 1100624 20126483 := bstep (se 1 (by rfl) ⟨15094862, by rfl⟩ : syracuseStep 20126483 = 30189725) B30189725
theorem B33987575 : Blo 1100624 33987575 := bstep (se 1 (by rfl) ⟨25490681, by rfl⟩ : syracuseStep 33987575 = 50981363) B50981363
theorem B2792495 : Blo 1100624 2792495 := bstep (se 1 (by rfl) ⟨2094371, by rfl⟩ : syracuseStep 2792495 = 4188743) B4188743
theorem B2794247 : Blo 1100624 2794247 := bstep (se 1 (by rfl) ⟨2095685, by rfl⟩ : syracuseStep 2794247 = 4191371) B4191371
theorem B13772585 : Blo 1100624 13772585 := bstep (se 2 (by rfl) ⟨5164719, by rfl⟩ : syracuseStep 13772585 = 10329439) B10329439
theorem B7939903 : Blo 1100624 7939903 := bstep (se 1 (by rfl) ⟨5954927, by rfl⟩ : syracuseStep 7939903 = 11909855) B11909855
theorem B64563077 : Blo 1100624 64563077 := bstep (se 4 (by rfl) ⟨6052788, by rfl⟩ : syracuseStep 64563077 = 12105577) B12105577
theorem B10594223 : Blo 1100624 10594223 := bstep (se 1 (by rfl) ⟨7945667, by rfl⟩ : syracuseStep 10594223 = 15891335) B15891335
theorem B1255807 : Blo 1100624 1255807 := bstep (se 1 (by rfl) ⟨941855, by rfl⟩ : syracuseStep 1255807 = 1883711) B1883711
theorem B3975659 : Blo 1100624 3975659 := bstep (se 1 (by rfl) ⟨2981744, by rfl⟩ : syracuseStep 3975659 = 5963489) B5963489
theorem B3975761 : Blo 1100624 3975761 := bstep (se 2 (by rfl) ⟨1490910, by rfl⟩ : syracuseStep 3975761 = 2981821) B2981821
theorem B10596221 : Blo 1100624 10596221 := bstep (se 3 (by rfl) ⟨1986791, by rfl⟩ : syracuseStep 10596221 = 3973583) B3973583
theorem B3715199 : Blo 1100624 3715199 := bstep (se 1 (by rfl) ⟨2786399, by rfl⟩ : syracuseStep 3715199 = 5572799) B5572799
theorem B21213899 : Blo 1100624 21213899 := bstep (se 1 (by rfl) ⟨15910424, by rfl⟩ : syracuseStep 21213899 = 31820849) B31820849
theorem B1651451 : Blo 1100624 1651451 := bstep (se 1 (by rfl) ⟨1238588, by rfl⟩ : syracuseStep 1651451 = 2477177) B2477177
theorem B5026585 : Blo 1100624 5026585 := bstep (se 2 (by rfl) ⟨1884969, by rfl⟩ : syracuseStep 5026585 = 3769939) B3769939
theorem B11940815 : Blo 1100624 11940815 := bstep (se 1 (by rfl) ⟨8955611, by rfl⟩ : syracuseStep 11940815 = 17911223) B17911223
theorem B3716225 : Blo 1100624 3716225 := bstep (se 2 (by rfl) ⟨1393584, by rfl⟩ : syracuseStep 3716225 = 2787169) B2787169
theorem B1651895 : Blo 1100624 1651895 := bstep (se 1 (by rfl) ⟨1238921, by rfl⟩ : syracuseStep 1651895 = 2477843) B2477843
theorem B7550171 : Blo 1100624 7550171 := bstep (se 1 (by rfl) ⟨5662628, by rfl⟩ : syracuseStep 7550171 = 11325257) B11325257
theorem B5584139 : Blo 1100624 5584139 := bstep (se 1 (by rfl) ⟨4188104, by rfl⟩ : syracuseStep 5584139 = 8376209) B8376209
theorem B1488191 : Blo 1100624 1488191 := bstep (se 1 (by rfl) ⟨1116143, by rfl⟩ : syracuseStep 1488191 = 2232287) B2232287
theorem B1652135 : Blo 1100624 1652135 := bstep (se 1 (by rfl) ⟨1239101, by rfl⟩ : syracuseStep 1652135 = 2478203) B2478203
theorem B1652315 : Blo 1100624 1652315 := bstep (se 1 (by rfl) ⟨1239236, by rfl⟩ : syracuseStep 1652315 = 2478473) B2478473
theorem B3717035 : Blo 1100624 3717035 := bstep (se 1 (by rfl) ⟨2787776, by rfl⟩ : syracuseStep 3717035 = 5575553) B5575553
theorem B5289943 : Blo 1100624 5289943 := bstep (se 1 (by rfl) ⟨3967457, by rfl⟩ : syracuseStep 5289943 = 7934915) B7934915
theorem B1652777 : Blo 1100624 1652777 := bstep (se 2 (by rfl) ⟨619791, by rfl⟩ : syracuseStep 1652777 = 1239583) B1239583
theorem B1652807 : Blo 1100624 1652807 := bstep (se 1 (by rfl) ⟨1239605, by rfl⟩ : syracuseStep 1652807 = 2479211) B2479211
theorem B4307039 : Blo 1100624 4307039 := bstep (se 1 (by rfl) ⟨3230279, by rfl⟩ : syracuseStep 4307039 = 6460559) B6460559
theorem B3717575 : Blo 1100624 3717575 := bstep (se 1 (by rfl) ⟨2788181, by rfl⟩ : syracuseStep 3717575 = 5576363) B5576363
theorem B1653191 : Blo 1100624 1653191 := bstep (se 1 (by rfl) ⟨1239893, by rfl⟩ : syracuseStep 1653191 = 2479787) B2479787
theorem B4307399 : Blo 1100624 4307399 := bstep (se 1 (by rfl) ⟨3230549, by rfl⟩ : syracuseStep 4307399 = 6461099) B6461099
theorem B3717791 : Blo 1100624 3717791 := bstep (se 1 (by rfl) ⟨2788343, by rfl⟩ : syracuseStep 3717791 = 5576687) B5576687
theorem B1653407 : Blo 1100624 1653407 := bstep (se 1 (by rfl) ⟨1240055, by rfl⟩ : syracuseStep 1653407 = 2480111) B2480111
theorem B1653551 : Blo 1100624 1653551 := bstep (se 1 (by rfl) ⟨1240163, by rfl⟩ : syracuseStep 1653551 = 2480327) B2480327
theorem B38255449 : Blo 1100624 38255449 := bstep (se 2 (by rfl) ⟨14345793, by rfl⟩ : syracuseStep 38255449 = 28691587) B28691587
theorem B5585759 : Blo 1100624 5585759 := bstep (se 1 (by rfl) ⟨4189319, by rfl⟩ : syracuseStep 5585759 = 8378639) B8378639
theorem B1653671 : Blo 1100624 1653671 := bstep (se 1 (by rfl) ⟨1240253, by rfl⟩ : syracuseStep 1653671 = 2480507) B2480507
theorem B1653851 : Blo 1100624 1653851 := bstep (se 1 (by rfl) ⟨1240388, by rfl⟩ : syracuseStep 1653851 = 2480777) B2480777
theorem B4471955 : Blo 1100624 4471955 := bstep (se 1 (by rfl) ⟨3353966, by rfl⟩ : syracuseStep 4471955 = 6707933) B6707933
theorem B3357895 : Blo 1100624 3357895 := bstep (se 1 (by rfl) ⟨2518421, by rfl⟩ : syracuseStep 3357895 = 5036843) B5036843
theorem B1654223 : Blo 1100624 1654223 := bstep (se 1 (by rfl) ⟨1240667, by rfl⟩ : syracuseStep 1654223 = 2481335) B2481335
theorem B3718763 : Blo 1100624 3718763 := bstep (se 1 (by rfl) ⟨2789072, by rfl⟩ : syracuseStep 3718763 = 5578145) B5578145
theorem B1654607 : Blo 1100624 1654607 := bstep (se 1 (by rfl) ⟨1240955, by rfl⟩ : syracuseStep 1654607 = 2481911) B2481911
theorem B3719033 : Blo 1100624 3719033 := bstep (se 2 (by rfl) ⟨1394637, by rfl⟩ : syracuseStep 3719033 = 2789275) B2789275
theorem B1654727 : Blo 1100624 1654727 := bstep (se 1 (by rfl) ⟨1241045, by rfl⟩ : syracuseStep 1654727 = 2482091) B2482091
theorem B7258085 : Blo 1100624 7258085 := bstep (se 4 (by rfl) ⟨680445, by rfl⟩ : syracuseStep 7258085 = 1360891) B1360891
theorem B12566501 : Blo 1100624 12566501 := bstep (se 4 (by rfl) ⟨1178109, by rfl⟩ : syracuseStep 12566501 = 2356219) B2356219
theorem B9421049 : Blo 1100624 9421049 := bstep (se 2 (by rfl) ⟨3532893, by rfl⟩ : syracuseStep 9421049 = 7065787) B7065787
theorem B1655087 : Blo 1100624 1655087 := bstep (se 1 (by rfl) ⟨1241315, by rfl⟩ : syracuseStep 1655087 = 2482631) B2482631
theorem B1655327 : Blo 1100624 1655327 := bstep (se 1 (by rfl) ⟨1241495, by rfl⟩ : syracuseStep 1655327 = 2482991) B2482991
theorem B8929925 : Blo 1100624 8929925 := bstep (se 4 (by rfl) ⟨837180, by rfl⟩ : syracuseStep 8929925 = 1674361) B1674361
theorem B3720383 : Blo 1100624 3720383 := bstep (se 1 (by rfl) ⟨2790287, by rfl⟩ : syracuseStep 3720383 = 5580575) B5580575
theorem B1655999 : Blo 1100624 1655999 := bstep (se 1 (by rfl) ⟨1241999, by rfl⟩ : syracuseStep 1655999 = 2483999) B2483999
theorem B1656143 : Blo 1100624 1656143 := bstep (se 1 (by rfl) ⟨1242107, by rfl⟩ : syracuseStep 1656143 = 2484215) B2484215
theorem B3720545 : Blo 1100624 3720545 := bstep (se 2 (by rfl) ⟨1395204, by rfl⟩ : syracuseStep 3720545 = 2790409) B2790409
theorem B1656233 : Blo 1100624 1656233 := bstep (se 2 (by rfl) ⟨621087, by rfl⟩ : syracuseStep 1656233 = 1242175) B1242175
theorem B8373779 : Blo 1100624 8373779 := bstep (se 1 (by rfl) ⟨6280334, by rfl⟩ : syracuseStep 8373779 = 12560669) B12560669
theorem B1656383 : Blo 1100624 1656383 := bstep (se 1 (by rfl) ⟨1242287, by rfl⟩ : syracuseStep 1656383 = 2484575) B2484575
theorem B1656425 : Blo 1100624 1656425 := bstep (se 2 (by rfl) ⟨621159, by rfl⟩ : syracuseStep 1656425 = 1242319) B1242319
theorem B5588675 : Blo 1100624 5588675 := bstep (se 1 (by rfl) ⟨4191506, by rfl⟩ : syracuseStep 5588675 = 8383013) B8383013
theorem B3721247 : Blo 1100624 3721247 := bstep (se 1 (by rfl) ⟨2790935, by rfl⟩ : syracuseStep 3721247 = 5581871) B5581871
theorem B1656863 : Blo 1100624 1656863 := bstep (se 1 (by rfl) ⟨1242647, by rfl⟩ : syracuseStep 1656863 = 2485295) B2485295
theorem B1394911 : Blo 1100624 1394911 := bstep (se 1 (by rfl) ⟨1046183, by rfl⟩ : syracuseStep 1394911 = 2092367) B2092367
theorem B2476457 : Blo 1100624 2476457 := bstep (se 2 (by rfl) ⟨928671, by rfl⟩ : syracuseStep 2476457 = 1857343) B1857343
theorem B4704905 : Blo 1100624 4704905 := bstep (se 2 (by rfl) ⟨1764339, by rfl⟩ : syracuseStep 4704905 = 3528679) B3528679
theorem B1100767 : Blo 1100624 1100767 := bstep (se 1 (by rfl) ⟨825575, by rfl⟩ : syracuseStep 1100767 = 1651151) B1651151
theorem B1100795 : Blo 1100624 1100795 := bstep (se 1 (by rfl) ⟨825596, by rfl⟩ : syracuseStep 1100795 = 1651193) B1651193
theorem B2477051 : Blo 1100624 2477051 := bstep (se 1 (by rfl) ⟨1857788, by rfl⟩ : syracuseStep 2477051 = 3715577) B3715577
theorem B1100863 : Blo 1100624 1100863 := bstep (se 1 (by rfl) ⟨825647, by rfl⟩ : syracuseStep 1100863 = 1651295) B1651295
theorem B2477231 : Blo 1100624 2477231 := bstep (se 1 (by rfl) ⟨1857923, by rfl⟩ : syracuseStep 2477231 = 3715847) B3715847
theorem B2477267 : Blo 1100624 2477267 := bstep (se 1 (by rfl) ⟨1857950, by rfl⟩ : syracuseStep 2477267 = 3715901) B3715901
theorem B7949677 : Blo 1100624 7949677 := bstep (se 3 (by rfl) ⟨1490564, by rfl⟩ : syracuseStep 7949677 = 2981129) B2981129
theorem B1101183 : Blo 1100624 1101183 := bstep (se 1 (by rfl) ⟨825887, by rfl⟩ : syracuseStep 1101183 = 1651775) B1651775
theorem B1101211 : Blo 1100624 1101211 := bstep (se 1 (by rfl) ⟨825908, by rfl⟩ : syracuseStep 1101211 = 1651817) B1651817
theorem B1101279 : Blo 1100624 1101279 := bstep (se 1 (by rfl) ⟨825959, by rfl⟩ : syracuseStep 1101279 = 1651919) B1651919
theorem B2477537 : Blo 1100624 2477537 := bstep (se 2 (by rfl) ⟨929076, by rfl⟩ : syracuseStep 2477537 = 1858153) B1858153
theorem B1101415 : Blo 1100624 1101415 := bstep (se 1 (by rfl) ⟨826061, by rfl⟩ : syracuseStep 1101415 = 1652123) B1652123
theorem B1101563 : Blo 1100624 1101563 := bstep (se 1 (by rfl) ⟨826172, by rfl⟩ : syracuseStep 1101563 = 1652345) B1652345
theorem B1101631 : Blo 1100624 1101631 := bstep (se 1 (by rfl) ⟨826223, by rfl⟩ : syracuseStep 1101631 = 1652447) B1652447
theorem B2477951 : Blo 1100624 2477951 := bstep (se 1 (by rfl) ⟨1858463, by rfl⟩ : syracuseStep 2477951 = 3716927) B3716927
theorem B1101695 : Blo 1100624 1101695 := bstep (se 1 (by rfl) ⟨826271, by rfl⟩ : syracuseStep 1101695 = 1652543) B1652543
theorem B1101807 : Blo 1100624 1101807 := bstep (se 1 (by rfl) ⟨826355, by rfl⟩ : syracuseStep 1101807 = 1652711) B1652711
theorem B1101819 : Blo 1100624 1101819 := bstep (se 1 (by rfl) ⟨826364, by rfl⟩ : syracuseStep 1101819 = 1652729) B1652729
theorem B1101887 : Blo 1100624 1101887 := bstep (se 1 (by rfl) ⟨826415, by rfl⟩ : syracuseStep 1101887 = 1652831) B1652831
theorem B1101927 : Blo 1100624 1101927 := bstep (se 1 (by rfl) ⟨826445, by rfl⟩ : syracuseStep 1101927 = 1652891) B1652891
theorem B1101951 : Blo 1100624 1101951 := bstep (se 1 (by rfl) ⟨826463, by rfl⟩ : syracuseStep 1101951 = 1652927) B1652927
theorem B1101979 : Blo 1100624 1101979 := bstep (se 1 (by rfl) ⟨826484, by rfl⟩ : syracuseStep 1101979 = 1652969) B1652969
theorem B6279515 : Blo 1100624 6279515 := bstep (se 1 (by rfl) ⟨4709636, by rfl⟩ : syracuseStep 6279515 = 9419273) B9419273
theorem B1102183 : Blo 1100624 1102183 := bstep (se 1 (by rfl) ⟨826637, by rfl⟩ : syracuseStep 1102183 = 1653275) B1653275
theorem B13390217 : Blo 1100624 13390217 := bstep (se 2 (by rfl) ⟨5021331, by rfl⟩ : syracuseStep 13390217 = 10042663) B10042663
theorem B1102235 : Blo 1100624 1102235 := bstep (se 1 (by rfl) ⟨826676, by rfl⟩ : syracuseStep 1102235 = 1653353) B1653353
theorem B9425423 : Blo 1100624 9425423 := bstep (se 1 (by rfl) ⟨7069067, by rfl⟩ : syracuseStep 9425423 = 14138135) B14138135
theorem B4182637 : Blo 1100624 4182637 := bstep (se 3 (by rfl) ⟨784244, by rfl⟩ : syracuseStep 4182637 = 1568489) B1568489
theorem B1102587 : Blo 1100624 1102587 := bstep (se 1 (by rfl) ⟨826940, by rfl⟩ : syracuseStep 1102587 = 1653881) B1653881
theorem B2478905 : Blo 1100624 2478905 := bstep (se 2 (by rfl) ⟨929589, by rfl⟩ : syracuseStep 2478905 = 1859179) B1859179
theorem B1102655 : Blo 1100624 1102655 := bstep (se 1 (by rfl) ⟨826991, by rfl⟩ : syracuseStep 1102655 = 1653983) B1653983
theorem B1102683 : Blo 1100624 1102683 := bstep (se 1 (by rfl) ⟨827012, by rfl⟩ : syracuseStep 1102683 = 1654025) B1654025
theorem B2478959 : Blo 1100624 2478959 := bstep (se 1 (by rfl) ⟨1859219, by rfl⟩ : syracuseStep 2478959 = 3718439) B3718439
theorem B1102751 : Blo 1100624 1102751 := bstep (se 1 (by rfl) ⟨827063, by rfl⟩ : syracuseStep 1102751 = 1654127) B1654127
theorem B1102831 : Blo 1100624 1102831 := bstep (se 1 (by rfl) ⟨827123, by rfl⟩ : syracuseStep 1102831 = 1654247) B1654247
theorem B1102919 : Blo 1100624 1102919 := bstep (se 1 (by rfl) ⟨827189, by rfl⟩ : syracuseStep 1102919 = 1654379) B1654379
theorem B1103003 : Blo 1100624 1103003 := bstep (se 1 (by rfl) ⟨827252, by rfl⟩ : syracuseStep 1103003 = 1654505) B1654505
theorem B2479265 : Blo 1100624 2479265 := bstep (se 2 (by rfl) ⟨929724, by rfl⟩ : syracuseStep 2479265 = 1859449) B1859449
theorem B1103099 : Blo 1100624 1103099 := bstep (se 1 (by rfl) ⟨827324, by rfl⟩ : syracuseStep 1103099 = 1654649) B1654649
theorem B3724541 : Blo 1100624 3724541 := bstep (se 3 (by rfl) ⟨698351, by rfl⟩ : syracuseStep 3724541 = 1396703) B1396703
theorem B1103167 : Blo 1100624 1103167 := bstep (se 1 (by rfl) ⟨827375, by rfl⟩ : syracuseStep 1103167 = 1654751) B1654751
theorem B7067017 : Blo 1100624 7067017 := bstep (se 2 (by rfl) ⟨2650131, by rfl⟩ : syracuseStep 7067017 = 5300263) B5300263
theorem B2479535 : Blo 1100624 2479535 := bstep (se 1 (by rfl) ⟨1859651, by rfl⟩ : syracuseStep 2479535 = 3719303) B3719303
theorem B38655449 : Blo 1100624 38655449 := bstep (se 2 (by rfl) ⟨14495793, by rfl⟩ : syracuseStep 38655449 = 28991587) B28991587
theorem B1103335 : Blo 1100624 1103335 := bstep (se 1 (by rfl) ⟨827501, by rfl⟩ : syracuseStep 1103335 = 1655003) B1655003
theorem B1103343 : Blo 1100624 1103343 := bstep (se 1 (by rfl) ⟨827507, by rfl⟩ : syracuseStep 1103343 = 1655015) B1655015
theorem B1103451 : Blo 1100624 1103451 := bstep (se 1 (by rfl) ⟨827588, by rfl⟩ : syracuseStep 1103451 = 1655177) B1655177
theorem B1103515 : Blo 1100624 1103515 := bstep (se 1 (by rfl) ⟨827636, by rfl⟩ : syracuseStep 1103515 = 1655273) B1655273
theorem B12572333 : Blo 1100624 12572333 := bstep (se 3 (by rfl) ⟨2357312, by rfl⟩ : syracuseStep 12572333 = 4714625) B4714625
theorem B1103599 : Blo 1100624 1103599 := bstep (se 1 (by rfl) ⟨827699, by rfl⟩ : syracuseStep 1103599 = 1655399) B1655399
theorem B1103687 : Blo 1100624 1103687 := bstep (se 1 (by rfl) ⟨827765, by rfl⟩ : syracuseStep 1103687 = 1655531) B1655531
theorem B1103707 : Blo 1100624 1103707 := bstep (se 1 (by rfl) ⟨827780, by rfl⟩ : syracuseStep 1103707 = 1655561) B1655561
theorem B1103775 : Blo 1100624 1103775 := bstep (se 1 (by rfl) ⟨827831, by rfl⟩ : syracuseStep 1103775 = 1655663) B1655663
theorem B3725351 : Blo 1100624 3725351 := bstep (se 1 (by rfl) ⟨2794013, by rfl⟩ : syracuseStep 3725351 = 5588027) B5588027
theorem B1103943 : Blo 1100624 1103943 := bstep (se 1 (by rfl) ⟨827957, by rfl⟩ : syracuseStep 1103943 = 1655915) B1655915
theorem B3725459 : Blo 1100624 3725459 := bstep (se 1 (by rfl) ⟨2794094, by rfl⟩ : syracuseStep 3725459 = 5588189) B5588189
theorem B13588651 : Blo 1100624 13588651 := bstep (se 1 (by rfl) ⟨10191488, by rfl⟩ : syracuseStep 13588651 = 20382977) B20382977
theorem B1857755 : Blo 1100624 1857755 := bstep (se 1 (by rfl) ⟨1393316, by rfl⟩ : syracuseStep 1857755 = 2786633) B2786633
theorem B1104103 : Blo 1100624 1104103 := bstep (se 1 (by rfl) ⟨828077, by rfl⟩ : syracuseStep 1104103 = 1656155) B1656155
theorem B12540257 : Blo 1100624 12540257 := bstep (se 2 (by rfl) ⟨4702596, by rfl⟩ : syracuseStep 12540257 = 9405193) B9405193
theorem B2480543 : Blo 1100624 2480543 := bstep (se 1 (by rfl) ⟨1860407, by rfl⟩ : syracuseStep 2480543 = 3720815) B3720815
theorem B1104287 : Blo 1100624 1104287 := bstep (se 1 (by rfl) ⟨828215, by rfl⟩ : syracuseStep 1104287 = 1656431) B1656431
theorem B3725729 : Blo 1100624 3725729 := bstep (se 2 (by rfl) ⟨1397148, by rfl⟩ : syracuseStep 3725729 = 2794297) B2794297
theorem B1104335 : Blo 1100624 1104335 := bstep (se 1 (by rfl) ⟨828251, by rfl⟩ : syracuseStep 1104335 = 1656503) B1656503
theorem B2480615 : Blo 1100624 2480615 := bstep (se 1 (by rfl) ⟨1860461, by rfl⟩ : syracuseStep 2480615 = 3720923) B3720923
theorem B1104359 : Blo 1100624 1104359 := bstep (se 1 (by rfl) ⟨828269, by rfl⟩ : syracuseStep 1104359 = 1656539) B1656539
theorem B1858025 : Blo 1100624 1858025 := bstep (se 2 (by rfl) ⟨696759, by rfl⟩ : syracuseStep 1858025 = 1393519) B1393519
theorem B1104475 : Blo 1100624 1104475 := bstep (se 1 (by rfl) ⟨828356, by rfl⟩ : syracuseStep 1104475 = 1656713) B1656713
theorem B1104543 : Blo 1100624 1104543 := bstep (se 1 (by rfl) ⟨828407, by rfl⟩ : syracuseStep 1104543 = 1656815) B1656815
theorem B3726269 : Blo 1100624 3726269 := bstep (se 3 (by rfl) ⟨698675, by rfl⟩ : syracuseStep 3726269 = 1397351) B1397351
theorem B4185067 : Blo 1100624 4185067 := bstep (se 1 (by rfl) ⟨3138800, by rfl⟩ : syracuseStep 4185067 = 6277601) B6277601
theorem B2481479 : Blo 1100624 2481479 := bstep (se 1 (by rfl) ⟨1861109, by rfl⟩ : syracuseStep 2481479 = 3722219) B3722219
theorem B2481515 : Blo 1100624 2481515 := bstep (se 1 (by rfl) ⟨1861136, by rfl⟩ : syracuseStep 2481515 = 3722273) B3722273
theorem B4185539 : Blo 1100624 4185539 := bstep (se 1 (by rfl) ⟨3139154, by rfl⟩ : syracuseStep 4185539 = 6278309) B6278309
theorem B2481641 : Blo 1100624 2481641 := bstep (se 2 (by rfl) ⟨930615, by rfl⟩ : syracuseStep 2481641 = 1861231) B1861231
theorem B5168731 : Blo 1100624 5168731 := bstep (se 1 (by rfl) ⟨3876548, by rfl⟩ : syracuseStep 5168731 = 7753097) B7753097
theorem B2481785 : Blo 1100624 2481785 := bstep (se 2 (by rfl) ⟨930669, by rfl⟩ : syracuseStep 2481785 = 1861339) B1861339
theorem B12541715 : Blo 1100624 12541715 := bstep (se 1 (by rfl) ⟨9406286, by rfl⟩ : syracuseStep 12541715 = 18812573) B18812573
theorem B2351359 : Blo 1100624 2351359 := bstep (se 1 (by rfl) ⟨1763519, by rfl⟩ : syracuseStep 2351359 = 3527039) B3527039
theorem B2482487 : Blo 1100624 2482487 := bstep (se 1 (by rfl) ⟨1861865, by rfl⟩ : syracuseStep 2482487 = 3723731) B3723731
theorem B3727673 : Blo 1100624 3727673 := bstep (se 2 (by rfl) ⟨1397877, by rfl⟩ : syracuseStep 3727673 = 2795755) B2795755
theorem B2351521 : Blo 1100624 2351521 := bstep (se 2 (by rfl) ⟨881820, by rfl⟩ : syracuseStep 2351521 = 1763641) B1763641
theorem B5956051 : Blo 1100624 5956051 := bstep (se 1 (by rfl) ⟨4467038, by rfl⟩ : syracuseStep 5956051 = 8934077) B8934077
theorem B4186799 : Blo 1100624 4186799 := bstep (se 1 (by rfl) ⟨3140099, by rfl⟩ : syracuseStep 4186799 = 6280199) B6280199
theorem B3138335 : Blo 1100624 3138335 := bstep (se 1 (by rfl) ⟨2353751, by rfl⟩ : syracuseStep 3138335 = 4707503) B4707503
theorem B2647019 : Blo 1100624 2647019 := bstep (se 1 (by rfl) ⟨1985264, by rfl⟩ : syracuseStep 2647019 = 3970529) B3970529
theorem B3531755 : Blo 1100624 3531755 := bstep (se 1 (by rfl) ⟨2648816, by rfl⟩ : syracuseStep 3531755 = 5297633) B5297633
theorem B5301227 : Blo 1100624 5301227 := bstep (se 1 (by rfl) ⟨3975920, by rfl⟩ : syracuseStep 5301227 = 7951841) B7951841
theorem B196338887 : Blo 1100624 196338887 := bstep (se 1 (by rfl) ⟨147254165, by rfl⟩ : syracuseStep 196338887 = 294508331) B294508331
theorem B2483513 : Blo 1100624 2483513 := bstep (se 2 (by rfl) ⟨931317, by rfl⟩ : syracuseStep 2483513 = 1862635) B1862635
theorem B2483783 : Blo 1100624 2483783 := bstep (se 1 (by rfl) ⟨1862837, by rfl⟩ : syracuseStep 2483783 = 3725675) B3725675
theorem B4187801 : Blo 1100624 4187801 := bstep (se 2 (by rfl) ⟨1570425, by rfl⟩ : syracuseStep 4187801 = 3140851) B3140851
theorem B1238719 : Blo 1100624 1238719 := bstep (se 1 (by rfl) ⟨929039, by rfl⟩ : syracuseStep 1238719 = 1858079) B1858079
theorem B2483963 : Blo 1100624 2483963 := bstep (se 1 (by rfl) ⟨1862972, by rfl⟩ : syracuseStep 2483963 = 3725945) B3725945
theorem B4187983 : Blo 1100624 4187983 := bstep (se 1 (by rfl) ⟨3140987, by rfl⟩ : syracuseStep 4187983 = 6281975) B6281975
theorem B6711119 : Blo 1100624 6711119 := bstep (se 1 (by rfl) ⟨5033339, by rfl⟩ : syracuseStep 6711119 = 10066679) B10066679
theorem B3139519 : Blo 1100624 3139519 := bstep (se 1 (by rfl) ⟨2354639, by rfl⟩ : syracuseStep 3139519 = 4709279) B4709279
theorem B1239007 : Blo 1100624 1239007 := bstep (se 1 (by rfl) ⟨929255, by rfl⟩ : syracuseStep 1239007 = 1858511) B1858511
theorem B2484251 : Blo 1100624 2484251 := bstep (se 1 (by rfl) ⟨1863188, by rfl⟩ : syracuseStep 2484251 = 3726377) B3726377
theorem B2091091 : Blo 1100624 2091091 := bstep (se 1 (by rfl) ⟨1568318, by rfl⟩ : syracuseStep 2091091 = 3136637) B3136637
theorem B3139667 : Blo 1100624 3139667 := bstep (se 1 (by rfl) ⟨2354750, by rfl⟩ : syracuseStep 3139667 = 4709501) B4709501
theorem B4188257 : Blo 1100624 4188257 := bstep (se 2 (by rfl) ⟨1570596, by rfl⟩ : syracuseStep 4188257 = 3141193) B3141193
theorem B2680955 : Blo 1100624 2680955 := bstep (se 1 (by rfl) ⟨2010716, by rfl⟩ : syracuseStep 2680955 = 4021433) B4021433
theorem B70772953 : Blo 1100624 70772953 := bstep (se 2 (by rfl) ⟨26539857, by rfl⟩ : syracuseStep 70772953 = 53079715) B53079715
theorem B90433853 : Blo 1100624 90433853 := bstep (se 3 (by rfl) ⟨16956347, by rfl⟩ : syracuseStep 90433853 = 33912695) B33912695
theorem B1567225 : Blo 1100624 1567225 := bstep (se 2 (by rfl) ⟨587709, by rfl⟩ : syracuseStep 1567225 = 1175419) B1175419
theorem B2353657 : Blo 1100624 2353657 := bstep (se 2 (by rfl) ⟨882621, by rfl⟩ : syracuseStep 2353657 = 1765243) B1765243
theorem B1239655 : Blo 1100624 1239655 := bstep (se 1 (by rfl) ⟨929741, by rfl⟩ : syracuseStep 1239655 = 1859483) B1859483
theorem B1240447 : Blo 1100624 1240447 := bstep (se 1 (by rfl) ⟨930335, by rfl⟩ : syracuseStep 1240447 = 1860671) B1860671
theorem B1863067 : Blo 1100624 1863067 := bstep (se 1 (by rfl) ⟨1397300, by rfl⟩ : syracuseStep 1863067 = 2794601) B2794601
theorem B5303879 : Blo 1100624 5303879 := bstep (se 1 (by rfl) ⟨3977909, by rfl⟩ : syracuseStep 5303879 = 7955819) B7955819
theorem B7073351 : Blo 1100624 7073351 := bstep (se 1 (by rfl) ⟨5305013, by rfl⟩ : syracuseStep 7073351 = 10610027) B10610027
theorem B10612295 : Blo 1100624 10612295 := bstep (se 1 (by rfl) ⟨7959221, by rfl⟩ : syracuseStep 10612295 = 15918443) B15918443
theorem B17198689 : Blo 1100624 17198689 := bstep (se 2 (by rfl) ⟨6449508, by rfl⟩ : syracuseStep 17198689 = 12899017) B12899017
theorem B20082401 : Blo 1100624 20082401 := bstep (se 2 (by rfl) ⟨7530900, by rfl⟩ : syracuseStep 20082401 = 15061801) B15061801
theorem B2354921 : Blo 1100624 2354921 := bstep (se 2 (by rfl) ⟨883095, by rfl⟩ : syracuseStep 2354921 = 1766191) B1766191
theorem B3534587 : Blo 1100624 3534587 := bstep (se 1 (by rfl) ⟨2650940, by rfl⟩ : syracuseStep 3534587 = 5301881) B5301881
theorem B1175359 : Blo 1100624 1175359 := bstep (se 1 (by rfl) ⟨881519, by rfl⟩ : syracuseStep 1175359 = 1763039) B1763039
theorem B1568575 : Blo 1100624 1568575 := bstep (se 1 (by rfl) ⟨1176431, by rfl⟩ : syracuseStep 1568575 = 2352863) B2352863
theorem B2355007 : Blo 1100624 2355007 := bstep (se 1 (by rfl) ⟨1766255, by rfl⟩ : syracuseStep 2355007 = 3532511) B3532511
theorem B14708567 : Blo 1100624 14708567 := bstep (se 1 (by rfl) ⟨11031425, by rfl⟩ : syracuseStep 14708567 = 22062851) B22062851
theorem B21458843 : Blo 1100624 21458843 := bstep (se 1 (by rfl) ⟨16094132, by rfl⟩ : syracuseStep 21458843 = 32188265) B32188265
theorem B4190201 : Blo 1100624 4190201 := bstep (se 2 (by rfl) ⟨1571325, by rfl⟩ : syracuseStep 4190201 = 3142651) B3142651
theorem B1863823 : Blo 1100624 1863823 := bstep (se 1 (by rfl) ⟨1397867, by rfl⟩ : syracuseStep 1863823 = 2795735) B2795735
theorem B2519315 : Blo 1100624 2519315 := bstep (se 1 (by rfl) ⟨1889486, by rfl⟩ : syracuseStep 2519315 = 3778973) B3778973
theorem B1569127 : Blo 1100624 1569127 := bstep (se 1 (by rfl) ⟨1176845, by rfl⟩ : syracuseStep 1569127 = 2353691) B2353691
theorem B1864039 : Blo 1100624 1864039 := bstep (se 1 (by rfl) ⟨1398029, by rfl⟩ : syracuseStep 1864039 = 2796059) B2796059
theorem B10580615 : Blo 1100624 10580615 := bstep (se 1 (by rfl) ⟨7935461, by rfl⟩ : syracuseStep 10580615 = 15870923) B15870923
theorem B1241851 : Blo 1100624 1241851 := bstep (se 1 (by rfl) ⟨931388, by rfl⟩ : syracuseStep 1241851 = 1862777) B1862777
theorem B434664305 : Blo 1100624 434664305 := bstep (se 2 (by rfl) ⟨162999114, by rfl⟩ : syracuseStep 434664305 = 325998229) B325998229
theorem B7074809 : Blo 1100624 7074809 := bstep (se 2 (by rfl) ⟨2653053, by rfl⟩ : syracuseStep 7074809 = 5306107) B5306107
theorem B10613753 : Blo 1100624 10613753 := bstep (se 2 (by rfl) ⟨3980157, by rfl⟩ : syracuseStep 10613753 = 7960315) B7960315
theorem B2356553 : Blo 1100624 2356553 := bstep (se 2 (by rfl) ⟨883707, by rfl⟩ : syracuseStep 2356553 = 1767415) B1767415
theorem B4191659 : Blo 1100624 4191659 := bstep (se 1 (by rfl) ⟨3143744, by rfl⟩ : syracuseStep 4191659 = 6287489) B6287489
theorem B1242607 : Blo 1100624 1242607 := bstep (se 1 (by rfl) ⟨931955, by rfl⟩ : syracuseStep 1242607 = 1863911) B1863911
theorem B3537199 : Blo 1100624 3537199 := bstep (se 1 (by rfl) ⟨2652899, by rfl⟩ : syracuseStep 3537199 = 5305799) B5305799
theorem B4717291 : Blo 1100624 4717291 := bstep (se 1 (by rfl) ⟨3537968, by rfl⟩ : syracuseStep 4717291 = 7075937) B7075937
theorem B6716321 : Blo 1100624 6716321 := bstep (se 2 (by rfl) ⟨2518620, by rfl⟩ : syracuseStep 6716321 = 5037241) B5037241
theorem B63536723 : Blo 1100624 63536723 := bstep (se 1 (by rfl) ⟨47652542, by rfl⟩ : syracuseStep 63536723 = 95305085) B95305085
theorem B10747961 : Blo 1100624 10747961 := bstep (se 2 (by rfl) ⟨4030485, by rfl⟩ : syracuseStep 10747961 = 8060971) B8060971
theorem B10586537 : Blo 1100624 10586537 := bstep (se 2 (by rfl) ⟨3969951, by rfl⟩ : syracuseStep 10586537 = 7939903) B7939903
theorem B2788121 : Blo 1100624 2788121 := bstep (se 2 (by rfl) ⟨1045545, by rfl⟩ : syracuseStep 2788121 = 2091091) B2091091
theorem B3968509 : Blo 1100624 3968509 := bstep (se 3 (by rfl) ⟨744095, by rfl⟩ : syracuseStep 3968509 = 1488191) B1488191
theorem B12717647 : Blo 1100624 12717647 := bstep (se 1 (by rfl) ⟨9538235, by rfl⟩ : syracuseStep 12717647 = 19076471) B19076471
theorem B7540427 : Blo 1100624 7540427 := bstep (se 1 (by rfl) ⟨5655320, by rfl⟩ : syracuseStep 7540427 = 11310641) B11310641
theorem B8360171 : Blo 1100624 8360171 := bstep (se 1 (by rfl) ⟨6270128, by rfl⟩ : syracuseStep 8360171 = 12540257) B12540257
theorem B2790359 : Blo 1100624 2790359 := bstep (se 1 (by rfl) ⟨2092769, by rfl⟩ : syracuseStep 2790359 = 4185539) B4185539
theorem B8361143 : Blo 1100624 8361143 := bstep (se 1 (by rfl) ⟨6270857, by rfl⟩ : syracuseStep 8361143 = 12541715) B12541715
theorem B2791199 : Blo 1100624 2791199 := bstep (se 1 (by rfl) ⟨2093399, by rfl⟩ : syracuseStep 2791199 = 4186799) B4186799
theorem B5576849 : Blo 1100624 5576849 := bstep (se 2 (by rfl) ⟨2091318, by rfl⟩ : syracuseStep 5576849 = 4182637) B4182637
theorem B2791867 : Blo 1100624 2791867 := bstep (se 1 (by rfl) ⟨2093900, by rfl⟩ : syracuseStep 2791867 = 4187801) B4187801
theorem B9181723 : Blo 1100624 9181723 := bstep (se 1 (by rfl) ⟨6886292, by rfl⟩ : syracuseStep 9181723 = 13772585) B13772585
theorem B2792171 : Blo 1100624 2792171 := bstep (se 1 (by rfl) ⟨2094128, by rfl⟩ : syracuseStep 2792171 = 4188257) B4188257
theorem B9805711 : Blo 1100624 9805711 := bstep (se 1 (by rfl) ⟨7354283, by rfl⟩ : syracuseStep 9805711 = 14708567) B14708567
theorem B7053257 : Blo 1100624 7053257 := bstep (se 2 (by rfl) ⟨2644971, by rfl⟩ : syracuseStep 7053257 = 5289943) B5289943
theorem B2793467 : Blo 1100624 2793467 := bstep (se 1 (by rfl) ⟨2095100, by rfl⟩ : syracuseStep 2793467 = 4190201) B4190201
theorem B1679543 : Blo 1100624 1679543 := bstep (se 1 (by rfl) ⟨1259657, by rfl⟩ : syracuseStep 1679543 = 2519315) B2519315
theorem B7053743 : Blo 1100624 7053743 := bstep (se 1 (by rfl) ⟨5290307, by rfl⟩ : syracuseStep 7053743 = 10580615) B10580615
theorem B289776203 : Blo 1100624 289776203 := bstep (se 1 (by rfl) ⟨217332152, by rfl⟩ : syracuseStep 289776203 = 434664305) B434664305
theorem B2794439 : Blo 1100624 2794439 := bstep (se 1 (by rfl) ⟨2095829, by rfl⟩ : syracuseStep 2794439 = 4191659) B4191659
theorem B5580089 : Blo 1100624 5580089 := bstep (se 2 (by rfl) ⟨2092533, by rfl⟩ : syracuseStep 5580089 = 4185067) B4185067
theorem B22390757 : Blo 1100624 22390757 := bstep (se 4 (by rfl) ⟨2099133, by rfl⟩ : syracuseStep 22390757 = 4198267) B4198267
theorem B6891641 : Blo 1100624 6891641 := bstep (se 2 (by rfl) ⟨2584365, by rfl⟩ : syracuseStep 6891641 = 5168731) B5168731
theorem B7941401 : Blo 1100624 7941401 := bstep (se 2 (by rfl) ⟨2978025, by rfl⟩ : syracuseStep 7941401 = 5956051) B5956051
theorem B5582519 : Blo 1100624 5582519 := bstep (se 1 (by rfl) ⟨4186889, by rfl⟩ : syracuseStep 5582519 = 8373779) B8373779
theorem B3584135 : Blo 1100624 3584135 := bstep (se 1 (by rfl) ⟨2688101, by rfl⟩ : syracuseStep 3584135 = 5376203) B5376203
theorem B1650971 : Blo 1100624 1650971 := bstep (se 1 (by rfl) ⟨1238228, by rfl⟩ : syracuseStep 1650971 = 2476457) B2476457
theorem B6697637 : Blo 1100624 6697637 := bstep (se 4 (by rfl) ⟨627903, by rfl⟩ : syracuseStep 6697637 = 1255807) B1255807
theorem B1651367 : Blo 1100624 1651367 := bstep (se 1 (by rfl) ⟨1238525, by rfl⟩ : syracuseStep 1651367 = 2477051) B2477051
theorem B1651487 : Blo 1100624 1651487 := bstep (se 1 (by rfl) ⟨1238615, by rfl⟩ : syracuseStep 1651487 = 2477231) B2477231
theorem B1651511 : Blo 1100624 1651511 := bstep (se 1 (by rfl) ⟨1238633, by rfl⟩ : syracuseStep 1651511 = 2477267) B2477267
theorem B3716009 : Blo 1100624 3716009 := bstep (se 2 (by rfl) ⟨1393503, by rfl⟩ : syracuseStep 3716009 = 2787007) B2787007
theorem B1651625 : Blo 1100624 1651625 := bstep (se 2 (by rfl) ⟨619359, by rfl⟩ : syracuseStep 1651625 = 1238719) B1238719
theorem B1651691 : Blo 1100624 1651691 := bstep (se 1 (by rfl) ⟨1238768, by rfl⟩ : syracuseStep 1651691 = 2477537) B2477537
theorem B5583977 : Blo 1100624 5583977 := bstep (se 2 (by rfl) ⟨2093991, by rfl⟩ : syracuseStep 5583977 = 4187983) B4187983
theorem B1651967 : Blo 1100624 1651967 := bstep (se 1 (by rfl) ⟨1238975, by rfl⟩ : syracuseStep 1651967 = 2477951) B2477951
theorem B1652009 : Blo 1100624 1652009 := bstep (se 2 (by rfl) ⟨619503, by rfl⟩ : syracuseStep 1652009 = 1239007) B1239007
theorem B5289499 : Blo 1100624 5289499 := bstep (se 1 (by rfl) ⟨3967124, by rfl⟩ : syracuseStep 5289499 = 7934249) B7934249
theorem B8926811 : Blo 1100624 8926811 := bstep (se 1 (by rfl) ⟨6695108, by rfl⟩ : syracuseStep 8926811 = 13390217) B13390217
theorem B1652603 : Blo 1100624 1652603 := bstep (se 1 (by rfl) ⟨1239452, by rfl⟩ : syracuseStep 1652603 = 2478905) B2478905
theorem B1652639 : Blo 1100624 1652639 := bstep (se 1 (by rfl) ⟨1239479, by rfl⟩ : syracuseStep 1652639 = 2478959) B2478959
theorem B1652843 : Blo 1100624 1652843 := bstep (se 1 (by rfl) ⟨1239632, by rfl⟩ : syracuseStep 1652843 = 2479265) B2479265
theorem B1652873 : Blo 1100624 1652873 := bstep (se 2 (by rfl) ⟨619827, by rfl⟩ : syracuseStep 1652873 = 1239655) B1239655
theorem B1653023 : Blo 1100624 1653023 := bstep (se 1 (by rfl) ⟨1239767, by rfl⟩ : syracuseStep 1653023 = 2479535) B2479535
theorem B25770299 : Blo 1100624 25770299 := bstep (se 1 (by rfl) ⟨19327724, by rfl⟩ : syracuseStep 25770299 = 38655449) B38655449
theorem B6273683 : Blo 1100624 6273683 := bstep (se 1 (by rfl) ⟨4705262, by rfl⟩ : syracuseStep 6273683 = 9410525) B9410525
theorem B1653695 : Blo 1100624 1653695 := bstep (se 1 (by rfl) ⟨1240271, by rfl⟩ : syracuseStep 1653695 = 2480543) B2480543
theorem B1653743 : Blo 1100624 1653743 := bstep (se 1 (by rfl) ⟨1240307, by rfl⟩ : syracuseStep 1653743 = 2480615) B2480615
theorem B10599569 : Blo 1100624 10599569 := bstep (se 2 (by rfl) ⟨3974838, by rfl⟩ : syracuseStep 10599569 = 7949677) B7949677
theorem B1653929 : Blo 1100624 1653929 := bstep (se 2 (by rfl) ⟨620223, by rfl⟩ : syracuseStep 1653929 = 1240447) B1240447
theorem B13417655 : Blo 1100624 13417655 := bstep (se 1 (by rfl) ⟨10063241, by rfl⟩ : syracuseStep 13417655 = 20126483) B20126483
theorem B22658383 : Blo 1100624 22658383 := bstep (se 1 (by rfl) ⟨16993787, by rfl⟩ : syracuseStep 22658383 = 33987575) B33987575
theorem B1654319 : Blo 1100624 1654319 := bstep (se 1 (by rfl) ⟨1240739, by rfl⟩ : syracuseStep 1654319 = 2481479) B2481479
theorem B1654343 : Blo 1100624 1654343 := bstep (se 1 (by rfl) ⟨1240757, by rfl⟩ : syracuseStep 1654343 = 2481515) B2481515
theorem B1654427 : Blo 1100624 1654427 := bstep (se 1 (by rfl) ⟨1240820, by rfl⟩ : syracuseStep 1654427 = 2481641) B2481641
theorem B1654523 : Blo 1100624 1654523 := bstep (se 1 (by rfl) ⟨1240892, by rfl⟩ : syracuseStep 1654523 = 2481785) B2481785
theorem B1654991 : Blo 1100624 1654991 := bstep (se 1 (by rfl) ⟨1241243, by rfl⟩ : syracuseStep 1654991 = 2482487) B2482487
theorem B130892591 : Blo 1100624 130892591 := bstep (se 1 (by rfl) ⟨98169443, by rfl⟩ : syracuseStep 130892591 = 196338887) B196338887
theorem B1655675 : Blo 1100624 1655675 := bstep (se 1 (by rfl) ⟨1241756, by rfl⟩ : syracuseStep 1655675 = 2483513) B2483513
theorem B1655801 : Blo 1100624 1655801 := bstep (se 2 (by rfl) ⟨620925, by rfl⟩ : syracuseStep 1655801 = 1241851) B1241851
theorem B6702113 : Blo 1100624 6702113 := bstep (se 2 (by rfl) ⟨2513292, by rfl⟩ : syracuseStep 6702113 = 5026585) B5026585
theorem B1655855 : Blo 1100624 1655855 := bstep (se 1 (by rfl) ⟨1241891, by rfl⟩ : syracuseStep 1655855 = 2483783) B2483783
theorem B1655975 : Blo 1100624 1655975 := bstep (se 1 (by rfl) ⟨1241981, by rfl⟩ : syracuseStep 1655975 = 2483963) B2483963
theorem B4474079 : Blo 1100624 4474079 := bstep (se 1 (by rfl) ⟨3355559, by rfl⟩ : syracuseStep 4474079 = 6711119) B6711119
theorem B43042051 : Blo 1100624 43042051 := bstep (se 1 (by rfl) ⟨32281538, by rfl⟩ : syracuseStep 43042051 = 64563077) B64563077
theorem B7062815 : Blo 1100624 7062815 := bstep (se 1 (by rfl) ⟨5297111, by rfl⟩ : syracuseStep 7062815 = 10594223) B10594223
theorem B1656167 : Blo 1100624 1656167 := bstep (se 1 (by rfl) ⟨1242125, by rfl⟩ : syracuseStep 1656167 = 2484251) B2484251
theorem B1787303 : Blo 1100624 1787303 := bstep (se 1 (by rfl) ⟨1340477, by rfl⟩ : syracuseStep 1787303 = 2680955) B2680955
theorem B10602029 : Blo 1100624 10602029 := bstep (se 3 (by rfl) ⟨1987880, by rfl⟩ : syracuseStep 10602029 = 3975761) B3975761
theorem B9422689 : Blo 1100624 9422689 := bstep (se 2 (by rfl) ⟨3533508, by rfl⟩ : syracuseStep 9422689 = 7067017) B7067017
theorem B1656809 : Blo 1100624 1656809 := bstep (se 2 (by rfl) ⟨621303, by rfl⟩ : syracuseStep 1656809 = 1242607) B1242607
theorem B13388267 : Blo 1100624 13388267 := bstep (se 1 (by rfl) ⟨10041200, by rfl⟩ : syracuseStep 13388267 = 20082401) B20082401
theorem B7064147 : Blo 1100624 7064147 := bstep (se 1 (by rfl) ⟨5298110, by rfl⟩ : syracuseStep 7064147 = 10596221) B10596221
theorem B14305895 : Blo 1100624 14305895 := bstep (se 1 (by rfl) ⟨10729421, by rfl⟩ : syracuseStep 14305895 = 21458843) B21458843
theorem B2476799 : Blo 1100624 2476799 := bstep (se 1 (by rfl) ⟨1857599, by rfl⟩ : syracuseStep 2476799 = 3715199) B3715199
theorem B14142599 : Blo 1100624 14142599 := bstep (se 1 (by rfl) ⟨10606949, by rfl⟩ : syracuseStep 14142599 = 21213899) B21213899
theorem B1100967 : Blo 1100624 1100967 := bstep (se 1 (by rfl) ⟨825725, by rfl⟩ : syracuseStep 1100967 = 1651451) B1651451
theorem B2477483 : Blo 1100624 2477483 := bstep (se 1 (by rfl) ⟨1858112, by rfl⟩ : syracuseStep 2477483 = 3716225) B3716225
theorem B1101263 : Blo 1100624 1101263 := bstep (se 1 (by rfl) ⟨825947, by rfl⟩ : syracuseStep 1101263 = 1651895) B1651895
theorem B5033447 : Blo 1100624 5033447 := bstep (se 1 (by rfl) ⟨3775085, by rfl⟩ : syracuseStep 5033447 = 7550171) B7550171
theorem B3722759 : Blo 1100624 3722759 := bstep (se 1 (by rfl) ⟨2792069, by rfl⟩ : syracuseStep 3722759 = 5584139) B5584139
theorem B1101423 : Blo 1100624 1101423 := bstep (se 1 (by rfl) ⟨826067, by rfl⟩ : syracuseStep 1101423 = 1652135) B1652135
theorem B1101543 : Blo 1100624 1101543 := bstep (se 1 (by rfl) ⟨826157, by rfl⟩ : syracuseStep 1101543 = 1652315) B1652315
theorem B51007265 : Blo 1100624 51007265 := bstep (se 2 (by rfl) ⟨19127724, by rfl⟩ : syracuseStep 51007265 = 38255449) B38255449
theorem B2478023 : Blo 1100624 2478023 := bstep (se 1 (by rfl) ⟨1858517, by rfl⟩ : syracuseStep 2478023 = 3717035) B3717035
theorem B1101851 : Blo 1100624 1101851 := bstep (se 1 (by rfl) ⟨826388, by rfl⟩ : syracuseStep 1101851 = 1652777) B1652777
theorem B1101871 : Blo 1100624 1101871 := bstep (se 1 (by rfl) ⟨826403, by rfl⟩ : syracuseStep 1101871 = 1652807) B1652807
theorem B2871359 : Blo 1100624 2871359 := bstep (se 1 (by rfl) ⟨2153519, by rfl⟩ : syracuseStep 2871359 = 4307039) B4307039
theorem B4477193 : Blo 1100624 4477193 := bstep (se 2 (by rfl) ⟨1678947, by rfl⟩ : syracuseStep 4477193 = 3357895) B3357895
theorem B2478383 : Blo 1100624 2478383 := bstep (se 1 (by rfl) ⟨1858787, by rfl⟩ : syracuseStep 2478383 = 3717575) B3717575
theorem B1102127 : Blo 1100624 1102127 := bstep (se 1 (by rfl) ⟨826595, by rfl⟩ : syracuseStep 1102127 = 1653191) B1653191
theorem B2871599 : Blo 1100624 2871599 := bstep (se 1 (by rfl) ⟨2153699, by rfl⟩ : syracuseStep 2871599 = 4307399) B4307399
theorem B2478527 : Blo 1100624 2478527 := bstep (se 1 (by rfl) ⟨1858895, by rfl⟩ : syracuseStep 2478527 = 3717791) B3717791
theorem B1102271 : Blo 1100624 1102271 := bstep (se 1 (by rfl) ⟨826703, by rfl⟩ : syracuseStep 1102271 = 1653407) B1653407
theorem B1102367 : Blo 1100624 1102367 := bstep (se 1 (by rfl) ⟨826775, by rfl⟩ : syracuseStep 1102367 = 1653551) B1653551
theorem B3723839 : Blo 1100624 3723839 := bstep (se 1 (by rfl) ⟨2792879, by rfl⟩ : syracuseStep 3723839 = 5585759) B5585759
theorem B4477547 : Blo 1100624 4477547 := bstep (se 1 (by rfl) ⟨3358160, by rfl⟩ : syracuseStep 4477547 = 6716321) B6716321
theorem B1102447 : Blo 1100624 1102447 := bstep (se 1 (by rfl) ⟨826835, by rfl⟩ : syracuseStep 1102447 = 1653671) B1653671
theorem B1102567 : Blo 1100624 1102567 := bstep (se 1 (by rfl) ⟨826925, by rfl⟩ : syracuseStep 1102567 = 1653851) B1653851
theorem B1102815 : Blo 1100624 1102815 := bstep (se 1 (by rfl) ⟨827111, by rfl⟩ : syracuseStep 1102815 = 1654223) B1654223
theorem B42357815 : Blo 1100624 42357815 := bstep (se 1 (by rfl) ⟨31768361, by rfl⟩ : syracuseStep 42357815 = 63536723) B63536723
theorem B2479175 : Blo 1100624 2479175 := bstep (se 1 (by rfl) ⟨1859381, by rfl⟩ : syracuseStep 2479175 = 3718763) B3718763
theorem B1103071 : Blo 1100624 1103071 := bstep (se 1 (by rfl) ⟨827303, by rfl⟩ : syracuseStep 1103071 = 1654607) B1654607
theorem B2479355 : Blo 1100624 2479355 := bstep (se 1 (by rfl) ⟨1859516, by rfl⟩ : syracuseStep 2479355 = 3719033) B3719033
theorem B1103151 : Blo 1100624 1103151 := bstep (se 1 (by rfl) ⟨827363, by rfl⟩ : syracuseStep 1103151 = 1654727) B1654727
theorem B8377667 : Blo 1100624 8377667 := bstep (se 1 (by rfl) ⟨6283250, by rfl⟩ : syracuseStep 8377667 = 12566501) B12566501
theorem B4838723 : Blo 1100624 4838723 := bstep (se 1 (by rfl) ⟨3629042, by rfl⟩ : syracuseStep 4838723 = 7258085) B7258085
theorem B6280699 : Blo 1100624 6280699 := bstep (se 1 (by rfl) ⟨4710524, by rfl⟩ : syracuseStep 6280699 = 9421049) B9421049
theorem B1103391 : Blo 1100624 1103391 := bstep (se 1 (by rfl) ⟨827543, by rfl⟩ : syracuseStep 1103391 = 1655087) B1655087
theorem B3135145 : Blo 1100624 3135145 := bstep (se 2 (by rfl) ⟨1175679, by rfl⟩ : syracuseStep 3135145 = 2351359) B2351359
theorem B1103551 : Blo 1100624 1103551 := bstep (se 1 (by rfl) ⟨827663, by rfl⟩ : syracuseStep 1103551 = 1655327) B1655327
theorem B5953283 : Blo 1100624 5953283 := bstep (se 1 (by rfl) ⟨4464962, by rfl⟩ : syracuseStep 5953283 = 8929925) B8929925
theorem B3135361 : Blo 1100624 3135361 := bstep (se 2 (by rfl) ⟨1175760, by rfl⟩ : syracuseStep 3135361 = 2351521) B2351521
theorem B24139781 : Blo 1100624 24139781 := bstep (se 4 (by rfl) ⟨2263104, by rfl⟩ : syracuseStep 24139781 = 4526209) B4526209
theorem B2480255 : Blo 1100624 2480255 := bstep (se 1 (by rfl) ⟨1860191, by rfl⟩ : syracuseStep 2480255 = 3720383) B3720383
theorem B1103999 : Blo 1100624 1103999 := bstep (se 1 (by rfl) ⟨827999, by rfl⟩ : syracuseStep 1103999 = 1655999) B1655999
theorem B1104095 : Blo 1100624 1104095 := bstep (se 1 (by rfl) ⟨828071, by rfl⟩ : syracuseStep 1104095 = 1656143) B1656143
theorem B2480363 : Blo 1100624 2480363 := bstep (se 1 (by rfl) ⟨1860272, by rfl⟩ : syracuseStep 2480363 = 3720545) B3720545
theorem B1104155 : Blo 1100624 1104155 := bstep (se 1 (by rfl) ⟨828116, by rfl⟩ : syracuseStep 1104155 = 1656233) B1656233
theorem B1104255 : Blo 1100624 1104255 := bstep (se 1 (by rfl) ⟨828191, by rfl⟩ : syracuseStep 1104255 = 1656383) B1656383
theorem B1104283 : Blo 1100624 1104283 := bstep (se 1 (by rfl) ⟨828212, by rfl⟩ : syracuseStep 1104283 = 1656425) B1656425
theorem B3725783 : Blo 1100624 3725783 := bstep (se 1 (by rfl) ⟨2794337, by rfl⟩ : syracuseStep 3725783 = 5588675) B5588675
theorem B1858207 : Blo 1100624 1858207 := bstep (se 1 (by rfl) ⟨1393655, by rfl⟩ : syracuseStep 1858207 = 2787311) B2787311
theorem B2480831 : Blo 1100624 2480831 := bstep (se 1 (by rfl) ⟨1860623, by rfl⟩ : syracuseStep 2480831 = 3721247) B3721247
theorem B1104575 : Blo 1100624 1104575 := bstep (se 1 (by rfl) ⟨828431, by rfl⟩ : syracuseStep 1104575 = 1656863) B1656863
theorem B18865061 : Blo 1100624 18865061 := bstep (se 4 (by rfl) ⟨1768599, by rfl⟩ : syracuseStep 18865061 = 3537199) B3537199
theorem B3136603 : Blo 1100624 3136603 := bstep (se 1 (by rfl) ⟨2352452, by rfl⟩ : syracuseStep 3136603 = 4704905) B4704905
theorem B1858943 : Blo 1100624 1858943 := bstep (se 1 (by rfl) ⟨1394207, by rfl⟩ : syracuseStep 1858943 = 2788415) B2788415
theorem B1990367 : Blo 1100624 1990367 := bstep (se 1 (by rfl) ⟨1492775, by rfl⟩ : syracuseStep 1990367 = 2985551) B2985551
theorem B31842173 : Blo 1100624 31842173 := bstep (se 3 (by rfl) ⟨5970407, by rfl⟩ : syracuseStep 31842173 = 11940815) B11940815
theorem B4186025 : Blo 1100624 4186025 := bstep (se 2 (by rfl) ⟨1569759, by rfl⟩ : syracuseStep 4186025 = 3139519) B3139519
theorem B4186343 : Blo 1100624 4186343 := bstep (se 1 (by rfl) ⟨3139757, by rfl⟩ : syracuseStep 4186343 = 6279515) B6279515
theorem B94363937 : Blo 1100624 94363937 := bstep (se 2 (by rfl) ⟨35386476, by rfl⟩ : syracuseStep 94363937 = 70772953) B70772953
theorem B1859881 : Blo 1100624 1859881 := bstep (se 2 (by rfl) ⟨697455, by rfl⟩ : syracuseStep 1859881 = 1394911) B1394911
theorem B6283615 : Blo 1100624 6283615 := bstep (se 1 (by rfl) ⟨4712711, by rfl⟩ : syracuseStep 6283615 = 9425423) B9425423
theorem B1860151 : Blo 1100624 1860151 := bstep (se 1 (by rfl) ⟨1395113, by rfl⟩ : syracuseStep 1860151 = 2790227) B2790227
theorem B2089633 : Blo 1100624 2089633 := bstep (se 2 (by rfl) ⟨783612, by rfl⟩ : syracuseStep 2089633 = 1567225) B1567225
theorem B3138209 : Blo 1100624 3138209 := bstep (se 2 (by rfl) ⟨1176828, by rfl⟩ : syracuseStep 3138209 = 2353657) B2353657
theorem B2483027 : Blo 1100624 2483027 := bstep (se 1 (by rfl) ⟨1862270, by rfl⟩ : syracuseStep 2483027 = 3724541) B3724541
theorem B6284141 : Blo 1100624 6284141 := bstep (se 3 (by rfl) ⟨1178276, by rfl⟩ : syracuseStep 6284141 = 2356553) B2356553
theorem B40821677 : Blo 1100624 40821677 := bstep (se 3 (by rfl) ⟨7654064, by rfl⟩ : syracuseStep 40821677 = 15308129) B15308129
theorem B8381555 : Blo 1100624 8381555 := bstep (se 1 (by rfl) ⟨6286166, by rfl⟩ : syracuseStep 8381555 = 12572333) B12572333
theorem B2483567 : Blo 1100624 2483567 := bstep (se 1 (by rfl) ⟨1862675, by rfl⟩ : syracuseStep 2483567 = 3725351) B3725351
theorem B2483639 : Blo 1100624 2483639 := bstep (se 1 (by rfl) ⟨1862729, by rfl⟩ : syracuseStep 2483639 = 3725459) B3725459
theorem B1238503 : Blo 1100624 1238503 := bstep (se 1 (by rfl) ⟨928877, by rfl⟩ : syracuseStep 1238503 = 1857755) B1857755
theorem B2483819 : Blo 1100624 2483819 := bstep (se 1 (by rfl) ⟨1862864, by rfl⟩ : syracuseStep 2483819 = 3725729) B3725729
theorem B1238683 : Blo 1100624 1238683 := bstep (se 1 (by rfl) ⟨929012, by rfl⟩ : syracuseStep 1238683 = 1858025) B1858025
theorem B2484089 : Blo 1100624 2484089 := bstep (se 2 (by rfl) ⟨931533, by rfl⟩ : syracuseStep 2484089 = 1863067) B1863067
theorem B2484179 : Blo 1100624 2484179 := bstep (se 1 (by rfl) ⟨1863134, by rfl⟩ : syracuseStep 2484179 = 3726269) B3726269
theorem B1861663 : Blo 1100624 1861663 := bstep (se 1 (by rfl) ⟨1396247, by rfl⟩ : syracuseStep 1861663 = 2792495) B2792495
theorem B22931585 : Blo 1100624 22931585 := bstep (se 2 (by rfl) ⟨8599344, by rfl⟩ : syracuseStep 22931585 = 17198689) B17198689
theorem B1567145 : Blo 1100624 1567145 := bstep (se 2 (by rfl) ⟨587679, by rfl⟩ : syracuseStep 1567145 = 1175359) B1175359
theorem B2091433 : Blo 1100624 2091433 := bstep (se 2 (by rfl) ⟨784287, by rfl⟩ : syracuseStep 2091433 = 1568575) B1568575
theorem B3140009 : Blo 1100624 3140009 := bstep (se 2 (by rfl) ⟨1177503, by rfl⟩ : syracuseStep 3140009 = 2355007) B2355007
theorem B2485097 : Blo 1100624 2485097 := bstep (se 2 (by rfl) ⟨931911, by rfl⟩ : syracuseStep 2485097 = 1863823) B1863823
theorem B2485115 : Blo 1100624 2485115 := bstep (se 1 (by rfl) ⟨1863836, by rfl⟩ : syracuseStep 2485115 = 3727673) B3727673
theorem B2092169 : Blo 1100624 2092169 := bstep (se 2 (by rfl) ⟨784563, by rfl⟩ : syracuseStep 2092169 = 1569127) B1569127
theorem B2485385 : Blo 1100624 2485385 := bstep (se 2 (by rfl) ⟨932019, by rfl⟩ : syracuseStep 2485385 = 1864039) B1864039
theorem B1862831 : Blo 1100624 1862831 := bstep (se 1 (by rfl) ⟨1397123, by rfl⟩ : syracuseStep 1862831 = 2794247) B2794247
theorem B2092223 : Blo 1100624 2092223 := bstep (se 1 (by rfl) ⟨1569167, by rfl⟩ : syracuseStep 2092223 = 3138335) B3138335
theorem B1764679 : Blo 1100624 1764679 := bstep (se 1 (by rfl) ⟨1323509, by rfl⟩ : syracuseStep 1764679 = 2647019) B2647019
theorem B2354503 : Blo 1100624 2354503 := bstep (se 1 (by rfl) ⟨1765877, by rfl⟩ : syracuseStep 2354503 = 3531755) B3531755
theorem B3534151 : Blo 1100624 3534151 := bstep (se 1 (by rfl) ⟨2650613, by rfl⟩ : syracuseStep 3534151 = 5301227) B5301227
theorem B16969661 : Blo 1100624 16969661 := bstep (se 3 (by rfl) ⟨3181811, by rfl⟩ : syracuseStep 16969661 = 6363623) B6363623
theorem B2093111 : Blo 1100624 2093111 := bstep (se 1 (by rfl) ⟨1569833, by rfl⟩ : syracuseStep 2093111 = 3139667) B3139667
theorem B60289235 : Blo 1100624 60289235 := bstep (se 1 (by rfl) ⟨45216926, by rfl⟩ : syracuseStep 60289235 = 90433853) B90433853
theorem B2650439 : Blo 1100624 2650439 := bstep (se 1 (by rfl) ⟨1987829, by rfl⟩ : syracuseStep 2650439 = 3975659) B3975659
theorem B3535919 : Blo 1100624 3535919 := bstep (se 1 (by rfl) ⟨2651939, by rfl⟩ : syracuseStep 3535919 = 5303879) B5303879
theorem B4715567 : Blo 1100624 4715567 := bstep (se 1 (by rfl) ⟨3536675, by rfl⟩ : syracuseStep 4715567 = 7073351) B7073351
theorem B7074863 : Blo 1100624 7074863 := bstep (se 1 (by rfl) ⟨5306147, by rfl⟩ : syracuseStep 7074863 = 10612295) B10612295
theorem B1569947 : Blo 1100624 1569947 := bstep (se 1 (by rfl) ⟨1177460, by rfl⟩ : syracuseStep 1569947 = 2354921) B2354921
theorem B2356391 : Blo 1100624 2356391 := bstep (se 1 (by rfl) ⟨1767293, by rfl⟩ : syracuseStep 2356391 = 3534587) B3534587
theorem B18118201 : Blo 1100624 18118201 := bstep (se 2 (by rfl) ⟨6794325, by rfl⟩ : syracuseStep 18118201 = 13588651) B13588651
theorem B4716539 : Blo 1100624 4716539 := bstep (se 1 (by rfl) ⟨3537404, by rfl⟩ : syracuseStep 4716539 = 7074809) B7074809
theorem B7075835 : Blo 1100624 7075835 := bstep (se 1 (by rfl) ⟨5306876, by rfl⟩ : syracuseStep 7075835 = 10613753) B10613753
theorem B6289721 : Blo 1100624 6289721 := bstep (se 2 (by rfl) ⟨2358645, by rfl⟩ : syracuseStep 6289721 = 4717291) B4717291
theorem B2981303 : Blo 1100624 2981303 := bstep (se 1 (by rfl) ⟨2235977, by rfl⟩ : syracuseStep 2981303 = 4471955) B4471955
theorem B2982719 : Blo 1100624 2982719 := bstep (se 1 (by rfl) ⟨2237039, by rfl⟩ : syracuseStep 2982719 = 4474079) B4474079
theorem B2786177 : Blo 1100624 2786177 := bstep (se 2 (by rfl) ⟨1044816, by rfl⟩ : syracuseStep 2786177 = 2089633) B2089633
theorem B9537263 : Blo 1100624 9537263 := bstep (se 1 (by rfl) ⟨7152947, by rfl⟩ : syracuseStep 9537263 = 14305895) B14305895
theorem B349046909 : Blo 1100624 349046909 := bstep (se 3 (by rfl) ⟨65446295, by rfl⟩ : syracuseStep 349046909 = 130892591) B130892591
theorem B5573447 : Blo 1100624 5573447 := bstep (se 1 (by rfl) ⟨4180085, by rfl⟩ : syracuseStep 5573447 = 8360171) B8360171
theorem B2984795 : Blo 1100624 2984795 := bstep (se 1 (by rfl) ⟨2238596, by rfl⟩ : syracuseStep 2984795 = 4477193) B4477193
theorem B2985031 : Blo 1100624 2985031 := bstep (se 1 (by rfl) ⟨2238773, by rfl⟩ : syracuseStep 2985031 = 4477547) B4477547
theorem B2788577 : Blo 1100624 2788577 := bstep (se 2 (by rfl) ⟨1045716, by rfl⟩ : syracuseStep 2788577 = 2091433) B2091433
theorem B5574095 : Blo 1100624 5574095 := bstep (se 1 (by rfl) ⟨4180571, by rfl⟩ : syracuseStep 5574095 = 8361143) B8361143
theorem B3968855 : Blo 1100624 3968855 := bstep (se 1 (by rfl) ⟨2976641, by rfl⟩ : syracuseStep 3968855 = 5953283) B5953283
theorem B16093187 : Blo 1100624 16093187 := bstep (se 1 (by rfl) ⟨12069890, by rfl⟩ : syracuseStep 16093187 = 24139781) B24139781
theorem B2790683 : Blo 1100624 2790683 := bstep (se 1 (by rfl) ⟨2093012, by rfl⟩ : syracuseStep 2790683 = 4186025) B4186025
theorem B1119695 : Blo 1100624 1119695 := bstep (se 1 (by rfl) ⟨839771, by rfl⟩ : syracuseStep 1119695 = 1679543) B1679543
theorem B2790895 : Blo 1100624 2790895 := bstep (se 1 (by rfl) ⟨2093171, by rfl⟩ : syracuseStep 2790895 = 4186343) B4186343
theorem B68720797 : Blo 1100624 68720797 := bstep (se 3 (by rfl) ⟨12885149, by rfl⟩ : syracuseStep 68720797 = 25770299) B25770299
theorem B4594427 : Blo 1100624 4594427 := bstep (se 1 (by rfl) ⟨3445820, by rfl⟩ : syracuseStep 4594427 = 6891641) B6891641
theorem B7052665 : Blo 1100624 7052665 := bstep (se 2 (by rfl) ⟨2644749, by rfl⟩ : syracuseStep 7052665 = 5289499) B5289499
theorem B24157601 : Blo 1100624 24157601 := bstep (se 2 (by rfl) ⟨9059100, by rfl⟩ : syracuseStep 24157601 = 18118201) B18118201
theorem B11313107 : Blo 1100624 11313107 := bstep (se 1 (by rfl) ⟨8484830, by rfl⟩ : syracuseStep 11313107 = 16969661) B16969661
theorem B5579117 : Blo 1100624 5579117 := bstep (se 3 (by rfl) ⟨1046084, by rfl⟩ : syracuseStep 5579117 = 2092169) B2092169
theorem B4465091 : Blo 1100624 4465091 := bstep (se 1 (by rfl) ⟨3348818, by rfl⟩ : syracuseStep 4465091 = 6697637) B6697637
theorem B7057691 : Blo 1100624 7057691 := bstep (se 1 (by rfl) ⟨5293268, by rfl⟩ : syracuseStep 7057691 = 10586537) B10586537
theorem B57389401 : Blo 1100624 57389401 := bstep (se 2 (by rfl) ⟨21521025, by rfl⟩ : syracuseStep 57389401 = 43042051) B43042051
theorem B1651199 : Blo 1100624 1651199 := bstep (se 1 (by rfl) ⟨1238399, by rfl⟩ : syracuseStep 1651199 = 2476799) B2476799
theorem B1651337 : Blo 1100624 1651337 := bstep (se 2 (by rfl) ⟨619251, by rfl⟩ : syracuseStep 1651337 = 1238503) B1238503
theorem B1651577 : Blo 1100624 1651577 := bstep (se 2 (by rfl) ⟨619341, by rfl⟩ : syracuseStep 1651577 = 1238683) B1238683
theorem B1651655 : Blo 1100624 1651655 := bstep (se 1 (by rfl) ⟨1238741, by rfl⟩ : syracuseStep 1651655 = 2477483) B2477483
theorem B3355631 : Blo 1100624 3355631 := bstep (se 1 (by rfl) ⟨2516723, by rfl⟩ : syracuseStep 3355631 = 5033447) B5033447
theorem B12563585 : Blo 1100624 12563585 := bstep (se 2 (by rfl) ⟨4711344, by rfl⟩ : syracuseStep 12563585 = 9422689) B9422689
theorem B5026951 : Blo 1100624 5026951 := bstep (se 1 (by rfl) ⟨3770213, by rfl⟩ : syracuseStep 5026951 = 7540427) B7540427
theorem B1652015 : Blo 1100624 1652015 := bstep (se 1 (by rfl) ⟨1239011, by rfl⟩ : syracuseStep 1652015 = 2478023) B2478023
theorem B1914239 : Blo 1100624 1914239 := bstep (se 1 (by rfl) ⟨1435679, by rfl⟩ : syracuseStep 1914239 = 2871359) B2871359
theorem B17872301 : Blo 1100624 17872301 := bstep (se 3 (by rfl) ⟨3351056, by rfl⟩ : syracuseStep 17872301 = 6702113) B6702113
theorem B1652255 : Blo 1100624 1652255 := bstep (se 1 (by rfl) ⟨1239191, by rfl⟩ : syracuseStep 1652255 = 2478383) B2478383
theorem B1652351 : Blo 1100624 1652351 := bstep (se 1 (by rfl) ⟨1239263, by rfl⟩ : syracuseStep 1652351 = 2478527) B2478527
theorem B1652783 : Blo 1100624 1652783 := bstep (se 1 (by rfl) ⟨1239587, by rfl⟩ : syracuseStep 1652783 = 2479175) B2479175
theorem B1652903 : Blo 1100624 1652903 := bstep (se 1 (by rfl) ⟨1239677, by rfl⟩ : syracuseStep 1652903 = 2479355) B2479355
theorem B3225815 : Blo 1100624 3225815 := bstep (se 1 (by rfl) ⟨2419361, by rfl⟩ : syracuseStep 3225815 = 4838723) B4838723
theorem B5585111 : Blo 1100624 5585111 := bstep (se 1 (by rfl) ⟨4188833, by rfl⟩ : syracuseStep 5585111 = 8377667) B8377667
theorem B4766141 : Blo 1100624 4766141 := bstep (se 3 (by rfl) ⟨893651, by rfl⟩ : syracuseStep 4766141 = 1787303) B1787303
theorem B1653503 : Blo 1100624 1653503 := bstep (se 1 (by rfl) ⟨1240127, by rfl⟩ : syracuseStep 1653503 = 2480255) B2480255
theorem B3717899 : Blo 1100624 3717899 := bstep (se 1 (by rfl) ⟨2788424, by rfl⟩ : syracuseStep 3717899 = 5576849) B5576849
theorem B1653575 : Blo 1100624 1653575 := bstep (se 1 (by rfl) ⟨1240181, by rfl⟩ : syracuseStep 1653575 = 2480363) B2480363
theorem B1653887 : Blo 1100624 1653887 := bstep (se 1 (by rfl) ⟨1240415, by rfl⟩ : syracuseStep 1653887 = 2480831) B2480831
theorem B5291345 : Blo 1100624 5291345 := bstep (se 2 (by rfl) ⟨1984254, by rfl⟩ : syracuseStep 5291345 = 3968509) B3968509
theorem B1326911 : Blo 1100624 1326911 := bstep (se 1 (by rfl) ⟨995183, by rfl⟩ : syracuseStep 1326911 = 1990367) B1990367
theorem B4702171 : Blo 1100624 4702171 := bstep (se 1 (by rfl) ⟨3526628, by rfl⟩ : syracuseStep 4702171 = 7053257) B7053257
theorem B4702495 : Blo 1100624 4702495 := bstep (se 1 (by rfl) ⟨3526871, by rfl⟩ : syracuseStep 4702495 = 7053743) B7053743
theorem B193184135 : Blo 1100624 193184135 := bstep (se 1 (by rfl) ⟨144888101, by rfl⟩ : syracuseStep 193184135 = 289776203) B289776203
theorem B1655351 : Blo 1100624 1655351 := bstep (se 1 (by rfl) ⟨1241513, by rfl⟩ : syracuseStep 1655351 = 2483027) B2483027
theorem B27214451 : Blo 1100624 27214451 := bstep (se 1 (by rfl) ⟨20410838, by rfl⟩ : syracuseStep 27214451 = 40821677) B40821677
theorem B5587703 : Blo 1100624 5587703 := bstep (se 1 (by rfl) ⟨4190777, by rfl⟩ : syracuseStep 5587703 = 8381555) B8381555
theorem B3720059 : Blo 1100624 3720059 := bstep (se 1 (by rfl) ⟨2790044, by rfl⟩ : syracuseStep 3720059 = 5580089) B5580089
theorem B1655711 : Blo 1100624 1655711 := bstep (se 1 (by rfl) ⟨1241783, by rfl⟩ : syracuseStep 1655711 = 2483567) B2483567
theorem B1655759 : Blo 1100624 1655759 := bstep (se 1 (by rfl) ⟨1241819, by rfl⟩ : syracuseStep 1655759 = 2483639) B2483639
theorem B1655879 : Blo 1100624 1655879 := bstep (se 1 (by rfl) ⟨1241909, by rfl⟩ : syracuseStep 1655879 = 2483819) B2483819
theorem B4179053 : Blo 1100624 4179053 := bstep (se 3 (by rfl) ⟨783572, by rfl⟩ : syracuseStep 4179053 = 1567145) B1567145
theorem B1656059 : Blo 1100624 1656059 := bstep (se 1 (by rfl) ⟨1242044, by rfl⟩ : syracuseStep 1656059 = 2484089) B2484089
theorem B35702045 : Blo 1100624 35702045 := bstep (se 3 (by rfl) ⟨6694133, by rfl⟩ : syracuseStep 35702045 = 13388267) B13388267
theorem B1656119 : Blo 1100624 1656119 := bstep (se 1 (by rfl) ⟨1242089, by rfl⟩ : syracuseStep 1656119 = 2484179) B2484179
theorem B14927171 : Blo 1100624 14927171 := bstep (se 1 (by rfl) ⟨11195378, by rfl⟩ : syracuseStep 14927171 = 22390757) B22390757
theorem B15287723 : Blo 1100624 15287723 := bstep (se 1 (by rfl) ⟨11465792, by rfl⟩ : syracuseStep 15287723 = 22931585) B22931585
theorem B1656731 : Blo 1100624 1656731 := bstep (se 1 (by rfl) ⟨1242548, by rfl⟩ : syracuseStep 1656731 = 2485097) B2485097
theorem B1656743 : Blo 1100624 1656743 := bstep (se 1 (by rfl) ⟨1242557, by rfl⟩ : syracuseStep 1656743 = 2485115) B2485115
theorem B8374265 : Blo 1100624 8374265 := bstep (se 2 (by rfl) ⟨3140349, by rfl⟩ : syracuseStep 8374265 = 6280699) B6280699
theorem B1656923 : Blo 1100624 1656923 := bstep (se 1 (by rfl) ⟨1242692, by rfl⟩ : syracuseStep 1656923 = 2485385) B2485385
theorem B1394815 : Blo 1100624 1394815 := bstep (se 1 (by rfl) ⟨1046111, by rfl⟩ : syracuseStep 1394815 = 2092223) B2092223
theorem B5294267 : Blo 1100624 5294267 := bstep (se 1 (by rfl) ⟨3970700, by rfl⟩ : syracuseStep 5294267 = 7941401) B7941401
theorem B4180193 : Blo 1100624 4180193 := bstep (se 2 (by rfl) ⟨1567572, by rfl⟩ : syracuseStep 4180193 = 3135145) B3135145
theorem B3721679 : Blo 1100624 3721679 := bstep (se 1 (by rfl) ⟨2791259, by rfl⟩ : syracuseStep 3721679 = 5582519) B5582519
theorem B4180481 : Blo 1100624 4180481 := bstep (se 2 (by rfl) ⟨1567680, by rfl⟩ : syracuseStep 4180481 = 3135361) B3135361
theorem B1395407 : Blo 1100624 1395407 := bstep (se 1 (by rfl) ⟨1046555, by rfl⟩ : syracuseStep 1395407 = 2093111) B2093111
theorem B40192823 : Blo 1100624 40192823 := bstep (se 1 (by rfl) ⟨30144617, by rfl⟩ : syracuseStep 40192823 = 60289235) B60289235
theorem B1100647 : Blo 1100624 1100647 := bstep (se 1 (by rfl) ⟨825485, by rfl⟩ : syracuseStep 1100647 = 1650971) B1650971
theorem B1100911 : Blo 1100624 1100911 := bstep (se 1 (by rfl) ⟨825683, by rfl⟩ : syracuseStep 1100911 = 1651367) B1651367
theorem B1100991 : Blo 1100624 1100991 := bstep (se 1 (by rfl) ⟨825743, by rfl⟩ : syracuseStep 1100991 = 1651487) B1651487
theorem B1101007 : Blo 1100624 1101007 := bstep (se 1 (by rfl) ⟨825755, by rfl⟩ : syracuseStep 1101007 = 1651511) B1651511
theorem B3722489 : Blo 1100624 3722489 := bstep (se 2 (by rfl) ⟨1395933, by rfl⟩ : syracuseStep 3722489 = 2791867) B2791867
theorem B2477339 : Blo 1100624 2477339 := bstep (se 1 (by rfl) ⟨1858004, by rfl⟩ : syracuseStep 2477339 = 3716009) B3716009
theorem B1101083 : Blo 1100624 1101083 := bstep (se 1 (by rfl) ⟨825812, by rfl⟩ : syracuseStep 1101083 = 1651625) B1651625
theorem B1101127 : Blo 1100624 1101127 := bstep (se 1 (by rfl) ⟨825845, by rfl⟩ : syracuseStep 1101127 = 1651691) B1651691
theorem B12242297 : Blo 1100624 12242297 := bstep (se 2 (by rfl) ⟨4590861, by rfl⟩ : syracuseStep 12242297 = 9181723) B9181723
theorem B3722651 : Blo 1100624 3722651 := bstep (se 1 (by rfl) ⟨2791988, by rfl⟩ : syracuseStep 3722651 = 5583977) B5583977
theorem B1101311 : Blo 1100624 1101311 := bstep (se 1 (by rfl) ⟨825983, by rfl⟩ : syracuseStep 1101311 = 1651967) B1651967
theorem B1101339 : Blo 1100624 1101339 := bstep (se 1 (by rfl) ⟨826004, by rfl⟩ : syracuseStep 1101339 = 1652009) B1652009
theorem B2477609 : Blo 1100624 2477609 := bstep (se 2 (by rfl) ⟨929103, by rfl⟩ : syracuseStep 2477609 = 1858207) B1858207
theorem B5951207 : Blo 1100624 5951207 := bstep (se 1 (by rfl) ⟨4463405, by rfl⟩ : syracuseStep 5951207 = 8926811) B8926811
theorem B1101735 : Blo 1100624 1101735 := bstep (se 1 (by rfl) ⟨826301, by rfl⟩ : syracuseStep 1101735 = 1652603) B1652603
theorem B1101759 : Blo 1100624 1101759 := bstep (se 1 (by rfl) ⟨826319, by rfl⟩ : syracuseStep 1101759 = 1652639) B1652639
theorem B1101895 : Blo 1100624 1101895 := bstep (se 1 (by rfl) ⟨826421, by rfl⟩ : syracuseStep 1101895 = 1652843) B1652843
theorem B1101915 : Blo 1100624 1101915 := bstep (se 1 (by rfl) ⟨826436, by rfl⟩ : syracuseStep 1101915 = 1652873) B1652873
theorem B4182137 : Blo 1100624 4182137 := bstep (se 2 (by rfl) ⟨1568301, by rfl⟩ : syracuseStep 4182137 = 3136603) B3136603
theorem B1102015 : Blo 1100624 1102015 := bstep (se 1 (by rfl) ⟨826511, by rfl⟩ : syracuseStep 1102015 = 1653023) B1653023
theorem B4182455 : Blo 1100624 4182455 := bstep (se 1 (by rfl) ⟨3136841, by rfl⟩ : syracuseStep 4182455 = 6273683) B6273683
theorem B1102463 : Blo 1100624 1102463 := bstep (se 1 (by rfl) ⟨826847, by rfl⟩ : syracuseStep 1102463 = 1653695) B1653695
theorem B1102495 : Blo 1100624 1102495 := bstep (se 1 (by rfl) ⟨826871, by rfl⟩ : syracuseStep 1102495 = 1653743) B1653743
theorem B7066379 : Blo 1100624 7066379 := bstep (se 1 (by rfl) ⟨5299784, by rfl⟩ : syracuseStep 7066379 = 10599569) B10599569
theorem B1102619 : Blo 1100624 1102619 := bstep (se 1 (by rfl) ⟨826964, by rfl⟩ : syracuseStep 1102619 = 1653929) B1653929
theorem B1987535 : Blo 1100624 1987535 := bstep (se 1 (by rfl) ⟨1490651, by rfl⟩ : syracuseStep 1987535 = 2981303) B2981303
theorem B1102879 : Blo 1100624 1102879 := bstep (se 1 (by rfl) ⟨827159, by rfl⟩ : syracuseStep 1102879 = 1654319) B1654319
theorem B1102895 : Blo 1100624 1102895 := bstep (se 1 (by rfl) ⟨827171, by rfl⟩ : syracuseStep 1102895 = 1654343) B1654343
theorem B1102951 : Blo 1100624 1102951 := bstep (se 1 (by rfl) ⟨827213, by rfl⟩ : syracuseStep 1102951 = 1654427) B1654427
theorem B1103015 : Blo 1100624 1103015 := bstep (se 1 (by rfl) ⟨827261, by rfl⟩ : syracuseStep 1103015 = 1654523) B1654523
theorem B7165307 : Blo 1100624 7165307 := bstep (se 1 (by rfl) ⟨5373980, by rfl⟩ : syracuseStep 7165307 = 10747961) B10747961
theorem B1103327 : Blo 1100624 1103327 := bstep (se 1 (by rfl) ⟨827495, by rfl⟩ : syracuseStep 1103327 = 1654991) B1654991
theorem B9557693 : Blo 1100624 9557693 := bstep (se 3 (by rfl) ⟨1792067, by rfl⟩ : syracuseStep 9557693 = 3584135) B3584135
theorem B2479841 : Blo 1100624 2479841 := bstep (se 2 (by rfl) ⟨929940, by rfl⟩ : syracuseStep 2479841 = 1859881) B1859881
theorem B8378153 : Blo 1100624 8378153 := bstep (se 2 (by rfl) ⟨3141807, by rfl⟩ : syracuseStep 8378153 = 6283615) B6283615
theorem B1103783 : Blo 1100624 1103783 := bstep (se 1 (by rfl) ⟨827837, by rfl⟩ : syracuseStep 1103783 = 1655675) B1655675
theorem B1103867 : Blo 1100624 1103867 := bstep (se 1 (by rfl) ⟨827900, by rfl⟩ : syracuseStep 1103867 = 1655801) B1655801
theorem B1103903 : Blo 1100624 1103903 := bstep (se 1 (by rfl) ⟨827927, by rfl⟩ : syracuseStep 1103903 = 1655855) B1655855
theorem B2480201 : Blo 1100624 2480201 := bstep (se 2 (by rfl) ⟨930075, by rfl⟩ : syracuseStep 2480201 = 1860151) B1860151
theorem B1103983 : Blo 1100624 1103983 := bstep (se 1 (by rfl) ⟨827987, by rfl⟩ : syracuseStep 1103983 = 1655975) B1655975
theorem B7657597 : Blo 1100624 7657597 := bstep (se 3 (by rfl) ⟨1435799, by rfl⟩ : syracuseStep 7657597 = 2871599) B2871599
theorem B7067837 : Blo 1100624 7067837 := bstep (se 3 (by rfl) ⟨1325219, by rfl⟩ : syracuseStep 7067837 = 2650439) B2650439
theorem B4708543 : Blo 1100624 4708543 := bstep (se 1 (by rfl) ⟨3531407, by rfl⟩ : syracuseStep 4708543 = 7062815) B7062815
theorem B1104111 : Blo 1100624 1104111 := bstep (se 1 (by rfl) ⟨828083, by rfl⟩ : syracuseStep 1104111 = 1656167) B1656167
theorem B7068019 : Blo 1100624 7068019 := bstep (se 1 (by rfl) ⟨5301014, by rfl⟩ : syracuseStep 7068019 = 10602029) B10602029
theorem B1104539 : Blo 1100624 1104539 := bstep (se 1 (by rfl) ⟨828404, by rfl⟩ : syracuseStep 1104539 = 1656809) B1656809
theorem B4709431 : Blo 1100624 4709431 := bstep (se 1 (by rfl) ⟨3532073, by rfl⟩ : syracuseStep 4709431 = 7064147) B7064147
theorem B1858747 : Blo 1100624 1858747 := bstep (se 1 (by rfl) ⟨1394060, by rfl⟩ : syracuseStep 1858747 = 2788121) B2788121
theorem B9428399 : Blo 1100624 9428399 := bstep (se 1 (by rfl) ⟨7071299, by rfl⟩ : syracuseStep 9428399 = 14142599) B14142599
theorem B2481839 : Blo 1100624 2481839 := bstep (se 1 (by rfl) ⟨1861379, by rfl⟩ : syracuseStep 2481839 = 3722759) B3722759
theorem B8478431 : Blo 1100624 8478431 := bstep (se 1 (by rfl) ⟨6358823, by rfl⟩ : syracuseStep 8478431 = 12717647) B12717647
theorem B34004843 : Blo 1100624 34004843 := bstep (se 1 (by rfl) ⟨25503632, by rfl⟩ : syracuseStep 34004843 = 51007265) B51007265
theorem B2482217 : Blo 1100624 2482217 := bstep (se 2 (by rfl) ⟨930831, by rfl⟩ : syracuseStep 2482217 = 1861663) B1861663
theorem B2482559 : Blo 1100624 2482559 := bstep (se 1 (by rfl) ⟨1861919, by rfl⟩ : syracuseStep 2482559 = 3723839) B3723839
theorem B4186525 : Blo 1100624 4186525 := bstep (se 3 (by rfl) ⟨784973, by rfl⟩ : syracuseStep 4186525 = 1569947) B1569947
theorem B1860239 : Blo 1100624 1860239 := bstep (se 1 (by rfl) ⟨1395179, by rfl⟩ : syracuseStep 1860239 = 2790359) B2790359
theorem B28238543 : Blo 1100624 28238543 := bstep (se 1 (by rfl) ⟨21178907, by rfl⟩ : syracuseStep 28238543 = 42357815) B42357815
theorem B1860799 : Blo 1100624 1860799 := bstep (se 1 (by rfl) ⟨1395599, by rfl⟩ : syracuseStep 1860799 = 2791199) B2791199
theorem B2483855 : Blo 1100624 2483855 := bstep (se 1 (by rfl) ⟨1862891, by rfl⟩ : syracuseStep 2483855 = 3725783) B3725783
theorem B2352905 : Blo 1100624 2352905 := bstep (se 2 (by rfl) ⟨882339, by rfl⟩ : syracuseStep 2352905 = 1764679) B1764679
theorem B3139337 : Blo 1100624 3139337 := bstep (se 2 (by rfl) ⟨1177251, by rfl⟩ : syracuseStep 3139337 = 2354503) B2354503
theorem B4712201 : Blo 1100624 4712201 := bstep (se 2 (by rfl) ⟨1767075, by rfl⟩ : syracuseStep 4712201 = 3534151) B3534151
theorem B1861447 : Blo 1100624 1861447 := bstep (se 1 (by rfl) ⟨1396085, by rfl⟩ : syracuseStep 1861447 = 2792171) B2792171
theorem B12576707 : Blo 1100624 12576707 := bstep (se 1 (by rfl) ⟨9432530, by rfl⟩ : syracuseStep 12576707 = 18865061) B18865061
theorem B1239295 : Blo 1100624 1239295 := bstep (se 1 (by rfl) ⟨929471, by rfl⟩ : syracuseStep 1239295 = 1858943) B1858943
theorem B21228115 : Blo 1100624 21228115 := bstep (se 1 (by rfl) ⟨15921086, by rfl⟩ : syracuseStep 21228115 = 31842173) B31842173
theorem B1862311 : Blo 1100624 1862311 := bstep (se 1 (by rfl) ⟨1396733, by rfl⟩ : syracuseStep 1862311 = 2793467) B2793467
theorem B62909291 : Blo 1100624 62909291 := bstep (se 1 (by rfl) ⟨47181968, by rfl⟩ : syracuseStep 62909291 = 94363937) B94363937
theorem B2092139 : Blo 1100624 2092139 := bstep (se 1 (by rfl) ⟨1569104, by rfl⟩ : syracuseStep 2092139 = 3138209) B3138209
theorem B4189427 : Blo 1100624 4189427 := bstep (se 1 (by rfl) ⟨3142070, by rfl⟩ : syracuseStep 4189427 = 6284141) B6284141
theorem B1862959 : Blo 1100624 1862959 := bstep (se 1 (by rfl) ⟨1397219, by rfl⟩ : syracuseStep 1862959 = 2794439) B2794439
theorem B2093339 : Blo 1100624 2093339 := bstep (se 1 (by rfl) ⟨1570004, by rfl⟩ : syracuseStep 2093339 = 3140009) B3140009
theorem B1241887 : Blo 1100624 1241887 := bstep (se 1 (by rfl) ⟨931415, by rfl⟩ : syracuseStep 1241887 = 1862831) B1862831
theorem B35780413 : Blo 1100624 35780413 := bstep (se 3 (by rfl) ⟨6708827, by rfl⟩ : syracuseStep 35780413 = 13417655) B13417655
theorem B2357279 : Blo 1100624 2357279 := bstep (se 1 (by rfl) ⟨1767959, by rfl⟩ : syracuseStep 2357279 = 3535919) B3535919
theorem B3143711 : Blo 1100624 3143711 := bstep (se 1 (by rfl) ⟨2357783, by rfl⟩ : syracuseStep 3143711 = 4715567) B4715567
theorem B4716575 : Blo 1100624 4716575 := bstep (se 1 (by rfl) ⟨3537431, by rfl⟩ : syracuseStep 4716575 = 7074863) B7074863
theorem B1570927 : Blo 1100624 1570927 := bstep (se 1 (by rfl) ⟨1178195, by rfl⟩ : syracuseStep 1570927 = 2356391) B2356391
theorem B3144359 : Blo 1100624 3144359 := bstep (se 1 (by rfl) ⟨2358269, by rfl⟩ : syracuseStep 3144359 = 4716539) B4716539
theorem B4717223 : Blo 1100624 4717223 := bstep (se 1 (by rfl) ⟨3537917, by rfl⟩ : syracuseStep 4717223 = 7075835) B7075835
theorem B4193147 : Blo 1100624 4193147 := bstep (se 1 (by rfl) ⟨3144860, by rfl⟩ : syracuseStep 4193147 = 6289721) B6289721
theorem B30211177 : Blo 1100624 30211177 := bstep (se 2 (by rfl) ⟨11329191, by rfl⟩ : syracuseStep 30211177 = 22658383) B22658383
theorem B13074281 : Blo 1100624 13074281 := bstep (se 2 (by rfl) ⟨4902855, by rfl⟩ : syracuseStep 13074281 = 9805711) B9805711
theorem B2786035 : Blo 1100624 2786035 := bstep (se 1 (by rfl) ⟨2089526, by rfl⟩ : syracuseStep 2786035 = 4179053) B4179053
theorem B10191815 : Blo 1100624 10191815 := bstep (se 1 (by rfl) ⟨7643861, by rfl⟩ : syracuseStep 10191815 = 15287723) B15287723
theorem B6358175 : Blo 1100624 6358175 := bstep (se 1 (by rfl) ⟨4768631, by rfl⟩ : syracuseStep 6358175 = 9537263) B9537263
theorem B2786795 : Blo 1100624 2786795 := bstep (se 1 (by rfl) ⟨2090096, by rfl⟩ : syracuseStep 2786795 = 4180193) B4180193
theorem B2786987 : Blo 1100624 2786987 := bstep (se 1 (by rfl) ⟨2090240, by rfl⟩ : syracuseStep 2786987 = 4180481) B4180481
theorem B3967471 : Blo 1100624 3967471 := bstep (se 1 (by rfl) ⟨2975603, by rfl⟩ : syracuseStep 3967471 = 5951207) B5951207
theorem B2788091 : Blo 1100624 2788091 := bstep (se 1 (by rfl) ⟨2091068, by rfl⟩ : syracuseStep 2788091 = 4182137) B4182137
theorem B2788303 : Blo 1100624 2788303 := bstep (se 1 (by rfl) ⟨2091227, by rfl⟩ : syracuseStep 2788303 = 4182455) B4182455
theorem B19107485 : Blo 1100624 19107485 := bstep (se 3 (by rfl) ⟨3582653, by rfl⟩ : syracuseStep 19107485 = 7165307) B7165307
theorem B7542071 : Blo 1100624 7542071 := bstep (se 1 (by rfl) ⟨5656553, by rfl⟩ : syracuseStep 7542071 = 11313107) B11313107
theorem B76519201 : Blo 1100624 76519201 := bstep (se 2 (by rfl) ⟨28694700, by rfl⟩ : syracuseStep 76519201 = 57389401) B57389401
theorem B18847565 : Blo 1100624 18847565 := bstep (se 3 (by rfl) ⟨3533918, by rfl⟩ : syracuseStep 18847565 = 7067837) B7067837
theorem B2792951 : Blo 1100624 2792951 := bstep (se 1 (by rfl) ⟨2094713, by rfl⟩ : syracuseStep 2792951 = 4189427) B4189427
theorem B91627729 : Blo 1100624 91627729 := bstep (se 2 (by rfl) ⟨34360398, by rfl⟩ : syracuseStep 91627729 = 68720797) B68720797
theorem B2237087 : Blo 1100624 2237087 := bstep (se 1 (by rfl) ⟨1677815, by rfl⟩ : syracuseStep 2237087 = 3355631) B3355631
theorem B32646125 : Blo 1100624 32646125 := bstep (se 3 (by rfl) ⟨6121148, by rfl⟩ : syracuseStep 32646125 = 12242297) B12242297
theorem B40281569 : Blo 1100624 40281569 := bstep (se 2 (by rfl) ⟨15105588, by rfl⟩ : syracuseStep 40281569 = 30211177) B30211177
theorem B2795431 : Blo 1100624 2795431 := bstep (se 1 (by rfl) ⟨2096573, by rfl⟩ : syracuseStep 2795431 = 4193147) B4193147
theorem B6269561 : Blo 1100624 6269561 := bstep (se 2 (by rfl) ⟨2351085, by rfl⟩ : syracuseStep 6269561 = 4702171) B4702171
theorem B128789423 : Blo 1100624 128789423 := bstep (se 1 (by rfl) ⟨96592067, by rfl⟩ : syracuseStep 128789423 = 193184135) B193184135
theorem B6269993 : Blo 1100624 6269993 := bstep (se 2 (by rfl) ⟨2351247, by rfl⟩ : syracuseStep 6269993 = 4702495) B4702495
theorem B5582033 : Blo 1100624 5582033 := bstep (se 2 (by rfl) ⟨2093262, by rfl⟩ : syracuseStep 5582033 = 4186525) B4186525
theorem B40840517 : Blo 1100624 40840517 := bstep (se 4 (by rfl) ⟨3828798, by rfl⟩ : syracuseStep 40840517 = 7657597) B7657597
theorem B23801363 : Blo 1100624 23801363 := bstep (se 1 (by rfl) ⟨17851022, by rfl⟩ : syracuseStep 23801363 = 35702045) B35702045
theorem B11906909 : Blo 1100624 11906909 := bstep (se 3 (by rfl) ⟨2232545, by rfl⟩ : syracuseStep 11906909 = 4465091) B4465091
theorem B5582843 : Blo 1100624 5582843 := bstep (se 1 (by rfl) ⟨4187132, by rfl⟩ : syracuseStep 5582843 = 8374265) B8374265
theorem B232697939 : Blo 1100624 232697939 := bstep (se 1 (by rfl) ⟨174523454, by rfl⟩ : syracuseStep 232697939 = 349046909) B349046909
theorem B3715631 : Blo 1100624 3715631 := bstep (se 1 (by rfl) ⟨2786723, by rfl⟩ : syracuseStep 3715631 = 5573447) B5573447
theorem B1651559 : Blo 1100624 1651559 := bstep (se 1 (by rfl) ⟨1238669, by rfl⟩ : syracuseStep 1651559 = 2477339) B2477339
theorem B3716063 : Blo 1100624 3716063 := bstep (se 1 (by rfl) ⟨2787047, by rfl⟩ : syracuseStep 3716063 = 5574095) B5574095
theorem B1651739 : Blo 1100624 1651739 := bstep (se 1 (by rfl) ⟨1238804, by rfl⟩ : syracuseStep 1651739 = 2477609) B2477609
theorem B10728791 : Blo 1100624 10728791 := bstep (se 1 (by rfl) ⟨8046593, by rfl⟩ : syracuseStep 10728791 = 16093187) B16093187
theorem B1652393 : Blo 1100624 1652393 := bstep (se 2 (by rfl) ⟨619647, by rfl⟩ : syracuseStep 1652393 = 1239295) B1239295
theorem B6371795 : Blo 1100624 6371795 := bstep (se 1 (by rfl) ⟨4778846, by rfl⟩ : syracuseStep 6371795 = 9557693) B9557693
theorem B1653227 : Blo 1100624 1653227 := bstep (se 1 (by rfl) ⟨1239920, by rfl⟩ : syracuseStep 1653227 = 2479841) B2479841
theorem B5585435 : Blo 1100624 5585435 := bstep (se 1 (by rfl) ⟨4189076, by rfl⟩ : syracuseStep 5585435 = 8378153) B8378153
theorem B1653467 : Blo 1100624 1653467 := bstep (se 1 (by rfl) ⟨1240100, by rfl⟩ : syracuseStep 1653467 = 2480201) B2480201
theorem B3062951 : Blo 1100624 3062951 := bstep (se 1 (by rfl) ⟨2297213, by rfl⟩ : syracuseStep 3062951 = 4594427) B4594427
theorem B11943413 : Blo 1100624 11943413 := bstep (se 5 (by rfl) ⟨559847, by rfl⟩ : syracuseStep 11943413 = 1119695) B1119695
theorem B16105067 : Blo 1100624 16105067 := bstep (se 1 (by rfl) ⟨12078800, by rfl⟩ : syracuseStep 16105067 = 24157601) B24157601
theorem B1654559 : Blo 1100624 1654559 := bstep (se 1 (by rfl) ⟨1240919, by rfl⟩ : syracuseStep 1654559 = 2481839) B2481839
theorem B5652287 : Blo 1100624 5652287 := bstep (se 1 (by rfl) ⟨4239215, by rfl⟩ : syracuseStep 5652287 = 8478431) B8478431
theorem B1654811 : Blo 1100624 1654811 := bstep (se 1 (by rfl) ⟨1241108, by rfl⟩ : syracuseStep 1654811 = 2482217) B2482217
theorem B3719411 : Blo 1100624 3719411 := bstep (se 1 (by rfl) ⟨2789558, by rfl⟩ : syracuseStep 3719411 = 5579117) B5579117
theorem B1655039 : Blo 1100624 1655039 := bstep (se 1 (by rfl) ⟨1241279, by rfl⟩ : syracuseStep 1655039 = 2482559) B2482559
theorem B18825695 : Blo 1100624 18825695 := bstep (se 1 (by rfl) ⟨14119271, by rfl⟩ : syracuseStep 18825695 = 28238543) B28238543
theorem B1655849 : Blo 1100624 1655849 := bstep (se 2 (by rfl) ⟨620943, by rfl⟩ : syracuseStep 1655849 = 1241887) B1241887
theorem B1655903 : Blo 1100624 1655903 := bstep (se 1 (by rfl) ⟨1241927, by rfl⟩ : syracuseStep 1655903 = 2483855) B2483855
theorem B6702601 : Blo 1100624 6702601 := bstep (se 2 (by rfl) ⟨2513475, by rfl⟩ : syracuseStep 6702601 = 5026951) B5026951
theorem B3721085 : Blo 1100624 3721085 := bstep (se 3 (by rfl) ⟨697703, by rfl⟩ : syracuseStep 3721085 = 1395407) B1395407
theorem B3721193 : Blo 1100624 3721193 := bstep (se 2 (by rfl) ⟨1395447, by rfl⟩ : syracuseStep 3721193 = 2790895) B2790895
theorem B1394759 : Blo 1100624 1394759 := bstep (se 1 (by rfl) ⟨1046069, by rfl⟩ : syracuseStep 1394759 = 2092139) B2092139
theorem B4705127 : Blo 1100624 4705127 := bstep (se 1 (by rfl) ⟨3528845, by rfl⟩ : syracuseStep 4705127 = 7057691) B7057691
theorem B1395559 : Blo 1100624 1395559 := bstep (se 1 (by rfl) ⟨1046669, by rfl⟩ : syracuseStep 1395559 = 2093339) B2093339
theorem B6278057 : Blo 1100624 6278057 := bstep (se 2 (by rfl) ⟨2354271, by rfl⟩ : syracuseStep 6278057 = 4708543) B4708543
theorem B1100799 : Blo 1100624 1100799 := bstep (se 1 (by rfl) ⟨825599, by rfl⟩ : syracuseStep 1100799 = 1651199) B1651199
theorem B1100891 : Blo 1100624 1100891 := bstep (se 1 (by rfl) ⟨825668, by rfl⟩ : syracuseStep 1100891 = 1651337) B1651337
theorem B9424025 : Blo 1100624 9424025 := bstep (se 2 (by rfl) ⟨3534009, by rfl⟩ : syracuseStep 9424025 = 7068019) B7068019
theorem B1101051 : Blo 1100624 1101051 := bstep (se 1 (by rfl) ⟨825788, by rfl⟩ : syracuseStep 1101051 = 1651577) B1651577
theorem B1101103 : Blo 1100624 1101103 := bstep (se 1 (by rfl) ⟨825827, by rfl⟩ : syracuseStep 1101103 = 1651655) B1651655
theorem B8375723 : Blo 1100624 8375723 := bstep (se 1 (by rfl) ⟨6281792, by rfl⟩ : syracuseStep 8375723 = 12563585) B12563585
theorem B1101343 : Blo 1100624 1101343 := bstep (se 1 (by rfl) ⟨826007, by rfl⟩ : syracuseStep 1101343 = 1652015) B1652015
theorem B11914867 : Blo 1100624 11914867 := bstep (se 1 (by rfl) ⟨8936150, by rfl⟩ : syracuseStep 11914867 = 17872301) B17872301
theorem B1101503 : Blo 1100624 1101503 := bstep (se 1 (by rfl) ⟨826127, by rfl⟩ : syracuseStep 1101503 = 1652255) B1652255
theorem B1101567 : Blo 1100624 1101567 := bstep (se 1 (by rfl) ⟨826175, by rfl⟩ : syracuseStep 1101567 = 1652351) B1652351
theorem B1101855 : Blo 1100624 1101855 := bstep (se 1 (by rfl) ⟨826391, by rfl⟩ : syracuseStep 1101855 = 1652783) B1652783
theorem B6279241 : Blo 1100624 6279241 := bstep (se 2 (by rfl) ⟨2354715, by rfl⟩ : syracuseStep 6279241 = 4709431) B4709431
theorem B1101935 : Blo 1100624 1101935 := bstep (se 1 (by rfl) ⟨826451, by rfl⟩ : syracuseStep 1101935 = 1652903) B1652903
theorem B2150543 : Blo 1100624 2150543 := bstep (se 1 (by rfl) ⟨1612907, by rfl⟩ : syracuseStep 2150543 = 3225815) B3225815
theorem B3723407 : Blo 1100624 3723407 := bstep (se 1 (by rfl) ⟨2792555, by rfl⟩ : syracuseStep 3723407 = 5585111) B5585111
theorem B2478329 : Blo 1100624 2478329 := bstep (se 2 (by rfl) ⟨929373, by rfl⟩ : syracuseStep 2478329 = 1858747) B1858747
theorem B1102335 : Blo 1100624 1102335 := bstep (se 1 (by rfl) ⟨826751, by rfl⟩ : syracuseStep 1102335 = 1653503) B1653503
theorem B2478599 : Blo 1100624 2478599 := bstep (se 1 (by rfl) ⟨1858949, by rfl⟩ : syracuseStep 2478599 = 3717899) B3717899
theorem B1102383 : Blo 1100624 1102383 := bstep (se 1 (by rfl) ⟨826787, by rfl⟩ : syracuseStep 1102383 = 1653575) B1653575
theorem B1102591 : Blo 1100624 1102591 := bstep (se 1 (by rfl) ⟨826943, by rfl⟩ : syracuseStep 1102591 = 1653887) B1653887
theorem B3527563 : Blo 1100624 3527563 := bstep (se 1 (by rfl) ⟨2645672, by rfl⟩ : syracuseStep 3527563 = 5291345) B5291345
theorem B1103567 : Blo 1100624 1103567 := bstep (se 1 (by rfl) ⟨827675, by rfl⟩ : syracuseStep 1103567 = 1655351) B1655351
theorem B18142967 : Blo 1100624 18142967 := bstep (se 1 (by rfl) ⟨13607225, by rfl⟩ : syracuseStep 18142967 = 27214451) B27214451
theorem B3725135 : Blo 1100624 3725135 := bstep (se 1 (by rfl) ⟨2793851, by rfl⟩ : syracuseStep 3725135 = 5587703) B5587703
theorem B1988479 : Blo 1100624 1988479 := bstep (se 1 (by rfl) ⟨1491359, by rfl⟩ : syracuseStep 1988479 = 2982719) B2982719
theorem B2480039 : Blo 1100624 2480039 := bstep (se 1 (by rfl) ⟨1860029, by rfl⟩ : syracuseStep 2480039 = 3720059) B3720059
theorem B1857451 : Blo 1100624 1857451 := bstep (se 1 (by rfl) ⟨1393088, by rfl⟩ : syracuseStep 1857451 = 2786177) B2786177
theorem B1103807 : Blo 1100624 1103807 := bstep (se 1 (by rfl) ⟨827855, by rfl⟩ : syracuseStep 1103807 = 1655711) B1655711
theorem B1103839 : Blo 1100624 1103839 := bstep (se 1 (by rfl) ⟨827879, by rfl⟩ : syracuseStep 1103839 = 1655759) B1655759
theorem B1103919 : Blo 1100624 1103919 := bstep (se 1 (by rfl) ⟨827939, by rfl⟩ : syracuseStep 1103919 = 1655879) B1655879
theorem B1104039 : Blo 1100624 1104039 := bstep (se 1 (by rfl) ⟨828029, by rfl⟩ : syracuseStep 1104039 = 1656059) B1656059
theorem B1104079 : Blo 1100624 1104079 := bstep (se 1 (by rfl) ⟨828059, by rfl⟩ : syracuseStep 1104079 = 1656119) B1656119
theorem B1104487 : Blo 1100624 1104487 := bstep (se 1 (by rfl) ⟨828365, by rfl⟩ : syracuseStep 1104487 = 1656731) B1656731
theorem B1104495 : Blo 1100624 1104495 := bstep (se 1 (by rfl) ⟨828371, by rfl⟩ : syracuseStep 1104495 = 1656743) B1656743
theorem B1104615 : Blo 1100624 1104615 := bstep (se 1 (by rfl) ⟨828461, by rfl⟩ : syracuseStep 1104615 = 1656923) B1656923
theorem B3529511 : Blo 1100624 3529511 := bstep (se 1 (by rfl) ⟨2647133, by rfl⟩ : syracuseStep 3529511 = 5294267) B5294267
theorem B2481065 : Blo 1100624 2481065 := bstep (se 2 (by rfl) ⟨930399, by rfl⟩ : syracuseStep 2481065 = 1860799) B1860799
theorem B2481119 : Blo 1100624 2481119 := bstep (se 1 (by rfl) ⟨1860839, by rfl⟩ : syracuseStep 2481119 = 3721679) B3721679
theorem B26795215 : Blo 1100624 26795215 := bstep (se 1 (by rfl) ⟨20096411, by rfl⟩ : syracuseStep 26795215 = 40192823) B40192823
theorem B1989863 : Blo 1100624 1989863 := bstep (se 1 (by rfl) ⟨1492397, by rfl⟩ : syracuseStep 1989863 = 2984795) B2984795
theorem B1859051 : Blo 1100624 1859051 := bstep (se 1 (by rfl) ⟨1394288, by rfl⟩ : syracuseStep 1859051 = 2788577) B2788577
theorem B2481659 : Blo 1100624 2481659 := bstep (se 1 (by rfl) ⟨1861244, by rfl⟩ : syracuseStep 2481659 = 3722489) B3722489
theorem B2481767 : Blo 1100624 2481767 := bstep (se 1 (by rfl) ⟨1861325, by rfl⟩ : syracuseStep 2481767 = 3722651) B3722651
theorem B2481929 : Blo 1100624 2481929 := bstep (se 2 (by rfl) ⟨930723, by rfl⟩ : syracuseStep 2481929 = 1861447) B1861447
theorem B5300093 : Blo 1100624 5300093 := bstep (se 3 (by rfl) ⟨993767, by rfl⟩ : syracuseStep 5300093 = 1987535) B1987535
theorem B2645903 : Blo 1100624 2645903 := bstep (se 1 (by rfl) ⟨1984427, by rfl⟩ : syracuseStep 2645903 = 3968855) B3968855
theorem B1859753 : Blo 1100624 1859753 := bstep (se 2 (by rfl) ⟨697407, by rfl⟩ : syracuseStep 1859753 = 1394815) B1394815
theorem B4710919 : Blo 1100624 4710919 := bstep (se 1 (by rfl) ⟨3533189, by rfl⟩ : syracuseStep 4710919 = 7066379) B7066379
theorem B28304153 : Blo 1100624 28304153 := bstep (se 2 (by rfl) ⟨10614057, by rfl⟩ : syracuseStep 28304153 = 21228115) B21228115
theorem B39805789 : Blo 1100624 39805789 := bstep (se 3 (by rfl) ⟨7463585, by rfl⟩ : syracuseStep 39805789 = 14927171) B14927171
theorem B1860455 : Blo 1100624 1860455 := bstep (se 1 (by rfl) ⟨1395341, by rfl⟩ : syracuseStep 1860455 = 2790683) B2790683
theorem B2483081 : Blo 1100624 2483081 := bstep (se 2 (by rfl) ⟨931155, by rfl⟩ : syracuseStep 2483081 = 1862311) B1862311
theorem B2483945 : Blo 1100624 2483945 := bstep (se 2 (by rfl) ⟨931479, by rfl⟩ : syracuseStep 2483945 = 1862959) B1862959
theorem B6285599 : Blo 1100624 6285599 := bstep (se 1 (by rfl) ⟨4714199, by rfl⟩ : syracuseStep 6285599 = 9428399) B9428399
theorem B22669895 : Blo 1100624 22669895 := bstep (se 1 (by rfl) ⟨17002421, by rfl⟩ : syracuseStep 22669895 = 34004843) B34004843
theorem B15920165 : Blo 1100624 15920165 := bstep (se 4 (by rfl) ⟨1492515, by rfl⟩ : syracuseStep 15920165 = 2985031) B2985031
theorem B1240159 : Blo 1100624 1240159 := bstep (se 1 (by rfl) ⟨930119, by rfl⟩ : syracuseStep 1240159 = 1860239) B1860239
theorem B3141467 : Blo 1100624 3141467 := bstep (se 1 (by rfl) ⟨2356100, by rfl⟩ : syracuseStep 3141467 = 4712201) B4712201
theorem B1568603 : Blo 1100624 1568603 := bstep (se 1 (by rfl) ⟨1176452, by rfl⟩ : syracuseStep 1568603 = 2352905) B2352905
theorem B2092891 : Blo 1100624 2092891 := bstep (se 1 (by rfl) ⟨1569668, by rfl⟩ : syracuseStep 2092891 = 3139337) B3139337
theorem B8384471 : Blo 1100624 8384471 := bstep (se 1 (by rfl) ⟨6288353, by rfl⟩ : syracuseStep 8384471 = 12576707) B12576707
theorem B8384957 : Blo 1100624 8384957 := bstep (se 3 (by rfl) ⟨1572179, by rfl⟩ : syracuseStep 8384957 = 3144359) B3144359
theorem B41939527 : Blo 1100624 41939527 := bstep (se 1 (by rfl) ⟨31454645, by rfl⟩ : syracuseStep 41939527 = 62909291) B62909291
theorem B47707217 : Blo 1100624 47707217 := bstep (se 2 (by rfl) ⟨17890206, by rfl⟩ : syracuseStep 47707217 = 35780413) B35780413
theorem B2094569 : Blo 1100624 2094569 := bstep (se 2 (by rfl) ⟨785463, by rfl⟩ : syracuseStep 2094569 = 1570927) B1570927
theorem B14153717 : Blo 1100624 14153717 := bstep (se 5 (by rfl) ⟨663455, by rfl⟩ : syracuseStep 14153717 = 1326911) B1326911
theorem B1276159 : Blo 1100624 1276159 := bstep (se 1 (by rfl) ⟨957119, by rfl⟩ : syracuseStep 1276159 = 1914239) B1914239
theorem B1571519 : Blo 1100624 1571519 := bstep (se 1 (by rfl) ⟨1178639, by rfl⟩ : syracuseStep 1571519 = 2357279) B2357279
theorem B2095807 : Blo 1100624 2095807 := bstep (se 1 (by rfl) ⟨1571855, by rfl⟩ : syracuseStep 2095807 = 3143711) B3143711
theorem B3144383 : Blo 1100624 3144383 := bstep (se 1 (by rfl) ⟨2358287, by rfl⟩ : syracuseStep 3144383 = 4716575) B4716575
theorem B3177427 : Blo 1100624 3177427 := bstep (se 1 (by rfl) ⟨2383070, by rfl⟩ : syracuseStep 3177427 = 4766141) B4766141
theorem B3144815 : Blo 1100624 3144815 := bstep (se 1 (by rfl) ⟨2358611, by rfl⟩ : syracuseStep 3144815 = 4717223) B4717223
theorem B9403553 : Blo 1100624 9403553 := bstep (se 2 (by rfl) ⟨3526332, by rfl⟩ : syracuseStep 9403553 = 7052665) B7052665
theorem B8716187 : Blo 1100624 8716187 := bstep (se 1 (by rfl) ⟨6537140, by rfl⟩ : syracuseStep 8716187 = 13074281) B13074281
theorem B620527837 : Blo 1100624 620527837 := bstep (se 3 (by rfl) ⟨116348969, by rfl⟩ : syracuseStep 620527837 = 232697939) B232697939
theorem B12550463 : Blo 1100624 12550463 := bstep (se 1 (by rfl) ⟨9412847, by rfl⟩ : syracuseStep 12550463 = 18825695) B18825695
theorem B2790521 : Blo 1100624 2790521 := bstep (se 2 (by rfl) ⟨1046445, by rfl⟩ : syracuseStep 2790521 = 2092891) B2092891
theorem B15113263 : Blo 1100624 15113263 := bstep (se 1 (by rfl) ⟨11334947, by rfl⟩ : syracuseStep 15113263 = 22669895) B22669895
theorem B85859615 : Blo 1100624 85859615 := bstep (se 1 (by rfl) ⟨64394711, by rfl⟩ : syracuseStep 85859615 = 128789423) B128789423
theorem B15867575 : Blo 1100624 15867575 := bstep (se 1 (by rfl) ⟨11900681, by rfl⟩ : syracuseStep 15867575 = 23801363) B23801363
theorem B7937939 : Blo 1100624 7937939 := bstep (se 1 (by rfl) ⟨5953454, by rfl⟩ : syracuseStep 7937939 = 11906909) B11906909
theorem B7152527 : Blo 1100624 7152527 := bstep (se 1 (by rfl) ⟨5364395, by rfl⟩ : syracuseStep 7152527 = 10728791) B10728791
theorem B2794409 : Blo 1100624 2794409 := bstep (se 2 (by rfl) ⟨1047903, by rfl⟩ : syracuseStep 2794409 = 2095807) B2095807
theorem B4236569 : Blo 1100624 4236569 := bstep (se 2 (by rfl) ⟨1588713, by rfl⟩ : syracuseStep 4236569 = 3177427) B3177427
theorem B35726953 : Blo 1100624 35726953 := bstep (se 2 (by rfl) ⟨13397607, by rfl⟩ : syracuseStep 35726953 = 26795215) B26795215
theorem B6269035 : Blo 1100624 6269035 := bstep (se 1 (by rfl) ⟨4701776, by rfl⟩ : syracuseStep 6269035 = 9403553) B9403553
theorem B2041967 : Blo 1100624 2041967 := bstep (se 1 (by rfl) ⟨1531475, by rfl⟩ : syracuseStep 2041967 = 3062951) B3062951
theorem B7055741 : Blo 1100624 7055741 := bstep (se 3 (by rfl) ⟨1322951, by rfl⟩ : syracuseStep 7055741 = 2645903) B2645903
theorem B5810791 : Blo 1100624 5810791 := bstep (se 1 (by rfl) ⟨4358093, by rfl⟩ : syracuseStep 5810791 = 8716187) B8716187
theorem B6794543 : Blo 1100624 6794543 := bstep (se 1 (by rfl) ⟨5095907, by rfl⟩ : syracuseStep 6794543 = 10191815) B10191815
theorem B4238783 : Blo 1100624 4238783 := bstep (se 1 (by rfl) ⟨3179087, by rfl⟩ : syracuseStep 4238783 = 6358175) B6358175
theorem B3714713 : Blo 1100624 3714713 := bstep (se 2 (by rfl) ⟨1393017, by rfl⟩ : syracuseStep 3714713 = 2786035) B2786035
theorem B488681221 : Blo 1100624 488681221 := bstep (se 4 (by rfl) ⟨45813864, by rfl⟩ : syracuseStep 488681221 = 91627729) B91627729
theorem B5583815 : Blo 1100624 5583815 := bstep (se 1 (by rfl) ⟨4187861, by rfl⟩ : syracuseStep 5583815 = 8375723) B8375723
theorem B1652219 : Blo 1100624 1652219 := bstep (se 1 (by rfl) ⟨1239164, by rfl⟩ : syracuseStep 1652219 = 2478329) B2478329
theorem B1652399 : Blo 1100624 1652399 := bstep (se 1 (by rfl) ⟨1239299, by rfl⟩ : syracuseStep 1652399 = 2478599) B2478599
theorem B5289961 : Blo 1100624 5289961 := bstep (se 2 (by rfl) ⟨1983735, by rfl⟩ : syracuseStep 5289961 = 3967471) B3967471
theorem B5028047 : Blo 1100624 5028047 := bstep (se 1 (by rfl) ⟨3771035, by rfl⟩ : syracuseStep 5028047 = 7542071) B7542071
theorem B12565043 : Blo 1100624 12565043 := bstep (se 1 (by rfl) ⟨9423782, by rfl⟩ : syracuseStep 12565043 = 18847565) B18847565
theorem B3717737 : Blo 1100624 3717737 := bstep (se 2 (by rfl) ⟨1394151, by rfl⟩ : syracuseStep 3717737 = 2788303) B2788303
theorem B1653359 : Blo 1100624 1653359 := bstep (se 1 (by rfl) ⟨1240019, by rfl⟩ : syracuseStep 1653359 = 2480039) B2480039
theorem B1653545 : Blo 1100624 1653545 := bstep (se 2 (by rfl) ⟨620079, by rfl⟩ : syracuseStep 1653545 = 1240159) B1240159
theorem B1654043 : Blo 1100624 1654043 := bstep (se 1 (by rfl) ⟨1240532, by rfl⟩ : syracuseStep 1654043 = 2481065) B2481065
theorem B48381245 : Blo 1100624 48381245 := bstep (se 3 (by rfl) ⟨9071483, by rfl⟩ : syracuseStep 48381245 = 18142967) B18142967
theorem B1654079 : Blo 1100624 1654079 := bstep (se 1 (by rfl) ⟨1240559, by rfl⟩ : syracuseStep 1654079 = 2481119) B2481119
theorem B1326575 : Blo 1100624 1326575 := bstep (se 1 (by rfl) ⟨994931, by rfl⟩ : syracuseStep 1326575 = 1989863) B1989863
theorem B1654439 : Blo 1100624 1654439 := bstep (se 1 (by rfl) ⟨1240829, by rfl⟩ : syracuseStep 1654439 = 2481659) B2481659
theorem B1654511 : Blo 1100624 1654511 := bstep (se 1 (by rfl) ⟨1240883, by rfl⟩ : syracuseStep 1654511 = 2481767) B2481767
theorem B1654619 : Blo 1100624 1654619 := bstep (se 1 (by rfl) ⟨1240964, by rfl⟩ : syracuseStep 1654619 = 2481929) B2481929
theorem B8372321 : Blo 1100624 8372321 := bstep (se 2 (by rfl) ⟨3139620, by rfl⟩ : syracuseStep 8372321 = 6279241) B6279241
theorem B3719357 : Blo 1100624 3719357 := bstep (se 3 (by rfl) ⟨697379, by rfl⟩ : syracuseStep 3719357 = 1394759) B1394759
theorem B1491391 : Blo 1100624 1491391 := bstep (se 1 (by rfl) ⟨1118543, by rfl⟩ : syracuseStep 1491391 = 2237087) B2237087
theorem B1655387 : Blo 1100624 1655387 := bstep (se 1 (by rfl) ⟨1241540, by rfl⟩ : syracuseStep 1655387 = 2483081) B2483081
theorem B55919369 : Blo 1100624 55919369 := bstep (se 2 (by rfl) ⟨20969763, by rfl⟩ : syracuseStep 55919369 = 41939527) B41939527
theorem B26854379 : Blo 1100624 26854379 := bstep (se 1 (by rfl) ⟨20140784, by rfl⟩ : syracuseStep 26854379 = 40281569) B40281569
theorem B1655963 : Blo 1100624 1655963 := bstep (se 1 (by rfl) ⟨1241972, by rfl⟩ : syracuseStep 1655963 = 2483945) B2483945
theorem B4703417 : Blo 1100624 4703417 := bstep (se 2 (by rfl) ⟨1763781, by rfl⟩ : syracuseStep 4703417 = 3527563) B3527563
theorem B16991453 : Blo 1100624 16991453 := bstep (se 3 (by rfl) ⟨3185897, by rfl⟩ : syracuseStep 16991453 = 6371795) B6371795
theorem B4179707 : Blo 1100624 4179707 := bstep (se 1 (by rfl) ⟨3134780, by rfl⟩ : syracuseStep 4179707 = 6269561) B6269561
theorem B4179995 : Blo 1100624 4179995 := bstep (se 1 (by rfl) ⟨3134996, by rfl⟩ : syracuseStep 4179995 = 6269993) B6269993
theorem B3721355 : Blo 1100624 3721355 := bstep (se 1 (by rfl) ⟨2791016, by rfl⟩ : syracuseStep 3721355 = 5582033) B5582033
theorem B102025601 : Blo 1100624 102025601 := bstep (se 2 (by rfl) ⟨38259600, by rfl⟩ : syracuseStep 102025601 = 76519201) B76519201
theorem B2476601 : Blo 1100624 2476601 := bstep (se 2 (by rfl) ⟨928725, by rfl⟩ : syracuseStep 2476601 = 1857451) B1857451
theorem B5589647 : Blo 1100624 5589647 := bstep (se 1 (by rfl) ⟨4192235, by rfl⟩ : syracuseStep 5589647 = 8384471) B8384471
theorem B3721895 : Blo 1100624 3721895 := bstep (se 1 (by rfl) ⟨2791421, by rfl⟩ : syracuseStep 3721895 = 5582843) B5582843
theorem B5589971 : Blo 1100624 5589971 := bstep (se 1 (by rfl) ⟨4192478, by rfl⟩ : syracuseStep 5589971 = 8384957) B8384957
theorem B2477087 : Blo 1100624 2477087 := bstep (se 1 (by rfl) ⟨1857815, by rfl⟩ : syracuseStep 2477087 = 3715631) B3715631
theorem B1101039 : Blo 1100624 1101039 := bstep (se 1 (by rfl) ⟨825779, by rfl⟩ : syracuseStep 1101039 = 1651559) B1651559
theorem B2477375 : Blo 1100624 2477375 := bstep (se 1 (by rfl) ⟨1858031, by rfl⟩ : syracuseStep 2477375 = 3716063) B3716063
theorem B1101159 : Blo 1100624 1101159 := bstep (se 1 (by rfl) ⟨825869, by rfl⟩ : syracuseStep 1101159 = 1651739) B1651739
theorem B31804811 : Blo 1100624 31804811 := bstep (se 1 (by rfl) ⟨23853608, by rfl⟩ : syracuseStep 31804811 = 47707217) B47707217
theorem B1396379 : Blo 1100624 1396379 := bstep (se 1 (by rfl) ⟨1047284, by rfl⟩ : syracuseStep 1396379 = 2094569) B2094569
theorem B1101595 : Blo 1100624 1101595 := bstep (se 1 (by rfl) ⟨826196, by rfl⟩ : syracuseStep 1101595 = 1652393) B1652393
theorem B1102151 : Blo 1100624 1102151 := bstep (se 1 (by rfl) ⟨826613, by rfl⟩ : syracuseStep 1102151 = 1653227) B1653227
theorem B3723623 : Blo 1100624 3723623 := bstep (se 1 (by rfl) ⟨2792717, by rfl⟩ : syracuseStep 3723623 = 5585435) B5585435
theorem B1102311 : Blo 1100624 1102311 := bstep (se 1 (by rfl) ⟨826733, by rfl⟩ : syracuseStep 1102311 = 1653467) B1653467
theorem B4182941 : Blo 1100624 4182941 := bstep (se 3 (by rfl) ⟨784301, by rfl⟩ : syracuseStep 4182941 = 1568603) B1568603
theorem B10736711 : Blo 1100624 10736711 := bstep (se 1 (by rfl) ⟨8052533, by rfl⟩ : syracuseStep 10736711 = 16105067) B16105067
theorem B1103039 : Blo 1100624 1103039 := bstep (se 1 (by rfl) ⟨827279, by rfl⟩ : syracuseStep 1103039 = 1654559) B1654559
theorem B1103207 : Blo 1100624 1103207 := bstep (se 1 (by rfl) ⟨827405, by rfl⟩ : syracuseStep 1103207 = 1654811) B1654811
theorem B2479607 : Blo 1100624 2479607 := bstep (se 1 (by rfl) ⟨1859705, by rfl⟩ : syracuseStep 2479607 = 3719411) B3719411
theorem B1103359 : Blo 1100624 1103359 := bstep (se 1 (by rfl) ⟨827519, by rfl⟩ : syracuseStep 1103359 = 1655039) B1655039
theorem B6281225 : Blo 1100624 6281225 := bstep (se 2 (by rfl) ⟨2355459, by rfl⟩ : syracuseStep 6281225 = 4710919) B4710919
theorem B1103899 : Blo 1100624 1103899 := bstep (se 1 (by rfl) ⟨827924, by rfl⟩ : syracuseStep 1103899 = 1655849) B1655849
theorem B1103935 : Blo 1100624 1103935 := bstep (se 1 (by rfl) ⟨827951, by rfl⟩ : syracuseStep 1103935 = 1655903) B1655903
theorem B1857863 : Blo 1100624 1857863 := bstep (se 1 (by rfl) ⟨1393397, by rfl⟩ : syracuseStep 1857863 = 2786795) B2786795
theorem B1857991 : Blo 1100624 1857991 := bstep (se 1 (by rfl) ⟨1393493, by rfl⟩ : syracuseStep 1857991 = 2786987) B2786987
theorem B53074385 : Blo 1100624 53074385 := bstep (se 2 (by rfl) ⟨19902894, by rfl⟩ : syracuseStep 53074385 = 39805789) B39805789
theorem B2480723 : Blo 1100624 2480723 := bstep (se 1 (by rfl) ⟨1860542, by rfl⟩ : syracuseStep 2480723 = 3721085) B3721085
theorem B2480795 : Blo 1100624 2480795 := bstep (se 1 (by rfl) ⟨1860596, by rfl⟩ : syracuseStep 2480795 = 3721193) B3721193
theorem B1858727 : Blo 1100624 1858727 := bstep (se 1 (by rfl) ⟨1394045, by rfl⟩ : syracuseStep 1858727 = 2788091) B2788091
theorem B3136751 : Blo 1100624 3136751 := bstep (se 1 (by rfl) ⟨2352563, by rfl⟩ : syracuseStep 3136751 = 4705127) B4705127
theorem B4185371 : Blo 1100624 4185371 := bstep (se 1 (by rfl) ⟨3139028, by rfl⟩ : syracuseStep 4185371 = 6278057) B6278057
theorem B8936801 : Blo 1100624 8936801 := bstep (se 2 (by rfl) ⟨3351300, by rfl⟩ : syracuseStep 8936801 = 6702601) B6702601
theorem B6282683 : Blo 1100624 6282683 := bstep (se 1 (by rfl) ⟨4712012, by rfl⟩ : syracuseStep 6282683 = 9424025) B9424025
theorem B12738323 : Blo 1100624 12738323 := bstep (se 1 (by rfl) ⟨9553742, by rfl⟩ : syracuseStep 12738323 = 19107485) B19107485
theorem B3727241 : Blo 1100624 3727241 := bstep (se 2 (by rfl) ⟨1397715, by rfl⟩ : syracuseStep 3727241 = 2795431) B2795431
theorem B87056333 : Blo 1100624 87056333 := bstep (se 3 (by rfl) ⟨16323062, by rfl⟩ : syracuseStep 87056333 = 32646125) B32646125
theorem B1433695 : Blo 1100624 1433695 := bstep (se 1 (by rfl) ⟨1075271, by rfl⟩ : syracuseStep 1433695 = 2150543) B2150543
theorem B2482271 : Blo 1100624 2482271 := bstep (se 1 (by rfl) ⟨1861703, by rfl⟩ : syracuseStep 2482271 = 3723407) B3723407
theorem B1860745 : Blo 1100624 1860745 := bstep (se 2 (by rfl) ⟨697779, by rfl⟩ : syracuseStep 1860745 = 1395559) B1395559
theorem B2483423 : Blo 1100624 2483423 := bstep (se 1 (by rfl) ⟨1862567, by rfl⟩ : syracuseStep 2483423 = 3725135) B3725135
theorem B2353007 : Blo 1100624 2353007 := bstep (se 1 (by rfl) ⟨1764755, by rfl⟩ : syracuseStep 2353007 = 3529511) B3529511
theorem B15886489 : Blo 1100624 15886489 := bstep (se 2 (by rfl) ⟨5957433, by rfl⟩ : syracuseStep 15886489 = 11914867) B11914867
theorem B1239367 : Blo 1100624 1239367 := bstep (se 1 (by rfl) ⟨929525, by rfl⟩ : syracuseStep 1239367 = 1859051) B1859051
theorem B1861967 : Blo 1100624 1861967 := bstep (se 1 (by rfl) ⟨1396475, by rfl⟩ : syracuseStep 1861967 = 2792951) B2792951
theorem B3533395 : Blo 1100624 3533395 := bstep (se 1 (by rfl) ⟨2650046, by rfl⟩ : syracuseStep 3533395 = 5300093) B5300093
theorem B1239835 : Blo 1100624 1239835 := bstep (se 1 (by rfl) ⟨929876, by rfl⟩ : syracuseStep 1239835 = 1859753) B1859753
theorem B18869435 : Blo 1100624 18869435 := bstep (se 1 (by rfl) ⟨14152076, by rfl⟩ : syracuseStep 18869435 = 28304153) B28304153
theorem B1240303 : Blo 1100624 1240303 := bstep (se 1 (by rfl) ⟨930227, by rfl⟩ : syracuseStep 1240303 = 1860455) B1860455
theorem B4190399 : Blo 1100624 4190399 := bstep (se 1 (by rfl) ⟨3142799, by rfl⟩ : syracuseStep 4190399 = 6285599) B6285599
theorem B4190717 : Blo 1100624 4190717 := bstep (se 3 (by rfl) ⟨785759, by rfl⟩ : syracuseStep 4190717 = 1571519) B1571519
theorem B10613443 : Blo 1100624 10613443 := bstep (se 1 (by rfl) ⟨7960082, by rfl⟩ : syracuseStep 10613443 = 15920165) B15920165
theorem B27227011 : Blo 1100624 27227011 := bstep (se 1 (by rfl) ⟨20420258, by rfl⟩ : syracuseStep 27227011 = 40840517) B40840517
theorem B2651305 : Blo 1100624 2651305 := bstep (se 2 (by rfl) ⟨994239, by rfl⟩ : syracuseStep 2651305 = 1988479) B1988479
theorem B2094311 : Blo 1100624 2094311 := bstep (se 1 (by rfl) ⟨1570733, by rfl⟩ : syracuseStep 2094311 = 3141467) B3141467
theorem B1701545 : Blo 1100624 1701545 := bstep (se 2 (by rfl) ⟨638079, by rfl⟩ : syracuseStep 1701545 = 1276159) B1276159
theorem B9435811 : Blo 1100624 9435811 := bstep (se 1 (by rfl) ⟨7076858, by rfl⟩ : syracuseStep 9435811 = 14153717) B14153717
theorem B2096255 : Blo 1100624 2096255 := bstep (se 1 (by rfl) ⟨1572191, by rfl⟩ : syracuseStep 2096255 = 3144383) B3144383
theorem B2096543 : Blo 1100624 2096543 := bstep (se 1 (by rfl) ⟨1572407, by rfl⟩ : syracuseStep 2096543 = 3144815) B3144815
theorem B7962275 : Blo 1100624 7962275 := bstep (se 1 (by rfl) ⟨5971706, by rfl⟩ : syracuseStep 7962275 = 11943413) B11943413
theorem B3768191 : Blo 1100624 3768191 := bstep (se 1 (by rfl) ⟨2826143, by rfl⟩ : syracuseStep 3768191 = 5652287) B5652287
theorem B2786471 : Blo 1100624 2786471 := bstep (se 1 (by rfl) ⟨2089853, by rfl⟩ : syracuseStep 2786471 = 4179707) B4179707
theorem B2786663 : Blo 1100624 2786663 := bstep (se 1 (by rfl) ⟨2089997, by rfl⟩ : syracuseStep 2786663 = 4179995) B4179995
theorem B21203207 : Blo 1100624 21203207 := bstep (se 1 (by rfl) ⟨15902405, by rfl⟩ : syracuseStep 21203207 = 31804811) B31804811
theorem B8358713 : Blo 1100624 8358713 := bstep (se 2 (by rfl) ⟨3134517, by rfl⟩ : syracuseStep 8358713 = 6269035) B6269035
theorem B2788627 : Blo 1100624 2788627 := bstep (se 1 (by rfl) ⟨2091470, by rfl⟩ : syracuseStep 2788627 = 4182941) B4182941
theorem B2790247 : Blo 1100624 2790247 := bstep (se 1 (by rfl) ⟨2092685, by rfl⟩ : syracuseStep 2790247 = 4185371) B4185371
theorem B58037555 : Blo 1100624 58037555 := bstep (se 1 (by rfl) ⟨43528166, by rfl⟩ : syracuseStep 58037555 = 87056333) B87056333
theorem B5445245 : Blo 1100624 5445245 := bstep (se 3 (by rfl) ⟨1020983, by rfl⟩ : syracuseStep 5445245 = 2041967) B2041967
theorem B2824379 : Blo 1100624 2824379 := bstep (se 1 (by rfl) ⟨2118284, by rfl⟩ : syracuseStep 2824379 = 4236569) B4236569
theorem B4529695 : Blo 1100624 4529695 := bstep (se 1 (by rfl) ⟨3397271, by rfl⟩ : syracuseStep 4529695 = 6794543) B6794543
theorem B2825855 : Blo 1100624 2825855 := bstep (se 1 (by rfl) ⟨2119391, by rfl⟩ : syracuseStep 2825855 = 4238783) B4238783
theorem B7053281 : Blo 1100624 7053281 := bstep (se 2 (by rfl) ⟨2644980, by rfl⟩ : syracuseStep 7053281 = 5289961) B5289961
theorem B2793599 : Blo 1100624 2793599 := bstep (se 1 (by rfl) ⟨2095199, by rfl⟩ : syracuseStep 2793599 = 4190399) B4190399
theorem B2793811 : Blo 1100624 2793811 := bstep (se 1 (by rfl) ⟨2095358, by rfl⟩ : syracuseStep 2793811 = 4190717) B4190717
theorem B3352031 : Blo 1100624 3352031 := bstep (se 1 (by rfl) ⟨2514023, by rfl⟩ : syracuseStep 3352031 = 5028047) B5028047
theorem B32254163 : Blo 1100624 32254163 := bstep (se 1 (by rfl) ⟨24190622, by rfl⟩ : syracuseStep 32254163 = 48381245) B48381245
theorem B5581547 : Blo 1100624 5581547 := bstep (se 1 (by rfl) ⟨4186160, by rfl⟩ : syracuseStep 5581547 = 8372321) B8372321
theorem B1911593 : Blo 1100624 1911593 := bstep (se 2 (by rfl) ⟨716847, by rfl⟩ : syracuseStep 1911593 = 1433695) B1433695
theorem B8366975 : Blo 1100624 8366975 := bstep (se 1 (by rfl) ⟨6275231, by rfl⟩ : syracuseStep 8366975 = 12550463) B12550463
theorem B827370449 : Blo 1100624 827370449 := bstep (se 2 (by rfl) ⟨310263918, by rfl⟩ : syracuseStep 827370449 = 620527837) B620527837
theorem B17902919 : Blo 1100624 17902919 := bstep (se 1 (by rfl) ⟨13427189, by rfl⟩ : syracuseStep 17902919 = 26854379) B26854379
theorem B1651067 : Blo 1100624 1651067 := bstep (se 1 (by rfl) ⟨1238300, by rfl⟩ : syracuseStep 1651067 = 2476601) B2476601
theorem B1651391 : Blo 1100624 1651391 := bstep (se 1 (by rfl) ⟨1238543, by rfl⟩ : syracuseStep 1651391 = 2477087) B2477087
theorem B1651583 : Blo 1100624 1651583 := bstep (se 1 (by rfl) ⟨1238687, by rfl⟩ : syracuseStep 1651583 = 2477375) B2477375
theorem B21181985 : Blo 1100624 21181985 := bstep (se 2 (by rfl) ⟨7943244, by rfl⟩ : syracuseStep 21181985 = 15886489) B15886489
theorem B1652489 : Blo 1100624 1652489 := bstep (se 2 (by rfl) ⟨619683, by rfl⟩ : syracuseStep 1652489 = 1239367) B1239367
theorem B7157807 : Blo 1100624 7157807 := bstep (se 1 (by rfl) ⟨5368355, by rfl⟩ : syracuseStep 7157807 = 10736711) B10736711
theorem B7747721 : Blo 1100624 7747721 := bstep (se 2 (by rfl) ⟨2905395, by rfl⟩ : syracuseStep 7747721 = 5810791) B5810791
theorem B1653071 : Blo 1100624 1653071 := bstep (se 1 (by rfl) ⟨1239803, by rfl⟩ : syracuseStep 1653071 = 2479607) B2479607
theorem B1653113 : Blo 1100624 1653113 := bstep (se 2 (by rfl) ⟨619917, by rfl⟩ : syracuseStep 1653113 = 1239835) B1239835
theorem B1653737 : Blo 1100624 1653737 := bstep (se 2 (by rfl) ⟨620151, by rfl⟩ : syracuseStep 1653737 = 1240303) B1240303
theorem B1653815 : Blo 1100624 1653815 := bstep (se 1 (by rfl) ⟨1240361, by rfl⟩ : syracuseStep 1653815 = 2480723) B2480723
theorem B1653863 : Blo 1100624 1653863 := bstep (se 1 (by rfl) ⟨1240397, by rfl⟩ : syracuseStep 1653863 = 2480795) B2480795
theorem B4537453 : Blo 1100624 4537453 := bstep (se 3 (by rfl) ⟨850772, by rfl⟩ : syracuseStep 4537453 = 1701545) B1701545
theorem B6274685 : Blo 1100624 6274685 := bstep (se 3 (by rfl) ⟨1176503, by rfl⟩ : syracuseStep 6274685 = 2353007) B2353007
theorem B651574961 : Blo 1100624 651574961 := bstep (se 2 (by rfl) ⟨244340610, by rfl⟩ : syracuseStep 651574961 = 488681221) B488681221
theorem B1654847 : Blo 1100624 1654847 := bstep (se 1 (by rfl) ⟨1241135, by rfl⟩ : syracuseStep 1654847 = 2482271) B2482271
theorem B4768351 : Blo 1100624 4768351 := bstep (se 1 (by rfl) ⟨3576263, by rfl⟩ : syracuseStep 4768351 = 7152527) B7152527
theorem B1655615 : Blo 1100624 1655615 := bstep (se 1 (by rfl) ⟨1241711, by rfl⟩ : syracuseStep 1655615 = 2483423) B2483423
theorem B4703827 : Blo 1100624 4703827 := bstep (se 1 (by rfl) ⟨3527870, by rfl⟩ : syracuseStep 4703827 = 7055741) B7055741
theorem B2476475 : Blo 1100624 2476475 := bstep (se 1 (by rfl) ⟨1857356, by rfl⟩ : syracuseStep 2476475 = 3714713) B3714713
theorem B2477321 : Blo 1100624 2477321 := bstep (se 2 (by rfl) ⟨928995, by rfl⟩ : syracuseStep 2477321 = 1857991) B1857991
theorem B3722543 : Blo 1100624 3722543 := bstep (se 1 (by rfl) ⟨2791907, by rfl⟩ : syracuseStep 3722543 = 5583815) B5583815
theorem B1396207 : Blo 1100624 1396207 := bstep (se 1 (by rfl) ⟨1047155, by rfl⟩ : syracuseStep 1396207 = 2094311) B2094311
theorem B1101479 : Blo 1100624 1101479 := bstep (se 1 (by rfl) ⟨826109, by rfl⟩ : syracuseStep 1101479 = 1652219) B1652219
theorem B5590781 : Blo 1100624 5590781 := bstep (se 3 (by rfl) ⟨1048271, by rfl⟩ : syracuseStep 5590781 = 2096543) B2096543
theorem B1101599 : Blo 1100624 1101599 := bstep (se 1 (by rfl) ⟨826199, by rfl⟩ : syracuseStep 1101599 = 1652399) B1652399
theorem B8376695 : Blo 1100624 8376695 := bstep (se 1 (by rfl) ⟨6282521, by rfl⟩ : syracuseStep 8376695 = 12565043) B12565043
theorem B2478491 : Blo 1100624 2478491 := bstep (se 1 (by rfl) ⟨1858868, by rfl⟩ : syracuseStep 2478491 = 3717737) B3717737
theorem B3723677 : Blo 1100624 3723677 := bstep (se 3 (by rfl) ⟨698189, by rfl⟩ : syracuseStep 3723677 = 1396379) B1396379
theorem B1102239 : Blo 1100624 1102239 := bstep (se 1 (by rfl) ⟨826679, by rfl⟩ : syracuseStep 1102239 = 1653359) B1653359
theorem B1102363 : Blo 1100624 1102363 := bstep (se 1 (by rfl) ⟨826772, by rfl⟩ : syracuseStep 1102363 = 1653545) B1653545
theorem B33968861 : Blo 1100624 33968861 := bstep (se 3 (by rfl) ⟨6369161, by rfl⟩ : syracuseStep 33968861 = 12738323) B12738323
theorem B1397503 : Blo 1100624 1397503 := bstep (se 1 (by rfl) ⟨1048127, by rfl⟩ : syracuseStep 1397503 = 2096255) B2096255
theorem B1102695 : Blo 1100624 1102695 := bstep (se 1 (by rfl) ⟨827021, by rfl⟩ : syracuseStep 1102695 = 1654043) B1654043
theorem B1102719 : Blo 1100624 1102719 := bstep (se 1 (by rfl) ⟨827039, by rfl⟩ : syracuseStep 1102719 = 1654079) B1654079
theorem B1102959 : Blo 1100624 1102959 := bstep (se 1 (by rfl) ⟨827219, by rfl⟩ : syracuseStep 1102959 = 1654439) B1654439
theorem B1103007 : Blo 1100624 1103007 := bstep (se 1 (by rfl) ⟨827255, by rfl⟩ : syracuseStep 1103007 = 1654511) B1654511
theorem B1103079 : Blo 1100624 1103079 := bstep (se 1 (by rfl) ⟨827309, by rfl⟩ : syracuseStep 1103079 = 1654619) B1654619
theorem B2512127 : Blo 1100624 2512127 := bstep (se 1 (by rfl) ⟨1884095, by rfl⟩ : syracuseStep 2512127 = 3768191) B3768191
theorem B2479571 : Blo 1100624 2479571 := bstep (se 1 (by rfl) ⟨1859678, by rfl⟩ : syracuseStep 2479571 = 3719357) B3719357
theorem B1103591 : Blo 1100624 1103591 := bstep (se 1 (by rfl) ⟨827693, by rfl⟩ : syracuseStep 1103591 = 1655387) B1655387
theorem B1103975 : Blo 1100624 1103975 := bstep (se 1 (by rfl) ⟨827981, by rfl⟩ : syracuseStep 1103975 = 1655963) B1655963
theorem B3135611 : Blo 1100624 3135611 := bstep (se 1 (by rfl) ⟨2351708, by rfl⟩ : syracuseStep 3135611 = 4703417) B4703417
theorem B11327635 : Blo 1100624 11327635 := bstep (se 1 (by rfl) ⟨8495726, by rfl⟩ : syracuseStep 11327635 = 16991453) B16991453
theorem B2480903 : Blo 1100624 2480903 := bstep (se 1 (by rfl) ⟨1860677, by rfl⟩ : syracuseStep 2480903 = 3721355) B3721355
theorem B2480993 : Blo 1100624 2480993 := bstep (se 2 (by rfl) ⟨930372, by rfl⟩ : syracuseStep 2480993 = 1860745) B1860745
theorem B68017067 : Blo 1100624 68017067 := bstep (se 1 (by rfl) ⟨51012800, by rfl⟩ : syracuseStep 68017067 = 102025601) B102025601
theorem B3726431 : Blo 1100624 3726431 := bstep (se 1 (by rfl) ⟨2794823, by rfl⟩ : syracuseStep 3726431 = 5589647) B5589647
theorem B2481263 : Blo 1100624 2481263 := bstep (se 1 (by rfl) ⟨1860947, by rfl⟩ : syracuseStep 2481263 = 3721895) B3721895
theorem B3726647 : Blo 1100624 3726647 := bstep (se 1 (by rfl) ⟨2794985, by rfl⟩ : syracuseStep 3726647 = 5589971) B5589971
theorem B149118317 : Blo 1100624 149118317 := bstep (se 3 (by rfl) ⟨27959684, by rfl⟩ : syracuseStep 149118317 = 55919369) B55919369
theorem B47635937 : Blo 1100624 47635937 := bstep (se 2 (by rfl) ⟨17863476, by rfl⟩ : syracuseStep 47635937 = 35726953) B35726953
theorem B7954085 : Blo 1100624 7954085 := bstep (se 4 (by rfl) ⟨745695, by rfl⟩ : syracuseStep 7954085 = 1491391) B1491391
theorem B2482415 : Blo 1100624 2482415 := bstep (se 1 (by rfl) ⟨1861811, by rfl⟩ : syracuseStep 2482415 = 3723623) B3723623
theorem B1860347 : Blo 1100624 1860347 := bstep (se 1 (by rfl) ⟨1395260, by rfl⟩ : syracuseStep 1860347 = 2790521) B2790521
theorem B4711193 : Blo 1100624 4711193 := bstep (se 2 (by rfl) ⟨1766697, by rfl⟩ : syracuseStep 4711193 = 3533395) B3533395
theorem B4187483 : Blo 1100624 4187483 := bstep (se 1 (by rfl) ⟨3140612, by rfl⟩ : syracuseStep 4187483 = 6281225) B6281225
theorem B1238575 : Blo 1100624 1238575 := bstep (se 1 (by rfl) ⟨928931, by rfl⟩ : syracuseStep 1238575 = 1857863) B1857863
theorem B35382923 : Blo 1100624 35382923 := bstep (se 1 (by rfl) ⟨26537192, by rfl⟩ : syracuseStep 35382923 = 53074385) B53074385
theorem B1239151 : Blo 1100624 1239151 := bstep (se 1 (by rfl) ⟨929363, by rfl⟩ : syracuseStep 1239151 = 1858727) B1858727
theorem B2091167 : Blo 1100624 2091167 := bstep (se 1 (by rfl) ⟨1568375, by rfl⟩ : syracuseStep 2091167 = 3136751) B3136751
theorem B57239743 : Blo 1100624 57239743 := bstep (se 1 (by rfl) ⟨42929807, by rfl⟩ : syracuseStep 57239743 = 85859615) B85859615
theorem B5957867 : Blo 1100624 5957867 := bstep (se 1 (by rfl) ⟨4468400, by rfl⟩ : syracuseStep 5957867 = 8936801) B8936801
theorem B4188455 : Blo 1100624 4188455 := bstep (se 1 (by rfl) ⟨3141341, by rfl⟩ : syracuseStep 4188455 = 6282683) B6282683
theorem B10578383 : Blo 1100624 10578383 := bstep (se 1 (by rfl) ⟨7933787, by rfl⟩ : syracuseStep 10578383 = 15867575) B15867575
theorem B2484827 : Blo 1100624 2484827 := bstep (se 1 (by rfl) ⟨1863620, by rfl⟩ : syracuseStep 2484827 = 3727241) B3727241
theorem B1862939 : Blo 1100624 1862939 := bstep (se 1 (by rfl) ⟨1397204, by rfl⟩ : syracuseStep 1862939 = 2794409) B2794409
theorem B14151257 : Blo 1100624 14151257 := bstep (se 2 (by rfl) ⟨5306721, by rfl⟩ : syracuseStep 14151257 = 10613443) B10613443
theorem B36302681 : Blo 1100624 36302681 := bstep (se 2 (by rfl) ⟨13613505, by rfl⟩ : syracuseStep 36302681 = 27227011) B27227011
theorem B1241311 : Blo 1100624 1241311 := bstep (se 1 (by rfl) ⟨930983, by rfl⟩ : syracuseStep 1241311 = 1861967) B1861967
theorem B3535073 : Blo 1100624 3535073 := bstep (se 2 (by rfl) ⟨1325652, by rfl⟩ : syracuseStep 3535073 = 2651305) B2651305
theorem B12579623 : Blo 1100624 12579623 := bstep (se 1 (by rfl) ⟨9434717, by rfl⟩ : syracuseStep 12579623 = 18869435) B18869435
theorem B12581081 : Blo 1100624 12581081 := bstep (se 2 (by rfl) ⟨4717905, by rfl⟩ : syracuseStep 12581081 = 9435811) B9435811
theorem B3537533 : Blo 1100624 3537533 := bstep (se 3 (by rfl) ⟨663287, by rfl⟩ : syracuseStep 3537533 = 1326575) B1326575
theorem B20151017 : Blo 1100624 20151017 := bstep (se 2 (by rfl) ⟨7556631, by rfl⟩ : syracuseStep 20151017 = 15113263) B15113263
theorem B21167837 : Blo 1100624 21167837 := bstep (se 3 (by rfl) ⟨3968969, by rfl⟩ : syracuseStep 21167837 = 7937939) B7937939
theorem B5308183 : Blo 1100624 5308183 := bstep (se 1 (by rfl) ⟨3981137, by rfl⟩ : syracuseStep 5308183 = 7962275) B7962275
theorem B5572475 : Blo 1100624 5572475 := bstep (se 1 (by rfl) ⟨4179356, by rfl⟩ : syracuseStep 5572475 = 8358713) B8358713
theorem B76319657 : Blo 1100624 76319657 := bstep (se 2 (by rfl) ⟨28619871, by rfl⟩ : syracuseStep 76319657 = 57239743) B57239743
theorem B22645907 : Blo 1100624 22645907 := bstep (se 1 (by rfl) ⟨16984430, by rfl⟩ : syracuseStep 22645907 = 33968861) B33968861
theorem B1674751 : Blo 1100624 1674751 := bstep (se 1 (by rfl) ⟨1256063, by rfl⟩ : syracuseStep 1674751 = 2512127) B2512127
theorem B14520653 : Blo 1100624 14520653 := bstep (se 3 (by rfl) ⟨2722622, by rfl⟩ : syracuseStep 14520653 = 5445245) B5445245
theorem B31757291 : Blo 1100624 31757291 := bstep (se 1 (by rfl) ⟨23817968, by rfl⟩ : syracuseStep 31757291 = 47635937) B47635937
theorem B8361629 : Blo 1100624 8361629 := bstep (se 3 (by rfl) ⟨1567805, by rfl⟩ : syracuseStep 8361629 = 3135611) B3135611
theorem B2791655 : Blo 1100624 2791655 := bstep (se 1 (by rfl) ⟨2093741, by rfl⟩ : syracuseStep 2791655 = 4187483) B4187483
theorem B2234687 : Blo 1100624 2234687 := bstep (se 1 (by rfl) ⟨1676015, by rfl⟩ : syracuseStep 2234687 = 3352031) B3352031
theorem B21502775 : Blo 1100624 21502775 := bstep (se 1 (by rfl) ⟨16127081, by rfl⟩ : syracuseStep 21502775 = 32254163) B32254163
theorem B3971911 : Blo 1100624 3971911 := bstep (se 1 (by rfl) ⟨2978933, by rfl⟩ : syracuseStep 3971911 = 5957867) B5957867
theorem B2792303 : Blo 1100624 2792303 := bstep (se 1 (by rfl) ⟨2094227, by rfl⟩ : syracuseStep 2792303 = 4188455) B4188455
theorem B7052255 : Blo 1100624 7052255 := bstep (se 1 (by rfl) ⟨5289191, by rfl⟩ : syracuseStep 7052255 = 10578383) B10578383
theorem B5577983 : Blo 1100624 5577983 := bstep (se 1 (by rfl) ⟨4183487, by rfl⟩ : syracuseStep 5577983 = 8366975) B8366975
theorem B11935279 : Blo 1100624 11935279 := bstep (se 1 (by rfl) ⟨8951459, by rfl⟩ : syracuseStep 11935279 = 17902919) B17902919
theorem B21210893 : Blo 1100624 21210893 := bstep (se 3 (by rfl) ⟨3977042, by rfl⟩ : syracuseStep 21210893 = 7954085) B7954085
theorem B6039593 : Blo 1100624 6039593 := bstep (se 2 (by rfl) ⟨2264847, by rfl⟩ : syracuseStep 6039593 = 4529695) B4529695
theorem B434383307 : Blo 1100624 434383307 := bstep (se 1 (by rfl) ⟨325787480, by rfl⟩ : syracuseStep 434383307 = 651574961) B651574961
theorem B14135471 : Blo 1100624 14135471 := bstep (se 1 (by rfl) ⟨10601603, by rfl⟩ : syracuseStep 14135471 = 21203207) B21203207
theorem B1650983 : Blo 1100624 1650983 := bstep (se 1 (by rfl) ⟨1238237, by rfl⟩ : syracuseStep 1650983 = 2476475) B2476475
theorem B101724821 : Blo 1100624 101724821 := bstep (se 6 (by rfl) ⟨2384175, by rfl⟩ : syracuseStep 101724821 = 4768351) B4768351
theorem B1651433 : Blo 1100624 1651433 := bstep (se 2 (by rfl) ⟨619287, by rfl⟩ : syracuseStep 1651433 = 1238575) B1238575
theorem B6271769 : Blo 1100624 6271769 := bstep (se 2 (by rfl) ⟨2351913, by rfl⟩ : syracuseStep 6271769 = 4703827) B4703827
theorem B1651547 : Blo 1100624 1651547 := bstep (se 1 (by rfl) ⟨1238660, by rfl⟩ : syracuseStep 1651547 = 2477321) B2477321
theorem B1652201 : Blo 1100624 1652201 := bstep (se 2 (by rfl) ⟨619575, by rfl⟩ : syracuseStep 1652201 = 1239151) B1239151
theorem B5584463 : Blo 1100624 5584463 := bstep (se 1 (by rfl) ⟨4188347, by rfl⟩ : syracuseStep 5584463 = 8376695) B8376695
theorem B1652327 : Blo 1100624 1652327 := bstep (se 1 (by rfl) ⟨1239245, by rfl⟩ : syracuseStep 1652327 = 2478491) B2478491
theorem B1653047 : Blo 1100624 1653047 := bstep (se 1 (by rfl) ⟨1239785, by rfl⟩ : syracuseStep 1653047 = 2479571) B2479571
theorem B1882919 : Blo 1100624 1882919 := bstep (se 1 (by rfl) ⟨1412189, by rfl⟩ : syracuseStep 1882919 = 2824379) B2824379
theorem B3718169 : Blo 1100624 3718169 := bstep (se 2 (by rfl) ⟨1394313, by rfl⟩ : syracuseStep 3718169 = 2788627) B2788627
theorem B1653935 : Blo 1100624 1653935 := bstep (se 1 (by rfl) ⟨1240451, by rfl⟩ : syracuseStep 1653935 = 2480903) B2480903
theorem B1653995 : Blo 1100624 1653995 := bstep (se 1 (by rfl) ⟨1240496, by rfl⟩ : syracuseStep 1653995 = 2480993) B2480993
theorem B1654175 : Blo 1100624 1654175 := bstep (se 1 (by rfl) ⟨1240631, by rfl⟩ : syracuseStep 1654175 = 2481263) B2481263
theorem B1883903 : Blo 1100624 1883903 := bstep (se 1 (by rfl) ⟨1412927, by rfl⟩ : syracuseStep 1883903 = 2825855) B2825855
theorem B4702187 : Blo 1100624 4702187 := bstep (se 1 (by rfl) ⟨3526640, by rfl⟩ : syracuseStep 4702187 = 7053281) B7053281
theorem B1654943 : Blo 1100624 1654943 := bstep (se 1 (by rfl) ⟨1241207, by rfl⟩ : syracuseStep 1654943 = 2482415) B2482415
theorem B1655081 : Blo 1100624 1655081 := bstep (se 2 (by rfl) ⟨620655, by rfl⟩ : syracuseStep 1655081 = 1241311) B1241311
theorem B3720329 : Blo 1100624 3720329 := bstep (se 2 (by rfl) ⟨1395123, by rfl⟩ : syracuseStep 3720329 = 2790247) B2790247
theorem B1394111 : Blo 1100624 1394111 := bstep (se 1 (by rfl) ⟨1045583, by rfl⟩ : syracuseStep 1394111 = 2091167) B2091167
theorem B1656551 : Blo 1100624 1656551 := bstep (se 1 (by rfl) ⟨1242413, by rfl⟩ : syracuseStep 1656551 = 2484827) B2484827
theorem B3721031 : Blo 1100624 3721031 := bstep (se 1 (by rfl) ⟨2790773, by rfl⟩ : syracuseStep 3721031 = 5581547) B5581547
theorem B24201787 : Blo 1100624 24201787 := bstep (se 1 (by rfl) ⟨18151340, by rfl⟩ : syracuseStep 24201787 = 36302681) B36302681
theorem B1100711 : Blo 1100624 1100711 := bstep (se 1 (by rfl) ⟨825533, by rfl⟩ : syracuseStep 1100711 = 1651067) B1651067
theorem B1100927 : Blo 1100624 1100927 := bstep (se 1 (by rfl) ⟨825695, by rfl⟩ : syracuseStep 1100927 = 1651391) B1651391
theorem B1101055 : Blo 1100624 1101055 := bstep (se 1 (by rfl) ⟨825791, by rfl⟩ : syracuseStep 1101055 = 1651583) B1651583
theorem B1101659 : Blo 1100624 1101659 := bstep (se 1 (by rfl) ⟨826244, by rfl⟩ : syracuseStep 1101659 = 1652489) B1652489
theorem B4771871 : Blo 1100624 4771871 := bstep (se 1 (by rfl) ⟨3578903, by rfl⟩ : syracuseStep 4771871 = 7157807) B7157807
theorem B5165147 : Blo 1100624 5165147 := bstep (se 1 (by rfl) ⟨3873860, by rfl⟩ : syracuseStep 5165147 = 7747721) B7747721
theorem B6049937 : Blo 1100624 6049937 := bstep (se 2 (by rfl) ⟨2268726, by rfl⟩ : syracuseStep 6049937 = 4537453) B4537453
theorem B1102047 : Blo 1100624 1102047 := bstep (se 1 (by rfl) ⟨826535, by rfl⟩ : syracuseStep 1102047 = 1653071) B1653071
theorem B1102075 : Blo 1100624 1102075 := bstep (se 1 (by rfl) ⟨826556, by rfl⟩ : syracuseStep 1102075 = 1653113) B1653113
theorem B1102491 : Blo 1100624 1102491 := bstep (se 1 (by rfl) ⟨826868, by rfl⟩ : syracuseStep 1102491 = 1653737) B1653737
theorem B1102543 : Blo 1100624 1102543 := bstep (se 1 (by rfl) ⟨826907, by rfl⟩ : syracuseStep 1102543 = 1653815) B1653815
theorem B1102575 : Blo 1100624 1102575 := bstep (se 1 (by rfl) ⟨826931, by rfl⟩ : syracuseStep 1102575 = 1653863) B1653863
theorem B4183123 : Blo 1100624 4183123 := bstep (se 1 (by rfl) ⟨3137342, by rfl⟩ : syracuseStep 4183123 = 6274685) B6274685
theorem B14111891 : Blo 1100624 14111891 := bstep (se 1 (by rfl) ⟨10583918, by rfl⟩ : syracuseStep 14111891 = 21167837) B21167837
theorem B1103231 : Blo 1100624 1103231 := bstep (se 1 (by rfl) ⟨827423, by rfl⟩ : syracuseStep 1103231 = 1654847) B1654847
theorem B3725081 : Blo 1100624 3725081 := bstep (se 2 (by rfl) ⟨1396905, by rfl⟩ : syracuseStep 3725081 = 2793811) B2793811
theorem B1103743 : Blo 1100624 1103743 := bstep (se 1 (by rfl) ⟨827807, by rfl⟩ : syracuseStep 1103743 = 1655615) B1655615
theorem B1857647 : Blo 1100624 1857647 := bstep (se 1 (by rfl) ⟨1393235, by rfl⟩ : syracuseStep 1857647 = 2786471) B2786471
theorem B1857775 : Blo 1100624 1857775 := bstep (se 1 (by rfl) ⟨1393331, by rfl⟩ : syracuseStep 1857775 = 2786663) B2786663
theorem B2481695 : Blo 1100624 2481695 := bstep (se 1 (by rfl) ⟨1861271, by rfl⟩ : syracuseStep 2481695 = 3722543) B3722543
theorem B3727187 : Blo 1100624 3727187 := bstep (se 1 (by rfl) ⟨2795390, by rfl⟩ : syracuseStep 3727187 = 5590781) B5590781
theorem B2482451 : Blo 1100624 2482451 := bstep (se 1 (by rfl) ⟨1861838, by rfl⟩ : syracuseStep 2482451 = 3723677) B3723677
theorem B38691703 : Blo 1100624 38691703 := bstep (se 1 (by rfl) ⟨29018777, by rfl⟩ : syracuseStep 38691703 = 58037555) B58037555
theorem B45344711 : Blo 1100624 45344711 := bstep (se 1 (by rfl) ⟨34008533, by rfl⟩ : syracuseStep 45344711 = 68017067) B68017067
theorem B1861609 : Blo 1100624 1861609 := bstep (se 2 (by rfl) ⟨698103, by rfl⟩ : syracuseStep 1861609 = 1396207) B1396207
theorem B2484287 : Blo 1100624 2484287 := bstep (se 1 (by rfl) ⟨1863215, by rfl⟩ : syracuseStep 2484287 = 3726431) B3726431
theorem B2484431 : Blo 1100624 2484431 := bstep (se 1 (by rfl) ⟨1863323, by rfl⟩ : syracuseStep 2484431 = 3726647) B3726647
theorem B99412211 : Blo 1100624 99412211 := bstep (se 1 (by rfl) ⟨74559158, by rfl⟩ : syracuseStep 99412211 = 149118317) B149118317
theorem B1862399 : Blo 1100624 1862399 := bstep (se 1 (by rfl) ⟨1396799, by rfl⟩ : syracuseStep 1862399 = 2793599) B2793599
theorem B1240231 : Blo 1100624 1240231 := bstep (se 1 (by rfl) ⟨930173, by rfl⟩ : syracuseStep 1240231 = 1860347) B1860347
theorem B3140795 : Blo 1100624 3140795 := bstep (se 1 (by rfl) ⟨2355596, by rfl⟩ : syracuseStep 3140795 = 4711193) B4711193
theorem B1863337 : Blo 1100624 1863337 := bstep (se 2 (by rfl) ⟨698751, by rfl⟩ : syracuseStep 1863337 = 1397503) B1397503
theorem B23588615 : Blo 1100624 23588615 := bstep (se 1 (by rfl) ⟨17691461, by rfl⟩ : syracuseStep 23588615 = 35382923) B35382923
theorem B9433421 : Blo 1100624 9433421 := bstep (se 3 (by rfl) ⟨1768766, by rfl⟩ : syracuseStep 9433421 = 3537533) B3537533
theorem B1274395 : Blo 1100624 1274395 := bstep (se 1 (by rfl) ⟨955796, by rfl⟩ : syracuseStep 1274395 = 1911593) B1911593
theorem B551580299 : Blo 1100624 551580299 := bstep (se 1 (by rfl) ⟨413685224, by rfl⟩ : syracuseStep 551580299 = 827370449) B827370449
theorem B1241959 : Blo 1100624 1241959 := bstep (se 1 (by rfl) ⟨931469, by rfl⟩ : syracuseStep 1241959 = 1862939) B1862939
theorem B9434171 : Blo 1100624 9434171 := bstep (se 1 (by rfl) ⟨7075628, by rfl⟩ : syracuseStep 9434171 = 14151257) B14151257
theorem B2356715 : Blo 1100624 2356715 := bstep (se 1 (by rfl) ⟨1767536, by rfl⟩ : syracuseStep 2356715 = 3535073) B3535073
theorem B15103513 : Blo 1100624 15103513 := bstep (se 2 (by rfl) ⟨5663817, by rfl⟩ : syracuseStep 15103513 = 11327635) B11327635
theorem B8386415 : Blo 1100624 8386415 := bstep (se 1 (by rfl) ⟨6289811, by rfl⟩ : syracuseStep 8386415 = 12579623) B12579623
theorem B14121323 : Blo 1100624 14121323 := bstep (se 1 (by rfl) ⟨10590992, by rfl⟩ : syracuseStep 14121323 = 21181985) B21181985
theorem B8387387 : Blo 1100624 8387387 := bstep (se 1 (by rfl) ⟨6290540, by rfl⟩ : syracuseStep 8387387 = 12581081) B12581081
theorem B13434011 : Blo 1100624 13434011 := bstep (se 1 (by rfl) ⟨10075508, by rfl⟩ : syracuseStep 13434011 = 20151017) B20151017
theorem B7077577 : Blo 1100624 7077577 := bstep (se 2 (by rfl) ⟨2654091, by rfl⟩ : syracuseStep 7077577 = 5308183) B5308183
theorem B3181247 : Blo 1100624 3181247 := bstep (se 1 (by rfl) ⟨2385935, by rfl⟩ : syracuseStep 3181247 = 4771871) B4771871
theorem B21171527 : Blo 1100624 21171527 := bstep (se 1 (by rfl) ⟨15878645, by rfl⟩ : syracuseStep 21171527 = 31757291) B31757291
theorem B9407927 : Blo 1100624 9407927 := bstep (se 1 (by rfl) ⟨7055945, by rfl⟩ : syracuseStep 9407927 = 14111891) B14111891
theorem B5574419 : Blo 1100624 5574419 := bstep (se 1 (by rfl) ⟨4180814, by rfl⟩ : syracuseStep 5574419 = 8361629) B8361629
theorem B2233001 : Blo 1100624 2233001 := bstep (se 2 (by rfl) ⟨837375, by rfl⟩ : syracuseStep 2233001 = 1674751) B1674751
theorem B5577497 : Blo 1100624 5577497 := bstep (se 2 (by rfl) ⟨2091561, by rfl⟩ : syracuseStep 5577497 = 4183123) B4183123
theorem B9414215 : Blo 1100624 9414215 := bstep (se 1 (by rfl) ⟨7060661, by rfl⟩ : syracuseStep 9414215 = 14121323) B14121323
theorem B1255279 : Blo 1100624 1255279 := bstep (se 1 (by rfl) ⟨941459, by rfl⟩ : syracuseStep 1255279 = 1882919) B1882919
theorem B5023741 : Blo 1100624 5023741 := bstep (se 3 (by rfl) ⟨941951, by rfl⟩ : syracuseStep 5023741 = 1883903) B1883903
theorem B8956007 : Blo 1100624 8956007 := bstep (se 1 (by rfl) ⟨6717005, by rfl⟩ : syracuseStep 8956007 = 13434011) B13434011
theorem B13773725 : Blo 1100624 13773725 := bstep (se 3 (by rfl) ⟨2582573, by rfl⟩ : syracuseStep 13773725 = 5165147) B5165147
theorem B16133165 : Blo 1100624 16133165 := bstep (se 3 (by rfl) ⟨3024968, by rfl⟩ : syracuseStep 16133165 = 6049937) B6049937
theorem B51588937 : Blo 1100624 51588937 := bstep (se 2 (by rfl) ⟨19345851, by rfl⟩ : syracuseStep 51588937 = 38691703) B38691703
theorem B3714983 : Blo 1100624 3714983 := bstep (se 1 (by rfl) ⟨2786237, by rfl⟩ : syracuseStep 3714983 = 5572475) B5572475
theorem B9680435 : Blo 1100624 9680435 := bstep (se 1 (by rfl) ⟨7260326, by rfl⟩ : syracuseStep 9680435 = 14520653) B14520653
theorem B3717629 : Blo 1100624 3717629 := bstep (se 3 (by rfl) ⟨697055, by rfl⟩ : syracuseStep 3717629 = 1394111) B1394111
theorem B1653641 : Blo 1100624 1653641 := bstep (se 2 (by rfl) ⟨620115, by rfl⟩ : syracuseStep 1653641 = 1240231) B1240231
theorem B14335183 : Blo 1100624 14335183 := bstep (se 1 (by rfl) ⟨10751387, by rfl⟩ : syracuseStep 14335183 = 21502775) B21502775
theorem B4701503 : Blo 1100624 4701503 := bstep (se 1 (by rfl) ⟨3526127, by rfl⟩ : syracuseStep 4701503 = 7052255) B7052255
theorem B3718655 : Blo 1100624 3718655 := bstep (se 1 (by rfl) ⟨2788991, by rfl⟩ : syracuseStep 3718655 = 5577983) B5577983
theorem B1654463 : Blo 1100624 1654463 := bstep (se 1 (by rfl) ⟨1240847, by rfl⟩ : syracuseStep 1654463 = 2481695) B2481695
theorem B1654967 : Blo 1100624 1654967 := bstep (se 1 (by rfl) ⟨1241225, by rfl⟩ : syracuseStep 1654967 = 2482451) B2482451
theorem B1655945 : Blo 1100624 1655945 := bstep (se 2 (by rfl) ⟨620979, by rfl⟩ : syracuseStep 1655945 = 1241959) B1241959
theorem B14140595 : Blo 1100624 14140595 := bstep (se 1 (by rfl) ⟨10605446, by rfl⟩ : syracuseStep 14140595 = 21210893) B21210893
theorem B30229807 : Blo 1100624 30229807 := bstep (se 1 (by rfl) ⟨22672355, by rfl⟩ : syracuseStep 30229807 = 45344711) B45344711
theorem B1656191 : Blo 1100624 1656191 := bstep (se 1 (by rfl) ⟨1242143, by rfl⟩ : syracuseStep 1656191 = 2484287) B2484287
theorem B1656287 : Blo 1100624 1656287 := bstep (se 1 (by rfl) ⟨1242215, by rfl⟩ : syracuseStep 1656287 = 2484431) B2484431
theorem B66274807 : Blo 1100624 66274807 := bstep (se 1 (by rfl) ⟨49706105, by rfl⟩ : syracuseStep 66274807 = 99412211) B99412211
theorem B289588871 : Blo 1100624 289588871 := bstep (se 1 (by rfl) ⟨217191653, by rfl⟩ : syracuseStep 289588871 = 434383307) B434383307
theorem B20138017 : Blo 1100624 20138017 := bstep (se 2 (by rfl) ⟨7551756, by rfl⟩ : syracuseStep 20138017 = 15103513) B15103513
theorem B9423647 : Blo 1100624 9423647 := bstep (se 1 (by rfl) ⟨7067735, by rfl⟩ : syracuseStep 9423647 = 14135471) B14135471
theorem B1100655 : Blo 1100624 1100655 := bstep (se 1 (by rfl) ⟨825491, by rfl⟩ : syracuseStep 1100655 = 1650983) B1650983
theorem B63654821 : Blo 1100624 63654821 := bstep (se 4 (by rfl) ⟨5967639, by rfl⟩ : syracuseStep 63654821 = 11935279) B11935279
theorem B2477033 : Blo 1100624 2477033 := bstep (se 2 (by rfl) ⟨928887, by rfl⟩ : syracuseStep 2477033 = 1857775) B1857775
theorem B67816547 : Blo 1100624 67816547 := bstep (se 1 (by rfl) ⟨50862410, by rfl⟩ : syracuseStep 67816547 = 101724821) B101724821
theorem B1100955 : Blo 1100624 1100955 := bstep (se 1 (by rfl) ⟨825716, by rfl⟩ : syracuseStep 1100955 = 1651433) B1651433
theorem B4181179 : Blo 1100624 4181179 := bstep (se 1 (by rfl) ⟨3135884, by rfl⟩ : syracuseStep 4181179 = 6271769) B6271769
theorem B1101031 : Blo 1100624 1101031 := bstep (se 1 (by rfl) ⟨825773, by rfl⟩ : syracuseStep 1101031 = 1651547) B1651547
theorem B1101467 : Blo 1100624 1101467 := bstep (se 1 (by rfl) ⟨826100, by rfl⟩ : syracuseStep 1101467 = 1652201) B1652201
theorem B3722975 : Blo 1100624 3722975 := bstep (se 1 (by rfl) ⟨2792231, by rfl⟩ : syracuseStep 3722975 = 5584463) B5584463
theorem B1101551 : Blo 1100624 1101551 := bstep (se 1 (by rfl) ⟨826163, by rfl⟩ : syracuseStep 1101551 = 1652327) B1652327
theorem B5295881 : Blo 1100624 5295881 := bstep (se 2 (by rfl) ⟨1985955, by rfl⟩ : syracuseStep 5295881 = 3971911) B3971911
theorem B5590943 : Blo 1100624 5590943 := bstep (se 1 (by rfl) ⟨4193207, by rfl⟩ : syracuseStep 5590943 = 8386415) B8386415
theorem B1102031 : Blo 1100624 1102031 := bstep (se 1 (by rfl) ⟨826523, by rfl⟩ : syracuseStep 1102031 = 1653047) B1653047
theorem B5591591 : Blo 1100624 5591591 := bstep (se 1 (by rfl) ⟨4193693, by rfl⟩ : syracuseStep 5591591 = 8387387) B8387387
theorem B2478779 : Blo 1100624 2478779 := bstep (se 1 (by rfl) ⟨1859084, by rfl⟩ : syracuseStep 2478779 = 3718169) B3718169
theorem B62902973 : Blo 1100624 62902973 := bstep (se 3 (by rfl) ⟨11794307, by rfl⟩ : syracuseStep 62902973 = 23588615) B23588615
theorem B1102623 : Blo 1100624 1102623 := bstep (se 1 (by rfl) ⟨826967, by rfl⟩ : syracuseStep 1102623 = 1653935) B1653935
theorem B1102663 : Blo 1100624 1102663 := bstep (se 1 (by rfl) ⟨826997, by rfl⟩ : syracuseStep 1102663 = 1653995) B1653995
theorem B1102783 : Blo 1100624 1102783 := bstep (se 1 (by rfl) ⟨827087, by rfl⟩ : syracuseStep 1102783 = 1654175) B1654175
theorem B3134791 : Blo 1100624 3134791 := bstep (se 1 (by rfl) ⟨2351093, by rfl⟩ : syracuseStep 3134791 = 4702187) B4702187
theorem B1103295 : Blo 1100624 1103295 := bstep (se 1 (by rfl) ⟨827471, by rfl⟩ : syracuseStep 1103295 = 1654943) B1654943
theorem B1103387 : Blo 1100624 1103387 := bstep (se 1 (by rfl) ⟨827540, by rfl⟩ : syracuseStep 1103387 = 1655081) B1655081
theorem B2480219 : Blo 1100624 2480219 := bstep (se 1 (by rfl) ⟨1860164, by rfl⟩ : syracuseStep 2480219 = 3720329) B3720329
theorem B1104367 : Blo 1100624 1104367 := bstep (se 1 (by rfl) ⟨828275, by rfl⟩ : syracuseStep 1104367 = 1656551) B1656551
theorem B2480687 : Blo 1100624 2480687 := bstep (se 1 (by rfl) ⟨1860515, by rfl⟩ : syracuseStep 2480687 = 3721031) B3721031
theorem B50879771 : Blo 1100624 50879771 := bstep (se 1 (by rfl) ⟨38159828, by rfl⟩ : syracuseStep 50879771 = 76319657) B76319657
theorem B15097271 : Blo 1100624 15097271 := bstep (se 1 (by rfl) ⟨11322953, by rfl⟩ : syracuseStep 15097271 = 22645907) B22645907
theorem B2482145 : Blo 1100624 2482145 := bstep (se 2 (by rfl) ⟨930804, by rfl⟩ : syracuseStep 2482145 = 1861609) B1861609
theorem B32269049 : Blo 1100624 32269049 := bstep (se 2 (by rfl) ⟨12100893, by rfl⟩ : syracuseStep 32269049 = 24201787) B24201787
theorem B2483387 : Blo 1100624 2483387 := bstep (se 1 (by rfl) ⟨1862540, by rfl⟩ : syracuseStep 2483387 = 3725081) B3725081
theorem B6284573 : Blo 1100624 6284573 := bstep (se 3 (by rfl) ⟨1178357, by rfl⟩ : syracuseStep 6284573 = 2356715) B2356715
theorem B1238431 : Blo 1100624 1238431 := bstep (se 1 (by rfl) ⟨928823, by rfl⟩ : syracuseStep 1238431 = 1857647) B1857647
theorem B1861103 : Blo 1100624 1861103 := bstep (se 1 (by rfl) ⟨1395827, by rfl⟩ : syracuseStep 1861103 = 2791655) B2791655
theorem B1861535 : Blo 1100624 1861535 := bstep (se 1 (by rfl) ⟨1396151, by rfl⟩ : syracuseStep 1861535 = 2792303) B2792303
theorem B2484449 : Blo 1100624 2484449 := bstep (se 2 (by rfl) ⟨931668, by rfl⟩ : syracuseStep 2484449 = 1863337) B1863337
theorem B2484791 : Blo 1100624 2484791 := bstep (se 1 (by rfl) ⟨1863593, by rfl⟩ : syracuseStep 2484791 = 3727187) B3727187
theorem B1699193 : Blo 1100624 1699193 := bstep (se 2 (by rfl) ⟨637197, by rfl⟩ : syracuseStep 1699193 = 1274395) B1274395
theorem B5959165 : Blo 1100624 5959165 := bstep (se 3 (by rfl) ⟨1117343, by rfl⟩ : syracuseStep 5959165 = 2234687) B2234687
theorem B4026395 : Blo 1100624 4026395 := bstep (se 1 (by rfl) ⟨3019796, by rfl⟩ : syracuseStep 4026395 = 6039593) B6039593
theorem B1241599 : Blo 1100624 1241599 := bstep (se 1 (by rfl) ⟨931199, by rfl⟩ : syracuseStep 1241599 = 1862399) B1862399
theorem B2093863 : Blo 1100624 2093863 := bstep (se 1 (by rfl) ⟨1570397, by rfl⟩ : syracuseStep 2093863 = 3140795) B3140795
theorem B6288947 : Blo 1100624 6288947 := bstep (se 1 (by rfl) ⟨4716710, by rfl⟩ : syracuseStep 6288947 = 9433421) B9433421
theorem B367720199 : Blo 1100624 367720199 := bstep (se 1 (by rfl) ⟨275790149, by rfl⟩ : syracuseStep 367720199 = 551580299) B551580299
theorem B6289447 : Blo 1100624 6289447 := bstep (se 1 (by rfl) ⟨4717085, by rfl⟩ : syracuseStep 6289447 = 9434171) B9434171
theorem B9436769 : Blo 1100624 9436769 := bstep (se 2 (by rfl) ⟨3538788, by rfl⟩ : syracuseStep 9436769 = 7077577) B7077577
theorem B40306409 : Blo 1100624 40306409 := bstep (se 2 (by rfl) ⟨15114903, by rfl⟩ : syracuseStep 40306409 = 30229807) B30229807
theorem B42436547 : Blo 1100624 42436547 := bstep (se 1 (by rfl) ⟨31827410, by rfl⟩ : syracuseStep 42436547 = 63654821) B63654821
theorem B1673705 : Blo 1100624 1673705 := bstep (se 2 (by rfl) ⟨627639, by rfl⟩ : syracuseStep 1673705 = 1255279) B1255279
theorem B5574905 : Blo 1100624 5574905 := bstep (se 2 (by rfl) ⟨2090589, by rfl⟩ : syracuseStep 5574905 = 4181179) B4181179
theorem B33919847 : Blo 1100624 33919847 := bstep (se 1 (by rfl) ⟨25439885, by rfl⟩ : syracuseStep 33919847 = 50879771) B50879771
theorem B68785249 : Blo 1100624 68785249 := bstep (se 2 (by rfl) ⟨25794468, by rfl⟩ : syracuseStep 68785249 = 51588937) B51588937
theorem B2791817 : Blo 1100624 2791817 := bstep (se 2 (by rfl) ⟨1046931, by rfl⟩ : syracuseStep 2791817 = 2093863) B2093863
theorem B5970671 : Blo 1100624 5970671 := bstep (se 1 (by rfl) ⟨4478003, by rfl⟩ : syracuseStep 5970671 = 8956007) B8956007
theorem B9182483 : Blo 1100624 9182483 := bstep (se 1 (by rfl) ⟨6886862, by rfl⟩ : syracuseStep 9182483 = 13773725) B13773725
theorem B10755443 : Blo 1100624 10755443 := bstep (se 1 (by rfl) ⟨8066582, by rfl⟩ : syracuseStep 10755443 = 16133165) B16133165
theorem B245146799 : Blo 1100624 245146799 := bstep (se 1 (by rfl) ⟨183860099, by rfl⟩ : syracuseStep 245146799 = 367720199) B367720199
theorem B19113577 : Blo 1100624 19113577 := bstep (se 2 (by rfl) ⟨7167591, by rfl⟩ : syracuseStep 19113577 = 14335183) B14335183
theorem B1651241 : Blo 1100624 1651241 := bstep (se 2 (by rfl) ⟨619215, by rfl⟩ : syracuseStep 1651241 = 1238431) B1238431
theorem B1651355 : Blo 1100624 1651355 := bstep (se 1 (by rfl) ⟨1238516, by rfl⟩ : syracuseStep 1651355 = 2477033) B2477033
theorem B6271951 : Blo 1100624 6271951 := bstep (se 1 (by rfl) ⟨4703963, by rfl⟩ : syracuseStep 6271951 = 9407927) B9407927
theorem B3716279 : Blo 1100624 3716279 := bstep (se 1 (by rfl) ⟨2787209, by rfl⟩ : syracuseStep 3716279 = 5574419) B5574419
theorem B6698321 : Blo 1100624 6698321 := bstep (se 2 (by rfl) ⟨2511870, by rfl⟩ : syracuseStep 6698321 = 5023741) B5023741
theorem B26850689 : Blo 1100624 26850689 := bstep (se 2 (by rfl) ⟨10069008, by rfl⟩ : syracuseStep 26850689 = 20138017) B20138017
theorem B1488667 : Blo 1100624 1488667 := bstep (se 1 (by rfl) ⟨1116500, by rfl⟩ : syracuseStep 1488667 = 2233001) B2233001
theorem B1652519 : Blo 1100624 1652519 := bstep (se 1 (by rfl) ⟨1239389, by rfl⟩ : syracuseStep 1652519 = 2478779) B2478779
theorem B1653479 : Blo 1100624 1653479 := bstep (se 1 (by rfl) ⟨1240109, by rfl⟩ : syracuseStep 1653479 = 2480219) B2480219
theorem B1653791 : Blo 1100624 1653791 := bstep (se 1 (by rfl) ⟨1240343, by rfl⟩ : syracuseStep 1653791 = 2480687) B2480687
theorem B3718331 : Blo 1100624 3718331 := bstep (se 1 (by rfl) ⟨2788748, by rfl⟩ : syracuseStep 3718331 = 5577497) B5577497
theorem B7945553 : Blo 1100624 7945553 := bstep (se 2 (by rfl) ⟨2979582, by rfl⟩ : syracuseStep 7945553 = 5959165) B5959165
theorem B1654763 : Blo 1100624 1654763 := bstep (se 1 (by rfl) ⟨1241072, by rfl⟩ : syracuseStep 1654763 = 2482145) B2482145
theorem B21512699 : Blo 1100624 21512699 := bstep (se 1 (by rfl) ⟨16134524, by rfl⟩ : syracuseStep 21512699 = 32269049) B32269049
theorem B1655465 : Blo 1100624 1655465 := bstep (se 2 (by rfl) ⟨620799, by rfl⟩ : syracuseStep 1655465 = 1241599) B1241599
theorem B1655591 : Blo 1100624 1655591 := bstep (se 1 (by rfl) ⟨1241693, by rfl⟩ : syracuseStep 1655591 = 2483387) B2483387
theorem B6276143 : Blo 1100624 6276143 := bstep (se 1 (by rfl) ⟨4707107, by rfl⟩ : syracuseStep 6276143 = 9414215) B9414215
theorem B1656299 : Blo 1100624 1656299 := bstep (se 1 (by rfl) ⟨1242224, by rfl⟩ : syracuseStep 1656299 = 2484449) B2484449
theorem B1656527 : Blo 1100624 1656527 := bstep (se 1 (by rfl) ⟨1242395, by rfl⟩ : syracuseStep 1656527 = 2484791) B2484791
theorem B4179721 : Blo 1100624 4179721 := bstep (se 2 (by rfl) ⟨1567395, by rfl⟩ : syracuseStep 4179721 = 3134791) B3134791
theorem B1132795 : Blo 1100624 1132795 := bstep (se 1 (by rfl) ⟨849596, by rfl⟩ : syracuseStep 1132795 = 1699193) B1699193
theorem B2476655 : Blo 1100624 2476655 := bstep (se 1 (by rfl) ⟨1857491, by rfl⟩ : syracuseStep 2476655 = 3714983) B3714983
theorem B12537341 : Blo 1100624 12537341 := bstep (se 3 (by rfl) ⟨2350751, by rfl⟩ : syracuseStep 12537341 = 4701503) B4701503
theorem B40259389 : Blo 1100624 40259389 := bstep (se 3 (by rfl) ⟨7548635, by rfl⟩ : syracuseStep 40259389 = 15097271) B15097271
theorem B2478419 : Blo 1100624 2478419 := bstep (se 1 (by rfl) ⟨1858814, by rfl⟩ : syracuseStep 2478419 = 3717629) B3717629
theorem B1102427 : Blo 1100624 1102427 := bstep (se 1 (by rfl) ⟨826820, by rfl⟩ : syracuseStep 1102427 = 1653641) B1653641
theorem B2479103 : Blo 1100624 2479103 := bstep (se 1 (by rfl) ⟨1859327, by rfl⟩ : syracuseStep 2479103 = 3718655) B3718655
theorem B1102975 : Blo 1100624 1102975 := bstep (se 1 (by rfl) ⟨827231, by rfl⟩ : syracuseStep 1102975 = 1654463) B1654463
theorem B1103311 : Blo 1100624 1103311 := bstep (se 1 (by rfl) ⟨827483, by rfl⟩ : syracuseStep 1103311 = 1654967) B1654967
theorem B1103963 : Blo 1100624 1103963 := bstep (se 1 (by rfl) ⟨827972, by rfl⟩ : syracuseStep 1103963 = 1655945) B1655945
theorem B9427063 : Blo 1100624 9427063 := bstep (se 1 (by rfl) ⟨7070297, by rfl⟩ : syracuseStep 9427063 = 14140595) B14140595
theorem B1104127 : Blo 1100624 1104127 := bstep (se 1 (by rfl) ⟨828095, by rfl⟩ : syracuseStep 1104127 = 1656191) B1656191
theorem B1104191 : Blo 1100624 1104191 := bstep (se 1 (by rfl) ⟨828143, by rfl⟩ : syracuseStep 1104191 = 1656287) B1656287
theorem B193059247 : Blo 1100624 193059247 := bstep (se 1 (by rfl) ⟨144794435, by rfl⟩ : syracuseStep 193059247 = 289588871) B289588871
theorem B2120831 : Blo 1100624 2120831 := bstep (se 1 (by rfl) ⟨1590623, by rfl⟩ : syracuseStep 2120831 = 3181247) B3181247
theorem B6282431 : Blo 1100624 6282431 := bstep (se 1 (by rfl) ⟨4711823, by rfl⟩ : syracuseStep 6282431 = 9423647) B9423647
theorem B88366409 : Blo 1100624 88366409 := bstep (se 2 (by rfl) ⟨33137403, by rfl⟩ : syracuseStep 88366409 = 66274807) B66274807
theorem B45211031 : Blo 1100624 45211031 := bstep (se 1 (by rfl) ⟨33908273, by rfl⟩ : syracuseStep 45211031 = 67816547) B67816547
theorem B14114351 : Blo 1100624 14114351 := bstep (se 1 (by rfl) ⟨10585763, by rfl⟩ : syracuseStep 14114351 = 21171527) B21171527
theorem B2481983 : Blo 1100624 2481983 := bstep (se 1 (by rfl) ⟨1861487, by rfl⟩ : syracuseStep 2481983 = 3722975) B3722975
theorem B3727295 : Blo 1100624 3727295 := bstep (se 1 (by rfl) ⟨2795471, by rfl⟩ : syracuseStep 3727295 = 5590943) B5590943
theorem B3727727 : Blo 1100624 3727727 := bstep (se 1 (by rfl) ⟨2795795, by rfl⟩ : syracuseStep 3727727 = 5591591) B5591591
theorem B41935315 : Blo 1100624 41935315 := bstep (se 1 (by rfl) ⟨31451486, by rfl⟩ : syracuseStep 41935315 = 62902973) B62902973
theorem B4189715 : Blo 1100624 4189715 := bstep (se 1 (by rfl) ⟨3142286, by rfl⟩ : syracuseStep 4189715 = 6284573) B6284573
theorem B1240735 : Blo 1100624 1240735 := bstep (se 1 (by rfl) ⟨930551, by rfl⟩ : syracuseStep 1240735 = 1861103) B1861103
theorem B1241023 : Blo 1100624 1241023 := bstep (se 1 (by rfl) ⟨930767, by rfl⟩ : syracuseStep 1241023 = 1861535) B1861535
theorem B2684263 : Blo 1100624 2684263 := bstep (se 1 (by rfl) ⟨2013197, by rfl⟩ : syracuseStep 2684263 = 4026395) B4026395
theorem B8385929 : Blo 1100624 8385929 := bstep (se 2 (by rfl) ⟨3144723, by rfl⟩ : syracuseStep 8385929 = 6289447) B6289447
theorem B6453623 : Blo 1100624 6453623 := bstep (se 1 (by rfl) ⟨4840217, by rfl⟩ : syracuseStep 6453623 = 9680435) B9680435
theorem B4192631 : Blo 1100624 4192631 := bstep (se 1 (by rfl) ⟨3144473, by rfl⟩ : syracuseStep 4192631 = 6288947) B6288947
theorem B14122349 : Blo 1100624 14122349 := bstep (se 3 (by rfl) ⟨2647940, by rfl⟩ : syracuseStep 14122349 = 5295881) B5295881
theorem B6291179 : Blo 1100624 6291179 := bstep (se 1 (by rfl) ⟨4718384, by rfl⟩ : syracuseStep 6291179 = 9436769) B9436769
theorem B26870939 : Blo 1100624 26870939 := bstep (se 1 (by rfl) ⟨20153204, by rfl⟩ : syracuseStep 26870939 = 40306409) B40306409
theorem B1115803 : Blo 1100624 1115803 := bstep (se 1 (by rfl) ⟨836852, by rfl⟩ : syracuseStep 1115803 = 1673705) B1673705
theorem B8358227 : Blo 1100624 8358227 := bstep (se 1 (by rfl) ⟨6268670, by rfl⟩ : syracuseStep 8358227 = 12537341) B12537341
theorem B5572961 : Blo 1100624 5572961 := bstep (se 2 (by rfl) ⟨2089860, by rfl⟩ : syracuseStep 5572961 = 4179721) B4179721
theorem B22613231 : Blo 1100624 22613231 := bstep (se 1 (by rfl) ⟨16959923, by rfl⟩ : syracuseStep 22613231 = 33919847) B33919847
theorem B1413887 : Blo 1100624 1413887 := bstep (se 1 (by rfl) ⟨1060415, by rfl⟩ : syracuseStep 1413887 = 2120831) B2120831
theorem B9409567 : Blo 1100624 9409567 := bstep (se 1 (by rfl) ⟨7057175, by rfl⟩ : syracuseStep 9409567 = 14114351) B14114351
theorem B53679185 : Blo 1100624 53679185 := bstep (se 2 (by rfl) ⟨20129694, by rfl⟩ : syracuseStep 53679185 = 40259389) B40259389
theorem B8362601 : Blo 1100624 8362601 := bstep (se 2 (by rfl) ⟨3135975, by rfl⟩ : syracuseStep 8362601 = 6271951) B6271951
theorem B3579017 : Blo 1100624 3579017 := bstep (se 2 (by rfl) ⟨1342131, by rfl⟩ : syracuseStep 3579017 = 2684263) B2684263
theorem B2793143 : Blo 1100624 2793143 := bstep (se 1 (by rfl) ⟨2094857, by rfl⟩ : syracuseStep 2793143 = 4189715) B4189715
theorem B4465547 : Blo 1100624 4465547 := bstep (se 1 (by rfl) ⟨3349160, by rfl⟩ : syracuseStep 4465547 = 6698321) B6698321
theorem B17900459 : Blo 1100624 17900459 := bstep (se 1 (by rfl) ⟨13425344, by rfl⟩ : syracuseStep 17900459 = 26850689) B26850689
theorem B4302415 : Blo 1100624 4302415 := bstep (se 1 (by rfl) ⟨3226811, by rfl⟩ : syracuseStep 4302415 = 6453623) B6453623
theorem B2795087 : Blo 1100624 2795087 := bstep (se 1 (by rfl) ⟨2096315, by rfl⟩ : syracuseStep 2795087 = 4192631) B4192631
theorem B9414899 : Blo 1100624 9414899 := bstep (se 1 (by rfl) ⟨7061174, by rfl⟩ : syracuseStep 9414899 = 14122349) B14122349
theorem B55913753 : Blo 1100624 55913753 := bstep (se 2 (by rfl) ⟨20967657, by rfl⟩ : syracuseStep 55913753 = 41935315) B41935315
theorem B28291031 : Blo 1100624 28291031 := bstep (se 1 (by rfl) ⟨21218273, by rfl⟩ : syracuseStep 28291031 = 42436547) B42436547
theorem B6041573 : Blo 1100624 6041573 := bstep (se 4 (by rfl) ⟨566397, by rfl⟩ : syracuseStep 6041573 = 1132795) B1132795
theorem B1651103 : Blo 1100624 1651103 := bstep (se 1 (by rfl) ⟨1238327, by rfl⟩ : syracuseStep 1651103 = 2476655) B2476655
theorem B3716603 : Blo 1100624 3716603 := bstep (se 1 (by rfl) ⟨2787452, by rfl⟩ : syracuseStep 3716603 = 5574905) B5574905
theorem B1652279 : Blo 1100624 1652279 := bstep (se 1 (by rfl) ⟨1239209, by rfl⟩ : syracuseStep 1652279 = 2478419) B2478419
theorem B1652735 : Blo 1100624 1652735 := bstep (se 1 (by rfl) ⟨1239551, by rfl⟩ : syracuseStep 1652735 = 2479103) B2479103
theorem B3980447 : Blo 1100624 3980447 := bstep (se 1 (by rfl) ⟨2985335, by rfl⟩ : syracuseStep 3980447 = 5970671) B5970671
theorem B1654313 : Blo 1100624 1654313 := bstep (se 2 (by rfl) ⟨620367, by rfl⟩ : syracuseStep 1654313 = 1240735) B1240735
theorem B1654655 : Blo 1100624 1654655 := bstep (se 1 (by rfl) ⟨1240991, by rfl⟩ : syracuseStep 1654655 = 2481983) B2481983
theorem B1654697 : Blo 1100624 1654697 := bstep (se 2 (by rfl) ⟨620511, by rfl⟩ : syracuseStep 1654697 = 1241023) B1241023
theorem B163431199 : Blo 1100624 163431199 := bstep (se 1 (by rfl) ⟨122573399, by rfl⟩ : syracuseStep 163431199 = 245146799) B245146799
theorem B1984889 : Blo 1100624 1984889 := bstep (se 2 (by rfl) ⟨744333, by rfl⟩ : syracuseStep 1984889 = 1488667) B1488667
theorem B12569417 : Blo 1100624 12569417 := bstep (se 2 (by rfl) ⟨4713531, by rfl⟩ : syracuseStep 12569417 = 9427063) B9427063
theorem B1100827 : Blo 1100624 1100827 := bstep (se 1 (by rfl) ⟨825620, by rfl⟩ : syracuseStep 1100827 = 1651241) B1651241
theorem B1100903 : Blo 1100624 1100903 := bstep (se 1 (by rfl) ⟨825677, by rfl⟩ : syracuseStep 1100903 = 1651355) B1651355
theorem B257412329 : Blo 1100624 257412329 := bstep (se 2 (by rfl) ⟨96529623, by rfl⟩ : syracuseStep 257412329 = 193059247) B193059247
theorem B2477519 : Blo 1100624 2477519 := bstep (se 1 (by rfl) ⟨1858139, by rfl⟩ : syracuseStep 2477519 = 3716279) B3716279
theorem B5590619 : Blo 1100624 5590619 := bstep (se 1 (by rfl) ⟨4192964, by rfl⟩ : syracuseStep 5590619 = 8385929) B8385929
theorem B1101679 : Blo 1100624 1101679 := bstep (se 1 (by rfl) ⟨826259, by rfl⟩ : syracuseStep 1101679 = 1652519) B1652519
theorem B1102319 : Blo 1100624 1102319 := bstep (se 1 (by rfl) ⟨826739, by rfl⟩ : syracuseStep 1102319 = 1653479) B1653479
theorem B1102527 : Blo 1100624 1102527 := bstep (se 1 (by rfl) ⟨826895, by rfl⟩ : syracuseStep 1102527 = 1653791) B1653791
theorem B2478887 : Blo 1100624 2478887 := bstep (se 1 (by rfl) ⟨1859165, by rfl⟩ : syracuseStep 2478887 = 3718331) B3718331
theorem B5297035 : Blo 1100624 5297035 := bstep (se 1 (by rfl) ⟨3972776, by rfl⟩ : syracuseStep 5297035 = 7945553) B7945553
theorem B1103175 : Blo 1100624 1103175 := bstep (se 1 (by rfl) ⟨827381, by rfl⟩ : syracuseStep 1103175 = 1654763) B1654763
theorem B14341799 : Blo 1100624 14341799 := bstep (se 1 (by rfl) ⟨10756349, by rfl⟩ : syracuseStep 14341799 = 21512699) B21512699
theorem B1103643 : Blo 1100624 1103643 := bstep (se 1 (by rfl) ⟨827732, by rfl⟩ : syracuseStep 1103643 = 1655465) B1655465
theorem B1103727 : Blo 1100624 1103727 := bstep (se 1 (by rfl) ⟨827795, by rfl⟩ : syracuseStep 1103727 = 1655591) B1655591
theorem B4184095 : Blo 1100624 4184095 := bstep (se 1 (by rfl) ⟨3138071, by rfl⟩ : syracuseStep 4184095 = 6276143) B6276143
theorem B1104199 : Blo 1100624 1104199 := bstep (se 1 (by rfl) ⟨828149, by rfl⟩ : syracuseStep 1104199 = 1656299) B1656299
theorem B1104351 : Blo 1100624 1104351 := bstep (se 1 (by rfl) ⟨828263, by rfl⟩ : syracuseStep 1104351 = 1656527) B1656527
theorem B1861211 : Blo 1100624 1861211 := bstep (se 1 (by rfl) ⟨1395908, by rfl⟩ : syracuseStep 1861211 = 2791817) B2791817
theorem B4188287 : Blo 1100624 4188287 := bstep (se 1 (by rfl) ⟨3141215, by rfl⟩ : syracuseStep 4188287 = 6282431) B6282431
theorem B6121655 : Blo 1100624 6121655 := bstep (se 1 (by rfl) ⟨4591241, by rfl⟩ : syracuseStep 6121655 = 9182483) B9182483
theorem B58910939 : Blo 1100624 58910939 := bstep (se 1 (by rfl) ⟨44183204, by rfl⟩ : syracuseStep 58910939 = 88366409) B88366409
theorem B7170295 : Blo 1100624 7170295 := bstep (se 1 (by rfl) ⟨5377721, by rfl⟩ : syracuseStep 7170295 = 10755443) B10755443
theorem B30140687 : Blo 1100624 30140687 := bstep (se 1 (by rfl) ⟨22605515, by rfl⟩ : syracuseStep 30140687 = 45211031) B45211031
theorem B2484863 : Blo 1100624 2484863 := bstep (se 1 (by rfl) ⟨1863647, by rfl⟩ : syracuseStep 2484863 = 3727295) B3727295
theorem B2485151 : Blo 1100624 2485151 := bstep (se 1 (by rfl) ⟨1863863, by rfl⟩ : syracuseStep 2485151 = 3727727) B3727727
theorem B91713665 : Blo 1100624 91713665 := bstep (se 2 (by rfl) ⟨34392624, by rfl⟩ : syracuseStep 91713665 = 68785249) B68785249
theorem B101939077 : Blo 1100624 101939077 := bstep (se 4 (by rfl) ⟨9556788, by rfl⟩ : syracuseStep 101939077 = 19113577) B19113577
theorem B4194119 : Blo 1100624 4194119 := bstep (se 1 (by rfl) ⟨3145589, by rfl⟩ : syracuseStep 4194119 = 6291179) B6291179
theorem B217908265 : Blo 1100624 217908265 := bstep (se 2 (by rfl) ⟨81715599, by rfl⟩ : syracuseStep 217908265 = 163431199) B163431199
theorem B38176181 : Blo 1100624 38176181 := bstep (se 5 (by rfl) ⟨1789508, by rfl⟩ : syracuseStep 38176181 = 3579017) B3579017
theorem B5572151 : Blo 1100624 5572151 := bstep (se 1 (by rfl) ⟨4179113, by rfl⟩ : syracuseStep 5572151 = 8358227) B8358227
theorem B5736553 : Blo 1100624 5736553 := bstep (se 2 (by rfl) ⟨2151207, by rfl⟩ : syracuseStep 5736553 = 4302415) B4302415
theorem B171608219 : Blo 1100624 171608219 := bstep (se 1 (by rfl) ⟨128706164, by rfl⟩ : syracuseStep 171608219 = 257412329) B257412329
theorem B15075487 : Blo 1100624 15075487 := bstep (se 1 (by rfl) ⟨11306615, by rfl⟩ : syracuseStep 15075487 = 22613231) B22613231
theorem B35786123 : Blo 1100624 35786123 := bstep (se 1 (by rfl) ⟨26839592, by rfl⟩ : syracuseStep 35786123 = 53679185) B53679185
theorem B5575067 : Blo 1100624 5575067 := bstep (se 1 (by rfl) ⟨4181300, by rfl⟩ : syracuseStep 5575067 = 8362601) B8362601
theorem B11933639 : Blo 1100624 11933639 := bstep (se 1 (by rfl) ⟨8950229, by rfl⟩ : syracuseStep 11933639 = 17900459) B17900459
theorem B2792191 : Blo 1100624 2792191 := bstep (se 1 (by rfl) ⟨2094143, by rfl⟩ : syracuseStep 2792191 = 4188287) B4188287
theorem B20093791 : Blo 1100624 20093791 := bstep (se 1 (by rfl) ⟨15070343, by rfl⟩ : syracuseStep 20093791 = 30140687) B30140687
theorem B15081461 : Blo 1100624 15081461 := bstep (se 5 (by rfl) ⟨706943, by rfl⟩ : syracuseStep 15081461 = 1413887) B1413887
theorem B5578793 : Blo 1100624 5578793 := bstep (se 2 (by rfl) ⟨2092047, by rfl⟩ : syracuseStep 5578793 = 4184095) B4184095
theorem B149103341 : Blo 1100624 149103341 := bstep (se 3 (by rfl) ⟨27956876, by rfl⟩ : syracuseStep 149103341 = 55913753) B55913753
theorem B2796079 : Blo 1100624 2796079 := bstep (se 1 (by rfl) ⟨2097059, by rfl⟩ : syracuseStep 2796079 = 4194119) B4194119
theorem B3715307 : Blo 1100624 3715307 := bstep (se 1 (by rfl) ⟨2786480, by rfl⟩ : syracuseStep 3715307 = 5572961) B5572961
theorem B1323259 : Blo 1100624 1323259 := bstep (se 1 (by rfl) ⟨992444, by rfl⟩ : syracuseStep 1323259 = 1984889) B1984889
theorem B1487737 : Blo 1100624 1487737 := bstep (se 2 (by rfl) ⟨557901, by rfl⟩ : syracuseStep 1487737 = 1115803) B1115803
theorem B1651679 : Blo 1100624 1651679 := bstep (se 1 (by rfl) ⟨1238759, by rfl⟩ : syracuseStep 1651679 = 2477519) B2477519
theorem B1652591 : Blo 1100624 1652591 := bstep (se 1 (by rfl) ⟨1239443, by rfl⟩ : syracuseStep 1652591 = 2478887) B2478887
theorem B7062713 : Blo 1100624 7062713 := bstep (se 2 (by rfl) ⟨2648517, by rfl⟩ : syracuseStep 7062713 = 5297035) B5297035
theorem B4081103 : Blo 1100624 4081103 := bstep (se 1 (by rfl) ⟨3060827, by rfl⟩ : syracuseStep 4081103 = 6121655) B6121655
theorem B39273959 : Blo 1100624 39273959 := bstep (se 1 (by rfl) ⟨29455469, by rfl⟩ : syracuseStep 39273959 = 58910939) B58910939
theorem B6276599 : Blo 1100624 6276599 := bstep (se 1 (by rfl) ⟨4707449, by rfl⟩ : syracuseStep 6276599 = 9414899) B9414899
theorem B1656575 : Blo 1100624 1656575 := bstep (se 1 (by rfl) ⟨1242431, by rfl⟩ : syracuseStep 1656575 = 2484863) B2484863
theorem B1656767 : Blo 1100624 1656767 := bstep (se 1 (by rfl) ⟨1242575, by rfl⟩ : syracuseStep 1656767 = 2485151) B2485151
theorem B18860687 : Blo 1100624 18860687 := bstep (se 1 (by rfl) ⟨14145515, by rfl⟩ : syracuseStep 18860687 = 28291031) B28291031
theorem B1100735 : Blo 1100624 1100735 := bstep (se 1 (by rfl) ⟨825551, by rfl⟩ : syracuseStep 1100735 = 1651103) B1651103
theorem B2477735 : Blo 1100624 2477735 := bstep (se 1 (by rfl) ⟨1858301, by rfl⟩ : syracuseStep 2477735 = 3716603) B3716603
theorem B1101519 : Blo 1100624 1101519 := bstep (se 1 (by rfl) ⟨826139, by rfl⟩ : syracuseStep 1101519 = 1652279) B1652279
theorem B1101823 : Blo 1100624 1101823 := bstep (se 1 (by rfl) ⟨826367, by rfl⟩ : syracuseStep 1101823 = 1652735) B1652735
theorem B1102875 : Blo 1100624 1102875 := bstep (se 1 (by rfl) ⟨827156, by rfl⟩ : syracuseStep 1102875 = 1654313) B1654313
theorem B1103103 : Blo 1100624 1103103 := bstep (se 1 (by rfl) ⟨827327, by rfl⟩ : syracuseStep 1103103 = 1654655) B1654655
theorem B1103131 : Blo 1100624 1103131 := bstep (se 1 (by rfl) ⟨827348, by rfl⟩ : syracuseStep 1103131 = 1654697) B1654697
theorem B244569773 : Blo 1100624 244569773 := bstep (se 3 (by rfl) ⟨45856832, by rfl⟩ : syracuseStep 244569773 = 91713665) B91713665
theorem B17913959 : Blo 1100624 17913959 := bstep (se 1 (by rfl) ⟨13435469, by rfl⟩ : syracuseStep 17913959 = 26870939) B26870939
theorem B8379611 : Blo 1100624 8379611 := bstep (se 1 (by rfl) ⟨6284708, by rfl⟩ : syracuseStep 8379611 = 12569417) B12569417
theorem B3727079 : Blo 1100624 3727079 := bstep (se 1 (by rfl) ⟨2795309, by rfl⟩ : syracuseStep 3727079 = 5590619) B5590619
theorem B9560393 : Blo 1100624 9560393 := bstep (se 2 (by rfl) ⟨3585147, by rfl⟩ : syracuseStep 9560393 = 7170295) B7170295
theorem B9561199 : Blo 1100624 9561199 := bstep (se 1 (by rfl) ⟨7170899, by rfl⟩ : syracuseStep 9561199 = 14341799) B14341799
theorem B1862095 : Blo 1100624 1862095 := bstep (se 1 (by rfl) ⟨1396571, by rfl⟩ : syracuseStep 1862095 = 2793143) B2793143
theorem B2977031 : Blo 1100624 2977031 := bstep (se 1 (by rfl) ⟨2232773, by rfl⟩ : syracuseStep 2977031 = 4465547) B4465547
theorem B1863391 : Blo 1100624 1863391 := bstep (se 1 (by rfl) ⟨1397543, by rfl⟩ : syracuseStep 1863391 = 2795087) B2795087
theorem B1240807 : Blo 1100624 1240807 := bstep (se 1 (by rfl) ⟨930605, by rfl⟩ : syracuseStep 1240807 = 1861211) B1861211
theorem B12546089 : Blo 1100624 12546089 := bstep (se 2 (by rfl) ⟨4704783, by rfl⟩ : syracuseStep 12546089 = 9409567) B9409567
theorem B135918769 : Blo 1100624 135918769 := bstep (se 2 (by rfl) ⟨50969538, by rfl⟩ : syracuseStep 135918769 = 101939077) B101939077
theorem B4027715 : Blo 1100624 4027715 := bstep (se 1 (by rfl) ⟨3020786, by rfl⟩ : syracuseStep 4027715 = 6041573) B6041573
theorem B2653631 : Blo 1100624 2653631 := bstep (se 1 (by rfl) ⟨1990223, by rfl⟩ : syracuseStep 2653631 = 3980447) B3980447
theorem B2720735 : Blo 1100624 2720735 := bstep (se 1 (by rfl) ⟨2040551, by rfl⟩ : syracuseStep 2720735 = 4081103) B4081103
theorem B26182639 : Blo 1100624 26182639 := bstep (se 1 (by rfl) ⟨19636979, by rfl⟩ : syracuseStep 26182639 = 39273959) B39273959
theorem B12748265 : Blo 1100624 12748265 := bstep (se 2 (by rfl) ⟨4780599, by rfl⟩ : syracuseStep 12748265 = 9561199) B9561199
theorem B23857415 : Blo 1100624 23857415 := bstep (se 1 (by rfl) ⟨17893061, by rfl⟩ : syracuseStep 23857415 = 35786123) B35786123
theorem B7934597 : Blo 1100624 7934597 := bstep (se 4 (by rfl) ⟨743868, by rfl⟩ : syracuseStep 7934597 = 1487737) B1487737
theorem B8364059 : Blo 1100624 8364059 := bstep (se 1 (by rfl) ⟨6273044, by rfl⟩ : syracuseStep 8364059 = 12546089) B12546089
theorem B7938749 : Blo 1100624 7938749 := bstep (se 3 (by rfl) ⟨1488515, by rfl⟩ : syracuseStep 7938749 = 2977031) B2977031
theorem B3714767 : Blo 1100624 3714767 := bstep (se 1 (by rfl) ⟨2786075, by rfl⟩ : syracuseStep 3714767 = 5572151) B5572151
theorem B7057381 : Blo 1100624 7057381 := bstep (se 4 (by rfl) ⟨661629, by rfl⟩ : syracuseStep 7057381 = 1323259) B1323259
theorem B114405479 : Blo 1100624 114405479 := bstep (se 1 (by rfl) ⟨85804109, by rfl⟩ : syracuseStep 114405479 = 171608219) B171608219
theorem B1651823 : Blo 1100624 1651823 := bstep (se 1 (by rfl) ⟨1238867, by rfl⟩ : syracuseStep 1651823 = 2477735) B2477735
theorem B20100649 : Blo 1100624 20100649 := bstep (se 2 (by rfl) ⟨7537743, by rfl⟩ : syracuseStep 20100649 = 15075487) B15075487
theorem B3716711 : Blo 1100624 3716711 := bstep (se 1 (by rfl) ⟨2787533, by rfl⟩ : syracuseStep 3716711 = 5575067) B5575067
theorem B11942639 : Blo 1100624 11942639 := bstep (se 1 (by rfl) ⟨8956979, by rfl⟩ : syracuseStep 11942639 = 17913959) B17913959
theorem B5586407 : Blo 1100624 5586407 := bstep (se 1 (by rfl) ⟨4189805, by rfl⟩ : syracuseStep 5586407 = 8379611) B8379611
theorem B1654409 : Blo 1100624 1654409 := bstep (se 2 (by rfl) ⟨620403, by rfl⟩ : syracuseStep 1654409 = 1240807) B1240807
theorem B3719195 : Blo 1100624 3719195 := bstep (se 1 (by rfl) ⟨2789396, by rfl⟩ : syracuseStep 3719195 = 5578793) B5578793
theorem B6373595 : Blo 1100624 6373595 := bstep (se 1 (by rfl) ⟨4780196, by rfl⟩ : syracuseStep 6373595 = 9560393) B9560393
theorem B99402227 : Blo 1100624 99402227 := bstep (se 1 (by rfl) ⟨74551670, by rfl⟩ : syracuseStep 99402227 = 149103341) B149103341
theorem B181225025 : Blo 1100624 181225025 := bstep (se 2 (by rfl) ⟨67959384, by rfl⟩ : syracuseStep 181225025 = 135918769) B135918769
theorem B2476871 : Blo 1100624 2476871 := bstep (se 1 (by rfl) ⟨1857653, by rfl⟩ : syracuseStep 2476871 = 3715307) B3715307
theorem B1101119 : Blo 1100624 1101119 := bstep (se 1 (by rfl) ⟨825839, by rfl⟩ : syracuseStep 1101119 = 1651679) B1651679
theorem B3722921 : Blo 1100624 3722921 := bstep (se 2 (by rfl) ⟨1396095, by rfl⟩ : syracuseStep 3722921 = 2792191) B2792191
theorem B26791721 : Blo 1100624 26791721 := bstep (se 2 (by rfl) ⟨10046895, by rfl⟩ : syracuseStep 26791721 = 20093791) B20093791
theorem B1101727 : Blo 1100624 1101727 := bstep (se 1 (by rfl) ⟨826295, by rfl⟩ : syracuseStep 1101727 = 1652591) B1652591
theorem B4708475 : Blo 1100624 4708475 := bstep (se 1 (by rfl) ⟨3531356, by rfl⟩ : syracuseStep 4708475 = 7062713) B7062713
theorem B25450787 : Blo 1100624 25450787 := bstep (se 1 (by rfl) ⟨19088090, by rfl⟩ : syracuseStep 25450787 = 38176181) B38176181
theorem B4184399 : Blo 1100624 4184399 := bstep (se 1 (by rfl) ⟨3138299, by rfl⟩ : syracuseStep 4184399 = 6276599) B6276599
theorem B1104383 : Blo 1100624 1104383 := bstep (se 1 (by rfl) ⟨828287, by rfl⟩ : syracuseStep 1104383 = 1656575) B1656575
theorem B1104511 : Blo 1100624 1104511 := bstep (se 1 (by rfl) ⟨828383, by rfl⟩ : syracuseStep 1104511 = 1656767) B1656767
theorem B290544353 : Blo 1100624 290544353 := bstep (se 2 (by rfl) ⟨108954132, by rfl⟩ : syracuseStep 290544353 = 217908265) B217908265
theorem B12573791 : Blo 1100624 12573791 := bstep (se 1 (by rfl) ⟨9430343, by rfl⟩ : syracuseStep 12573791 = 18860687) B18860687
theorem B122379797 : Blo 1100624 122379797 := bstep (se 6 (by rfl) ⟨2868276, by rfl⟩ : syracuseStep 122379797 = 5736553) B5736553
theorem B2482793 : Blo 1100624 2482793 := bstep (se 2 (by rfl) ⟨931047, by rfl⟩ : syracuseStep 2482793 = 1862095) B1862095
theorem B3728105 : Blo 1100624 3728105 := bstep (se 2 (by rfl) ⟨1398039, by rfl⟩ : syracuseStep 3728105 = 2796079) B2796079
theorem B163046515 : Blo 1100624 163046515 := bstep (se 1 (by rfl) ⟨122284886, by rfl⟩ : syracuseStep 163046515 = 244569773) B244569773
theorem B7955759 : Blo 1100624 7955759 := bstep (se 1 (by rfl) ⟨5966819, by rfl⟩ : syracuseStep 7955759 = 11933639) B11933639
theorem B2484521 : Blo 1100624 2484521 := bstep (se 2 (by rfl) ⟨931695, by rfl⟩ : syracuseStep 2484521 = 1863391) B1863391
theorem B2484719 : Blo 1100624 2484719 := bstep (se 1 (by rfl) ⟨1863539, by rfl⟩ : syracuseStep 2484719 = 3727079) B3727079
theorem B10054307 : Blo 1100624 10054307 := bstep (se 1 (by rfl) ⟨7540730, by rfl⟩ : syracuseStep 10054307 = 15081461) B15081461
theorem B2685143 : Blo 1100624 2685143 := bstep (se 1 (by rfl) ⟨2013857, by rfl⟩ : syracuseStep 2685143 = 4027715) B4027715
theorem B1769087 : Blo 1100624 1769087 := bstep (se 1 (by rfl) ⟨1326815, by rfl⟩ : syracuseStep 1769087 = 2653631) B2653631
theorem B120816683 : Blo 1100624 120816683 := bstep (se 1 (by rfl) ⟨90612512, by rfl⟩ : syracuseStep 120816683 = 181225025) B181225025
theorem B17861147 : Blo 1100624 17861147 := bstep (se 1 (by rfl) ⟨13395860, by rfl⟩ : syracuseStep 17861147 = 26791721) B26791721
theorem B2789599 : Blo 1100624 2789599 := bstep (se 1 (by rfl) ⟨2092199, by rfl⟩ : syracuseStep 2789599 = 4184399) B4184399
theorem B193696235 : Blo 1100624 193696235 := bstep (se 1 (by rfl) ⟨145272176, by rfl⟩ : syracuseStep 193696235 = 290544353) B290544353
theorem B9409841 : Blo 1100624 9409841 := bstep (se 2 (by rfl) ⟨3528690, by rfl⟩ : syracuseStep 9409841 = 7057381) B7057381
theorem B5576039 : Blo 1100624 5576039 := bstep (se 1 (by rfl) ⟨4182029, by rfl⟩ : syracuseStep 5576039 = 8364059) B8364059
theorem B66268151 : Blo 1100624 66268151 := bstep (se 1 (by rfl) ⟨49701113, by rfl⟩ : syracuseStep 66268151 = 99402227) B99402227
theorem B1813823 : Blo 1100624 1813823 := bstep (se 1 (by rfl) ⟨1360367, by rfl⟩ : syracuseStep 1813823 = 2720735) B2720735
theorem B8498843 : Blo 1100624 8498843 := bstep (se 1 (by rfl) ⟨6374132, by rfl⟩ : syracuseStep 8498843 = 12748265) B12748265
theorem B34910185 : Blo 1100624 34910185 := bstep (se 2 (by rfl) ⟨13091319, by rfl⟩ : syracuseStep 34910185 = 26182639) B26182639
theorem B217395353 : Blo 1100624 217395353 := bstep (se 2 (by rfl) ⟨81523257, by rfl⟩ : syracuseStep 217395353 = 163046515) B163046515
theorem B15904943 : Blo 1100624 15904943 := bstep (se 1 (by rfl) ⟨11928707, by rfl⟩ : syracuseStep 15904943 = 23857415) B23857415
theorem B1651247 : Blo 1100624 1651247 := bstep (se 1 (by rfl) ⟨1238435, by rfl⟩ : syracuseStep 1651247 = 2476871) B2476871
theorem B5289731 : Blo 1100624 5289731 := bstep (se 1 (by rfl) ⟨3967298, by rfl⟩ : syracuseStep 5289731 = 7934597) B7934597
theorem B21215357 : Blo 1100624 21215357 := bstep (se 3 (by rfl) ⟨3977879, by rfl⟩ : syracuseStep 21215357 = 7955759) B7955759
theorem B1655195 : Blo 1100624 1655195 := bstep (se 1 (by rfl) ⟨1241396, by rfl⟩ : syracuseStep 1655195 = 2482793) B2482793
theorem B5292499 : Blo 1100624 5292499 := bstep (se 1 (by rfl) ⟨3969374, by rfl⟩ : syracuseStep 5292499 = 7938749) B7938749
theorem B1656347 : Blo 1100624 1656347 := bstep (se 1 (by rfl) ⟨1242260, by rfl⟩ : syracuseStep 1656347 = 2484521) B2484521
theorem B1656479 : Blo 1100624 1656479 := bstep (se 1 (by rfl) ⟨1242359, by rfl⟩ : syracuseStep 1656479 = 2484719) B2484719
theorem B6702871 : Blo 1100624 6702871 := bstep (se 1 (by rfl) ⟨5027153, by rfl⟩ : syracuseStep 6702871 = 10054307) B10054307
theorem B2476511 : Blo 1100624 2476511 := bstep (se 1 (by rfl) ⟨1857383, by rfl⟩ : syracuseStep 2476511 = 3714767) B3714767
theorem B76270319 : Blo 1100624 76270319 := bstep (se 1 (by rfl) ⟨57202739, by rfl⟩ : syracuseStep 76270319 = 114405479) B114405479
theorem B1101215 : Blo 1100624 1101215 := bstep (se 1 (by rfl) ⟨825911, by rfl⟩ : syracuseStep 1101215 = 1651823) B1651823
theorem B2477807 : Blo 1100624 2477807 := bstep (se 1 (by rfl) ⟨1858355, by rfl⟩ : syracuseStep 2477807 = 3716711) B3716711
theorem B1790095 : Blo 1100624 1790095 := bstep (se 1 (by rfl) ⟨1342571, by rfl⟩ : syracuseStep 1790095 = 2685143) B2685143
theorem B3724271 : Blo 1100624 3724271 := bstep (se 1 (by rfl) ⟨2793203, by rfl⟩ : syracuseStep 3724271 = 5586407) B5586407
theorem B1102939 : Blo 1100624 1102939 := bstep (se 1 (by rfl) ⟨827204, by rfl⟩ : syracuseStep 1102939 = 1654409) B1654409
theorem B2479463 : Blo 1100624 2479463 := bstep (se 1 (by rfl) ⟨1859597, by rfl⟩ : syracuseStep 2479463 = 3719195) B3719195
theorem B4249063 : Blo 1100624 4249063 := bstep (se 1 (by rfl) ⟨3186797, by rfl⟩ : syracuseStep 4249063 = 6373595) B6373595
theorem B2481947 : Blo 1100624 2481947 := bstep (se 1 (by rfl) ⟨1861460, by rfl⟩ : syracuseStep 2481947 = 3722921) B3722921
theorem B3138983 : Blo 1100624 3138983 := bstep (se 1 (by rfl) ⟨2354237, by rfl⟩ : syracuseStep 3138983 = 4708475) B4708475
theorem B16967191 : Blo 1100624 16967191 := bstep (se 1 (by rfl) ⟨12725393, by rfl⟩ : syracuseStep 16967191 = 25450787) B25450787
theorem B8382527 : Blo 1100624 8382527 := bstep (se 1 (by rfl) ⟨6286895, by rfl⟩ : syracuseStep 8382527 = 12573791) B12573791
theorem B81586531 : Blo 1100624 81586531 := bstep (se 1 (by rfl) ⟨61189898, by rfl⟩ : syracuseStep 81586531 = 122379797) B122379797
theorem B2485403 : Blo 1100624 2485403 := bstep (se 1 (by rfl) ⟨1864052, by rfl⟩ : syracuseStep 2485403 = 3728105) B3728105
theorem B26800865 : Blo 1100624 26800865 := bstep (se 2 (by rfl) ⟨10050324, by rfl⟩ : syracuseStep 26800865 = 20100649) B20100649
theorem B4717565 : Blo 1100624 4717565 := bstep (se 3 (by rfl) ⟨884543, by rfl⟩ : syracuseStep 4717565 = 1769087) B1769087
theorem B7961759 : Blo 1100624 7961759 := bstep (se 1 (by rfl) ⟨5971319, by rfl⟩ : syracuseStep 7961759 = 11942639) B11942639
theorem B80544455 : Blo 1100624 80544455 := bstep (se 1 (by rfl) ⟨60408341, by rfl⟩ : syracuseStep 80544455 = 120816683) B120816683
theorem B44178767 : Blo 1100624 44178767 := bstep (se 1 (by rfl) ⟨33134075, by rfl⟩ : syracuseStep 44178767 = 66268151) B66268151
theorem B17867243 : Blo 1100624 17867243 := bstep (se 1 (by rfl) ⟨13400432, by rfl⟩ : syracuseStep 17867243 = 26800865) B26800865
theorem B7056665 : Blo 1100624 7056665 := bstep (se 2 (by rfl) ⟨2646249, by rfl⟩ : syracuseStep 7056665 = 5292499) B5292499
theorem B1651007 : Blo 1100624 1651007 := bstep (se 1 (by rfl) ⟨1238255, by rfl⟩ : syracuseStep 1651007 = 2476511) B2476511
theorem B11907431 : Blo 1100624 11907431 := bstep (se 1 (by rfl) ⟨8930573, by rfl⟩ : syracuseStep 11907431 = 17861147) B17861147
theorem B22622921 : Blo 1100624 22622921 := bstep (se 2 (by rfl) ⟨8483595, by rfl⟩ : syracuseStep 22622921 = 16967191) B16967191
theorem B1651871 : Blo 1100624 1651871 := bstep (se 1 (by rfl) ⟨1238903, by rfl⟩ : syracuseStep 1651871 = 2477807) B2477807
theorem B6273227 : Blo 1100624 6273227 := bstep (se 1 (by rfl) ⟨4704920, by rfl⟩ : syracuseStep 6273227 = 9409841) B9409841
theorem B3717359 : Blo 1100624 3717359 := bstep (se 1 (by rfl) ⟨2788019, by rfl⟩ : syracuseStep 3717359 = 5576039) B5576039
theorem B1652975 : Blo 1100624 1652975 := bstep (se 1 (by rfl) ⟨1239731, by rfl⟩ : syracuseStep 1652975 = 2479463) B2479463
theorem B1654631 : Blo 1100624 1654631 := bstep (se 1 (by rfl) ⟨1240973, by rfl⟩ : syracuseStep 1654631 = 2481947) B2481947
theorem B46546913 : Blo 1100624 46546913 := bstep (se 2 (by rfl) ⟨17455092, by rfl⟩ : syracuseStep 46546913 = 34910185) B34910185
theorem B3719465 : Blo 1100624 3719465 := bstep (se 2 (by rfl) ⟨1394799, by rfl⟩ : syracuseStep 3719465 = 2789599) B2789599
theorem B5588351 : Blo 1100624 5588351 := bstep (se 1 (by rfl) ⟨4191263, by rfl⟩ : syracuseStep 5588351 = 8382527) B8382527
theorem B1656935 : Blo 1100624 1656935 := bstep (se 1 (by rfl) ⟨1242701, by rfl⟩ : syracuseStep 1656935 = 2485403) B2485403
theorem B22661669 : Blo 1100624 22661669 := bstep (se 4 (by rfl) ⟨2124531, by rfl⟩ : syracuseStep 22661669 = 4249063) B4249063
theorem B10603295 : Blo 1100624 10603295 := bstep (se 1 (by rfl) ⟨7952471, by rfl⟩ : syracuseStep 10603295 = 15904943) B15904943
theorem B1100831 : Blo 1100624 1100831 := bstep (se 1 (by rfl) ⟨825623, by rfl⟩ : syracuseStep 1100831 = 1651247) B1651247
theorem B3526487 : Blo 1100624 3526487 := bstep (se 1 (by rfl) ⟨2644865, by rfl⟩ : syracuseStep 3526487 = 5289731) B5289731
theorem B14143571 : Blo 1100624 14143571 := bstep (se 1 (by rfl) ⟨10607678, by rfl⟩ : syracuseStep 14143571 = 21215357) B21215357
theorem B1103463 : Blo 1100624 1103463 := bstep (se 1 (by rfl) ⟨827597, by rfl⟩ : syracuseStep 1103463 = 1655195) B1655195
theorem B1104231 : Blo 1100624 1104231 := bstep (se 1 (by rfl) ⟨828173, by rfl⟩ : syracuseStep 1104231 = 1656347) B1656347
theorem B1104319 : Blo 1100624 1104319 := bstep (se 1 (by rfl) ⟨828239, by rfl⟩ : syracuseStep 1104319 = 1656479) B1656479
theorem B50846879 : Blo 1100624 50846879 := bstep (se 1 (by rfl) ⟨38135159, by rfl⟩ : syracuseStep 50846879 = 76270319) B76270319
theorem B8937161 : Blo 1100624 8937161 := bstep (se 2 (by rfl) ⟨3351435, by rfl⟩ : syracuseStep 8937161 = 6702871) B6702871
theorem B129130823 : Blo 1100624 129130823 := bstep (se 1 (by rfl) ⟨96848117, by rfl⟩ : syracuseStep 129130823 = 193696235) B193696235
theorem B108782041 : Blo 1100624 108782041 := bstep (se 2 (by rfl) ⟨40793265, by rfl⟩ : syracuseStep 108782041 = 81586531) B81586531
theorem B2482847 : Blo 1100624 2482847 := bstep (se 1 (by rfl) ⟨1862135, by rfl⟩ : syracuseStep 2482847 = 3724271) B3724271
theorem B2386793 : Blo 1100624 2386793 := bstep (se 2 (by rfl) ⟨895047, by rfl⟩ : syracuseStep 2386793 = 1790095) B1790095
theorem B2092655 : Blo 1100624 2092655 := bstep (se 1 (by rfl) ⟨1569491, by rfl⟩ : syracuseStep 2092655 = 3138983) B3138983
theorem B1209215 : Blo 1100624 1209215 := bstep (se 1 (by rfl) ⟨906911, by rfl⟩ : syracuseStep 1209215 = 1813823) B1813823
theorem B5665895 : Blo 1100624 5665895 := bstep (se 1 (by rfl) ⟨4249421, by rfl⟩ : syracuseStep 5665895 = 8498843) B8498843
theorem B144930235 : Blo 1100624 144930235 := bstep (se 1 (by rfl) ⟨108697676, by rfl⟩ : syracuseStep 144930235 = 217395353) B217395353
theorem B3145043 : Blo 1100624 3145043 := bstep (se 1 (by rfl) ⟨2358782, by rfl⟩ : syracuseStep 3145043 = 4717565) B4717565
theorem B5307839 : Blo 1100624 5307839 := bstep (se 1 (by rfl) ⟨3980879, by rfl⟩ : syracuseStep 5307839 = 7961759) B7961759
theorem B47645981 : Blo 1100624 47645981 := bstep (se 3 (by rfl) ⟨8933621, by rfl⟩ : syracuseStep 47645981 = 17867243) B17867243
theorem B15107779 : Blo 1100624 15107779 := bstep (se 1 (by rfl) ⟨11330834, by rfl⟩ : syracuseStep 15107779 = 22661669) B22661669
theorem B86087215 : Blo 1100624 86087215 := bstep (se 1 (by rfl) ⟨64565411, by rfl⟩ : syracuseStep 86087215 = 129130823) B129130823
theorem B193240313 : Blo 1100624 193240313 := bstep (se 2 (by rfl) ⟨72465117, by rfl⟩ : syracuseStep 193240313 = 144930235) B144930235
theorem B6364781 : Blo 1100624 6364781 := bstep (se 3 (by rfl) ⟨1193396, by rfl⟩ : syracuseStep 6364781 = 2386793) B2386793
theorem B7938287 : Blo 1100624 7938287 := bstep (se 1 (by rfl) ⟨5953715, by rfl⟩ : syracuseStep 7938287 = 11907431) B11907431
theorem B15081947 : Blo 1100624 15081947 := bstep (se 1 (by rfl) ⟨11311460, by rfl⟩ : syracuseStep 15081947 = 22622921) B22622921
theorem B3777263 : Blo 1100624 3777263 := bstep (se 1 (by rfl) ⟨2832947, by rfl⟩ : syracuseStep 3777263 = 5665895) B5665895
theorem B5580413 : Blo 1100624 5580413 := bstep (se 3 (by rfl) ⟨1046327, by rfl⟩ : syracuseStep 5580413 = 2092655) B2092655
theorem B145042721 : Blo 1100624 145042721 := bstep (se 2 (by rfl) ⟨54391020, by rfl⟩ : syracuseStep 145042721 = 108782041) B108782041
theorem B3224573 : Blo 1100624 3224573 := bstep (se 3 (by rfl) ⟨604607, by rfl⟩ : syracuseStep 3224573 = 1209215) B1209215
theorem B1655231 : Blo 1100624 1655231 := bstep (se 1 (by rfl) ⟨1241423, by rfl⟩ : syracuseStep 1655231 = 2482847) B2482847
theorem B4704443 : Blo 1100624 4704443 := bstep (se 1 (by rfl) ⟨3528332, by rfl⟩ : syracuseStep 4704443 = 7056665) B7056665
theorem B1100671 : Blo 1100624 1100671 := bstep (se 1 (by rfl) ⟨825503, by rfl⟩ : syracuseStep 1100671 = 1651007) B1651007
theorem B1101247 : Blo 1100624 1101247 := bstep (se 1 (by rfl) ⟨825935, by rfl⟩ : syracuseStep 1101247 = 1651871) B1651871
theorem B4182151 : Blo 1100624 4182151 := bstep (se 1 (by rfl) ⟨3136613, by rfl⟩ : syracuseStep 4182151 = 6273227) B6273227
theorem B2478239 : Blo 1100624 2478239 := bstep (se 1 (by rfl) ⟨1858679, by rfl⟩ : syracuseStep 2478239 = 3717359) B3717359
theorem B1101983 : Blo 1100624 1101983 := bstep (se 1 (by rfl) ⟨826487, by rfl⟩ : syracuseStep 1101983 = 1652975) B1652975
theorem B1103087 : Blo 1100624 1103087 := bstep (se 1 (by rfl) ⟨827315, by rfl⟩ : syracuseStep 1103087 = 1654631) B1654631
theorem B2479643 : Blo 1100624 2479643 := bstep (se 1 (by rfl) ⟨1859732, by rfl⟩ : syracuseStep 2479643 = 3719465) B3719465
theorem B53696303 : Blo 1100624 53696303 := bstep (se 1 (by rfl) ⟨40272227, by rfl⟩ : syracuseStep 53696303 = 80544455) B80544455
theorem B3725567 : Blo 1100624 3725567 := bstep (se 1 (by rfl) ⟨2794175, by rfl⟩ : syracuseStep 3725567 = 5588351) B5588351
theorem B1104623 : Blo 1100624 1104623 := bstep (se 1 (by rfl) ⟨828467, by rfl⟩ : syracuseStep 1104623 = 1656935) B1656935
theorem B7068863 : Blo 1100624 7068863 := bstep (se 1 (by rfl) ⟨5301647, by rfl⟩ : syracuseStep 7068863 = 10603295) B10603295
theorem B2350991 : Blo 1100624 2350991 := bstep (se 1 (by rfl) ⟨1763243, by rfl⟩ : syracuseStep 2350991 = 3526487) B3526487
theorem B9429047 : Blo 1100624 9429047 := bstep (se 1 (by rfl) ⟨7071785, by rfl⟩ : syracuseStep 9429047 = 14143571) B14143571
theorem B29452511 : Blo 1100624 29452511 := bstep (se 1 (by rfl) ⟨22089383, by rfl⟩ : syracuseStep 29452511 = 44178767) B44178767
theorem B5958107 : Blo 1100624 5958107 := bstep (se 1 (by rfl) ⟨4468580, by rfl⟩ : syracuseStep 5958107 = 8937161) B8937161
theorem B135591677 : Blo 1100624 135591677 := bstep (se 3 (by rfl) ⟨25423439, by rfl⟩ : syracuseStep 135591677 = 50846879) B50846879
theorem B2096695 : Blo 1100624 2096695 := bstep (se 1 (by rfl) ⟨1572521, by rfl⟩ : syracuseStep 2096695 = 3145043) B3145043
theorem B3538559 : Blo 1100624 3538559 := bstep (se 1 (by rfl) ⟨2653919, by rfl⟩ : syracuseStep 3538559 = 5307839) B5307839
theorem B31031275 : Blo 1100624 31031275 := bstep (se 1 (by rfl) ⟨23273456, by rfl⟩ : syracuseStep 31031275 = 46546913) B46546913
theorem B5576201 : Blo 1100624 5576201 := bstep (se 2 (by rfl) ⟨2091075, by rfl⟩ : syracuseStep 5576201 = 4182151) B4182151
theorem B19635007 : Blo 1100624 19635007 := bstep (se 1 (by rfl) ⟨14726255, by rfl⟩ : syracuseStep 19635007 = 29452511) B29452511
theorem B3972071 : Blo 1100624 3972071 := bstep (se 1 (by rfl) ⟨2979053, by rfl⟩ : syracuseStep 3972071 = 5958107) B5958107
theorem B2795593 : Blo 1100624 2795593 := bstep (se 2 (by rfl) ⟨1048347, by rfl⟩ : syracuseStep 2795593 = 2096695) B2096695
theorem B6269309 : Blo 1100624 6269309 := bstep (se 3 (by rfl) ⟨1175495, by rfl⟩ : syracuseStep 6269309 = 2350991) B2350991
theorem B31763987 : Blo 1100624 31763987 := bstep (se 1 (by rfl) ⟨23822990, by rfl⟩ : syracuseStep 31763987 = 47645981) B47645981
theorem B1652159 : Blo 1100624 1652159 := bstep (se 1 (by rfl) ⟨1239119, by rfl⟩ : syracuseStep 1652159 = 2478239) B2478239
theorem B1653095 : Blo 1100624 1653095 := bstep (se 1 (by rfl) ⟨1239821, by rfl⟩ : syracuseStep 1653095 = 2479643) B2479643
theorem B35797535 : Blo 1100624 35797535 := bstep (se 1 (by rfl) ⟨26848151, by rfl⟩ : syracuseStep 35797535 = 53696303) B53696303
theorem B128826875 : Blo 1100624 128826875 := bstep (se 1 (by rfl) ⟨96620156, by rfl⟩ : syracuseStep 128826875 = 193240313) B193240313
theorem B4243187 : Blo 1100624 4243187 := bstep (se 1 (by rfl) ⟨3182390, by rfl⟩ : syracuseStep 4243187 = 6364781) B6364781
theorem B5292191 : Blo 1100624 5292191 := bstep (se 1 (by rfl) ⟨3969143, by rfl⟩ : syracuseStep 5292191 = 7938287) B7938287
theorem B3720275 : Blo 1100624 3720275 := bstep (se 1 (by rfl) ⟨2790206, by rfl⟩ : syracuseStep 3720275 = 5580413) B5580413
theorem B2149715 : Blo 1100624 2149715 := bstep (se 1 (by rfl) ⟨1612286, by rfl⟩ : syracuseStep 2149715 = 3224573) B3224573
theorem B90394451 : Blo 1100624 90394451 := bstep (se 1 (by rfl) ⟨67795838, by rfl⟩ : syracuseStep 90394451 = 135591677) B135591677
theorem B41375033 : Blo 1100624 41375033 := bstep (se 2 (by rfl) ⟨15515637, by rfl⟩ : syracuseStep 41375033 = 31031275) B31031275
theorem B1103487 : Blo 1100624 1103487 := bstep (se 1 (by rfl) ⟨827615, by rfl⟩ : syracuseStep 1103487 = 1655231) B1655231
theorem B3136295 : Blo 1100624 3136295 := bstep (se 1 (by rfl) ⟨2352221, by rfl⟩ : syracuseStep 3136295 = 4704443) B4704443
theorem B2483711 : Blo 1100624 2483711 := bstep (se 1 (by rfl) ⟨1862783, by rfl⟩ : syracuseStep 2483711 = 3725567) B3725567
theorem B4712575 : Blo 1100624 4712575 := bstep (se 1 (by rfl) ⟨3534431, by rfl⟩ : syracuseStep 4712575 = 7068863) B7068863
theorem B6286031 : Blo 1100624 6286031 := bstep (se 1 (by rfl) ⟨4714523, by rfl⟩ : syracuseStep 6286031 = 9429047) B9429047
theorem B10054631 : Blo 1100624 10054631 := bstep (se 1 (by rfl) ⟨7540973, by rfl⟩ : syracuseStep 10054631 = 15081947) B15081947
theorem B2518175 : Blo 1100624 2518175 := bstep (se 1 (by rfl) ⟨1888631, by rfl⟩ : syracuseStep 2518175 = 3777263) B3777263
theorem B114782953 : Blo 1100624 114782953 := bstep (se 2 (by rfl) ⟨43043607, by rfl⟩ : syracuseStep 114782953 = 86087215) B86087215
theorem B96695147 : Blo 1100624 96695147 := bstep (se 1 (by rfl) ⟨72521360, by rfl⟩ : syracuseStep 96695147 = 145042721) B145042721
theorem B80574821 : Blo 1100624 80574821 := bstep (se 4 (by rfl) ⟨7553889, by rfl⟩ : syracuseStep 80574821 = 15107779) B15107779
theorem B2359039 : Blo 1100624 2359039 := bstep (se 1 (by rfl) ⟨1769279, by rfl⟩ : syracuseStep 2359039 = 3538559) B3538559
theorem B257853725 : Blo 1100624 257853725 := bstep (se 3 (by rfl) ⟨48347573, by rfl⟩ : syracuseStep 257853725 = 96695147) B96695147
theorem B60262967 : Blo 1100624 60262967 := bstep (se 1 (by rfl) ⟨45197225, by rfl⟩ : syracuseStep 60262967 = 90394451) B90394451
theorem B21175991 : Blo 1100624 21175991 := bstep (se 1 (by rfl) ⟨15881993, by rfl⟩ : syracuseStep 21175991 = 31763987) B31763987
theorem B53716547 : Blo 1100624 53716547 := bstep (se 1 (by rfl) ⟨40287410, by rfl⟩ : syracuseStep 53716547 = 80574821) B80574821
theorem B23865023 : Blo 1100624 23865023 := bstep (se 1 (by rfl) ⟨17898767, by rfl⟩ : syracuseStep 23865023 = 35797535) B35797535
theorem B2828791 : Blo 1100624 2828791 := bstep (se 1 (by rfl) ⟨2121593, by rfl⟩ : syracuseStep 2828791 = 4243187) B4243187
theorem B3717467 : Blo 1100624 3717467 := bstep (se 1 (by rfl) ⟨2788100, by rfl⟩ : syracuseStep 3717467 = 5576201) B5576201
theorem B153043937 : Blo 1100624 153043937 := bstep (se 2 (by rfl) ⟨57391476, by rfl⟩ : syracuseStep 153043937 = 114782953) B114782953
theorem B1655807 : Blo 1100624 1655807 := bstep (se 1 (by rfl) ⟨1241855, by rfl⟩ : syracuseStep 1655807 = 2483711) B2483711
theorem B4179539 : Blo 1100624 4179539 := bstep (se 1 (by rfl) ⟨3134654, by rfl⟩ : syracuseStep 4179539 = 6269309) B6269309
theorem B6703087 : Blo 1100624 6703087 := bstep (se 1 (by rfl) ⟨5027315, by rfl⟩ : syracuseStep 6703087 = 10054631) B10054631
theorem B1101439 : Blo 1100624 1101439 := bstep (se 1 (by rfl) ⟨826079, by rfl⟩ : syracuseStep 1101439 = 1652159) B1652159
theorem B1102063 : Blo 1100624 1102063 := bstep (se 1 (by rfl) ⟨826547, by rfl⟩ : syracuseStep 1102063 = 1653095) B1653095
theorem B3528127 : Blo 1100624 3528127 := bstep (se 1 (by rfl) ⟨2646095, by rfl⟩ : syracuseStep 3528127 = 5292191) B5292191
theorem B2480183 : Blo 1100624 2480183 := bstep (se 1 (by rfl) ⟨1860137, by rfl⟩ : syracuseStep 2480183 = 3720275) B3720275
theorem B1433143 : Blo 1100624 1433143 := bstep (se 1 (by rfl) ⟨1074857, by rfl⟩ : syracuseStep 1433143 = 2149715) B2149715
theorem B3727457 : Blo 1100624 3727457 := bstep (se 2 (by rfl) ⟨1397796, by rfl⟩ : syracuseStep 3727457 = 2795593) B2795593
theorem B6283433 : Blo 1100624 6283433 := bstep (se 2 (by rfl) ⟨2356287, by rfl⟩ : syracuseStep 6283433 = 4712575) B4712575
theorem B27583355 : Blo 1100624 27583355 := bstep (se 1 (by rfl) ⟨20687516, by rfl⟩ : syracuseStep 27583355 = 41375033) B41375033
theorem B2090863 : Blo 1100624 2090863 := bstep (se 1 (by rfl) ⟨1568147, by rfl⟩ : syracuseStep 2090863 = 3136295) B3136295
theorem B2648047 : Blo 1100624 2648047 := bstep (se 1 (by rfl) ⟨1986035, by rfl⟩ : syracuseStep 2648047 = 3972071) B3972071
theorem B4190687 : Blo 1100624 4190687 := bstep (se 1 (by rfl) ⟨3143015, by rfl⟩ : syracuseStep 4190687 = 6286031) B6286031
theorem B6715133 : Blo 1100624 6715133 := bstep (se 3 (by rfl) ⟨1259087, by rfl⟩ : syracuseStep 6715133 = 2518175) B2518175
theorem B26180009 : Blo 1100624 26180009 := bstep (se 2 (by rfl) ⟨9817503, by rfl⟩ : syracuseStep 26180009 = 19635007) B19635007
theorem B85884583 : Blo 1100624 85884583 := bstep (se 1 (by rfl) ⟨64413437, by rfl⟩ : syracuseStep 85884583 = 128826875) B128826875
theorem B3145385 : Blo 1100624 3145385 := bstep (se 2 (by rfl) ⟨1179519, by rfl⟩ : syracuseStep 3145385 = 2359039) B2359039
theorem B2786359 : Blo 1100624 2786359 := bstep (se 1 (by rfl) ⟨2089769, by rfl⟩ : syracuseStep 2786359 = 4179539) B4179539
theorem B171902483 : Blo 1100624 171902483 := bstep (se 1 (by rfl) ⟨128926862, by rfl⟩ : syracuseStep 171902483 = 257853725) B257853725
theorem B40175311 : Blo 1100624 40175311 := bstep (se 1 (by rfl) ⟨30131483, by rfl⟩ : syracuseStep 40175311 = 60262967) B60262967
theorem B2787817 : Blo 1100624 2787817 := bstep (se 2 (by rfl) ⟨1045431, by rfl⟩ : syracuseStep 2787817 = 2090863) B2090863
theorem B3771721 : Blo 1100624 3771721 := bstep (se 2 (by rfl) ⟨1414395, by rfl⟩ : syracuseStep 3771721 = 2828791) B2828791
theorem B7643429 : Blo 1100624 7643429 := bstep (se 4 (by rfl) ⟨716571, by rfl⟩ : syracuseStep 7643429 = 1433143) B1433143
theorem B2793791 : Blo 1100624 2793791 := bstep (se 1 (by rfl) ⟨2095343, by rfl⟩ : syracuseStep 2793791 = 4190687) B4190687
theorem B1653455 : Blo 1100624 1653455 := bstep (se 1 (by rfl) ⟨1240091, by rfl⟩ : syracuseStep 1653455 = 2480183) B2480183
theorem B15910015 : Blo 1100624 15910015 := bstep (se 1 (by rfl) ⟨11932511, by rfl⟩ : syracuseStep 15910015 = 23865023) B23865023
theorem B4704169 : Blo 1100624 4704169 := bstep (se 2 (by rfl) ⟨1764063, by rfl⟩ : syracuseStep 4704169 = 3528127) B3528127
theorem B4476755 : Blo 1100624 4476755 := bstep (se 1 (by rfl) ⟨3357566, by rfl⟩ : syracuseStep 4476755 = 6715133) B6715133
theorem B2478311 : Blo 1100624 2478311 := bstep (se 1 (by rfl) ⟨1858733, by rfl⟩ : syracuseStep 2478311 = 3717467) B3717467
theorem B17453339 : Blo 1100624 17453339 := bstep (se 1 (by rfl) ⟨13090004, by rfl⟩ : syracuseStep 17453339 = 26180009) B26180009
theorem B114512777 : Blo 1100624 114512777 := bstep (se 2 (by rfl) ⟨42942291, by rfl⟩ : syracuseStep 114512777 = 85884583) B85884583
theorem B102029291 : Blo 1100624 102029291 := bstep (se 1 (by rfl) ⟨76521968, by rfl⟩ : syracuseStep 102029291 = 153043937) B153043937
theorem B1103871 : Blo 1100624 1103871 := bstep (se 1 (by rfl) ⟨827903, by rfl⟩ : syracuseStep 1103871 = 1655807) B1655807
theorem B73555613 : Blo 1100624 73555613 := bstep (se 3 (by rfl) ⟨13791677, by rfl⟩ : syracuseStep 73555613 = 27583355) B27583355
theorem B3530729 : Blo 1100624 3530729 := bstep (se 2 (by rfl) ⟨1324023, by rfl⟩ : syracuseStep 3530729 = 2648047) B2648047
theorem B8937449 : Blo 1100624 8937449 := bstep (se 2 (by rfl) ⟨3351543, by rfl⟩ : syracuseStep 8937449 = 6703087) B6703087
theorem B14117327 : Blo 1100624 14117327 := bstep (se 1 (by rfl) ⟨10587995, by rfl⟩ : syracuseStep 14117327 = 21175991) B21175991
theorem B2484971 : Blo 1100624 2484971 := bstep (se 1 (by rfl) ⟨1863728, by rfl⟩ : syracuseStep 2484971 = 3727457) B3727457
theorem B4188955 : Blo 1100624 4188955 := bstep (se 1 (by rfl) ⟨3141716, by rfl⟩ : syracuseStep 4188955 = 6283433) B6283433
theorem B35811031 : Blo 1100624 35811031 := bstep (se 1 (by rfl) ⟨26858273, by rfl⟩ : syracuseStep 35811031 = 53716547) B53716547
theorem B2096923 : Blo 1100624 2096923 := bstep (se 1 (by rfl) ⟨1572692, by rfl⟩ : syracuseStep 2096923 = 3145385) B3145385
theorem B11635559 : Blo 1100624 11635559 := bstep (se 1 (by rfl) ⟨8726669, by rfl⟩ : syracuseStep 11635559 = 17453339) B17453339
theorem B47748041 : Blo 1100624 47748041 := bstep (se 2 (by rfl) ⟨17905515, by rfl⟩ : syracuseStep 47748041 = 35811031) B35811031
theorem B9411551 : Blo 1100624 9411551 := bstep (se 1 (by rfl) ⟨7058663, by rfl⟩ : syracuseStep 9411551 = 14117327) B14117327
theorem B11938013 : Blo 1100624 11938013 := bstep (se 3 (by rfl) ⟨2238377, by rfl⟩ : syracuseStep 11938013 = 4476755) B4476755
theorem B2795897 : Blo 1100624 2795897 := bstep (se 2 (by rfl) ⟨1048461, by rfl⟩ : syracuseStep 2795897 = 2096923) B2096923
theorem B9415277 : Blo 1100624 9415277 := bstep (se 3 (by rfl) ⟨1765364, by rfl⟩ : syracuseStep 9415277 = 3530729) B3530729
theorem B114601655 : Blo 1100624 114601655 := bstep (se 1 (by rfl) ⟨85951241, by rfl⟩ : syracuseStep 114601655 = 171902483) B171902483
theorem B3715145 : Blo 1100624 3715145 := bstep (se 2 (by rfl) ⟨1393179, by rfl⟩ : syracuseStep 3715145 = 2786359) B2786359
theorem B21213353 : Blo 1100624 21213353 := bstep (se 2 (by rfl) ⟨7955007, by rfl⟩ : syracuseStep 21213353 = 15910015) B15910015
theorem B6272225 : Blo 1100624 6272225 := bstep (se 2 (by rfl) ⟨2352084, by rfl⟩ : syracuseStep 6272225 = 4704169) B4704169
theorem B1652207 : Blo 1100624 1652207 := bstep (se 1 (by rfl) ⟨1239155, by rfl⟩ : syracuseStep 1652207 = 2478311) B2478311
theorem B3717089 : Blo 1100624 3717089 := bstep (se 2 (by rfl) ⟨1393908, by rfl⟩ : syracuseStep 3717089 = 2787817) B2787817
theorem B5585273 : Blo 1100624 5585273 := bstep (se 2 (by rfl) ⟨2094477, by rfl⟩ : syracuseStep 5585273 = 4188955) B4188955
theorem B5028961 : Blo 1100624 5028961 := bstep (se 2 (by rfl) ⟨1885860, by rfl⟩ : syracuseStep 5028961 = 3771721) B3771721
theorem B49037075 : Blo 1100624 49037075 := bstep (se 1 (by rfl) ⟨36777806, by rfl⟩ : syracuseStep 49037075 = 73555613) B73555613
theorem B5095619 : Blo 1100624 5095619 := bstep (se 1 (by rfl) ⟨3821714, by rfl⟩ : syracuseStep 5095619 = 7643429) B7643429
theorem B1656647 : Blo 1100624 1656647 := bstep (se 1 (by rfl) ⟨1242485, by rfl⟩ : syracuseStep 1656647 = 2484971) B2484971
theorem B1102303 : Blo 1100624 1102303 := bstep (se 1 (by rfl) ⟨826727, by rfl⟩ : syracuseStep 1102303 = 1653455) B1653455
theorem B53567081 : Blo 1100624 53567081 := bstep (se 2 (by rfl) ⟨20087655, by rfl⟩ : syracuseStep 53567081 = 40175311) B40175311
theorem B76341851 : Blo 1100624 76341851 := bstep (se 1 (by rfl) ⟨57256388, by rfl⟩ : syracuseStep 76341851 = 114512777) B114512777
theorem B68019527 : Blo 1100624 68019527 := bstep (se 1 (by rfl) ⟨51014645, by rfl⟩ : syracuseStep 68019527 = 102029291) B102029291
theorem B5958299 : Blo 1100624 5958299 := bstep (se 1 (by rfl) ⟨4468724, by rfl⟩ : syracuseStep 5958299 = 8937449) B8937449
theorem B1862527 : Blo 1100624 1862527 := bstep (se 1 (by rfl) ⟨1396895, by rfl⟩ : syracuseStep 1862527 = 2793791) B2793791
theorem B50894567 : Blo 1100624 50894567 := bstep (se 1 (by rfl) ⟨38170925, by rfl⟩ : syracuseStep 50894567 = 76341851) B76341851
theorem B31832027 : Blo 1100624 31832027 := bstep (se 1 (by rfl) ⟨23874020, by rfl⟩ : syracuseStep 31832027 = 47748041) B47748041
theorem B6274367 : Blo 1100624 6274367 := bstep (se 1 (by rfl) ⟨4705775, by rfl⟩ : syracuseStep 6274367 = 9411551) B9411551
theorem B6276851 : Blo 1100624 6276851 := bstep (se 1 (by rfl) ⟨4707638, by rfl⟩ : syracuseStep 6276851 = 9415277) B9415277
theorem B76401103 : Blo 1100624 76401103 := bstep (se 1 (by rfl) ⟨57300827, by rfl⟩ : syracuseStep 76401103 = 114601655) B114601655
theorem B2476763 : Blo 1100624 2476763 := bstep (se 1 (by rfl) ⟨1857572, by rfl⟩ : syracuseStep 2476763 = 3715145) B3715145
theorem B14142235 : Blo 1100624 14142235 := bstep (se 1 (by rfl) ⟨10606676, by rfl⟩ : syracuseStep 14142235 = 21213353) B21213353
theorem B4181483 : Blo 1100624 4181483 := bstep (se 1 (by rfl) ⟨3136112, by rfl⟩ : syracuseStep 4181483 = 6272225) B6272225
theorem B1101471 : Blo 1100624 1101471 := bstep (se 1 (by rfl) ⟨826103, by rfl⟩ : syracuseStep 1101471 = 1652207) B1652207
theorem B2478059 : Blo 1100624 2478059 := bstep (se 1 (by rfl) ⟨1858544, by rfl⟩ : syracuseStep 2478059 = 3717089) B3717089
theorem B6705281 : Blo 1100624 6705281 := bstep (se 2 (by rfl) ⟨2514480, by rfl⟩ : syracuseStep 6705281 = 5028961) B5028961
theorem B3723515 : Blo 1100624 3723515 := bstep (se 1 (by rfl) ⟨2792636, by rfl⟩ : syracuseStep 3723515 = 5585273) B5585273
theorem B32691383 : Blo 1100624 32691383 := bstep (se 1 (by rfl) ⟨24518537, by rfl⟩ : syracuseStep 32691383 = 49037075) B49037075
theorem B3397079 : Blo 1100624 3397079 := bstep (se 1 (by rfl) ⟨2547809, by rfl⟩ : syracuseStep 3397079 = 5095619) B5095619
theorem B1104431 : Blo 1100624 1104431 := bstep (se 1 (by rfl) ⟨828323, by rfl⟩ : syracuseStep 1104431 = 1656647) B1656647
theorem B7757039 : Blo 1100624 7757039 := bstep (se 1 (by rfl) ⟨5817779, by rfl⟩ : syracuseStep 7757039 = 11635559) B11635559
theorem B2483369 : Blo 1100624 2483369 := bstep (se 2 (by rfl) ⟨931263, by rfl⟩ : syracuseStep 2483369 = 1862527) B1862527
theorem B35711387 : Blo 1100624 35711387 := bstep (se 1 (by rfl) ⟨26783540, by rfl⟩ : syracuseStep 35711387 = 53567081) B53567081
theorem B45346351 : Blo 1100624 45346351 := bstep (se 1 (by rfl) ⟨34009763, by rfl⟩ : syracuseStep 45346351 = 68019527) B68019527
theorem B7958675 : Blo 1100624 7958675 := bstep (se 1 (by rfl) ⟨5969006, by rfl⟩ : syracuseStep 7958675 = 11938013) B11938013
theorem B1863931 : Blo 1100624 1863931 := bstep (se 1 (by rfl) ⟨1397948, by rfl⟩ : syracuseStep 1863931 = 2795897) B2795897
theorem B15888797 : Blo 1100624 15888797 := bstep (se 3 (by rfl) ⟨2979149, by rfl⟩ : syracuseStep 15888797 = 5958299) B5958299
theorem B2787655 : Blo 1100624 2787655 := bstep (se 1 (by rfl) ⟨2090741, by rfl⟩ : syracuseStep 2787655 = 4181483) B4181483
theorem B21794255 : Blo 1100624 21794255 := bstep (se 1 (by rfl) ⟨16345691, by rfl⟩ : syracuseStep 21794255 = 32691383) B32691383
theorem B2264719 : Blo 1100624 2264719 := bstep (se 1 (by rfl) ⟨1698539, by rfl⟩ : syracuseStep 2264719 = 3397079) B3397079
theorem B60461801 : Blo 1100624 60461801 := bstep (se 2 (by rfl) ⟨22673175, by rfl⟩ : syracuseStep 60461801 = 45346351) B45346351
theorem B10592531 : Blo 1100624 10592531 := bstep (se 1 (by rfl) ⟨7944398, by rfl⟩ : syracuseStep 10592531 = 15888797) B15888797
theorem B1651175 : Blo 1100624 1651175 := bstep (se 1 (by rfl) ⟨1238381, by rfl⟩ : syracuseStep 1651175 = 2476763) B2476763
theorem B1652039 : Blo 1100624 1652039 := bstep (se 1 (by rfl) ⟨1239029, by rfl⟩ : syracuseStep 1652039 = 2478059) B2478059
theorem B4470187 : Blo 1100624 4470187 := bstep (se 1 (by rfl) ⟨3352640, by rfl⟩ : syracuseStep 4470187 = 6705281) B6705281
theorem B18856313 : Blo 1100624 18856313 := bstep (se 2 (by rfl) ⟨7071117, by rfl⟩ : syracuseStep 18856313 = 14142235) B14142235
theorem B33929711 : Blo 1100624 33929711 := bstep (se 1 (by rfl) ⟨25447283, by rfl⟩ : syracuseStep 33929711 = 50894567) B50894567
theorem B1655579 : Blo 1100624 1655579 := bstep (se 1 (by rfl) ⟨1241684, by rfl⟩ : syracuseStep 1655579 = 2483369) B2483369
theorem B23807591 : Blo 1100624 23807591 := bstep (se 1 (by rfl) ⟨17855693, by rfl⟩ : syracuseStep 23807591 = 35711387) B35711387
theorem B21221351 : Blo 1100624 21221351 := bstep (se 1 (by rfl) ⟨15916013, by rfl⟩ : syracuseStep 21221351 = 31832027) B31832027
theorem B4182911 : Blo 1100624 4182911 := bstep (se 1 (by rfl) ⟨3137183, by rfl⟩ : syracuseStep 4182911 = 6274367) B6274367
theorem B4184567 : Blo 1100624 4184567 := bstep (se 1 (by rfl) ⟨3138425, by rfl⟩ : syracuseStep 4184567 = 6276851) B6276851
theorem B2482343 : Blo 1100624 2482343 := bstep (se 1 (by rfl) ⟨1861757, by rfl⟩ : syracuseStep 2482343 = 3723515) B3723515
theorem B101868137 : Blo 1100624 101868137 := bstep (se 2 (by rfl) ⟨38200551, by rfl⟩ : syracuseStep 101868137 = 76401103) B76401103
theorem B5171359 : Blo 1100624 5171359 := bstep (se 1 (by rfl) ⟨3878519, by rfl⟩ : syracuseStep 5171359 = 7757039) B7757039
theorem B2485241 : Blo 1100624 2485241 := bstep (se 2 (by rfl) ⟨931965, by rfl⟩ : syracuseStep 2485241 = 1863931) B1863931
theorem B5305783 : Blo 1100624 5305783 := bstep (se 1 (by rfl) ⟨3979337, by rfl⟩ : syracuseStep 5305783 = 7958675) B7958675
theorem B40307867 : Blo 1100624 40307867 := bstep (se 1 (by rfl) ⟨30230900, by rfl⟩ : syracuseStep 40307867 = 60461801) B60461801
theorem B2788607 : Blo 1100624 2788607 := bstep (se 1 (by rfl) ⟨2091455, by rfl⟩ : syracuseStep 2788607 = 4182911) B4182911
theorem B2789711 : Blo 1100624 2789711 := bstep (se 1 (by rfl) ⟨2092283, by rfl⟩ : syracuseStep 2789711 = 4184567) B4184567
theorem B3019625 : Blo 1100624 3019625 := bstep (se 2 (by rfl) ⟨1132359, by rfl⟩ : syracuseStep 3019625 = 2264719) B2264719
theorem B22619807 : Blo 1100624 22619807 := bstep (se 1 (by rfl) ⟨16964855, by rfl⟩ : syracuseStep 22619807 = 33929711) B33929711
theorem B15871727 : Blo 1100624 15871727 := bstep (se 1 (by rfl) ⟨11903795, by rfl⟩ : syracuseStep 15871727 = 23807591) B23807591
theorem B14529503 : Blo 1100624 14529503 := bstep (se 1 (by rfl) ⟨10897127, by rfl⟩ : syracuseStep 14529503 = 21794255) B21794255
theorem B6895145 : Blo 1100624 6895145 := bstep (se 2 (by rfl) ⟨2585679, by rfl⟩ : syracuseStep 6895145 = 5171359) B5171359
theorem B3716873 : Blo 1100624 3716873 := bstep (se 2 (by rfl) ⟨1393827, by rfl⟩ : syracuseStep 3716873 = 2787655) B2787655
theorem B1654895 : Blo 1100624 1654895 := bstep (se 1 (by rfl) ⟨1241171, by rfl⟩ : syracuseStep 1654895 = 2482343) B2482343
theorem B7061687 : Blo 1100624 7061687 := bstep (se 1 (by rfl) ⟨5296265, by rfl⟩ : syracuseStep 7061687 = 10592531) B10592531
theorem B67912091 : Blo 1100624 67912091 := bstep (se 1 (by rfl) ⟨50934068, by rfl⟩ : syracuseStep 67912091 = 101868137) B101868137
theorem B1656827 : Blo 1100624 1656827 := bstep (se 1 (by rfl) ⟨1242620, by rfl⟩ : syracuseStep 1656827 = 2485241) B2485241
theorem B1100783 : Blo 1100624 1100783 := bstep (se 1 (by rfl) ⟨825587, by rfl⟩ : syracuseStep 1100783 = 1651175) B1651175
theorem B1101359 : Blo 1100624 1101359 := bstep (se 1 (by rfl) ⟨826019, by rfl⟩ : syracuseStep 1101359 = 1652039) B1652039
theorem B12570875 : Blo 1100624 12570875 := bstep (se 1 (by rfl) ⟨9428156, by rfl⟩ : syracuseStep 12570875 = 18856313) B18856313
theorem B1103719 : Blo 1100624 1103719 := bstep (se 1 (by rfl) ⟨827789, by rfl⟩ : syracuseStep 1103719 = 1655579) B1655579
theorem B14147567 : Blo 1100624 14147567 := bstep (se 1 (by rfl) ⟨10610675, by rfl⟩ : syracuseStep 14147567 = 21221351) B21221351
theorem B5960249 : Blo 1100624 5960249 := bstep (se 2 (by rfl) ⟨2235093, by rfl⟩ : syracuseStep 5960249 = 4470187) B4470187
theorem B7074377 : Blo 1100624 7074377 := bstep (se 2 (by rfl) ⟨2652891, by rfl⟩ : syracuseStep 7074377 = 5305783) B5305783
theorem B26871911 : Blo 1100624 26871911 := bstep (se 1 (by rfl) ⟨20153933, by rfl⟩ : syracuseStep 26871911 = 40307867) B40307867
theorem B15079871 : Blo 1100624 15079871 := bstep (se 1 (by rfl) ⟨11309903, by rfl⟩ : syracuseStep 15079871 = 22619807) B22619807
theorem B3973499 : Blo 1100624 3973499 := bstep (se 1 (by rfl) ⟨2980124, by rfl⟩ : syracuseStep 3973499 = 5960249) B5960249
theorem B4596763 : Blo 1100624 4596763 := bstep (se 1 (by rfl) ⟨3447572, by rfl⟩ : syracuseStep 4596763 = 6895145) B6895145
theorem B38745341 : Blo 1100624 38745341 := bstep (se 3 (by rfl) ⟨7264751, by rfl⟩ : syracuseStep 38745341 = 14529503) B14529503
theorem B2013083 : Blo 1100624 2013083 := bstep (se 1 (by rfl) ⟨1509812, by rfl⟩ : syracuseStep 2013083 = 3019625) B3019625
theorem B2477915 : Blo 1100624 2477915 := bstep (se 1 (by rfl) ⟨1858436, by rfl⟩ : syracuseStep 2477915 = 3716873) B3716873
theorem B1103263 : Blo 1100624 1103263 := bstep (se 1 (by rfl) ⟨827447, by rfl⟩ : syracuseStep 1103263 = 1654895) B1654895
theorem B4707791 : Blo 1100624 4707791 := bstep (se 1 (by rfl) ⟨3530843, by rfl⟩ : syracuseStep 4707791 = 7061687) B7061687
theorem B45274727 : Blo 1100624 45274727 := bstep (se 1 (by rfl) ⟨33956045, by rfl⟩ : syracuseStep 45274727 = 67912091) B67912091
theorem B1104551 : Blo 1100624 1104551 := bstep (se 1 (by rfl) ⟨828413, by rfl⟩ : syracuseStep 1104551 = 1656827) B1656827
theorem B1859071 : Blo 1100624 1859071 := bstep (se 1 (by rfl) ⟨1394303, by rfl⟩ : syracuseStep 1859071 = 2788607) B2788607
theorem B8380583 : Blo 1100624 8380583 := bstep (se 1 (by rfl) ⟨6285437, by rfl⟩ : syracuseStep 8380583 = 12570875) B12570875
theorem B1859807 : Blo 1100624 1859807 := bstep (se 1 (by rfl) ⟨1394855, by rfl⟩ : syracuseStep 1859807 = 2789711) B2789711
theorem B9431711 : Blo 1100624 9431711 := bstep (se 1 (by rfl) ⟨7073783, by rfl⟩ : syracuseStep 9431711 = 14147567) B14147567
theorem B10581151 : Blo 1100624 10581151 := bstep (se 1 (by rfl) ⟨7935863, by rfl⟩ : syracuseStep 10581151 = 15871727) B15871727
theorem B4716251 : Blo 1100624 4716251 := bstep (se 1 (by rfl) ⟨3537188, by rfl⟩ : syracuseStep 4716251 = 7074377) B7074377
theorem B6129017 : Blo 1100624 6129017 := bstep (se 2 (by rfl) ⟨2298381, by rfl⟩ : syracuseStep 6129017 = 4596763) B4596763
theorem B25830227 : Blo 1100624 25830227 := bstep (se 1 (by rfl) ⟨19372670, by rfl⟩ : syracuseStep 25830227 = 38745341) B38745341
theorem B1651943 : Blo 1100624 1651943 := bstep (se 1 (by rfl) ⟨1238957, by rfl⟩ : syracuseStep 1651943 = 2477915) B2477915
theorem B120732605 : Blo 1100624 120732605 := bstep (se 3 (by rfl) ⟨22637363, by rfl⟩ : syracuseStep 120732605 = 45274727) B45274727
theorem B5587055 : Blo 1100624 5587055 := bstep (se 1 (by rfl) ⟨4190291, by rfl⟩ : syracuseStep 5587055 = 8380583) B8380583
theorem B14108201 : Blo 1100624 14108201 := bstep (se 2 (by rfl) ⟨5290575, by rfl⟩ : syracuseStep 14108201 = 10581151) B10581151
theorem B2478761 : Blo 1100624 2478761 := bstep (se 2 (by rfl) ⟨929535, by rfl⟩ : syracuseStep 2478761 = 1859071) B1859071
theorem B17914607 : Blo 1100624 17914607 := bstep (se 1 (by rfl) ⟨13435955, by rfl⟩ : syracuseStep 17914607 = 26871911) B26871911
theorem B3138527 : Blo 1100624 3138527 := bstep (se 1 (by rfl) ⟨2353895, by rfl⟩ : syracuseStep 3138527 = 4707791) B4707791
theorem B10053247 : Blo 1100624 10053247 := bstep (se 1 (by rfl) ⟨7539935, by rfl⟩ : syracuseStep 10053247 = 15079871) B15079871
theorem B1239871 : Blo 1100624 1239871 := bstep (se 1 (by rfl) ⟨929903, by rfl⟩ : syracuseStep 1239871 = 1859807) B1859807
theorem B2648999 : Blo 1100624 2648999 := bstep (se 1 (by rfl) ⟨1986749, by rfl⟩ : syracuseStep 2648999 = 3973499) B3973499
theorem B6287807 : Blo 1100624 6287807 := bstep (se 1 (by rfl) ⟨4715855, by rfl⟩ : syracuseStep 6287807 = 9431711) B9431711
theorem B3144167 : Blo 1100624 3144167 := bstep (se 1 (by rfl) ⟨2358125, by rfl⟩ : syracuseStep 3144167 = 4716251) B4716251
theorem B1342055 : Blo 1100624 1342055 := bstep (se 1 (by rfl) ⟨1006541, by rfl⟩ : syracuseStep 1342055 = 2013083) B2013083
theorem B9405467 : Blo 1100624 9405467 := bstep (se 1 (by rfl) ⟨7054100, by rfl⟩ : syracuseStep 9405467 = 14108201) B14108201
theorem B13404329 : Blo 1100624 13404329 := bstep (se 2 (by rfl) ⟨5026623, by rfl⟩ : syracuseStep 13404329 = 10053247) B10053247
theorem B3578813 : Blo 1100624 3578813 := bstep (se 3 (by rfl) ⟨671027, by rfl⟩ : syracuseStep 3578813 = 1342055) B1342055
theorem B80488403 : Blo 1100624 80488403 := bstep (se 1 (by rfl) ⟨60366302, by rfl⟩ : syracuseStep 80488403 = 120732605) B120732605
theorem B8369405 : Blo 1100624 8369405 := bstep (se 3 (by rfl) ⟨1569263, by rfl⟩ : syracuseStep 8369405 = 3138527) B3138527
theorem B1652507 : Blo 1100624 1652507 := bstep (se 1 (by rfl) ⟨1239380, by rfl⟩ : syracuseStep 1652507 = 2478761) B2478761
theorem B1653161 : Blo 1100624 1653161 := bstep (se 2 (by rfl) ⟨619935, by rfl⟩ : syracuseStep 1653161 = 1239871) B1239871
theorem B11943071 : Blo 1100624 11943071 := bstep (se 1 (by rfl) ⟨8957303, by rfl⟩ : syracuseStep 11943071 = 17914607) B17914607
theorem B17220151 : Blo 1100624 17220151 := bstep (se 1 (by rfl) ⟨12915113, by rfl⟩ : syracuseStep 17220151 = 25830227) B25830227
theorem B1101295 : Blo 1100624 1101295 := bstep (se 1 (by rfl) ⟨825971, by rfl⟩ : syracuseStep 1101295 = 1651943) B1651943
theorem B3724703 : Blo 1100624 3724703 := bstep (se 1 (by rfl) ⟨2793527, by rfl⟩ : syracuseStep 3724703 = 5587055) B5587055
theorem B4086011 : Blo 1100624 4086011 := bstep (se 1 (by rfl) ⟨3064508, by rfl⟩ : syracuseStep 4086011 = 6129017) B6129017
theorem B1765999 : Blo 1100624 1765999 := bstep (se 1 (by rfl) ⟨1324499, by rfl⟩ : syracuseStep 1765999 = 2648999) B2648999
theorem B4191871 : Blo 1100624 4191871 := bstep (se 1 (by rfl) ⟨3143903, by rfl⟩ : syracuseStep 4191871 = 6287807) B6287807
theorem B2096111 : Blo 1100624 2096111 := bstep (se 1 (by rfl) ⟨1572083, by rfl⟩ : syracuseStep 2096111 = 3144167) B3144167
theorem B5579603 : Blo 1100624 5579603 := bstep (se 1 (by rfl) ⟨4184702, by rfl⟩ : syracuseStep 5579603 = 8369405) B8369405
theorem B6270311 : Blo 1100624 6270311 := bstep (se 1 (by rfl) ⟨4702733, by rfl⟩ : syracuseStep 6270311 = 9405467) B9405467
theorem B10896029 : Blo 1100624 10896029 := bstep (se 3 (by rfl) ⟨2043005, by rfl⟩ : syracuseStep 10896029 = 4086011) B4086011
theorem B53658935 : Blo 1100624 53658935 := bstep (se 1 (by rfl) ⟨40244201, by rfl⟩ : syracuseStep 53658935 = 80488403) B80488403
theorem B5589161 : Blo 1100624 5589161 := bstep (se 2 (by rfl) ⟨2095935, by rfl⟩ : syracuseStep 5589161 = 4191871) B4191871
theorem B1101671 : Blo 1100624 1101671 := bstep (se 1 (by rfl) ⟨826253, by rfl⟩ : syracuseStep 1101671 = 1652507) B1652507
theorem B1102107 : Blo 1100624 1102107 := bstep (se 1 (by rfl) ⟨826580, by rfl⟩ : syracuseStep 1102107 = 1653161) B1653161
theorem B1397407 : Blo 1100624 1397407 := bstep (se 1 (by rfl) ⟨1048055, by rfl⟩ : syracuseStep 1397407 = 2096111) B2096111
theorem B22960201 : Blo 1100624 22960201 := bstep (se 2 (by rfl) ⟨8610075, by rfl⟩ : syracuseStep 22960201 = 17220151) B17220151
theorem B8936219 : Blo 1100624 8936219 := bstep (se 1 (by rfl) ⟨6702164, by rfl⟩ : syracuseStep 8936219 = 13404329) B13404329
theorem B2483135 : Blo 1100624 2483135 := bstep (se 1 (by rfl) ⟨1862351, by rfl⟩ : syracuseStep 2483135 = 3724703) B3724703
theorem B2385875 : Blo 1100624 2385875 := bstep (se 1 (by rfl) ⟨1789406, by rfl⟩ : syracuseStep 2385875 = 3578813) B3578813
theorem B2354665 : Blo 1100624 2354665 := bstep (se 2 (by rfl) ⟨882999, by rfl⟩ : syracuseStep 2354665 = 1765999) B1765999
theorem B7962047 : Blo 1100624 7962047 := bstep (se 1 (by rfl) ⟨5971535, by rfl⟩ : syracuseStep 7962047 = 11943071) B11943071
theorem B6362333 : Blo 1100624 6362333 := bstep (se 3 (by rfl) ⟨1192937, by rfl⟩ : syracuseStep 6362333 = 2385875) B2385875
theorem B30613601 : Blo 1100624 30613601 := bstep (se 2 (by rfl) ⟨11480100, by rfl⟩ : syracuseStep 30613601 = 22960201) B22960201
theorem B3719735 : Blo 1100624 3719735 := bstep (se 1 (by rfl) ⟨2789801, by rfl⟩ : syracuseStep 3719735 = 5579603) B5579603
theorem B1655423 : Blo 1100624 1655423 := bstep (se 1 (by rfl) ⟨1241567, by rfl⟩ : syracuseStep 1655423 = 2483135) B2483135
theorem B4180207 : Blo 1100624 4180207 := bstep (se 1 (by rfl) ⟨3135155, by rfl⟩ : syracuseStep 4180207 = 6270311) B6270311
theorem B7264019 : Blo 1100624 7264019 := bstep (se 1 (by rfl) ⟨5448014, by rfl⟩ : syracuseStep 7264019 = 10896029) B10896029
theorem B35772623 : Blo 1100624 35772623 := bstep (se 1 (by rfl) ⟨26829467, by rfl⟩ : syracuseStep 35772623 = 53658935) B53658935
theorem B3726107 : Blo 1100624 3726107 := bstep (se 1 (by rfl) ⟨2794580, by rfl⟩ : syracuseStep 3726107 = 5589161) B5589161
theorem B5957479 : Blo 1100624 5957479 := bstep (se 1 (by rfl) ⟨4468109, by rfl⟩ : syracuseStep 5957479 = 8936219) B8936219
theorem B3139553 : Blo 1100624 3139553 := bstep (se 2 (by rfl) ⟨1177332, by rfl⟩ : syracuseStep 3139553 = 2354665) B2354665
theorem B1863209 : Blo 1100624 1863209 := bstep (se 2 (by rfl) ⟨698703, by rfl⟩ : syracuseStep 1863209 = 1397407) B1397407
theorem B5308031 : Blo 1100624 5308031 := bstep (se 1 (by rfl) ⟨3981023, by rfl⟩ : syracuseStep 5308031 = 7962047) B7962047
theorem B5573609 : Blo 1100624 5573609 := bstep (se 2 (by rfl) ⟨2090103, by rfl⟩ : syracuseStep 5573609 = 4180207) B4180207
theorem B7943305 : Blo 1100624 7943305 := bstep (se 2 (by rfl) ⟨2978739, by rfl⟩ : syracuseStep 7943305 = 5957479) B5957479
theorem B4241555 : Blo 1100624 4241555 := bstep (se 1 (by rfl) ⟨3181166, by rfl⟩ : syracuseStep 4241555 = 6362333) B6362333
theorem B2479823 : Blo 1100624 2479823 := bstep (se 1 (by rfl) ⟨1859867, by rfl⟩ : syracuseStep 2479823 = 3719735) B3719735
theorem B1103615 : Blo 1100624 1103615 := bstep (se 1 (by rfl) ⟨827711, by rfl⟩ : syracuseStep 1103615 = 1655423) B1655423
theorem B4842679 : Blo 1100624 4842679 := bstep (se 1 (by rfl) ⟨3632009, by rfl⟩ : syracuseStep 4842679 = 7264019) B7264019
theorem B23848415 : Blo 1100624 23848415 := bstep (se 1 (by rfl) ⟨17886311, by rfl⟩ : syracuseStep 23848415 = 35772623) B35772623
theorem B2484071 : Blo 1100624 2484071 := bstep (se 1 (by rfl) ⟨1863053, by rfl⟩ : syracuseStep 2484071 = 3726107) B3726107
theorem B20409067 : Blo 1100624 20409067 := bstep (se 1 (by rfl) ⟨15306800, by rfl⟩ : syracuseStep 20409067 = 30613601) B30613601
theorem B2093035 : Blo 1100624 2093035 := bstep (se 1 (by rfl) ⟨1569776, by rfl⟩ : syracuseStep 2093035 = 3139553) B3139553
theorem B1242139 : Blo 1100624 1242139 := bstep (se 1 (by rfl) ⟨931604, by rfl⟩ : syracuseStep 1242139 = 1863209) B1863209
theorem B3538687 : Blo 1100624 3538687 := bstep (se 1 (by rfl) ⟨2654015, by rfl⟩ : syracuseStep 3538687 = 5308031) B5308031
theorem B6456905 : Blo 1100624 6456905 := bstep (se 2 (by rfl) ⟨2421339, by rfl⟩ : syracuseStep 6456905 = 4842679) B4842679
theorem B2790713 : Blo 1100624 2790713 := bstep (se 2 (by rfl) ⟨1046517, by rfl⟩ : syracuseStep 2790713 = 2093035) B2093035
theorem B15898943 : Blo 1100624 15898943 := bstep (se 1 (by rfl) ⟨11924207, by rfl⟩ : syracuseStep 15898943 = 23848415) B23848415
theorem B10591073 : Blo 1100624 10591073 := bstep (se 2 (by rfl) ⟨3971652, by rfl⟩ : syracuseStep 10591073 = 7943305) B7943305
theorem B2827703 : Blo 1100624 2827703 := bstep (se 1 (by rfl) ⟨2120777, by rfl⟩ : syracuseStep 2827703 = 4241555) B4241555
theorem B3715739 : Blo 1100624 3715739 := bstep (se 1 (by rfl) ⟨2786804, by rfl⟩ : syracuseStep 3715739 = 5573609) B5573609
theorem B1653215 : Blo 1100624 1653215 := bstep (se 1 (by rfl) ⟨1239911, by rfl⟩ : syracuseStep 1653215 = 2479823) B2479823
theorem B1656047 : Blo 1100624 1656047 := bstep (se 1 (by rfl) ⟨1242035, by rfl⟩ : syracuseStep 1656047 = 2484071) B2484071
theorem B1656185 : Blo 1100624 1656185 := bstep (se 2 (by rfl) ⟨621069, by rfl⟩ : syracuseStep 1656185 = 1242139) B1242139
theorem B108848357 : Blo 1100624 108848357 := bstep (se 4 (by rfl) ⟨10204533, by rfl⟩ : syracuseStep 108848357 = 20409067) B20409067
theorem B4718249 : Blo 1100624 4718249 := bstep (se 2 (by rfl) ⟨1769343, by rfl⟩ : syracuseStep 4718249 = 3538687) B3538687
theorem B4304603 : Blo 1100624 4304603 := bstep (se 1 (by rfl) ⟨3228452, by rfl⟩ : syracuseStep 4304603 = 6456905) B6456905
theorem B7060715 : Blo 1100624 7060715 := bstep (se 1 (by rfl) ⟨5295536, by rfl⟩ : syracuseStep 7060715 = 10591073) B10591073
theorem B72565571 : Blo 1100624 72565571 := bstep (se 1 (by rfl) ⟨54424178, by rfl⟩ : syracuseStep 72565571 = 108848357) B108848357
theorem B1885135 : Blo 1100624 1885135 := bstep (se 1 (by rfl) ⟨1413851, by rfl⟩ : syracuseStep 1885135 = 2827703) B2827703
theorem B2477159 : Blo 1100624 2477159 := bstep (se 1 (by rfl) ⟨1857869, by rfl⟩ : syracuseStep 2477159 = 3715739) B3715739
theorem B1102143 : Blo 1100624 1102143 := bstep (se 1 (by rfl) ⟨826607, by rfl⟩ : syracuseStep 1102143 = 1653215) B1653215
theorem B1104031 : Blo 1100624 1104031 := bstep (se 1 (by rfl) ⟨828023, by rfl⟩ : syracuseStep 1104031 = 1656047) B1656047
theorem B1104123 : Blo 1100624 1104123 := bstep (se 1 (by rfl) ⟨828092, by rfl⟩ : syracuseStep 1104123 = 1656185) B1656185
theorem B1860475 : Blo 1100624 1860475 := bstep (se 1 (by rfl) ⟨1395356, by rfl⟩ : syracuseStep 1860475 = 2790713) B2790713
theorem B42397181 : Blo 1100624 42397181 := bstep (se 3 (by rfl) ⟨7949471, by rfl⟩ : syracuseStep 42397181 = 15898943) B15898943
theorem B3145499 : Blo 1100624 3145499 := bstep (se 1 (by rfl) ⟨2359124, by rfl⟩ : syracuseStep 3145499 = 4718249) B4718249
theorem B1651439 : Blo 1100624 1651439 := bstep (se 1 (by rfl) ⟨1238579, by rfl⟩ : syracuseStep 1651439 = 2477159) B2477159
theorem B193508189 : Blo 1100624 193508189 := bstep (se 3 (by rfl) ⟨36282785, by rfl⟩ : syracuseStep 193508189 = 72565571) B72565571
theorem B28264787 : Blo 1100624 28264787 := bstep (se 1 (by rfl) ⟨21198590, by rfl⟩ : syracuseStep 28264787 = 42397181) B42397181
theorem B2869735 : Blo 1100624 2869735 := bstep (se 1 (by rfl) ⟨2152301, by rfl⟩ : syracuseStep 2869735 = 4304603) B4304603
theorem B4707143 : Blo 1100624 4707143 := bstep (se 1 (by rfl) ⟨3530357, by rfl⟩ : syracuseStep 4707143 = 7060715) B7060715
theorem B2480633 : Blo 1100624 2480633 := bstep (se 2 (by rfl) ⟨930237, by rfl⟩ : syracuseStep 2480633 = 1860475) B1860475
theorem B2513513 : Blo 1100624 2513513 := bstep (se 2 (by rfl) ⟨942567, by rfl⟩ : syracuseStep 2513513 = 1885135) B1885135
theorem B2096999 : Blo 1100624 2096999 := bstep (se 1 (by rfl) ⟨1572749, by rfl⟩ : syracuseStep 2096999 = 3145499) B3145499
theorem B18843191 : Blo 1100624 18843191 := bstep (se 1 (by rfl) ⟨14132393, by rfl⟩ : syracuseStep 18843191 = 28264787) B28264787
theorem B1675675 : Blo 1100624 1675675 := bstep (se 1 (by rfl) ⟨1256756, by rfl⟩ : syracuseStep 1675675 = 2513513) B2513513
theorem B1653755 : Blo 1100624 1653755 := bstep (se 1 (by rfl) ⟨1240316, by rfl⟩ : syracuseStep 1653755 = 2480633) B2480633
theorem B1100959 : Blo 1100624 1100959 := bstep (se 1 (by rfl) ⟨825719, by rfl⟩ : syracuseStep 1100959 = 1651439) B1651439
theorem B1397999 : Blo 1100624 1397999 := bstep (se 1 (by rfl) ⟨1048499, by rfl⟩ : syracuseStep 1397999 = 2096999) B2096999
theorem B3138095 : Blo 1100624 3138095 := bstep (se 1 (by rfl) ⟨2353571, by rfl⟩ : syracuseStep 3138095 = 4707143) B4707143
theorem B3826313 : Blo 1100624 3826313 := bstep (se 2 (by rfl) ⟨1434867, by rfl⟩ : syracuseStep 3826313 = 2869735) B2869735
theorem B129005459 : Blo 1100624 129005459 := bstep (se 1 (by rfl) ⟨96754094, by rfl⟩ : syracuseStep 129005459 = 193508189) B193508189
theorem B2234233 : Blo 1100624 2234233 := bstep (se 2 (by rfl) ⟨837837, by rfl⟩ : syracuseStep 2234233 = 1675675) B1675675
theorem B12562127 : Blo 1100624 12562127 := bstep (se 1 (by rfl) ⟨9421595, by rfl⟩ : syracuseStep 12562127 = 18843191) B18843191
theorem B86003639 : Blo 1100624 86003639 := bstep (se 1 (by rfl) ⟨64502729, by rfl⟩ : syracuseStep 86003639 = 129005459) B129005459
theorem B1102503 : Blo 1100624 1102503 := bstep (se 1 (by rfl) ⟨826877, by rfl⟩ : syracuseStep 1102503 = 1653755) B1653755
theorem B3727997 : Blo 1100624 3727997 := bstep (se 3 (by rfl) ⟨698999, by rfl⟩ : syracuseStep 3727997 = 1397999) B1397999
theorem B2092063 : Blo 1100624 2092063 := bstep (se 1 (by rfl) ⟨1569047, by rfl⟩ : syracuseStep 2092063 = 3138095) B3138095
theorem B2550875 : Blo 1100624 2550875 := bstep (se 1 (by rfl) ⟨1913156, by rfl⟩ : syracuseStep 2550875 = 3826313) B3826313
theorem B2789417 : Blo 1100624 2789417 := bstep (se 2 (by rfl) ⟨1046031, by rfl⟩ : syracuseStep 2789417 = 2092063) B2092063
theorem B27209333 : Blo 1100624 27209333 := bstep (se 5 (by rfl) ⟨1275437, by rfl⟩ : syracuseStep 27209333 = 2550875) B2550875
theorem B8374751 : Blo 1100624 8374751 := bstep (se 1 (by rfl) ⟨6281063, by rfl⟩ : syracuseStep 8374751 = 12562127) B12562127
theorem B57335759 : Blo 1100624 57335759 := bstep (se 1 (by rfl) ⟨43001819, by rfl⟩ : syracuseStep 57335759 = 86003639) B86003639
theorem B2485331 : Blo 1100624 2485331 := bstep (se 1 (by rfl) ⟨1863998, by rfl⟩ : syracuseStep 2485331 = 3727997) B3727997
theorem B2978977 : Blo 1100624 2978977 := bstep (se 2 (by rfl) ⟨1117116, by rfl⟩ : syracuseStep 2978977 = 2234233) B2234233
theorem B3971969 : Blo 1100624 3971969 := bstep (se 2 (by rfl) ⟨1489488, by rfl⟩ : syracuseStep 3971969 = 2978977) B2978977
theorem B5583167 : Blo 1100624 5583167 := bstep (se 1 (by rfl) ⟨4187375, by rfl⟩ : syracuseStep 5583167 = 8374751) B8374751
theorem B38223839 : Blo 1100624 38223839 := bstep (se 1 (by rfl) ⟨28667879, by rfl⟩ : syracuseStep 38223839 = 57335759) B57335759
theorem B1656887 : Blo 1100624 1656887 := bstep (se 1 (by rfl) ⟨1242665, by rfl⟩ : syracuseStep 1656887 = 2485331) B2485331
theorem B18139555 : Blo 1100624 18139555 := bstep (se 1 (by rfl) ⟨13604666, by rfl⟩ : syracuseStep 18139555 = 27209333) B27209333
theorem B1859611 : Blo 1100624 1859611 := bstep (se 1 (by rfl) ⟨1394708, by rfl⟩ : syracuseStep 1859611 = 2789417) B2789417
theorem B96744293 : Blo 1100624 96744293 := bstep (se 4 (by rfl) ⟨9069777, by rfl⟩ : syracuseStep 96744293 = 18139555) B18139555
theorem B3722111 : Blo 1100624 3722111 := bstep (se 1 (by rfl) ⟨2791583, by rfl⟩ : syracuseStep 3722111 = 5583167) B5583167
theorem B25482559 : Blo 1100624 25482559 := bstep (se 1 (by rfl) ⟨19111919, by rfl⟩ : syracuseStep 25482559 = 38223839) B38223839
theorem B2479481 : Blo 1100624 2479481 := bstep (se 2 (by rfl) ⟨929805, by rfl⟩ : syracuseStep 2479481 = 1859611) B1859611
theorem B1104591 : Blo 1100624 1104591 := bstep (se 1 (by rfl) ⟨828443, by rfl⟩ : syracuseStep 1104591 = 1656887) B1656887
theorem B2647979 : Blo 1100624 2647979 := bstep (se 1 (by rfl) ⟨1985984, by rfl⟩ : syracuseStep 2647979 = 3971969) B3971969
theorem B64496195 : Blo 1100624 64496195 := bstep (se 1 (by rfl) ⟨48372146, by rfl⟩ : syracuseStep 64496195 = 96744293) B96744293
theorem B1652987 : Blo 1100624 1652987 := bstep (se 1 (by rfl) ⟨1239740, by rfl⟩ : syracuseStep 1652987 = 2479481) B2479481
theorem B2481407 : Blo 1100624 2481407 := bstep (se 1 (by rfl) ⟨1861055, by rfl⟩ : syracuseStep 2481407 = 3722111) B3722111
theorem B1765319 : Blo 1100624 1765319 := bstep (se 1 (by rfl) ⟨1323989, by rfl⟩ : syracuseStep 1765319 = 2647979) B2647979
theorem B33976745 : Blo 1100624 33976745 := bstep (se 2 (by rfl) ⟨12741279, by rfl⟩ : syracuseStep 33976745 = 25482559) B25482559
theorem B42997463 : Blo 1100624 42997463 := bstep (se 1 (by rfl) ⟨32248097, by rfl⟩ : syracuseStep 42997463 = 64496195) B64496195
theorem B22651163 : Blo 1100624 22651163 := bstep (se 1 (by rfl) ⟨16988372, by rfl⟩ : syracuseStep 22651163 = 33976745) B33976745
theorem B1654271 : Blo 1100624 1654271 := bstep (se 1 (by rfl) ⟨1240703, by rfl⟩ : syracuseStep 1654271 = 2481407) B2481407
theorem B1101991 : Blo 1100624 1101991 := bstep (se 1 (by rfl) ⟨826493, by rfl⟩ : syracuseStep 1101991 = 1652987) B1652987
theorem B18830069 : Blo 1100624 18830069 := bstep (se 5 (by rfl) ⟨882659, by rfl⟩ : syracuseStep 18830069 = 1765319) B1765319
theorem B12553379 : Blo 1100624 12553379 := bstep (se 1 (by rfl) ⟨9415034, by rfl⟩ : syracuseStep 12553379 = 18830069) B18830069
theorem B1102847 : Blo 1100624 1102847 := bstep (se 1 (by rfl) ⟨827135, by rfl⟩ : syracuseStep 1102847 = 1654271) B1654271
theorem B28664975 : Blo 1100624 28664975 := bstep (se 1 (by rfl) ⟨21498731, by rfl⟩ : syracuseStep 28664975 = 42997463) B42997463
theorem B15100775 : Blo 1100624 15100775 := bstep (se 1 (by rfl) ⟨11325581, by rfl⟩ : syracuseStep 15100775 = 22651163) B22651163
theorem B10067183 : Blo 1100624 10067183 := bstep (se 1 (by rfl) ⟨7550387, by rfl⟩ : syracuseStep 10067183 = 15100775) B15100775
theorem B8368919 : Blo 1100624 8368919 := bstep (se 1 (by rfl) ⟨6276689, by rfl⟩ : syracuseStep 8368919 = 12553379) B12553379
theorem B76439933 : Blo 1100624 76439933 := bstep (se 3 (by rfl) ⟨14332487, by rfl⟩ : syracuseStep 76439933 = 28664975) B28664975
theorem B50959955 : Blo 1100624 50959955 := bstep (se 1 (by rfl) ⟨38219966, by rfl⟩ : syracuseStep 50959955 = 76439933) B76439933
theorem B5579279 : Blo 1100624 5579279 := bstep (se 1 (by rfl) ⟨4184459, by rfl⟩ : syracuseStep 5579279 = 8368919) B8368919
theorem B6711455 : Blo 1100624 6711455 := bstep (se 1 (by rfl) ⟨5033591, by rfl⟩ : syracuseStep 6711455 = 10067183) B10067183
theorem B17897213 : Blo 1100624 17897213 := bstep (se 3 (by rfl) ⟨3355727, by rfl⟩ : syracuseStep 17897213 = 6711455) B6711455
theorem B3719519 : Blo 1100624 3719519 := bstep (se 1 (by rfl) ⟨2789639, by rfl⟩ : syracuseStep 3719519 = 5579279) B5579279
theorem B33973303 : Blo 1100624 33973303 := bstep (se 1 (by rfl) ⟨25479977, by rfl⟩ : syracuseStep 33973303 = 50959955) B50959955
theorem B11931475 : Blo 1100624 11931475 := bstep (se 1 (by rfl) ⟨8948606, by rfl⟩ : syracuseStep 11931475 = 17897213) B17897213
theorem B45297737 : Blo 1100624 45297737 := bstep (se 2 (by rfl) ⟨16986651, by rfl⟩ : syracuseStep 45297737 = 33973303) B33973303
theorem B2479679 : Blo 1100624 2479679 := bstep (se 1 (by rfl) ⟨1859759, by rfl⟩ : syracuseStep 2479679 = 3719519) B3719519
theorem B1653119 : Blo 1100624 1653119 := bstep (se 1 (by rfl) ⟨1239839, by rfl⟩ : syracuseStep 1653119 = 2479679) B2479679
theorem B15908633 : Blo 1100624 15908633 := bstep (se 2 (by rfl) ⟨5965737, by rfl⟩ : syracuseStep 15908633 = 11931475) B11931475
theorem B30198491 : Blo 1100624 30198491 := bstep (se 1 (by rfl) ⟨22648868, by rfl⟩ : syracuseStep 30198491 = 45297737) B45297737
theorem B20132327 : Blo 1100624 20132327 := bstep (se 1 (by rfl) ⟨15099245, by rfl⟩ : syracuseStep 20132327 = 30198491) B30198491
theorem B1102079 : Blo 1100624 1102079 := bstep (se 1 (by rfl) ⟨826559, by rfl⟩ : syracuseStep 1102079 = 1653119) B1653119
theorem B10605755 : Blo 1100624 10605755 := bstep (se 1 (by rfl) ⟨7954316, by rfl⟩ : syracuseStep 10605755 = 15908633) B15908633
theorem B13421551 : Blo 1100624 13421551 := bstep (se 1 (by rfl) ⟨10066163, by rfl⟩ : syracuseStep 13421551 = 20132327) B20132327
theorem B7070503 : Blo 1100624 7070503 := bstep (se 1 (by rfl) ⟨5302877, by rfl⟩ : syracuseStep 7070503 = 10605755) B10605755
theorem B17895401 : Blo 1100624 17895401 := bstep (se 2 (by rfl) ⟨6710775, by rfl⟩ : syracuseStep 17895401 = 13421551) B13421551
theorem B9427337 : Blo 1100624 9427337 := bstep (se 2 (by rfl) ⟨3535251, by rfl⟩ : syracuseStep 9427337 = 7070503) B7070503
theorem B11930267 : Blo 1100624 11930267 := bstep (se 1 (by rfl) ⟨8947700, by rfl⟩ : syracuseStep 11930267 = 17895401) B17895401
theorem B6284891 : Blo 1100624 6284891 := bstep (se 1 (by rfl) ⟨4713668, by rfl⟩ : syracuseStep 6284891 = 9427337) B9427337
theorem B7953511 : Blo 1100624 7953511 := bstep (se 1 (by rfl) ⟨5965133, by rfl⟩ : syracuseStep 7953511 = 11930267) B11930267
theorem B4189927 : Blo 1100624 4189927 := bstep (se 1 (by rfl) ⟨3142445, by rfl⟩ : syracuseStep 4189927 = 6284891) B6284891
theorem B5586569 : Blo 1100624 5586569 := bstep (se 2 (by rfl) ⟨2094963, by rfl⟩ : syracuseStep 5586569 = 4189927) B4189927
theorem B10604681 : Blo 1100624 10604681 := bstep (se 2 (by rfl) ⟨3976755, by rfl⟩ : syracuseStep 10604681 = 7953511) B7953511
theorem B3724379 : Blo 1100624 3724379 := bstep (se 1 (by rfl) ⟨2793284, by rfl⟩ : syracuseStep 3724379 = 5586569) B5586569
theorem B7069787 : Blo 1100624 7069787 := bstep (se 1 (by rfl) ⟨5302340, by rfl⟩ : syracuseStep 7069787 = 10604681) B10604681
theorem B2482919 : Blo 1100624 2482919 := bstep (se 1 (by rfl) ⟨1862189, by rfl⟩ : syracuseStep 2482919 = 3724379) B3724379
theorem B4713191 : Blo 1100624 4713191 := bstep (se 1 (by rfl) ⟨3534893, by rfl⟩ : syracuseStep 4713191 = 7069787) B7069787
theorem B1655279 : Blo 1100624 1655279 := bstep (se 1 (by rfl) ⟨1241459, by rfl⟩ : syracuseStep 1655279 = 2482919) B2482919
theorem B3142127 : Blo 1100624 3142127 := bstep (se 1 (by rfl) ⟨2356595, by rfl⟩ : syracuseStep 3142127 = 4713191) B4713191
theorem B1103519 : Blo 1100624 1103519 := bstep (se 1 (by rfl) ⟨827639, by rfl⟩ : syracuseStep 1103519 = 1655279) B1655279
theorem B2094751 : Blo 1100624 2094751 := bstep (se 1 (by rfl) ⟨1571063, by rfl⟩ : syracuseStep 2094751 = 3142127) B3142127
theorem B2793001 : Blo 1100624 2793001 := bstep (se 2 (by rfl) ⟨1047375, by rfl⟩ : syracuseStep 2793001 = 2094751) B2094751
theorem B3724001 : Blo 1100624 3724001 := bstep (se 2 (by rfl) ⟨1396500, by rfl⟩ : syracuseStep 3724001 = 2793001) B2793001
theorem B2482667 : Blo 1100624 2482667 := bstep (se 1 (by rfl) ⟨1862000, by rfl⟩ : syracuseStep 2482667 = 3724001) B3724001
theorem B1655111 : Blo 1100624 1655111 := bstep (se 1 (by rfl) ⟨1241333, by rfl⟩ : syracuseStep 1655111 = 2482667) B2482667
theorem B1103407 : Blo 1100624 1103407 := bstep (se 1 (by rfl) ⟨827555, by rfl⟩ : syracuseStep 1103407 = 1655111) B1655111

theorem C0 (j : ℕ) (h1 : 275156 ≤ j) (h2 : j ≤ 275855) : Blo 1100624 (4 * j + 3) := by
  interval_cases j
  · exact B1100627
  · exact B1100631
  · exact B1100635
  · exact B1100639
  · exact B1100643
  · exact B1100647
  · exact B1100651
  · exact B1100655
  · exact B1100659
  · exact B1100663
  · exact B1100667
  · exact B1100671
  · exact B1100675
  · exact B1100679
  · exact B1100683
  · exact B1100687
  · exact B1100691
  · exact B1100695
  · exact B1100699
  · exact B1100703
  · exact B1100707
  · exact B1100711
  · exact B1100715
  · exact B1100719
  · exact B1100723
  · exact B1100727
  · exact B1100731
  · exact B1100735
  · exact B1100739
  · exact B1100743
  · exact B1100747
  · exact B1100751
  · exact B1100755
  · exact B1100759
  · exact B1100763
  · exact B1100767
  · exact B1100771
  · exact B1100775
  · exact B1100779
  · exact B1100783
  · exact B1100787
  · exact B1100791
  · exact B1100795
  · exact B1100799
  · exact B1100803
  · exact B1100807
  · exact B1100811
  · exact B1100815
  · exact B1100819
  · exact B1100823
  · exact B1100827
  · exact B1100831
  · exact B1100835
  · exact B1100839
  · exact B1100843
  · exact B1100847
  · exact B1100851
  · exact B1100855
  · exact B1100859
  · exact B1100863
  · exact B1100867
  · exact B1100871
  · exact B1100875
  · exact B1100879
  · exact B1100883
  · exact B1100887
  · exact B1100891
  · exact B1100895
  · exact B1100899
  · exact B1100903
  · exact B1100907
  · exact B1100911
  · exact B1100915
  · exact B1100919
  · exact B1100923
  · exact B1100927
  · exact B1100931
  · exact B1100935
  · exact B1100939
  · exact B1100943
  · exact B1100947
  · exact B1100951
  · exact B1100955
  · exact B1100959
  · exact B1100963
  · exact B1100967
  · exact B1100971
  · exact B1100975
  · exact B1100979
  · exact B1100983
  · exact B1100987
  · exact B1100991
  · exact B1100995
  · exact B1100999
  · exact B1101003
  · exact B1101007
  · exact B1101011
  · exact B1101015
  · exact B1101019
  · exact B1101023
  · exact B1101027
  · exact B1101031
  · exact B1101035
  · exact B1101039
  · exact B1101043
  · exact B1101047
  · exact B1101051
  · exact B1101055
  · exact B1101059
  · exact B1101063
  · exact B1101067
  · exact B1101071
  · exact B1101075
  · exact B1101079
  · exact B1101083
  · exact B1101087
  · exact B1101091
  · exact B1101095
  · exact B1101099
  · exact B1101103
  · exact B1101107
  · exact B1101111
  · exact B1101115
  · exact B1101119
  · exact B1101123
  · exact B1101127
  · exact B1101131
  · exact B1101135
  · exact B1101139
  · exact B1101143
  · exact B1101147
  · exact B1101151
  · exact B1101155
  · exact B1101159
  · exact B1101163
  · exact B1101167
  · exact B1101171
  · exact B1101175
  · exact B1101179
  · exact B1101183
  · exact B1101187
  · exact B1101191
  · exact B1101195
  · exact B1101199
  · exact B1101203
  · exact B1101207
  · exact B1101211
  · exact B1101215
  · exact B1101219
  · exact B1101223
  · exact B1101227
  · exact B1101231
  · exact B1101235
  · exact B1101239
  · exact B1101243
  · exact B1101247
  · exact B1101251
  · exact B1101255
  · exact B1101259
  · exact B1101263
  · exact B1101267
  · exact B1101271
  · exact B1101275
  · exact B1101279
  · exact B1101283
  · exact B1101287
  · exact B1101291
  · exact B1101295
  · exact B1101299
  · exact B1101303
  · exact B1101307
  · exact B1101311
  · exact B1101315
  · exact B1101319
  · exact B1101323
  · exact B1101327
  · exact B1101331
  · exact B1101335
  · exact B1101339
  · exact B1101343
  · exact B1101347
  · exact B1101351
  · exact B1101355
  · exact B1101359
  · exact B1101363
  · exact B1101367
  · exact B1101371
  · exact B1101375
  · exact B1101379
  · exact B1101383
  · exact B1101387
  · exact B1101391
  · exact B1101395
  · exact B1101399
  · exact B1101403
  · exact B1101407
  · exact B1101411
  · exact B1101415
  · exact B1101419
  · exact B1101423
  · exact B1101427
  · exact B1101431
  · exact B1101435
  · exact B1101439
  · exact B1101443
  · exact B1101447
  · exact B1101451
  · exact B1101455
  · exact B1101459
  · exact B1101463
  · exact B1101467
  · exact B1101471
  · exact B1101475
  · exact B1101479
  · exact B1101483
  · exact B1101487
  · exact B1101491
  · exact B1101495
  · exact B1101499
  · exact B1101503
  · exact B1101507
  · exact B1101511
  · exact B1101515
  · exact B1101519
  · exact B1101523
  · exact B1101527
  · exact B1101531
  · exact B1101535
  · exact B1101539
  · exact B1101543
  · exact B1101547
  · exact B1101551
  · exact B1101555
  · exact B1101559
  · exact B1101563
  · exact B1101567
  · exact B1101571
  · exact B1101575
  · exact B1101579
  · exact B1101583
  · exact B1101587
  · exact B1101591
  · exact B1101595
  · exact B1101599
  · exact B1101603
  · exact B1101607
  · exact B1101611
  · exact B1101615
  · exact B1101619
  · exact B1101623
  · exact B1101627
  · exact B1101631
  · exact B1101635
  · exact B1101639
  · exact B1101643
  · exact B1101647
  · exact B1101651
  · exact B1101655
  · exact B1101659
  · exact B1101663
  · exact B1101667
  · exact B1101671
  · exact B1101675
  · exact B1101679
  · exact B1101683
  · exact B1101687
  · exact B1101691
  · exact B1101695
  · exact B1101699
  · exact B1101703
  · exact B1101707
  · exact B1101711
  · exact B1101715
  · exact B1101719
  · exact B1101723
  · exact B1101727
  · exact B1101731
  · exact B1101735
  · exact B1101739
  · exact B1101743
  · exact B1101747
  · exact B1101751
  · exact B1101755
  · exact B1101759
  · exact B1101763
  · exact B1101767
  · exact B1101771
  · exact B1101775
  · exact B1101779
  · exact B1101783
  · exact B1101787
  · exact B1101791
  · exact B1101795
  · exact B1101799
  · exact B1101803
  · exact B1101807
  · exact B1101811
  · exact B1101815
  · exact B1101819
  · exact B1101823
  · exact B1101827
  · exact B1101831
  · exact B1101835
  · exact B1101839
  · exact B1101843
  · exact B1101847
  · exact B1101851
  · exact B1101855
  · exact B1101859
  · exact B1101863
  · exact B1101867
  · exact B1101871
  · exact B1101875
  · exact B1101879
  · exact B1101883
  · exact B1101887
  · exact B1101891
  · exact B1101895
  · exact B1101899
  · exact B1101903
  · exact B1101907
  · exact B1101911
  · exact B1101915
  · exact B1101919
  · exact B1101923
  · exact B1101927
  · exact B1101931
  · exact B1101935
  · exact B1101939
  · exact B1101943
  · exact B1101947
  · exact B1101951
  · exact B1101955
  · exact B1101959
  · exact B1101963
  · exact B1101967
  · exact B1101971
  · exact B1101975
  · exact B1101979
  · exact B1101983
  · exact B1101987
  · exact B1101991
  · exact B1101995
  · exact B1101999
  · exact B1102003
  · exact B1102007
  · exact B1102011
  · exact B1102015
  · exact B1102019
  · exact B1102023
  · exact B1102027
  · exact B1102031
  · exact B1102035
  · exact B1102039
  · exact B1102043
  · exact B1102047
  · exact B1102051
  · exact B1102055
  · exact B1102059
  · exact B1102063
  · exact B1102067
  · exact B1102071
  · exact B1102075
  · exact B1102079
  · exact B1102083
  · exact B1102087
  · exact B1102091
  · exact B1102095
  · exact B1102099
  · exact B1102103
  · exact B1102107
  · exact B1102111
  · exact B1102115
  · exact B1102119
  · exact B1102123
  · exact B1102127
  · exact B1102131
  · exact B1102135
  · exact B1102139
  · exact B1102143
  · exact B1102147
  · exact B1102151
  · exact B1102155
  · exact B1102159
  · exact B1102163
  · exact B1102167
  · exact B1102171
  · exact B1102175
  · exact B1102179
  · exact B1102183
  · exact B1102187
  · exact B1102191
  · exact B1102195
  · exact B1102199
  · exact B1102203
  · exact B1102207
  · exact B1102211
  · exact B1102215
  · exact B1102219
  · exact B1102223
  · exact B1102227
  · exact B1102231
  · exact B1102235
  · exact B1102239
  · exact B1102243
  · exact B1102247
  · exact B1102251
  · exact B1102255
  · exact B1102259
  · exact B1102263
  · exact B1102267
  · exact B1102271
  · exact B1102275
  · exact B1102279
  · exact B1102283
  · exact B1102287
  · exact B1102291
  · exact B1102295
  · exact B1102299
  · exact B1102303
  · exact B1102307
  · exact B1102311
  · exact B1102315
  · exact B1102319
  · exact B1102323
  · exact B1102327
  · exact B1102331
  · exact B1102335
  · exact B1102339
  · exact B1102343
  · exact B1102347
  · exact B1102351
  · exact B1102355
  · exact B1102359
  · exact B1102363
  · exact B1102367
  · exact B1102371
  · exact B1102375
  · exact B1102379
  · exact B1102383
  · exact B1102387
  · exact B1102391
  · exact B1102395
  · exact B1102399
  · exact B1102403
  · exact B1102407
  · exact B1102411
  · exact B1102415
  · exact B1102419
  · exact B1102423
  · exact B1102427
  · exact B1102431
  · exact B1102435
  · exact B1102439
  · exact B1102443
  · exact B1102447
  · exact B1102451
  · exact B1102455
  · exact B1102459
  · exact B1102463
  · exact B1102467
  · exact B1102471
  · exact B1102475
  · exact B1102479
  · exact B1102483
  · exact B1102487
  · exact B1102491
  · exact B1102495
  · exact B1102499
  · exact B1102503
  · exact B1102507
  · exact B1102511
  · exact B1102515
  · exact B1102519
  · exact B1102523
  · exact B1102527
  · exact B1102531
  · exact B1102535
  · exact B1102539
  · exact B1102543
  · exact B1102547
  · exact B1102551
  · exact B1102555
  · exact B1102559
  · exact B1102563
  · exact B1102567
  · exact B1102571
  · exact B1102575
  · exact B1102579
  · exact B1102583
  · exact B1102587
  · exact B1102591
  · exact B1102595
  · exact B1102599
  · exact B1102603
  · exact B1102607
  · exact B1102611
  · exact B1102615
  · exact B1102619
  · exact B1102623
  · exact B1102627
  · exact B1102631
  · exact B1102635
  · exact B1102639
  · exact B1102643
  · exact B1102647
  · exact B1102651
  · exact B1102655
  · exact B1102659
  · exact B1102663
  · exact B1102667
  · exact B1102671
  · exact B1102675
  · exact B1102679
  · exact B1102683
  · exact B1102687
  · exact B1102691
  · exact B1102695
  · exact B1102699
  · exact B1102703
  · exact B1102707
  · exact B1102711
  · exact B1102715
  · exact B1102719
  · exact B1102723
  · exact B1102727
  · exact B1102731
  · exact B1102735
  · exact B1102739
  · exact B1102743
  · exact B1102747
  · exact B1102751
  · exact B1102755
  · exact B1102759
  · exact B1102763
  · exact B1102767
  · exact B1102771
  · exact B1102775
  · exact B1102779
  · exact B1102783
  · exact B1102787
  · exact B1102791
  · exact B1102795
  · exact B1102799
  · exact B1102803
  · exact B1102807
  · exact B1102811
  · exact B1102815
  · exact B1102819
  · exact B1102823
  · exact B1102827
  · exact B1102831
  · exact B1102835
  · exact B1102839
  · exact B1102843
  · exact B1102847
  · exact B1102851
  · exact B1102855
  · exact B1102859
  · exact B1102863
  · exact B1102867
  · exact B1102871
  · exact B1102875
  · exact B1102879
  · exact B1102883
  · exact B1102887
  · exact B1102891
  · exact B1102895
  · exact B1102899
  · exact B1102903
  · exact B1102907
  · exact B1102911
  · exact B1102915
  · exact B1102919
  · exact B1102923
  · exact B1102927
  · exact B1102931
  · exact B1102935
  · exact B1102939
  · exact B1102943
  · exact B1102947
  · exact B1102951
  · exact B1102955
  · exact B1102959
  · exact B1102963
  · exact B1102967
  · exact B1102971
  · exact B1102975
  · exact B1102979
  · exact B1102983
  · exact B1102987
  · exact B1102991
  · exact B1102995
  · exact B1102999
  · exact B1103003
  · exact B1103007
  · exact B1103011
  · exact B1103015
  · exact B1103019
  · exact B1103023
  · exact B1103027
  · exact B1103031
  · exact B1103035
  · exact B1103039
  · exact B1103043
  · exact B1103047
  · exact B1103051
  · exact B1103055
  · exact B1103059
  · exact B1103063
  · exact B1103067
  · exact B1103071
  · exact B1103075
  · exact B1103079
  · exact B1103083
  · exact B1103087
  · exact B1103091
  · exact B1103095
  · exact B1103099
  · exact B1103103
  · exact B1103107
  · exact B1103111
  · exact B1103115
  · exact B1103119
  · exact B1103123
  · exact B1103127
  · exact B1103131
  · exact B1103135
  · exact B1103139
  · exact B1103143
  · exact B1103147
  · exact B1103151
  · exact B1103155
  · exact B1103159
  · exact B1103163
  · exact B1103167
  · exact B1103171
  · exact B1103175
  · exact B1103179
  · exact B1103183
  · exact B1103187
  · exact B1103191
  · exact B1103195
  · exact B1103199
  · exact B1103203
  · exact B1103207
  · exact B1103211
  · exact B1103215
  · exact B1103219
  · exact B1103223
  · exact B1103227
  · exact B1103231
  · exact B1103235
  · exact B1103239
  · exact B1103243
  · exact B1103247
  · exact B1103251
  · exact B1103255
  · exact B1103259
  · exact B1103263
  · exact B1103267
  · exact B1103271
  · exact B1103275
  · exact B1103279
  · exact B1103283
  · exact B1103287
  · exact B1103291
  · exact B1103295
  · exact B1103299
  · exact B1103303
  · exact B1103307
  · exact B1103311
  · exact B1103315
  · exact B1103319
  · exact B1103323
  · exact B1103327
  · exact B1103331
  · exact B1103335
  · exact B1103339
  · exact B1103343
  · exact B1103347
  · exact B1103351
  · exact B1103355
  · exact B1103359
  · exact B1103363
  · exact B1103367
  · exact B1103371
  · exact B1103375
  · exact B1103379
  · exact B1103383
  · exact B1103387
  · exact B1103391
  · exact B1103395
  · exact B1103399
  · exact B1103403
  · exact B1103407
  · exact B1103411
  · exact B1103415
  · exact B1103419
  · exact B1103423

theorem C1 (j : ℕ) (h1 : 275856 ≤ j) (h2 : j ≤ 276155) : Blo 1100624 (4 * j + 3) := by
  interval_cases j
  · exact B1103427
  · exact B1103431
  · exact B1103435
  · exact B1103439
  · exact B1103443
  · exact B1103447
  · exact B1103451
  · exact B1103455
  · exact B1103459
  · exact B1103463
  · exact B1103467
  · exact B1103471
  · exact B1103475
  · exact B1103479
  · exact B1103483
  · exact B1103487
  · exact B1103491
  · exact B1103495
  · exact B1103499
  · exact B1103503
  · exact B1103507
  · exact B1103511
  · exact B1103515
  · exact B1103519
  · exact B1103523
  · exact B1103527
  · exact B1103531
  · exact B1103535
  · exact B1103539
  · exact B1103543
  · exact B1103547
  · exact B1103551
  · exact B1103555
  · exact B1103559
  · exact B1103563
  · exact B1103567
  · exact B1103571
  · exact B1103575
  · exact B1103579
  · exact B1103583
  · exact B1103587
  · exact B1103591
  · exact B1103595
  · exact B1103599
  · exact B1103603
  · exact B1103607
  · exact B1103611
  · exact B1103615
  · exact B1103619
  · exact B1103623
  · exact B1103627
  · exact B1103631
  · exact B1103635
  · exact B1103639
  · exact B1103643
  · exact B1103647
  · exact B1103651
  · exact B1103655
  · exact B1103659
  · exact B1103663
  · exact B1103667
  · exact B1103671
  · exact B1103675
  · exact B1103679
  · exact B1103683
  · exact B1103687
  · exact B1103691
  · exact B1103695
  · exact B1103699
  · exact B1103703
  · exact B1103707
  · exact B1103711
  · exact B1103715
  · exact B1103719
  · exact B1103723
  · exact B1103727
  · exact B1103731
  · exact B1103735
  · exact B1103739
  · exact B1103743
  · exact B1103747
  · exact B1103751
  · exact B1103755
  · exact B1103759
  · exact B1103763
  · exact B1103767
  · exact B1103771
  · exact B1103775
  · exact B1103779
  · exact B1103783
  · exact B1103787
  · exact B1103791
  · exact B1103795
  · exact B1103799
  · exact B1103803
  · exact B1103807
  · exact B1103811
  · exact B1103815
  · exact B1103819
  · exact B1103823
  · exact B1103827
  · exact B1103831
  · exact B1103835
  · exact B1103839
  · exact B1103843
  · exact B1103847
  · exact B1103851
  · exact B1103855
  · exact B1103859
  · exact B1103863
  · exact B1103867
  · exact B1103871
  · exact B1103875
  · exact B1103879
  · exact B1103883
  · exact B1103887
  · exact B1103891
  · exact B1103895
  · exact B1103899
  · exact B1103903
  · exact B1103907
  · exact B1103911
  · exact B1103915
  · exact B1103919
  · exact B1103923
  · exact B1103927
  · exact B1103931
  · exact B1103935
  · exact B1103939
  · exact B1103943
  · exact B1103947
  · exact B1103951
  · exact B1103955
  · exact B1103959
  · exact B1103963
  · exact B1103967
  · exact B1103971
  · exact B1103975
  · exact B1103979
  · exact B1103983
  · exact B1103987
  · exact B1103991
  · exact B1103995
  · exact B1103999
  · exact B1104003
  · exact B1104007
  · exact B1104011
  · exact B1104015
  · exact B1104019
  · exact B1104023
  · exact B1104027
  · exact B1104031
  · exact B1104035
  · exact B1104039
  · exact B1104043
  · exact B1104047
  · exact B1104051
  · exact B1104055
  · exact B1104059
  · exact B1104063
  · exact B1104067
  · exact B1104071
  · exact B1104075
  · exact B1104079
  · exact B1104083
  · exact B1104087
  · exact B1104091
  · exact B1104095
  · exact B1104099
  · exact B1104103
  · exact B1104107
  · exact B1104111
  · exact B1104115
  · exact B1104119
  · exact B1104123
  · exact B1104127
  · exact B1104131
  · exact B1104135
  · exact B1104139
  · exact B1104143
  · exact B1104147
  · exact B1104151
  · exact B1104155
  · exact B1104159
  · exact B1104163
  · exact B1104167
  · exact B1104171
  · exact B1104175
  · exact B1104179
  · exact B1104183
  · exact B1104187
  · exact B1104191
  · exact B1104195
  · exact B1104199
  · exact B1104203
  · exact B1104207
  · exact B1104211
  · exact B1104215
  · exact B1104219
  · exact B1104223
  · exact B1104227
  · exact B1104231
  · exact B1104235
  · exact B1104239
  · exact B1104243
  · exact B1104247
  · exact B1104251
  · exact B1104255
  · exact B1104259
  · exact B1104263
  · exact B1104267
  · exact B1104271
  · exact B1104275
  · exact B1104279
  · exact B1104283
  · exact B1104287
  · exact B1104291
  · exact B1104295
  · exact B1104299
  · exact B1104303
  · exact B1104307
  · exact B1104311
  · exact B1104315
  · exact B1104319
  · exact B1104323
  · exact B1104327
  · exact B1104331
  · exact B1104335
  · exact B1104339
  · exact B1104343
  · exact B1104347
  · exact B1104351
  · exact B1104355
  · exact B1104359
  · exact B1104363
  · exact B1104367
  · exact B1104371
  · exact B1104375
  · exact B1104379
  · exact B1104383
  · exact B1104387
  · exact B1104391
  · exact B1104395
  · exact B1104399
  · exact B1104403
  · exact B1104407
  · exact B1104411
  · exact B1104415
  · exact B1104419
  · exact B1104423
  · exact B1104427
  · exact B1104431
  · exact B1104435
  · exact B1104439
  · exact B1104443
  · exact B1104447
  · exact B1104451
  · exact B1104455
  · exact B1104459
  · exact B1104463
  · exact B1104467
  · exact B1104471
  · exact B1104475
  · exact B1104479
  · exact B1104483
  · exact B1104487
  · exact B1104491
  · exact B1104495
  · exact B1104499
  · exact B1104503
  · exact B1104507
  · exact B1104511
  · exact B1104515
  · exact B1104519
  · exact B1104523
  · exact B1104527
  · exact B1104531
  · exact B1104535
  · exact B1104539
  · exact B1104543
  · exact B1104547
  · exact B1104551
  · exact B1104555
  · exact B1104559
  · exact B1104563
  · exact B1104567
  · exact B1104571
  · exact B1104575
  · exact B1104579
  · exact B1104583
  · exact B1104587
  · exact B1104591
  · exact B1104595
  · exact B1104599
  · exact B1104603
  · exact B1104607
  · exact B1104611
  · exact B1104615
  · exact B1104619
  · exact B1104623

theorem solution (m : ℕ) (hlo : 1100624 ≤ m) (hhi : m ≤ 1104624) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 275156 ≤ j := by omega
    have hj2 : j ≤ 276155 := by omega
    have hb : Blo 1100624 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 275856 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
