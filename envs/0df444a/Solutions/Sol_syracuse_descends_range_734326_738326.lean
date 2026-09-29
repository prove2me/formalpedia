-- Prove2me | solution 1 for syracuse_descends_range_734326_738326
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T19:05:11.806991+00:00
-- url     : https://prove2.me/submissions/ba19d528-88f5-4ec4-90e2-79d748827879

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


theorem B3735557 : Blo 734326 3735557 := bbase (se 4 (by rfl) ⟨350208, by rfl⟩ : syracuseStep 3735557 = 700417) (by norm_num)
theorem B786449 : Blo 734326 786449 := bbase (se 2 (by rfl) ⟨294918, by rfl⟩ : syracuseStep 786449 = 589837) (by norm_num)
theorem B1048621 : Blo 734326 1048621 := bbase (se 3 (by rfl) ⟨196616, by rfl⟩ : syracuseStep 1048621 = 393233) (by norm_num)
theorem B1245253 : Blo 734326 1245253 := bbase (se 4 (by rfl) ⟨116742, by rfl⟩ : syracuseStep 1245253 = 233485) (by norm_num)
theorem B1572949 : Blo 734326 1572949 := bbase (se 8 (by rfl) ⟨9216, by rfl⟩ : syracuseStep 1572949 = 18433) (by norm_num)
theorem B1245341 : Blo 734326 1245341 := bbase (se 3 (by rfl) ⟨233501, by rfl⟩ : syracuseStep 1245341 = 467003) (by norm_num)
theorem B2490533 : Blo 734326 2490533 := bbase (se 4 (by rfl) ⟨233487, by rfl⟩ : syracuseStep 2490533 = 466975) (by norm_num)
theorem B1867981 : Blo 734326 1867981 := bbase (se 3 (by rfl) ⟨350246, by rfl⟩ : syracuseStep 1867981 = 700493) (by norm_num)
theorem B1769693 : Blo 734326 1769693 := bbase (se 3 (by rfl) ⟨331817, by rfl⟩ : syracuseStep 1769693 = 663635) (by norm_num)
theorem B885001 : Blo 734326 885001 := bbase (se 2 (by rfl) ⟨331875, by rfl⟩ : syracuseStep 885001 = 663751) (by norm_num)
theorem B1245469 : Blo 734326 1245469 := bbase (se 3 (by rfl) ⟨233525, by rfl⟩ : syracuseStep 1245469 = 467051) (by norm_num)
theorem B1868093 : Blo 734326 1868093 := bbase (se 3 (by rfl) ⟨350267, by rfl⟩ : syracuseStep 1868093 = 700535) (by norm_num)
theorem B885101 : Blo 734326 885101 := bbase (se 3 (by rfl) ⟨165956, by rfl⟩ : syracuseStep 885101 = 331913) (by norm_num)
theorem B1245557 : Blo 734326 1245557 := bbase (se 5 (by rfl) ⟨58385, by rfl⟩ : syracuseStep 1245557 = 116771) (by norm_num)
theorem B1048997 : Blo 734326 1048997 := bbase (se 4 (by rfl) ⟨98343, by rfl⟩ : syracuseStep 1048997 = 196687) (by norm_num)
theorem B1769933 : Blo 734326 1769933 := bbase (se 3 (by rfl) ⟨331862, by rfl⟩ : syracuseStep 1769933 = 663725) (by norm_num)
theorem B1180109 : Blo 734326 1180109 := bbase (se 3 (by rfl) ⟨221270, by rfl⟩ : syracuseStep 1180109 = 442541) (by norm_num)
theorem B786893 : Blo 734326 786893 := bbase (se 3 (by rfl) ⟨147542, by rfl⟩ : syracuseStep 786893 = 295085) (by norm_num)
theorem B1245685 : Blo 734326 1245685 := bbase (se 5 (by rfl) ⟨58391, by rfl⟩ : syracuseStep 1245685 = 116783) (by norm_num)
theorem B1868285 : Blo 734326 1868285 := bbase (se 3 (by rfl) ⟨350303, by rfl⟩ : syracuseStep 1868285 = 700607) (by norm_num)
theorem B786953 : Blo 734326 786953 := bbase (se 2 (by rfl) ⟨295107, by rfl⟩ : syracuseStep 786953 = 590215) (by norm_num)
theorem B3146309 : Blo 734326 3146309 := bbase (se 4 (by rfl) ⟨294966, by rfl⟩ : syracuseStep 3146309 = 589933) (by norm_num)
theorem B1573445 : Blo 734326 1573445 := bbase (se 4 (by rfl) ⟨147510, by rfl⟩ : syracuseStep 1573445 = 295021) (by norm_num)
theorem B1245773 : Blo 734326 1245773 := bbase (se 3 (by rfl) ⟨233582, by rfl⟩ : syracuseStep 1245773 = 467165) (by norm_num)
theorem B2490965 : Blo 734326 2490965 := bbase (se 8 (by rfl) ⟨14595, by rfl⟩ : syracuseStep 2490965 = 29191) (by norm_num)
theorem B787081 : Blo 734326 787081 := bbase (se 2 (by rfl) ⟨295155, by rfl⟩ : syracuseStep 787081 = 590311) (by norm_num)
theorem B1245901 : Blo 734326 1245901 := bbase (se 3 (by rfl) ⟨233606, by rfl⟩ : syracuseStep 1245901 = 467213) (by norm_num)
theorem B2425589 : Blo 734326 2425589 := bbase (se 5 (by rfl) ⟨113699, by rfl⟩ : syracuseStep 2425589 = 227399) (by norm_num)
theorem B885505 : Blo 734326 885505 := bbase (se 2 (by rfl) ⟨332064, by rfl⟩ : syracuseStep 885505 = 664129) (by norm_num)
theorem B1868629 : Blo 734326 1868629 := bbase (se 9 (by rfl) ⟨5474, by rfl⟩ : syracuseStep 1868629 = 10949) (by norm_num)
theorem B1344365 : Blo 734326 1344365 := bbase (se 3 (by rfl) ⟨252068, by rfl⟩ : syracuseStep 1344365 = 504137) (by norm_num)
theorem B14156693 : Blo 734326 14156693 := bbase (se 6 (by rfl) ⟨331797, by rfl⟩ : syracuseStep 14156693 = 663595) (by norm_num)
theorem B10617749 : Blo 734326 10617749 := bbase (se 6 (by rfl) ⟨248853, by rfl⟩ : syracuseStep 10617749 = 497707) (by norm_num)
theorem B1180565 : Blo 734326 1180565 := bbase (se 6 (by rfl) ⟨27669, by rfl⟩ : syracuseStep 1180565 = 55339) (by norm_num)
theorem B885661 : Blo 734326 885661 := bbase (se 3 (by rfl) ⟨166061, by rfl⟩ : syracuseStep 885661 = 332123) (by norm_num)
theorem B1868741 : Blo 734326 1868741 := bbase (se 4 (by rfl) ⟨175194, by rfl⟩ : syracuseStep 1868741 = 350389) (by norm_num)
theorem B2491397 : Blo 734326 2491397 := bbase (se 4 (by rfl) ⟨233568, by rfl⟩ : syracuseStep 2491397 = 467137) (by norm_num)
theorem B787525 : Blo 734326 787525 := bbase (se 4 (by rfl) ⟨73830, by rfl⟩ : syracuseStep 787525 = 147661) (by norm_num)
theorem B885889 : Blo 734326 885889 := bbase (se 2 (by rfl) ⟨332208, by rfl⟩ : syracuseStep 885889 = 664417) (by norm_num)
theorem B2098325 : Blo 734326 2098325 := bbase (se 6 (by rfl) ⟨49179, by rfl⟩ : syracuseStep 2098325 = 98359) (by norm_num)
theorem B787645 : Blo 734326 787645 := bbase (se 3 (by rfl) ⟨147683, by rfl⟩ : syracuseStep 787645 = 295367) (by norm_num)
theorem B3736853 : Blo 734326 3736853 := bbase (se 6 (by rfl) ⟨87582, by rfl⟩ : syracuseStep 3736853 = 175165) (by norm_num)
theorem B2491829 : Blo 734326 2491829 := bbase (se 5 (by rfl) ⟨116804, by rfl⟩ : syracuseStep 2491829 = 233609) (by norm_num)
theorem B787897 : Blo 734326 787897 := bbase (se 2 (by rfl) ⟨295461, by rfl⟩ : syracuseStep 787897 = 590923) (by norm_num)
theorem B1574333 : Blo 734326 1574333 := bbase (se 3 (by rfl) ⟨295187, by rfl⟩ : syracuseStep 1574333 = 590375) (by norm_num)
theorem B787901 : Blo 734326 787901 := bbase (se 3 (by rfl) ⟨147731, by rfl⟩ : syracuseStep 787901 = 295463) (by norm_num)
theorem B2360821 : Blo 734326 2360821 := bbase (se 5 (by rfl) ⟨110663, by rfl⟩ : syracuseStep 2360821 = 221327) (by norm_num)
theorem B1574453 : Blo 734326 1574453 := bbase (se 5 (by rfl) ⟨73802, by rfl⟩ : syracuseStep 1574453 = 147605) (by norm_num)
theorem B2098997 : Blo 734326 2098997 := bbase (se 5 (by rfl) ⟨98390, by rfl⟩ : syracuseStep 2098997 = 196781) (by norm_num)
theorem B1050421 : Blo 734326 1050421 := bbase (se 5 (by rfl) ⟨49238, by rfl⟩ : syracuseStep 1050421 = 98477) (by norm_num)
theorem B1181557 : Blo 734326 1181557 := bbase (se 5 (by rfl) ⟨55385, by rfl⟩ : syracuseStep 1181557 = 110771) (by norm_num)
theorem B14125013 : Blo 734326 14125013 := bbase (se 7 (by rfl) ⟨165527, by rfl⟩ : syracuseStep 14125013 = 331055) (by norm_num)
theorem B886745 : Blo 734326 886745 := bbase (se 2 (by rfl) ⟨332529, by rfl⟩ : syracuseStep 886745 = 665059) (by norm_num)
theorem B1771645 : Blo 734326 1771645 := bbase (se 3 (by rfl) ⟨332183, by rfl⟩ : syracuseStep 1771645 = 664367) (by norm_num)
theorem B1575085 : Blo 734326 1575085 := bbase (se 3 (by rfl) ⟨295328, by rfl⟩ : syracuseStep 1575085 = 590657) (by norm_num)
theorem B2099429 : Blo 734326 2099429 := bbase (se 4 (by rfl) ⟨196821, by rfl⟩ : syracuseStep 2099429 = 393643) (by norm_num)
theorem B4720949 : Blo 734326 4720949 := bbase (se 5 (by rfl) ⟨221294, by rfl⟩ : syracuseStep 4720949 = 442589) (by norm_num)
theorem B3148085 : Blo 734326 3148085 := bbase (se 5 (by rfl) ⟨147566, by rfl⟩ : syracuseStep 3148085 = 295133) (by norm_num)
theorem B2361653 : Blo 734326 2361653 := bbase (se 5 (by rfl) ⟨110702, by rfl⟩ : syracuseStep 2361653 = 221405) (by norm_num)
theorem B1116533 : Blo 734326 1116533 := bbase (se 5 (by rfl) ⟨52337, by rfl⟩ : syracuseStep 1116533 = 104675) (by norm_num)
theorem B1051013 : Blo 734326 1051013 := bbase (se 4 (by rfl) ⟨98532, by rfl⟩ : syracuseStep 1051013 = 197065) (by norm_num)
theorem B1051093 : Blo 734326 1051093 := bbase (se 7 (by rfl) ⟨12317, by rfl⟩ : syracuseStep 1051093 = 24635) (by norm_num)
theorem B1182205 : Blo 734326 1182205 := bbase (se 3 (by rfl) ⟨221663, by rfl⟩ : syracuseStep 1182205 = 443327) (by norm_num)
theorem B1051213 : Blo 734326 1051213 := bbase (se 3 (by rfl) ⟨197102, by rfl⟩ : syracuseStep 1051213 = 394205) (by norm_num)
theorem B2394917 : Blo 734326 2394917 := bbase (se 4 (by rfl) ⟨224523, by rfl⟩ : syracuseStep 2394917 = 449047) (by norm_num)
theorem B756649 : Blo 734326 756649 := bbase (se 2 (by rfl) ⟨283743, by rfl⟩ : syracuseStep 756649 = 567487) (by norm_num)
theorem B2100181 : Blo 734326 2100181 := bbase (se 7 (by rfl) ⟨24611, by rfl⟩ : syracuseStep 2100181 = 49223) (by norm_num)
theorem B1575973 : Blo 734326 1575973 := bbase (se 4 (by rfl) ⟨147747, by rfl⟩ : syracuseStep 1575973 = 295495) (by norm_num)
theorem B756797 : Blo 734326 756797 := bbase (se 3 (by rfl) ⟨141899, by rfl⟩ : syracuseStep 756797 = 283799) (by norm_num)
theorem B3771461 : Blo 734326 3771461 := bbase (se 4 (by rfl) ⟨353574, by rfl⟩ : syracuseStep 3771461 = 707149) (by norm_num)
theorem B1576093 : Blo 734326 1576093 := bbase (se 3 (by rfl) ⟨295517, by rfl⟩ : syracuseStep 1576093 = 591035) (by norm_num)
theorem B1576349 : Blo 734326 1576349 := bbase (se 3 (by rfl) ⟨295565, by rfl⟩ : syracuseStep 1576349 = 591131) (by norm_num)
theorem B2788789 : Blo 734326 2788789 := bbase (se 5 (by rfl) ⟨130724, by rfl⟩ : syracuseStep 2788789 = 261449) (by norm_num)
theorem B1773085 : Blo 734326 1773085 := bbase (se 3 (by rfl) ⟨332453, by rfl⟩ : syracuseStep 1773085 = 664907) (by norm_num)
theorem B1379885 : Blo 734326 1379885 := bbase (se 3 (by rfl) ⟨258728, by rfl⟩ : syracuseStep 1379885 = 517457) (by norm_num)
theorem B1674893 : Blo 734326 1674893 := bbase (se 3 (by rfl) ⟨314042, by rfl⟩ : syracuseStep 1674893 = 628085) (by norm_num)
theorem B757405 : Blo 734326 757405 := bbase (se 3 (by rfl) ⟨142013, by rfl⟩ : syracuseStep 757405 = 284027) (by norm_num)
theorem B2789093 : Blo 734326 2789093 := bbase (se 4 (by rfl) ⟨261477, by rfl⟩ : syracuseStep 2789093 = 522955) (by norm_num)
theorem B1675037 : Blo 734326 1675037 := bbase (se 3 (by rfl) ⟨314069, by rfl⟩ : syracuseStep 1675037 = 628139) (by norm_num)
theorem B15109973 : Blo 734326 15109973 := bbase (se 9 (by rfl) ⟨44267, by rfl⟩ : syracuseStep 15109973 = 88535) (by norm_num)
theorem B3543077 : Blo 734326 3543077 := bbase (se 4 (by rfl) ⟨332163, by rfl⟩ : syracuseStep 3543077 = 664327) (by norm_num)
theorem B3543173 : Blo 734326 3543173 := bbase (se 4 (by rfl) ⟨332172, by rfl⟩ : syracuseStep 3543173 = 664345) (by norm_num)
theorem B2363525 : Blo 734326 2363525 := bbase (se 4 (by rfl) ⟨221580, by rfl⟩ : syracuseStep 2363525 = 443161) (by norm_num)
theorem B1773701 : Blo 734326 1773701 := bbase (se 4 (by rfl) ⟨166284, by rfl⟩ : syracuseStep 1773701 = 332569) (by norm_num)
theorem B5902645 : Blo 734326 5902645 := bbase (se 5 (by rfl) ⟨276686, by rfl⟩ : syracuseStep 5902645 = 553373) (by norm_num)
theorem B1773893 : Blo 734326 1773893 := bbase (se 4 (by rfl) ⟨166302, by rfl⟩ : syracuseStep 1773893 = 332605) (by norm_num)
theorem B12751253 : Blo 734326 12751253 := bbase (se 6 (by rfl) ⟨298857, by rfl⟩ : syracuseStep 12751253 = 597715) (by norm_num)
theorem B2233541 : Blo 734326 2233541 := bbase (se 4 (by rfl) ⟨209394, by rfl⟩ : syracuseStep 2233541 = 418789) (by norm_num)
theorem B1676837 : Blo 734326 1676837 := bbase (se 4 (by rfl) ⟨157203, by rfl⟩ : syracuseStep 1676837 = 314407) (by norm_num)
theorem B2659973 : Blo 734326 2659973 := bbase (se 4 (by rfl) ⟨249372, by rfl⟩ : syracuseStep 2659973 = 498745) (by norm_num)
theorem B10753685 : Blo 734326 10753685 := bbase (se 6 (by rfl) ⟨252039, by rfl⟩ : syracuseStep 10753685 = 504079) (by norm_num)
theorem B2791205 : Blo 734326 2791205 := bbase (se 4 (by rfl) ⟨261675, by rfl⟩ : syracuseStep 2791205 = 523351) (by norm_num)
theorem B1120085 : Blo 734326 1120085 := bbase (se 9 (by rfl) ⟨3281, by rfl⟩ : syracuseStep 1120085 = 6563) (by norm_num)
theorem B1120133 : Blo 734326 1120133 := bbase (se 4 (by rfl) ⟨105012, by rfl⟩ : syracuseStep 1120133 = 210025) (by norm_num)
theorem B2660309 : Blo 734326 2660309 := bbase (se 7 (by rfl) ⟨31175, by rfl⟩ : syracuseStep 2660309 = 62351) (by norm_num)
theorem B3545093 : Blo 734326 3545093 := bbase (se 4 (by rfl) ⟨332352, by rfl⟩ : syracuseStep 3545093 = 664705) (by norm_num)
theorem B2791493 : Blo 734326 2791493 := bbase (se 4 (by rfl) ⟨261702, by rfl⟩ : syracuseStep 2791493 = 523405) (by norm_num)
theorem B3152357 : Blo 734326 3152357 := bbase (se 4 (by rfl) ⟨295533, by rfl⟩ : syracuseStep 3152357 = 591067) (by norm_num)
theorem B826141 : Blo 734326 826141 := bbase (se 3 (by rfl) ⟨154901, by rfl⟩ : syracuseStep 826141 = 309803) (by norm_num)
theorem B826177 : Blo 734326 826177 := bbase (se 2 (by rfl) ⟨309816, by rfl⟩ : syracuseStep 826177 = 619633) (by norm_num)
theorem B826213 : Blo 734326 826213 := bbase (se 4 (by rfl) ⟨77457, by rfl⟩ : syracuseStep 826213 = 154915) (by norm_num)
theorem B826249 : Blo 734326 826249 := bbase (se 2 (by rfl) ⟨309843, by rfl⟩ : syracuseStep 826249 = 619687) (by norm_num)
theorem B826285 : Blo 734326 826285 := bbase (se 3 (by rfl) ⟨154928, by rfl⟩ : syracuseStep 826285 = 309857) (by norm_num)
theorem B826321 : Blo 734326 826321 := bbase (se 2 (by rfl) ⟨309870, by rfl⟩ : syracuseStep 826321 = 619741) (by norm_num)
theorem B826357 : Blo 734326 826357 := bbase (se 5 (by rfl) ⟨38735, by rfl⟩ : syracuseStep 826357 = 77471) (by norm_num)
theorem B826393 : Blo 734326 826393 := bbase (se 2 (by rfl) ⟨309897, by rfl⟩ : syracuseStep 826393 = 619795) (by norm_num)
theorem B826429 : Blo 734326 826429 := bbase (se 3 (by rfl) ⟨154955, by rfl⟩ : syracuseStep 826429 = 309911) (by norm_num)
theorem B826465 : Blo 734326 826465 := bbase (se 2 (by rfl) ⟨309924, by rfl⟩ : syracuseStep 826465 = 619849) (by norm_num)
theorem B826501 : Blo 734326 826501 := bbase (se 4 (by rfl) ⟨77484, by rfl⟩ : syracuseStep 826501 = 154969) (by norm_num)
theorem B826537 : Blo 734326 826537 := bbase (se 2 (by rfl) ⟨309951, by rfl⟩ : syracuseStep 826537 = 619903) (by norm_num)
theorem B826573 : Blo 734326 826573 := bbase (se 3 (by rfl) ⟨154982, by rfl⟩ : syracuseStep 826573 = 309965) (by norm_num)
theorem B2792677 : Blo 734326 2792677 := bbase (se 4 (by rfl) ⟨261813, by rfl⟩ : syracuseStep 2792677 = 523627) (by norm_num)
theorem B826609 : Blo 734326 826609 := bbase (se 2 (by rfl) ⟨309978, by rfl⟩ : syracuseStep 826609 = 619957) (by norm_num)
theorem B826645 : Blo 734326 826645 := bbase (se 6 (by rfl) ⟨19374, by rfl⟩ : syracuseStep 826645 = 38749) (by norm_num)
theorem B826681 : Blo 734326 826681 := bbase (se 2 (by rfl) ⟨310005, by rfl⟩ : syracuseStep 826681 = 620011) (by norm_num)
theorem B826717 : Blo 734326 826717 := bbase (se 3 (by rfl) ⟨155009, by rfl⟩ : syracuseStep 826717 = 310019) (by norm_num)
theorem B826753 : Blo 734326 826753 := bbase (se 2 (by rfl) ⟨310032, by rfl⟩ : syracuseStep 826753 = 620065) (by norm_num)
theorem B3546517 : Blo 734326 3546517 := bbase (se 6 (by rfl) ⟨83121, by rfl⟩ : syracuseStep 3546517 = 166243) (by norm_num)
theorem B826789 : Blo 734326 826789 := bbase (se 4 (by rfl) ⟨77511, by rfl⟩ : syracuseStep 826789 = 155023) (by norm_num)
theorem B826825 : Blo 734326 826825 := bbase (se 2 (by rfl) ⟨310059, by rfl⟩ : syracuseStep 826825 = 620119) (by norm_num)
theorem B826861 : Blo 734326 826861 := bbase (se 3 (by rfl) ⟨155036, by rfl⟩ : syracuseStep 826861 = 310073) (by norm_num)
theorem B826897 : Blo 734326 826897 := bbase (se 2 (by rfl) ⟨310086, by rfl⟩ : syracuseStep 826897 = 620173) (by norm_num)
theorem B2792981 : Blo 734326 2792981 := bbase (se 6 (by rfl) ⟨65460, by rfl⟩ : syracuseStep 2792981 = 130921) (by norm_num)
theorem B826933 : Blo 734326 826933 := bbase (se 5 (by rfl) ⟨38762, by rfl⟩ : syracuseStep 826933 = 77525) (by norm_num)
theorem B1121861 : Blo 734326 1121861 := bbase (se 4 (by rfl) ⟨105174, by rfl⟩ : syracuseStep 1121861 = 210349) (by norm_num)
theorem B826969 : Blo 734326 826969 := bbase (se 2 (by rfl) ⟨310113, by rfl⟩ : syracuseStep 826969 = 620227) (by norm_num)
theorem B827005 : Blo 734326 827005 := bbase (se 3 (by rfl) ⟨155063, by rfl⟩ : syracuseStep 827005 = 310127) (by norm_num)
theorem B827041 : Blo 734326 827041 := bbase (se 2 (by rfl) ⟨310140, by rfl⟩ : syracuseStep 827041 = 620281) (by norm_num)
theorem B827077 : Blo 734326 827077 := bbase (se 4 (by rfl) ⟨77538, by rfl⟩ : syracuseStep 827077 = 155077) (by norm_num)
theorem B2989781 : Blo 734326 2989781 := bbase (se 7 (by rfl) ⟨35036, by rfl⟩ : syracuseStep 2989781 = 70073) (by norm_num)
theorem B827113 : Blo 734326 827113 := bbase (se 2 (by rfl) ⟨310167, by rfl⟩ : syracuseStep 827113 = 620335) (by norm_num)
theorem B827149 : Blo 734326 827149 := bbase (se 3 (by rfl) ⟨155090, by rfl⟩ : syracuseStep 827149 = 310181) (by norm_num)
theorem B827185 : Blo 734326 827185 := bbase (se 2 (by rfl) ⟨310194, by rfl⟩ : syracuseStep 827185 = 620389) (by norm_num)
theorem B827221 : Blo 734326 827221 := bbase (se 9 (by rfl) ⟨2423, by rfl⟩ : syracuseStep 827221 = 4847) (by norm_num)
theorem B827257 : Blo 734326 827257 := bbase (se 2 (by rfl) ⟨310221, by rfl⟩ : syracuseStep 827257 = 620443) (by norm_num)
theorem B827293 : Blo 734326 827293 := bbase (se 3 (by rfl) ⟨155117, by rfl⟩ : syracuseStep 827293 = 310235) (by norm_num)
theorem B827329 : Blo 734326 827329 := bbase (se 2 (by rfl) ⟨310248, by rfl⟩ : syracuseStep 827329 = 620497) (by norm_num)
theorem B827365 : Blo 734326 827365 := bbase (se 4 (by rfl) ⟨77565, by rfl⟩ : syracuseStep 827365 = 155131) (by norm_num)
theorem B827401 : Blo 734326 827401 := bbase (se 2 (by rfl) ⟨310275, by rfl⟩ : syracuseStep 827401 = 620551) (by norm_num)
theorem B827437 : Blo 734326 827437 := bbase (se 3 (by rfl) ⟨155144, by rfl⟩ : syracuseStep 827437 = 310289) (by norm_num)
theorem B4202549 : Blo 734326 4202549 := bbase (se 5 (by rfl) ⟨196994, by rfl⟩ : syracuseStep 4202549 = 393989) (by norm_num)
theorem B827473 : Blo 734326 827473 := bbase (se 2 (by rfl) ⟨310302, by rfl⟩ : syracuseStep 827473 = 620605) (by norm_num)
theorem B827509 : Blo 734326 827509 := bbase (se 5 (by rfl) ⟨38789, by rfl⟩ : syracuseStep 827509 = 77579) (by norm_num)
theorem B827545 : Blo 734326 827545 := bbase (se 2 (by rfl) ⟨310329, by rfl⟩ : syracuseStep 827545 = 620659) (by norm_num)
theorem B827581 : Blo 734326 827581 := bbase (se 3 (by rfl) ⟨155171, by rfl⟩ : syracuseStep 827581 = 310343) (by norm_num)
theorem B4726997 : Blo 734326 4726997 := bbase (se 7 (by rfl) ⟨55394, by rfl⟩ : syracuseStep 4726997 = 110789) (by norm_num)
theorem B827617 : Blo 734326 827617 := bbase (se 2 (by rfl) ⟨310356, by rfl⟩ : syracuseStep 827617 = 620713) (by norm_num)
theorem B827653 : Blo 734326 827653 := bbase (se 4 (by rfl) ⟨77592, by rfl⟩ : syracuseStep 827653 = 155185) (by norm_num)
theorem B827689 : Blo 734326 827689 := bbase (se 2 (by rfl) ⟨310383, by rfl⟩ : syracuseStep 827689 = 620767) (by norm_num)
theorem B827725 : Blo 734326 827725 := bbase (se 3 (by rfl) ⟨155198, by rfl⟩ : syracuseStep 827725 = 310397) (by norm_num)
theorem B827761 : Blo 734326 827761 := bbase (se 2 (by rfl) ⟨310410, by rfl⟩ : syracuseStep 827761 = 620821) (by norm_num)
theorem B827797 : Blo 734326 827797 := bbase (se 6 (by rfl) ⟨19401, by rfl⟩ : syracuseStep 827797 = 38803) (by norm_num)
theorem B827833 : Blo 734326 827833 := bbase (se 2 (by rfl) ⟨310437, by rfl⟩ : syracuseStep 827833 = 620875) (by norm_num)
theorem B827869 : Blo 734326 827869 := bbase (se 3 (by rfl) ⟨155225, by rfl⟩ : syracuseStep 827869 = 310451) (by norm_num)
theorem B827905 : Blo 734326 827905 := bbase (se 2 (by rfl) ⟨310464, by rfl⟩ : syracuseStep 827905 = 620929) (by norm_num)
theorem B827941 : Blo 734326 827941 := bbase (se 4 (by rfl) ⟨77619, by rfl⟩ : syracuseStep 827941 = 155239) (by norm_num)
theorem B827977 : Blo 734326 827977 := bbase (se 2 (by rfl) ⟨310491, by rfl⟩ : syracuseStep 827977 = 620983) (by norm_num)
theorem B828013 : Blo 734326 828013 := bbase (se 3 (by rfl) ⟨155252, by rfl⟩ : syracuseStep 828013 = 310505) (by norm_num)
theorem B828049 : Blo 734326 828049 := bbase (se 2 (by rfl) ⟨310518, by rfl⟩ : syracuseStep 828049 = 621037) (by norm_num)
theorem B828085 : Blo 734326 828085 := bbase (se 5 (by rfl) ⟨38816, by rfl⟩ : syracuseStep 828085 = 77633) (by norm_num)
theorem B828121 : Blo 734326 828121 := bbase (se 2 (by rfl) ⟨310545, by rfl⟩ : syracuseStep 828121 = 621091) (by norm_num)
theorem B828157 : Blo 734326 828157 := bbase (se 3 (by rfl) ⟨155279, by rfl⟩ : syracuseStep 828157 = 310559) (by norm_num)
theorem B828193 : Blo 734326 828193 := bbase (se 2 (by rfl) ⟨310572, by rfl⟩ : syracuseStep 828193 = 621145) (by norm_num)
theorem B828229 : Blo 734326 828229 := bbase (se 4 (by rfl) ⟨77646, by rfl⟩ : syracuseStep 828229 = 155293) (by norm_num)
theorem B828265 : Blo 734326 828265 := bbase (se 2 (by rfl) ⟨310599, by rfl⟩ : syracuseStep 828265 = 621199) (by norm_num)
theorem B828301 : Blo 734326 828301 := bbase (se 3 (by rfl) ⟨155306, by rfl⟩ : syracuseStep 828301 = 310613) (by norm_num)
theorem B828337 : Blo 734326 828337 := bbase (se 2 (by rfl) ⟨310626, by rfl⟩ : syracuseStep 828337 = 621253) (by norm_num)
theorem B828373 : Blo 734326 828373 := bbase (se 7 (by rfl) ⟨9707, by rfl⟩ : syracuseStep 828373 = 19415) (by norm_num)
theorem B5579765 : Blo 734326 5579765 := bbase (se 5 (by rfl) ⟨261551, by rfl⟩ : syracuseStep 5579765 = 523103) (by norm_num)
theorem B828409 : Blo 734326 828409 := bbase (se 2 (by rfl) ⟨310653, by rfl⟩ : syracuseStep 828409 = 621307) (by norm_num)
theorem B828445 : Blo 734326 828445 := bbase (se 3 (by rfl) ⟨155333, by rfl⟩ : syracuseStep 828445 = 310667) (by norm_num)
theorem B828481 : Blo 734326 828481 := bbase (se 2 (by rfl) ⟨310680, by rfl⟩ : syracuseStep 828481 = 621361) (by norm_num)
theorem B828517 : Blo 734326 828517 := bbase (se 4 (by rfl) ⟨77673, by rfl⟩ : syracuseStep 828517 = 155347) (by norm_num)
theorem B828553 : Blo 734326 828553 := bbase (se 2 (by rfl) ⟨310707, by rfl⟩ : syracuseStep 828553 = 621415) (by norm_num)
theorem B828589 : Blo 734326 828589 := bbase (se 3 (by rfl) ⟨155360, by rfl⟩ : syracuseStep 828589 = 310721) (by norm_num)
theorem B828625 : Blo 734326 828625 := bbase (se 2 (by rfl) ⟨310734, by rfl⟩ : syracuseStep 828625 = 621469) (by norm_num)
theorem B828661 : Blo 734326 828661 := bbase (se 5 (by rfl) ⟨38843, by rfl⟩ : syracuseStep 828661 = 77687) (by norm_num)
theorem B828697 : Blo 734326 828697 := bbase (se 2 (by rfl) ⟨310761, by rfl⟩ : syracuseStep 828697 = 621523) (by norm_num)
theorem B828733 : Blo 734326 828733 := bbase (se 3 (by rfl) ⟨155387, by rfl⟩ : syracuseStep 828733 = 310775) (by norm_num)
theorem B828769 : Blo 734326 828769 := bbase (se 2 (by rfl) ⟨310788, by rfl⟩ : syracuseStep 828769 = 621577) (by norm_num)
theorem B828805 : Blo 734326 828805 := bbase (se 4 (by rfl) ⟨77700, by rfl⟩ : syracuseStep 828805 = 155401) (by norm_num)
theorem B828841 : Blo 734326 828841 := bbase (se 2 (by rfl) ⟨310815, by rfl⟩ : syracuseStep 828841 = 621631) (by norm_num)
theorem B828877 : Blo 734326 828877 := bbase (se 3 (by rfl) ⟨155414, by rfl⟩ : syracuseStep 828877 = 310829) (by norm_num)
theorem B828913 : Blo 734326 828913 := bbase (se 2 (by rfl) ⟨310842, by rfl⟩ : syracuseStep 828913 = 621685) (by norm_num)
theorem B828949 : Blo 734326 828949 := bbase (se 6 (by rfl) ⟨19428, by rfl⟩ : syracuseStep 828949 = 38857) (by norm_num)
theorem B828985 : Blo 734326 828985 := bbase (se 2 (by rfl) ⟨310869, by rfl⟩ : syracuseStep 828985 = 621739) (by norm_num)
theorem B2795093 : Blo 734326 2795093 := bbase (se 8 (by rfl) ⟨16377, by rfl⟩ : syracuseStep 2795093 = 32755) (by norm_num)
theorem B829021 : Blo 734326 829021 := bbase (se 3 (by rfl) ⟨155441, by rfl⟩ : syracuseStep 829021 = 310883) (by norm_num)
theorem B829057 : Blo 734326 829057 := bbase (se 2 (by rfl) ⟨310896, by rfl⟩ : syracuseStep 829057 = 621793) (by norm_num)
theorem B829093 : Blo 734326 829093 := bbase (se 4 (by rfl) ⟨77727, by rfl⟩ : syracuseStep 829093 = 155455) (by norm_num)
theorem B829129 : Blo 734326 829129 := bbase (se 2 (by rfl) ⟨310923, by rfl⟩ : syracuseStep 829129 = 621847) (by norm_num)
theorem B829165 : Blo 734326 829165 := bbase (se 3 (by rfl) ⟨155468, by rfl⟩ : syracuseStep 829165 = 310937) (by norm_num)
theorem B829201 : Blo 734326 829201 := bbase (se 2 (by rfl) ⟨310950, by rfl⟩ : syracuseStep 829201 = 621901) (by norm_num)
theorem B829237 : Blo 734326 829237 := bbase (se 5 (by rfl) ⟨38870, by rfl⟩ : syracuseStep 829237 = 77741) (by norm_num)
theorem B829273 : Blo 734326 829273 := bbase (se 2 (by rfl) ⟨310977, by rfl⟩ : syracuseStep 829273 = 621955) (by norm_num)
theorem B2795381 : Blo 734326 2795381 := bbase (se 5 (by rfl) ⟨131033, by rfl⟩ : syracuseStep 2795381 = 262067) (by norm_num)
theorem B829309 : Blo 734326 829309 := bbase (se 3 (by rfl) ⟨155495, by rfl⟩ : syracuseStep 829309 = 310991) (by norm_num)
theorem B829345 : Blo 734326 829345 := bbase (se 2 (by rfl) ⟨311004, by rfl⟩ : syracuseStep 829345 = 622009) (by norm_num)
theorem B829381 : Blo 734326 829381 := bbase (se 4 (by rfl) ⟨77754, by rfl⟩ : syracuseStep 829381 = 155509) (by norm_num)
theorem B829417 : Blo 734326 829417 := bbase (se 2 (by rfl) ⟨311031, by rfl⟩ : syracuseStep 829417 = 622063) (by norm_num)
theorem B829453 : Blo 734326 829453 := bbase (se 3 (by rfl) ⟨155522, by rfl⟩ : syracuseStep 829453 = 311045) (by norm_num)
theorem B829489 : Blo 734326 829489 := bbase (se 2 (by rfl) ⟨311058, by rfl⟩ : syracuseStep 829489 = 622117) (by norm_num)
theorem B829525 : Blo 734326 829525 := bbase (se 8 (by rfl) ⟨4860, by rfl⟩ : syracuseStep 829525 = 9721) (by norm_num)
theorem B829561 : Blo 734326 829561 := bbase (se 2 (by rfl) ⟨311085, by rfl⟩ : syracuseStep 829561 = 622171) (by norm_num)
theorem B829597 : Blo 734326 829597 := bbase (se 3 (by rfl) ⟨155549, by rfl⟩ : syracuseStep 829597 = 311099) (by norm_num)
theorem B7088309 : Blo 734326 7088309 := bbase (se 5 (by rfl) ⟨332264, by rfl⟩ : syracuseStep 7088309 = 664529) (by norm_num)
theorem B829633 : Blo 734326 829633 := bbase (se 2 (by rfl) ⟨311112, by rfl⟩ : syracuseStep 829633 = 622225) (by norm_num)
theorem B829669 : Blo 734326 829669 := bbase (se 4 (by rfl) ⟨77781, by rfl⟩ : syracuseStep 829669 = 155563) (by norm_num)
theorem B1681661 : Blo 734326 1681661 := bbase (se 3 (by rfl) ⟨315311, by rfl⟩ : syracuseStep 1681661 = 630623) (by norm_num)
theorem B829705 : Blo 734326 829705 := bbase (se 2 (by rfl) ⟨311139, by rfl⟩ : syracuseStep 829705 = 622279) (by norm_num)
theorem B829741 : Blo 734326 829741 := bbase (se 3 (by rfl) ⟨155576, by rfl⟩ : syracuseStep 829741 = 311153) (by norm_num)
theorem B829777 : Blo 734326 829777 := bbase (se 2 (by rfl) ⟨311166, by rfl⟩ : syracuseStep 829777 = 622333) (by norm_num)
theorem B20195669 : Blo 734326 20195669 := bbase (se 10 (by rfl) ⟨29583, by rfl⟩ : syracuseStep 20195669 = 59167) (by norm_num)
theorem B829813 : Blo 734326 829813 := bbase (se 5 (by rfl) ⟨38897, by rfl⟩ : syracuseStep 829813 = 77795) (by norm_num)
theorem B829849 : Blo 734326 829849 := bbase (se 2 (by rfl) ⟨311193, by rfl⟩ : syracuseStep 829849 = 622387) (by norm_num)
theorem B829885 : Blo 734326 829885 := bbase (se 3 (by rfl) ⟨155603, by rfl⟩ : syracuseStep 829885 = 311207) (by norm_num)
theorem B829921 : Blo 734326 829921 := bbase (se 2 (by rfl) ⟨311220, by rfl⟩ : syracuseStep 829921 = 622441) (by norm_num)
theorem B829957 : Blo 734326 829957 := bbase (se 4 (by rfl) ⟨77808, by rfl⟩ : syracuseStep 829957 = 155617) (by norm_num)
theorem B829993 : Blo 734326 829993 := bbase (se 2 (by rfl) ⟨311247, by rfl⟩ : syracuseStep 829993 = 622495) (by norm_num)
theorem B830029 : Blo 734326 830029 := bbase (se 3 (by rfl) ⟨155630, by rfl⟩ : syracuseStep 830029 = 311261) (by norm_num)
theorem B830065 : Blo 734326 830065 := bbase (se 2 (by rfl) ⟨311274, by rfl⟩ : syracuseStep 830065 = 622549) (by norm_num)
theorem B830101 : Blo 734326 830101 := bbase (se 6 (by rfl) ⟨19455, by rfl⟩ : syracuseStep 830101 = 38911) (by norm_num)
theorem B830137 : Blo 734326 830137 := bbase (se 2 (by rfl) ⟨311301, by rfl⟩ : syracuseStep 830137 = 622603) (by norm_num)
theorem B830173 : Blo 734326 830173 := bbase (se 3 (by rfl) ⟨155657, by rfl⟩ : syracuseStep 830173 = 311315) (by norm_num)
theorem B830209 : Blo 734326 830209 := bbase (se 2 (by rfl) ⟨311328, by rfl⟩ : syracuseStep 830209 = 622657) (by norm_num)
theorem B994069 : Blo 734326 994069 := bbase (se 6 (by rfl) ⟨23298, by rfl⟩ : syracuseStep 994069 = 46597) (by norm_num)
theorem B830245 : Blo 734326 830245 := bbase (se 4 (by rfl) ⟨77835, by rfl⟩ : syracuseStep 830245 = 155671) (by norm_num)
theorem B994117 : Blo 734326 994117 := bbase (se 4 (by rfl) ⟨93198, by rfl⟩ : syracuseStep 994117 = 186397) (by norm_num)
theorem B830281 : Blo 734326 830281 := bbase (se 2 (by rfl) ⟨311355, by rfl⟩ : syracuseStep 830281 = 622711) (by norm_num)
theorem B830317 : Blo 734326 830317 := bbase (se 3 (by rfl) ⟨155684, by rfl⟩ : syracuseStep 830317 = 311369) (by norm_num)
theorem B830353 : Blo 734326 830353 := bbase (se 2 (by rfl) ⟨311382, by rfl⟩ : syracuseStep 830353 = 622765) (by norm_num)
theorem B830389 : Blo 734326 830389 := bbase (se 5 (by rfl) ⟨38924, by rfl⟩ : syracuseStep 830389 = 77849) (by norm_num)
theorem B830425 : Blo 734326 830425 := bbase (se 2 (by rfl) ⟨311409, by rfl⟩ : syracuseStep 830425 = 622819) (by norm_num)
theorem B830461 : Blo 734326 830461 := bbase (se 3 (by rfl) ⟨155711, by rfl⟩ : syracuseStep 830461 = 311423) (by norm_num)
theorem B2796565 : Blo 734326 2796565 := bbase (se 6 (by rfl) ⟨65544, by rfl⟩ : syracuseStep 2796565 = 131089) (by norm_num)
theorem B830497 : Blo 734326 830497 := bbase (se 2 (by rfl) ⟨311436, by rfl⟩ : syracuseStep 830497 = 622873) (by norm_num)
theorem B830533 : Blo 734326 830533 := bbase (se 4 (by rfl) ⟨77862, by rfl⟩ : syracuseStep 830533 = 155725) (by norm_num)
theorem B830569 : Blo 734326 830569 := bbase (se 2 (by rfl) ⟨311463, by rfl⟩ : syracuseStep 830569 = 622927) (by norm_num)
theorem B830605 : Blo 734326 830605 := bbase (se 3 (by rfl) ⟨155738, by rfl⟩ : syracuseStep 830605 = 311477) (by norm_num)
theorem B2993381 : Blo 734326 2993381 := bbase (se 4 (by rfl) ⟨280629, by rfl⟩ : syracuseStep 2993381 = 561259) (by norm_num)
theorem B10595605 : Blo 734326 10595605 := bbase (se 6 (by rfl) ⟨248334, by rfl⟩ : syracuseStep 10595605 = 496669) (by norm_num)
theorem B797993 : Blo 734326 797993 := bbase (se 2 (by rfl) ⟨299247, by rfl⟩ : syracuseStep 797993 = 598495) (by norm_num)
theorem B2796869 : Blo 734326 2796869 := bbase (se 4 (by rfl) ⟨262206, by rfl⟩ : syracuseStep 2796869 = 524413) (by norm_num)
theorem B32320853 : Blo 734326 32320853 := bbase (se 11 (by rfl) ⟨23672, by rfl⟩ : syracuseStep 32320853 = 47345) (by norm_num)
theorem B1682893 : Blo 734326 1682893 := bbase (se 3 (by rfl) ⟨315542, by rfl⟩ : syracuseStep 1682893 = 631085) (by norm_num)
theorem B4304341 : Blo 734326 4304341 := bbase (se 7 (by rfl) ⟨50441, by rfl⟩ : syracuseStep 4304341 = 100883) (by norm_num)
theorem B929389 : Blo 734326 929389 := bbase (se 3 (by rfl) ⟨174260, by rfl⟩ : syracuseStep 929389 = 348521) (by norm_num)
theorem B798409 : Blo 734326 798409 := bbase (se 2 (by rfl) ⟨299403, by rfl⟩ : syracuseStep 798409 = 598807) (by norm_num)
theorem B929485 : Blo 734326 929485 := bbase (se 3 (by rfl) ⟨174278, by rfl⟩ : syracuseStep 929485 = 348557) (by norm_num)
theorem B2273093 : Blo 734326 2273093 := bbase (se 4 (by rfl) ⟨213102, by rfl⟩ : syracuseStep 2273093 = 426205) (by norm_num)
theorem B929657 : Blo 734326 929657 := bbase (se 2 (by rfl) ⟨348621, by rfl⟩ : syracuseStep 929657 = 697243) (by norm_num)
theorem B1257373 : Blo 734326 1257373 := bbase (se 3 (by rfl) ⟨235757, by rfl⟩ : syracuseStep 1257373 = 471515) (by norm_num)
theorem B929713 : Blo 734326 929713 := bbase (se 2 (by rfl) ⟨348642, by rfl⟩ : syracuseStep 929713 = 697285) (by norm_num)
theorem B1683413 : Blo 734326 1683413 := bbase (se 7 (by rfl) ⟨19727, by rfl⟩ : syracuseStep 1683413 = 39455) (by norm_num)
theorem B929809 : Blo 734326 929809 := bbase (se 2 (by rfl) ⟨348678, by rfl⟩ : syracuseStep 929809 = 697357) (by norm_num)
theorem B3977333 : Blo 734326 3977333 := bbase (se 5 (by rfl) ⟨186437, by rfl⟩ : syracuseStep 3977333 = 372875) (by norm_num)
theorem B995501 : Blo 734326 995501 := bbase (se 3 (by rfl) ⟨186656, by rfl⟩ : syracuseStep 995501 = 373313) (by norm_num)
theorem B929981 : Blo 734326 929981 := bbase (se 3 (by rfl) ⟨174371, by rfl⟩ : syracuseStep 929981 = 348743) (by norm_num)
theorem B3354853 : Blo 734326 3354853 := bbase (se 4 (by rfl) ⟨314517, by rfl⟩ : syracuseStep 3354853 = 629035) (by norm_num)
theorem B930037 : Blo 734326 930037 := bbase (se 5 (by rfl) ⟨43595, by rfl⟩ : syracuseStep 930037 = 87191) (by norm_num)
theorem B930133 : Blo 734326 930133 := bbase (se 10 (by rfl) ⟨1362, by rfl⟩ : syracuseStep 930133 = 2725) (by norm_num)
theorem B930305 : Blo 734326 930305 := bbase (se 2 (by rfl) ⟨348864, by rfl⟩ : syracuseStep 930305 = 697729) (by norm_num)
theorem B930361 : Blo 734326 930361 := bbase (se 2 (by rfl) ⟨348885, by rfl⟩ : syracuseStep 930361 = 697771) (by norm_num)
theorem B930457 : Blo 734326 930457 := bbase (se 2 (by rfl) ⟨348921, by rfl⟩ : syracuseStep 930457 = 697843) (by norm_num)
theorem B996085 : Blo 734326 996085 := bbase (se 5 (by rfl) ⟨46691, by rfl⟩ : syracuseStep 996085 = 93383) (by norm_num)
theorem B930629 : Blo 734326 930629 := bbase (se 4 (by rfl) ⟨87246, by rfl⟩ : syracuseStep 930629 = 174493) (by norm_num)
theorem B930685 : Blo 734326 930685 := bbase (se 3 (by rfl) ⟨174503, by rfl⟩ : syracuseStep 930685 = 349007) (by norm_num)
theorem B3978197 : Blo 734326 3978197 := bbase (se 7 (by rfl) ⟨46619, by rfl⟩ : syracuseStep 3978197 = 93239) (by norm_num)
theorem B930781 : Blo 734326 930781 := bbase (se 3 (by rfl) ⟨174521, by rfl⟩ : syracuseStep 930781 = 349043) (by norm_num)
theorem B930953 : Blo 734326 930953 := bbase (se 2 (by rfl) ⟨349107, by rfl⟩ : syracuseStep 930953 = 698215) (by norm_num)
theorem B931009 : Blo 734326 931009 := bbase (se 2 (by rfl) ⟨349128, by rfl⟩ : syracuseStep 931009 = 698257) (by norm_num)
theorem B1193197 : Blo 734326 1193197 := bbase (se 3 (by rfl) ⟨223724, by rfl⟩ : syracuseStep 1193197 = 447449) (by norm_num)
theorem B931105 : Blo 734326 931105 := bbase (se 2 (by rfl) ⟨349164, by rfl⟩ : syracuseStep 931105 = 698329) (by norm_num)
theorem B2798981 : Blo 734326 2798981 := bbase (se 4 (by rfl) ⟨262404, by rfl⟩ : syracuseStep 2798981 = 524809) (by norm_num)
theorem B931277 : Blo 734326 931277 := bbase (se 3 (by rfl) ⟨174614, by rfl⟩ : syracuseStep 931277 = 349229) (by norm_num)
theorem B931333 : Blo 734326 931333 := bbase (se 4 (by rfl) ⟨87312, by rfl⟩ : syracuseStep 931333 = 174625) (by norm_num)
theorem B1652237 : Blo 734326 1652237 := bbase (se 3 (by rfl) ⟨309794, by rfl⟩ : syracuseStep 1652237 = 619589) (by norm_num)
theorem B8402453 : Blo 734326 8402453 := bbase (se 6 (by rfl) ⟨196932, by rfl⟩ : syracuseStep 8402453 = 393865) (by norm_num)
theorem B3192389 : Blo 734326 3192389 := bbase (se 4 (by rfl) ⟨299286, by rfl⟩ : syracuseStep 3192389 = 598573) (by norm_num)
theorem B1652309 : Blo 734326 1652309 := bbase (se 8 (by rfl) ⟨9681, by rfl⟩ : syracuseStep 1652309 = 19363) (by norm_num)
theorem B931429 : Blo 734326 931429 := bbase (se 4 (by rfl) ⟨87321, by rfl⟩ : syracuseStep 931429 = 174643) (by norm_num)
theorem B1652381 : Blo 734326 1652381 := bbase (se 3 (by rfl) ⟨309821, by rfl⟩ : syracuseStep 1652381 = 619643) (by norm_num)
theorem B2799269 : Blo 734326 2799269 := bbase (se 4 (by rfl) ⟨262431, by rfl⟩ : syracuseStep 2799269 = 524863) (by norm_num)
theorem B1652453 : Blo 734326 1652453 := bbase (se 4 (by rfl) ⟨154917, by rfl⟩ : syracuseStep 1652453 = 309835) (by norm_num)
theorem B931601 : Blo 734326 931601 := bbase (se 2 (by rfl) ⟨349350, by rfl⟩ : syracuseStep 931601 = 698701) (by norm_num)
theorem B1652525 : Blo 734326 1652525 := bbase (se 3 (by rfl) ⟨309848, by rfl⟩ : syracuseStep 1652525 = 619697) (by norm_num)
theorem B931657 : Blo 734326 931657 := bbase (se 2 (by rfl) ⟨349371, by rfl⟩ : syracuseStep 931657 = 698743) (by norm_num)
theorem B1062757 : Blo 734326 1062757 := bbase (se 4 (by rfl) ⟨99633, by rfl⟩ : syracuseStep 1062757 = 199267) (by norm_num)
theorem B1652597 : Blo 734326 1652597 := bbase (se 5 (by rfl) ⟨77465, by rfl⟩ : syracuseStep 1652597 = 154931) (by norm_num)
theorem B931753 : Blo 734326 931753 := bbase (se 2 (by rfl) ⟨349407, by rfl⟩ : syracuseStep 931753 = 698815) (by norm_num)
theorem B1652669 : Blo 734326 1652669 := bbase (se 3 (by rfl) ⟨309875, by rfl⟩ : syracuseStep 1652669 = 619751) (by norm_num)
theorem B1652741 : Blo 734326 1652741 := bbase (se 4 (by rfl) ⟨154944, by rfl⟩ : syracuseStep 1652741 = 309889) (by norm_num)
theorem B7976981 : Blo 734326 7976981 := bbase (se 6 (by rfl) ⟨186960, by rfl⟩ : syracuseStep 7976981 = 373921) (by norm_num)
theorem B1652813 : Blo 734326 1652813 := bbase (se 3 (by rfl) ⟨309902, by rfl⟩ : syracuseStep 1652813 = 619805) (by norm_num)
theorem B931925 : Blo 734326 931925 := bbase (se 8 (by rfl) ⟨5460, by rfl⟩ : syracuseStep 931925 = 10921) (by norm_num)
theorem B931981 : Blo 734326 931981 := bbase (se 3 (by rfl) ⟨174746, by rfl⟩ : syracuseStep 931981 = 349493) (by norm_num)
theorem B1652885 : Blo 734326 1652885 := bbase (se 6 (by rfl) ⟨38739, by rfl⟩ : syracuseStep 1652885 = 77479) (by norm_num)
theorem B1489117 : Blo 734326 1489117 := bbase (se 3 (by rfl) ⟨279209, by rfl⟩ : syracuseStep 1489117 = 558419) (by norm_num)
theorem B1652957 : Blo 734326 1652957 := bbase (se 3 (by rfl) ⟨309929, by rfl⟩ : syracuseStep 1652957 = 619859) (by norm_num)
theorem B932077 : Blo 734326 932077 := bbase (se 3 (by rfl) ⟨174764, by rfl⟩ : syracuseStep 932077 = 349529) (by norm_num)
theorem B1325317 : Blo 734326 1325317 := bbase (se 4 (by rfl) ⟨124248, by rfl⟩ : syracuseStep 1325317 = 248497) (by norm_num)
theorem B1653029 : Blo 734326 1653029 := bbase (se 4 (by rfl) ⟨154971, by rfl⟩ : syracuseStep 1653029 = 309943) (by norm_num)
theorem B1653101 : Blo 734326 1653101 := bbase (se 3 (by rfl) ⟨309956, by rfl⟩ : syracuseStep 1653101 = 619913) (by norm_num)
theorem B932249 : Blo 734326 932249 := bbase (se 2 (by rfl) ⟨349593, by rfl⟩ : syracuseStep 932249 = 699187) (by norm_num)
theorem B1653173 : Blo 734326 1653173 := bbase (se 5 (by rfl) ⟨77492, by rfl⟩ : syracuseStep 1653173 = 154985) (by norm_num)
theorem B932305 : Blo 734326 932305 := bbase (se 2 (by rfl) ⟨349614, by rfl⟩ : syracuseStep 932305 = 699229) (by norm_num)
theorem B1653245 : Blo 734326 1653245 := bbase (se 3 (by rfl) ⟨309983, by rfl⟩ : syracuseStep 1653245 = 619967) (by norm_num)
theorem B1325605 : Blo 734326 1325605 := bbase (se 4 (by rfl) ⟨124275, by rfl⟩ : syracuseStep 1325605 = 248551) (by norm_num)
theorem B932401 : Blo 734326 932401 := bbase (se 2 (by rfl) ⟨349650, by rfl⟩ : syracuseStep 932401 = 699301) (by norm_num)
theorem B1653317 : Blo 734326 1653317 := bbase (se 4 (by rfl) ⟨154998, by rfl⟩ : syracuseStep 1653317 = 309997) (by norm_num)
theorem B3357317 : Blo 734326 3357317 := bbase (se 4 (by rfl) ⟨314748, by rfl⟩ : syracuseStep 3357317 = 629497) (by norm_num)
theorem B1653389 : Blo 734326 1653389 := bbase (se 3 (by rfl) ⟨310010, by rfl⟩ : syracuseStep 1653389 = 620021) (by norm_num)
theorem B1653461 : Blo 734326 1653461 := bbase (se 7 (by rfl) ⟨19376, by rfl⟩ : syracuseStep 1653461 = 38753) (by norm_num)
theorem B2243285 : Blo 734326 2243285 := bbase (se 7 (by rfl) ⟨26288, by rfl⟩ : syracuseStep 2243285 = 52577) (by norm_num)
theorem B932573 : Blo 734326 932573 := bbase (se 3 (by rfl) ⟨174857, by rfl⟩ : syracuseStep 932573 = 349715) (by norm_num)
theorem B932629 : Blo 734326 932629 := bbase (se 6 (by rfl) ⟨21858, by rfl⟩ : syracuseStep 932629 = 43717) (by norm_num)
theorem B1653533 : Blo 734326 1653533 := bbase (se 3 (by rfl) ⟨310037, by rfl⟩ : syracuseStep 1653533 = 620075) (by norm_num)
theorem B2800453 : Blo 734326 2800453 := bbase (se 4 (by rfl) ⟨262542, by rfl⟩ : syracuseStep 2800453 = 525085) (by norm_num)
theorem B1653605 : Blo 734326 1653605 := bbase (se 4 (by rfl) ⟨155025, by rfl⟩ : syracuseStep 1653605 = 310051) (by norm_num)
theorem B932725 : Blo 734326 932725 := bbase (se 5 (by rfl) ⟨43721, by rfl⟩ : syracuseStep 932725 = 87443) (by norm_num)
theorem B7093109 : Blo 734326 7093109 := bbase (se 5 (by rfl) ⟨332489, by rfl⟩ : syracuseStep 7093109 = 664979) (by norm_num)
theorem B1653677 : Blo 734326 1653677 := bbase (se 3 (by rfl) ⟨310064, by rfl⟩ : syracuseStep 1653677 = 620129) (by norm_num)
theorem B1653749 : Blo 734326 1653749 := bbase (se 5 (by rfl) ⟨77519, by rfl⟩ : syracuseStep 1653749 = 155039) (by norm_num)
theorem B932897 : Blo 734326 932897 := bbase (se 2 (by rfl) ⟨349836, by rfl⟩ : syracuseStep 932897 = 699673) (by norm_num)
theorem B1653821 : Blo 734326 1653821 := bbase (se 3 (by rfl) ⟨310091, by rfl⟩ : syracuseStep 1653821 = 620183) (by norm_num)
theorem B932953 : Blo 734326 932953 := bbase (se 2 (by rfl) ⟨349857, by rfl⟩ : syracuseStep 932953 = 699715) (by norm_num)
theorem B1326181 : Blo 734326 1326181 := bbase (se 4 (by rfl) ⟨124329, by rfl⟩ : syracuseStep 1326181 = 248659) (by norm_num)
theorem B2800757 : Blo 734326 2800757 := bbase (se 5 (by rfl) ⟨131285, by rfl⟩ : syracuseStep 2800757 = 262571) (by norm_num)
theorem B1653893 : Blo 734326 1653893 := bbase (se 4 (by rfl) ⟨155052, by rfl⟩ : syracuseStep 1653893 = 310105) (by norm_num)
theorem B933049 : Blo 734326 933049 := bbase (se 2 (by rfl) ⟨349893, by rfl⟩ : syracuseStep 933049 = 699787) (by norm_num)
theorem B1653965 : Blo 734326 1653965 := bbase (se 3 (by rfl) ⟨310118, by rfl⟩ : syracuseStep 1653965 = 620237) (by norm_num)
theorem B933125 : Blo 734326 933125 := bbase (se 4 (by rfl) ⟨87480, by rfl⟩ : syracuseStep 933125 = 174961) (by norm_num)
theorem B1654037 : Blo 734326 1654037 := bbase (se 6 (by rfl) ⟨38766, by rfl⟩ : syracuseStep 1654037 = 77533) (by norm_num)
theorem B1064245 : Blo 734326 1064245 := bbase (se 5 (by rfl) ⟨49886, by rfl⟩ : syracuseStep 1064245 = 99773) (by norm_num)
theorem B1654109 : Blo 734326 1654109 := bbase (se 3 (by rfl) ⟨310145, by rfl⟩ : syracuseStep 1654109 = 620291) (by norm_num)
theorem B933221 : Blo 734326 933221 := bbase (se 4 (by rfl) ⟨87489, by rfl⟩ : syracuseStep 933221 = 174979) (by norm_num)
theorem B933277 : Blo 734326 933277 := bbase (se 3 (by rfl) ⟨174989, by rfl⟩ : syracuseStep 933277 = 349979) (by norm_num)
theorem B1654181 : Blo 734326 1654181 := bbase (se 4 (by rfl) ⟨155079, by rfl⟩ : syracuseStep 1654181 = 310159) (by norm_num)
theorem B1654253 : Blo 734326 1654253 := bbase (se 3 (by rfl) ⟨310172, by rfl⟩ : syracuseStep 1654253 = 620345) (by norm_num)
theorem B933373 : Blo 734326 933373 := bbase (se 3 (by rfl) ⟨175007, by rfl⟩ : syracuseStep 933373 = 350015) (by norm_num)
theorem B3784229 : Blo 734326 3784229 := bbase (se 4 (by rfl) ⟨354771, by rfl⟩ : syracuseStep 3784229 = 709543) (by norm_num)
theorem B3718709 : Blo 734326 3718709 := bbase (se 5 (by rfl) ⟨174314, by rfl⟩ : syracuseStep 3718709 = 348629) (by norm_num)
theorem B1654325 : Blo 734326 1654325 := bbase (se 5 (by rfl) ⟨77546, by rfl⟩ : syracuseStep 1654325 = 155093) (by norm_num)
theorem B1326701 : Blo 734326 1326701 := bbase (se 3 (by rfl) ⟨248756, by rfl⟩ : syracuseStep 1326701 = 497513) (by norm_num)
theorem B1654397 : Blo 734326 1654397 := bbase (se 3 (by rfl) ⟨310199, by rfl⟩ : syracuseStep 1654397 = 620399) (by norm_num)
theorem B933545 : Blo 734326 933545 := bbase (se 2 (by rfl) ⟨350079, by rfl⟩ : syracuseStep 933545 = 700159) (by norm_num)
theorem B1654469 : Blo 734326 1654469 := bbase (se 4 (by rfl) ⟨155106, by rfl⟩ : syracuseStep 1654469 = 310213) (by norm_num)
theorem B933601 : Blo 734326 933601 := bbase (se 2 (by rfl) ⟨350100, by rfl⟩ : syracuseStep 933601 = 700201) (by norm_num)
theorem B1654541 : Blo 734326 1654541 := bbase (se 3 (by rfl) ⟨310226, by rfl⟩ : syracuseStep 1654541 = 620453) (by norm_num)
theorem B933697 : Blo 734326 933697 := bbase (se 2 (by rfl) ⟨350136, by rfl⟩ : syracuseStep 933697 = 700273) (by norm_num)
theorem B1654613 : Blo 734326 1654613 := bbase (se 9 (by rfl) ⟨4847, by rfl⟩ : syracuseStep 1654613 = 9695) (by norm_num)
theorem B1654685 : Blo 734326 1654685 := bbase (se 3 (by rfl) ⟨310253, by rfl⟩ : syracuseStep 1654685 = 620507) (by norm_num)
theorem B1327061 : Blo 734326 1327061 := bbase (se 7 (by rfl) ⟨15551, by rfl⟩ : syracuseStep 1327061 = 31103) (by norm_num)
theorem B1654757 : Blo 734326 1654757 := bbase (se 4 (by rfl) ⟨155133, by rfl⟩ : syracuseStep 1654757 = 310267) (by norm_num)
theorem B933869 : Blo 734326 933869 := bbase (se 3 (by rfl) ⟨175100, by rfl⟩ : syracuseStep 933869 = 350201) (by norm_num)
theorem B933925 : Blo 734326 933925 := bbase (se 4 (by rfl) ⟨87555, by rfl⟩ : syracuseStep 933925 = 175111) (by norm_num)
theorem B1654829 : Blo 734326 1654829 := bbase (se 3 (by rfl) ⟨310280, by rfl⟩ : syracuseStep 1654829 = 620561) (by norm_num)
theorem B1491013 : Blo 734326 1491013 := bbase (se 4 (by rfl) ⟨139782, by rfl⟩ : syracuseStep 1491013 = 279565) (by norm_num)
theorem B1327213 : Blo 734326 1327213 := bbase (se 3 (by rfl) ⟨248852, by rfl⟩ : syracuseStep 1327213 = 497705) (by norm_num)
theorem B1654901 : Blo 734326 1654901 := bbase (se 5 (by rfl) ⟨77573, by rfl⟩ : syracuseStep 1654901 = 155147) (by norm_num)
theorem B934021 : Blo 734326 934021 := bbase (se 4 (by rfl) ⟨87564, by rfl⟩ : syracuseStep 934021 = 175129) (by norm_num)
theorem B1654973 : Blo 734326 1654973 := bbase (se 3 (by rfl) ⟨310307, by rfl⟩ : syracuseStep 1654973 = 620615) (by norm_num)
theorem B1655045 : Blo 734326 1655045 := bbase (se 4 (by rfl) ⟨155160, by rfl⟩ : syracuseStep 1655045 = 310321) (by norm_num)
theorem B934193 : Blo 734326 934193 := bbase (se 2 (by rfl) ⟨350322, by rfl⟩ : syracuseStep 934193 = 700645) (by norm_num)
theorem B1818949 : Blo 734326 1818949 := bbase (se 4 (by rfl) ⟨170526, by rfl⟩ : syracuseStep 1818949 = 341053) (by norm_num)
theorem B1655117 : Blo 734326 1655117 := bbase (se 3 (by rfl) ⟨310334, by rfl⟩ : syracuseStep 1655117 = 620669) (by norm_num)
theorem B934249 : Blo 734326 934249 := bbase (se 2 (by rfl) ⟨350343, by rfl⟩ : syracuseStep 934249 = 700687) (by norm_num)
theorem B1655189 : Blo 734326 1655189 := bbase (se 6 (by rfl) ⟨38793, by rfl⟩ : syracuseStep 1655189 = 77587) (by norm_num)
theorem B7553429 : Blo 734326 7553429 := bbase (se 6 (by rfl) ⟨177033, by rfl⟩ : syracuseStep 7553429 = 354067) (by norm_num)
theorem B934345 : Blo 734326 934345 := bbase (se 2 (by rfl) ⟨350379, by rfl⟩ : syracuseStep 934345 = 700759) (by norm_num)
theorem B1655261 : Blo 734326 1655261 := bbase (se 3 (by rfl) ⟨310361, by rfl⟩ : syracuseStep 1655261 = 620723) (by norm_num)
theorem B5980661 : Blo 734326 5980661 := bbase (se 5 (by rfl) ⟨280343, by rfl⟩ : syracuseStep 5980661 = 560687) (by norm_num)
theorem B1065469 : Blo 734326 1065469 := bbase (se 3 (by rfl) ⟨199775, by rfl⟩ : syracuseStep 1065469 = 399551) (by norm_num)
theorem B1655333 : Blo 734326 1655333 := bbase (se 4 (by rfl) ⟨155187, by rfl⟩ : syracuseStep 1655333 = 310375) (by norm_num)
theorem B5587541 : Blo 734326 5587541 := bbase (se 8 (by rfl) ⟨32739, by rfl⟩ : syracuseStep 5587541 = 65479) (by norm_num)
theorem B1655405 : Blo 734326 1655405 := bbase (se 3 (by rfl) ⟨310388, by rfl⟩ : syracuseStep 1655405 = 620777) (by norm_num)
theorem B1655477 : Blo 734326 1655477 := bbase (se 5 (by rfl) ⟨77600, by rfl⟩ : syracuseStep 1655477 = 155201) (by norm_num)
theorem B1655549 : Blo 734326 1655549 := bbase (se 3 (by rfl) ⟨310415, by rfl⟩ : syracuseStep 1655549 = 620831) (by norm_num)
theorem B3720005 : Blo 734326 3720005 := bbase (se 4 (by rfl) ⟨348750, by rfl⟩ : syracuseStep 3720005 = 697501) (by norm_num)
theorem B1655621 : Blo 734326 1655621 := bbase (se 4 (by rfl) ⟨155214, by rfl⟩ : syracuseStep 1655621 = 310429) (by norm_num)
theorem B1655693 : Blo 734326 1655693 := bbase (se 3 (by rfl) ⟨310442, by rfl⟩ : syracuseStep 1655693 = 620885) (by norm_num)
theorem B1655765 : Blo 734326 1655765 := bbase (se 7 (by rfl) ⟨19403, by rfl⟩ : syracuseStep 1655765 = 38807) (by norm_num)
theorem B1655837 : Blo 734326 1655837 := bbase (se 3 (by rfl) ⟨310469, by rfl⟩ : syracuseStep 1655837 = 620939) (by norm_num)
theorem B1655909 : Blo 734326 1655909 := bbase (se 4 (by rfl) ⟨155241, by rfl⟩ : syracuseStep 1655909 = 310483) (by norm_num)
theorem B1655981 : Blo 734326 1655981 := bbase (se 3 (by rfl) ⟨310496, by rfl⟩ : syracuseStep 1655981 = 620993) (by norm_num)
theorem B1328309 : Blo 734326 1328309 := bbase (se 5 (by rfl) ⟨62264, by rfl⟩ : syracuseStep 1328309 = 124529) (by norm_num)
theorem B2802869 : Blo 734326 2802869 := bbase (se 5 (by rfl) ⟨131384, by rfl⟩ : syracuseStep 2802869 = 262769) (by norm_num)
theorem B1656053 : Blo 734326 1656053 := bbase (se 5 (by rfl) ⟨77627, by rfl⟩ : syracuseStep 1656053 = 155255) (by norm_num)
theorem B1656125 : Blo 734326 1656125 := bbase (se 3 (by rfl) ⟨310523, by rfl⟩ : syracuseStep 1656125 = 621047) (by norm_num)
theorem B1656197 : Blo 734326 1656197 := bbase (se 4 (by rfl) ⟨155268, by rfl⟩ : syracuseStep 1656197 = 310537) (by norm_num)
theorem B1656269 : Blo 734326 1656269 := bbase (se 3 (by rfl) ⟨310550, by rfl⟩ : syracuseStep 1656269 = 621101) (by norm_num)
theorem B2803157 : Blo 734326 2803157 := bbase (se 7 (by rfl) ⟨32849, by rfl⟩ : syracuseStep 2803157 = 65699) (by norm_num)
theorem B1820141 : Blo 734326 1820141 := bbase (se 3 (by rfl) ⟨341276, by rfl⟩ : syracuseStep 1820141 = 682553) (by norm_num)
theorem B1656341 : Blo 734326 1656341 := bbase (se 6 (by rfl) ⟨38820, by rfl⟩ : syracuseStep 1656341 = 77641) (by norm_num)
theorem B1361485 : Blo 734326 1361485 := bbase (se 3 (by rfl) ⟨255278, by rfl⟩ : syracuseStep 1361485 = 510557) (by norm_num)
theorem B1656413 : Blo 734326 1656413 := bbase (se 3 (by rfl) ⟨310577, by rfl⟩ : syracuseStep 1656413 = 621155) (by norm_num)
theorem B3884645 : Blo 734326 3884645 := bbase (se 4 (by rfl) ⟨364185, by rfl⟩ : syracuseStep 3884645 = 728371) (by norm_num)
theorem B1492597 : Blo 734326 1492597 := bbase (se 5 (by rfl) ⟨69965, by rfl⟩ : syracuseStep 1492597 = 139931) (by norm_num)
theorem B1656485 : Blo 734326 1656485 := bbase (se 4 (by rfl) ⟨155295, by rfl⟩ : syracuseStep 1656485 = 310591) (by norm_num)
theorem B1492661 : Blo 734326 1492661 := bbase (se 5 (by rfl) ⟨69968, by rfl⟩ : syracuseStep 1492661 = 139937) (by norm_num)
theorem B1656557 : Blo 734326 1656557 := bbase (se 3 (by rfl) ⟨310604, by rfl⟩ : syracuseStep 1656557 = 621209) (by norm_num)
theorem B1656629 : Blo 734326 1656629 := bbase (se 5 (by rfl) ⟨77654, by rfl⟩ : syracuseStep 1656629 = 155309) (by norm_num)
theorem B1394509 : Blo 734326 1394509 := bbase (se 3 (by rfl) ⟨261470, by rfl⟩ : syracuseStep 1394509 = 522941) (by norm_num)
theorem B837473 : Blo 734326 837473 := bbase (se 2 (by rfl) ⟨314052, by rfl⟩ : syracuseStep 837473 = 628105) (by norm_num)
theorem B1656701 : Blo 734326 1656701 := bbase (se 3 (by rfl) ⟨310631, by rfl⟩ : syracuseStep 1656701 = 621263) (by norm_num)
theorem B1656773 : Blo 734326 1656773 := bbase (se 4 (by rfl) ⟨155322, by rfl⟩ : syracuseStep 1656773 = 310645) (by norm_num)
theorem B1394653 : Blo 734326 1394653 := bbase (se 3 (by rfl) ⟨261497, by rfl⟩ : syracuseStep 1394653 = 522995) (by norm_num)
theorem B1656845 : Blo 734326 1656845 := bbase (se 3 (by rfl) ⟨310658, by rfl⟩ : syracuseStep 1656845 = 621317) (by norm_num)
theorem B3721301 : Blo 734326 3721301 := bbase (se 8 (by rfl) ⟨21804, by rfl⟩ : syracuseStep 3721301 = 43609) (by norm_num)
theorem B1656917 : Blo 734326 1656917 := bbase (se 8 (by rfl) ⟨9708, by rfl⟩ : syracuseStep 1656917 = 19417) (by norm_num)
theorem B1394813 : Blo 734326 1394813 := bbase (se 3 (by rfl) ⟨261527, by rfl⟩ : syracuseStep 1394813 = 523055) (by norm_num)
theorem B12601493 : Blo 734326 12601493 := bbase (se 6 (by rfl) ⟨295347, by rfl⟩ : syracuseStep 12601493 = 590695) (by norm_num)
theorem B1656989 : Blo 734326 1656989 := bbase (se 3 (by rfl) ⟨310685, by rfl⟩ : syracuseStep 1656989 = 621371) (by norm_num)
theorem B1657061 : Blo 734326 1657061 := bbase (se 4 (by rfl) ⟨155349, by rfl⟩ : syracuseStep 1657061 = 310699) (by norm_num)
theorem B1394957 : Blo 734326 1394957 := bbase (se 3 (by rfl) ⟨261554, by rfl⟩ : syracuseStep 1394957 = 523109) (by norm_num)
theorem B1657133 : Blo 734326 1657133 := bbase (se 3 (by rfl) ⟨310712, by rfl⟩ : syracuseStep 1657133 = 621425) (by norm_num)
theorem B1493333 : Blo 734326 1493333 := bbase (se 10 (by rfl) ⟨2187, by rfl⟩ : syracuseStep 1493333 = 4375) (by norm_num)
theorem B1657205 : Blo 734326 1657205 := bbase (se 5 (by rfl) ⟨77681, by rfl⟩ : syracuseStep 1657205 = 155363) (by norm_num)
theorem B1657277 : Blo 734326 1657277 := bbase (se 3 (by rfl) ⟨310739, by rfl⟩ : syracuseStep 1657277 = 621479) (by norm_num)
theorem B1657349 : Blo 734326 1657349 := bbase (se 4 (by rfl) ⟨155376, by rfl⟩ : syracuseStep 1657349 = 310753) (by norm_num)
theorem B1395245 : Blo 734326 1395245 := bbase (se 3 (by rfl) ⟨261608, by rfl⟩ : syracuseStep 1395245 = 523217) (by norm_num)
theorem B1657421 : Blo 734326 1657421 := bbase (se 3 (by rfl) ⟨310766, by rfl⟩ : syracuseStep 1657421 = 621533) (by norm_num)
theorem B1657493 : Blo 734326 1657493 := bbase (se 6 (by rfl) ⟨38847, by rfl⟩ : syracuseStep 1657493 = 77695) (by norm_num)
theorem B1395397 : Blo 734326 1395397 := bbase (se 4 (by rfl) ⟨130818, by rfl⟩ : syracuseStep 1395397 = 261637) (by norm_num)
theorem B1657565 : Blo 734326 1657565 := bbase (se 3 (by rfl) ⟨310793, by rfl⟩ : syracuseStep 1657565 = 621587) (by norm_num)
theorem B1657637 : Blo 734326 1657637 := bbase (se 4 (by rfl) ⟨155403, by rfl⟩ : syracuseStep 1657637 = 310807) (by norm_num)
theorem B1657709 : Blo 734326 1657709 := bbase (se 3 (by rfl) ⟨310820, by rfl⟩ : syracuseStep 1657709 = 621641) (by norm_num)
theorem B1657781 : Blo 734326 1657781 := bbase (se 5 (by rfl) ⟨77708, by rfl⟩ : syracuseStep 1657781 = 155417) (by norm_num)
theorem B1493965 : Blo 734326 1493965 := bbase (se 3 (by rfl) ⟨280118, by rfl⟩ : syracuseStep 1493965 = 560237) (by norm_num)
theorem B1395701 : Blo 734326 1395701 := bbase (se 5 (by rfl) ⟨65423, by rfl⟩ : syracuseStep 1395701 = 130847) (by norm_num)
theorem B1657853 : Blo 734326 1657853 := bbase (se 3 (by rfl) ⟨310847, by rfl⟩ : syracuseStep 1657853 = 621695) (by norm_num)
theorem B1657925 : Blo 734326 1657925 := bbase (se 4 (by rfl) ⟨155430, by rfl⟩ : syracuseStep 1657925 = 310861) (by norm_num)
theorem B1657997 : Blo 734326 1657997 := bbase (se 3 (by rfl) ⟨310874, by rfl⟩ : syracuseStep 1657997 = 621749) (by norm_num)
theorem B1658069 : Blo 734326 1658069 := bbase (se 7 (by rfl) ⟨19430, by rfl⟩ : syracuseStep 1658069 = 38861) (by norm_num)
theorem B3788005 : Blo 734326 3788005 := bbase (se 4 (by rfl) ⟨355125, by rfl⟩ : syracuseStep 3788005 = 710251) (by norm_num)
theorem B1658141 : Blo 734326 1658141 := bbase (se 3 (by rfl) ⟨310901, by rfl⟩ : syracuseStep 1658141 = 621803) (by norm_num)
theorem B3722597 : Blo 734326 3722597 := bbase (se 4 (by rfl) ⟨348993, by rfl⟩ : syracuseStep 3722597 = 697987) (by norm_num)
theorem B1658213 : Blo 734326 1658213 := bbase (se 4 (by rfl) ⟨155457, by rfl⟩ : syracuseStep 1658213 = 310915) (by norm_num)
theorem B1658285 : Blo 734326 1658285 := bbase (se 3 (by rfl) ⟨310928, by rfl⟩ : syracuseStep 1658285 = 621857) (by norm_num)
theorem B1658357 : Blo 734326 1658357 := bbase (se 5 (by rfl) ⟨77735, by rfl⟩ : syracuseStep 1658357 = 155471) (by norm_num)
theorem B1658429 : Blo 734326 1658429 := bbase (se 3 (by rfl) ⟨310955, by rfl⟩ : syracuseStep 1658429 = 621911) (by norm_num)
theorem B4705877 : Blo 734326 4705877 := bbase (se 8 (by rfl) ⟨27573, by rfl⟩ : syracuseStep 4705877 = 55147) (by norm_num)
theorem B6278741 : Blo 734326 6278741 := bbase (se 8 (by rfl) ⟨36789, by rfl⟩ : syracuseStep 6278741 = 73579) (by norm_num)
theorem B1658501 : Blo 734326 1658501 := bbase (se 4 (by rfl) ⟨155484, by rfl⟩ : syracuseStep 1658501 = 310969) (by norm_num)
theorem B1101509 : Blo 734326 1101509 := bbase (se 4 (by rfl) ⟨103266, by rfl⟩ : syracuseStep 1101509 = 206533) (by norm_num)
theorem B1658573 : Blo 734326 1658573 := bbase (se 3 (by rfl) ⟨310982, by rfl⟩ : syracuseStep 1658573 = 621965) (by norm_num)
theorem B1101533 : Blo 734326 1101533 := bbase (se 3 (by rfl) ⟨206537, by rfl⟩ : syracuseStep 1101533 = 413075) (by norm_num)
theorem B1396453 : Blo 734326 1396453 := bbase (se 4 (by rfl) ⟨130917, by rfl⟩ : syracuseStep 1396453 = 261835) (by norm_num)
theorem B1101557 : Blo 734326 1101557 := bbase (se 5 (by rfl) ⟨51635, by rfl⟩ : syracuseStep 1101557 = 103271) (by norm_num)
theorem B1101581 : Blo 734326 1101581 := bbase (se 3 (by rfl) ⟨206546, by rfl⟩ : syracuseStep 1101581 = 413093) (by norm_num)
theorem B1658645 : Blo 734326 1658645 := bbase (se 6 (by rfl) ⟨38874, by rfl⟩ : syracuseStep 1658645 = 77749) (by norm_num)
theorem B1101605 : Blo 734326 1101605 := bbase (se 4 (by rfl) ⟨103275, by rfl⟩ : syracuseStep 1101605 = 206551) (by norm_num)
theorem B1101629 : Blo 734326 1101629 := bbase (se 3 (by rfl) ⟨206555, by rfl⟩ : syracuseStep 1101629 = 413111) (by norm_num)
theorem B1101653 : Blo 734326 1101653 := bbase (se 9 (by rfl) ⟨3227, by rfl⟩ : syracuseStep 1101653 = 6455) (by norm_num)
theorem B1658717 : Blo 734326 1658717 := bbase (se 3 (by rfl) ⟨311009, by rfl⟩ : syracuseStep 1658717 = 622019) (by norm_num)
theorem B1101677 : Blo 734326 1101677 := bbase (se 3 (by rfl) ⟨206564, by rfl⟩ : syracuseStep 1101677 = 413129) (by norm_num)
theorem B1396597 : Blo 734326 1396597 := bbase (se 5 (by rfl) ⟨65465, by rfl⟩ : syracuseStep 1396597 = 130931) (by norm_num)
theorem B1101701 : Blo 734326 1101701 := bbase (se 4 (by rfl) ⟨103284, by rfl⟩ : syracuseStep 1101701 = 206569) (by norm_num)
theorem B1101725 : Blo 734326 1101725 := bbase (se 3 (by rfl) ⟨206573, by rfl⟩ : syracuseStep 1101725 = 413147) (by norm_num)
theorem B1658789 : Blo 734326 1658789 := bbase (se 4 (by rfl) ⟨155511, by rfl⟩ : syracuseStep 1658789 = 311023) (by norm_num)
theorem B1101749 : Blo 734326 1101749 := bbase (se 5 (by rfl) ⟨51644, by rfl⟩ : syracuseStep 1101749 = 103289) (by norm_num)
theorem B1101773 : Blo 734326 1101773 := bbase (se 3 (by rfl) ⟨206582, by rfl⟩ : syracuseStep 1101773 = 413165) (by norm_num)
theorem B1101797 : Blo 734326 1101797 := bbase (se 4 (by rfl) ⟨103293, by rfl⟩ : syracuseStep 1101797 = 206587) (by norm_num)
theorem B1658861 : Blo 734326 1658861 := bbase (se 3 (by rfl) ⟨311036, by rfl⟩ : syracuseStep 1658861 = 622073) (by norm_num)
theorem B970741 : Blo 734326 970741 := bbase (se 5 (by rfl) ⟨45503, by rfl⟩ : syracuseStep 970741 = 91007) (by norm_num)
theorem B1101821 : Blo 734326 1101821 := bbase (se 3 (by rfl) ⟨206591, by rfl⟩ : syracuseStep 1101821 = 413183) (by norm_num)
theorem B1101845 : Blo 734326 1101845 := bbase (se 6 (by rfl) ⟨25824, by rfl⟩ : syracuseStep 1101845 = 51649) (by norm_num)
theorem B1396757 : Blo 734326 1396757 := bbase (se 6 (by rfl) ⟨32736, by rfl⟩ : syracuseStep 1396757 = 65473) (by norm_num)
theorem B1101869 : Blo 734326 1101869 := bbase (se 3 (by rfl) ⟨206600, by rfl⟩ : syracuseStep 1101869 = 413201) (by norm_num)
theorem B1658933 : Blo 734326 1658933 := bbase (se 5 (by rfl) ⟨77762, by rfl⟩ : syracuseStep 1658933 = 155525) (by norm_num)
theorem B1101893 : Blo 734326 1101893 := bbase (se 4 (by rfl) ⟨103302, by rfl⟩ : syracuseStep 1101893 = 206605) (by norm_num)
theorem B1101917 : Blo 734326 1101917 := bbase (se 3 (by rfl) ⟨206609, by rfl⟩ : syracuseStep 1101917 = 413219) (by norm_num)
theorem B1101941 : Blo 734326 1101941 := bbase (se 5 (by rfl) ⟨51653, by rfl⟩ : syracuseStep 1101941 = 103307) (by norm_num)
theorem B1659005 : Blo 734326 1659005 := bbase (se 3 (by rfl) ⟨311063, by rfl⟩ : syracuseStep 1659005 = 622127) (by norm_num)
theorem B1101965 : Blo 734326 1101965 := bbase (se 3 (by rfl) ⟨206618, by rfl⟩ : syracuseStep 1101965 = 413237) (by norm_num)
theorem B1101989 : Blo 734326 1101989 := bbase (se 4 (by rfl) ⟨103311, by rfl⟩ : syracuseStep 1101989 = 206623) (by norm_num)
theorem B1396901 : Blo 734326 1396901 := bbase (se 4 (by rfl) ⟨130959, by rfl⟩ : syracuseStep 1396901 = 261919) (by norm_num)
theorem B1102013 : Blo 734326 1102013 := bbase (se 3 (by rfl) ⟨206627, by rfl⟩ : syracuseStep 1102013 = 413255) (by norm_num)
theorem B1659077 : Blo 734326 1659077 := bbase (se 4 (by rfl) ⟨155538, by rfl⟩ : syracuseStep 1659077 = 311077) (by norm_num)
theorem B1102037 : Blo 734326 1102037 := bbase (se 7 (by rfl) ⟨12914, by rfl⟩ : syracuseStep 1102037 = 25829) (by norm_num)
theorem B1102061 : Blo 734326 1102061 := bbase (se 3 (by rfl) ⟨206636, by rfl⟩ : syracuseStep 1102061 = 413273) (by norm_num)
theorem B1102085 : Blo 734326 1102085 := bbase (se 4 (by rfl) ⟨103320, by rfl⟩ : syracuseStep 1102085 = 206641) (by norm_num)
theorem B1659149 : Blo 734326 1659149 := bbase (se 3 (by rfl) ⟨311090, by rfl⟩ : syracuseStep 1659149 = 622181) (by norm_num)
theorem B1102109 : Blo 734326 1102109 := bbase (se 3 (by rfl) ⟨206645, by rfl⟩ : syracuseStep 1102109 = 413291) (by norm_num)
theorem B1102133 : Blo 734326 1102133 := bbase (se 5 (by rfl) ⟨51662, by rfl⟩ : syracuseStep 1102133 = 103325) (by norm_num)
theorem B1102157 : Blo 734326 1102157 := bbase (se 3 (by rfl) ⟨206654, by rfl⟩ : syracuseStep 1102157 = 413309) (by norm_num)
theorem B1659221 : Blo 734326 1659221 := bbase (se 10 (by rfl) ⟨2430, by rfl⟩ : syracuseStep 1659221 = 4861) (by norm_num)
theorem B2478437 : Blo 734326 2478437 := bbase (se 4 (by rfl) ⟨232353, by rfl⟩ : syracuseStep 2478437 = 464707) (by norm_num)
theorem B1102181 : Blo 734326 1102181 := bbase (se 4 (by rfl) ⟨103329, by rfl⟩ : syracuseStep 1102181 = 206659) (by norm_num)
theorem B1102205 : Blo 734326 1102205 := bbase (se 3 (by rfl) ⟨206663, by rfl⟩ : syracuseStep 1102205 = 413327) (by norm_num)
theorem B1102229 : Blo 734326 1102229 := bbase (se 6 (by rfl) ⟨25833, by rfl⟩ : syracuseStep 1102229 = 51667) (by norm_num)
theorem B1659293 : Blo 734326 1659293 := bbase (se 3 (by rfl) ⟨311117, by rfl⟩ : syracuseStep 1659293 = 622235) (by norm_num)
theorem B1102253 : Blo 734326 1102253 := bbase (se 3 (by rfl) ⟨206672, by rfl⟩ : syracuseStep 1102253 = 413345) (by norm_num)
theorem B1102277 : Blo 734326 1102277 := bbase (se 4 (by rfl) ⟨103338, by rfl⟩ : syracuseStep 1102277 = 206677) (by norm_num)
theorem B1397189 : Blo 734326 1397189 := bbase (se 4 (by rfl) ⟨130986, by rfl⟩ : syracuseStep 1397189 = 261973) (by norm_num)
theorem B1102301 : Blo 734326 1102301 := bbase (se 3 (by rfl) ⟨206681, by rfl⟩ : syracuseStep 1102301 = 413363) (by norm_num)
theorem B1659365 : Blo 734326 1659365 := bbase (se 4 (by rfl) ⟨155565, by rfl⟩ : syracuseStep 1659365 = 311131) (by norm_num)
theorem B1102325 : Blo 734326 1102325 := bbase (se 5 (by rfl) ⟨51671, by rfl⟩ : syracuseStep 1102325 = 103343) (by norm_num)
theorem B1102349 : Blo 734326 1102349 := bbase (se 3 (by rfl) ⟨206690, by rfl⟩ : syracuseStep 1102349 = 413381) (by norm_num)
theorem B1102373 : Blo 734326 1102373 := bbase (se 4 (by rfl) ⟨103347, by rfl⟩ : syracuseStep 1102373 = 206695) (by norm_num)
theorem B1659437 : Blo 734326 1659437 := bbase (se 3 (by rfl) ⟨311144, by rfl⟩ : syracuseStep 1659437 = 622289) (by norm_num)
theorem B1102397 : Blo 734326 1102397 := bbase (se 3 (by rfl) ⟨206699, by rfl⟩ : syracuseStep 1102397 = 413399) (by norm_num)
theorem B1102421 : Blo 734326 1102421 := bbase (se 8 (by rfl) ⟨6459, by rfl⟩ : syracuseStep 1102421 = 12919) (by norm_num)
theorem B1397341 : Blo 734326 1397341 := bbase (se 3 (by rfl) ⟨262001, by rfl⟩ : syracuseStep 1397341 = 524003) (by norm_num)
theorem B1102445 : Blo 734326 1102445 := bbase (se 3 (by rfl) ⟨206708, by rfl⟩ : syracuseStep 1102445 = 413417) (by norm_num)
theorem B3723893 : Blo 734326 3723893 := bbase (se 5 (by rfl) ⟨174557, by rfl⟩ : syracuseStep 3723893 = 349115) (by norm_num)
theorem B1659509 : Blo 734326 1659509 := bbase (se 5 (by rfl) ⟨77789, by rfl⟩ : syracuseStep 1659509 = 155579) (by norm_num)
theorem B1102469 : Blo 734326 1102469 := bbase (se 4 (by rfl) ⟨103356, by rfl⟩ : syracuseStep 1102469 = 206713) (by norm_num)
theorem B1102493 : Blo 734326 1102493 := bbase (se 3 (by rfl) ⟨206717, by rfl⟩ : syracuseStep 1102493 = 413435) (by norm_num)
theorem B1102517 : Blo 734326 1102517 := bbase (se 5 (by rfl) ⟨51680, by rfl⟩ : syracuseStep 1102517 = 103361) (by norm_num)
theorem B1659581 : Blo 734326 1659581 := bbase (se 3 (by rfl) ⟨311171, by rfl⟩ : syracuseStep 1659581 = 622343) (by norm_num)
theorem B1102541 : Blo 734326 1102541 := bbase (se 3 (by rfl) ⟨206726, by rfl⟩ : syracuseStep 1102541 = 413453) (by norm_num)
theorem B1102565 : Blo 734326 1102565 := bbase (se 4 (by rfl) ⟨103365, by rfl⟩ : syracuseStep 1102565 = 206731) (by norm_num)
theorem B1102589 : Blo 734326 1102589 := bbase (se 3 (by rfl) ⟨206735, by rfl⟩ : syracuseStep 1102589 = 413471) (by norm_num)
theorem B1659653 : Blo 734326 1659653 := bbase (se 4 (by rfl) ⟨155592, by rfl⟩ : syracuseStep 1659653 = 311185) (by norm_num)
theorem B2478869 : Blo 734326 2478869 := bbase (se 6 (by rfl) ⟨58098, by rfl⟩ : syracuseStep 2478869 = 116197) (by norm_num)
theorem B1102613 : Blo 734326 1102613 := bbase (se 6 (by rfl) ⟨25842, by rfl⟩ : syracuseStep 1102613 = 51685) (by norm_num)
theorem B1102637 : Blo 734326 1102637 := bbase (se 3 (by rfl) ⟨206744, by rfl⟩ : syracuseStep 1102637 = 413489) (by norm_num)
theorem B840497 : Blo 734326 840497 := bbase (se 2 (by rfl) ⟨315186, by rfl⟩ : syracuseStep 840497 = 630373) (by norm_num)
theorem B1102661 : Blo 734326 1102661 := bbase (se 4 (by rfl) ⟨103374, by rfl⟩ : syracuseStep 1102661 = 206749) (by norm_num)
theorem B1659725 : Blo 734326 1659725 := bbase (se 3 (by rfl) ⟨311198, by rfl⟩ : syracuseStep 1659725 = 622397) (by norm_num)
theorem B1102685 : Blo 734326 1102685 := bbase (se 3 (by rfl) ⟨206753, by rfl⟩ : syracuseStep 1102685 = 413507) (by norm_num)
theorem B1102709 : Blo 734326 1102709 := bbase (se 5 (by rfl) ⟨51689, by rfl⟩ : syracuseStep 1102709 = 103379) (by norm_num)
theorem B1102733 : Blo 734326 1102733 := bbase (se 3 (by rfl) ⟨206762, by rfl⟩ : syracuseStep 1102733 = 413525) (by norm_num)
theorem B1397645 : Blo 734326 1397645 := bbase (se 3 (by rfl) ⟨262058, by rfl⟩ : syracuseStep 1397645 = 524117) (by norm_num)
theorem B1659797 : Blo 734326 1659797 := bbase (se 6 (by rfl) ⟨38901, by rfl⟩ : syracuseStep 1659797 = 77803) (by norm_num)
theorem B1102757 : Blo 734326 1102757 := bbase (se 4 (by rfl) ⟨103383, by rfl⟩ : syracuseStep 1102757 = 206767) (by norm_num)
theorem B1102781 : Blo 734326 1102781 := bbase (se 3 (by rfl) ⟨206771, by rfl⟩ : syracuseStep 1102781 = 413543) (by norm_num)
theorem B1102805 : Blo 734326 1102805 := bbase (se 7 (by rfl) ⟨12923, by rfl⟩ : syracuseStep 1102805 = 25847) (by norm_num)
theorem B1659869 : Blo 734326 1659869 := bbase (se 3 (by rfl) ⟨311225, by rfl⟩ : syracuseStep 1659869 = 622451) (by norm_num)
theorem B1102829 : Blo 734326 1102829 := bbase (se 3 (by rfl) ⟨206780, by rfl⟩ : syracuseStep 1102829 = 413561) (by norm_num)
theorem B1102853 : Blo 734326 1102853 := bbase (se 4 (by rfl) ⟨103392, by rfl⟩ : syracuseStep 1102853 = 206785) (by norm_num)
theorem B1102877 : Blo 734326 1102877 := bbase (se 3 (by rfl) ⟨206789, by rfl⟩ : syracuseStep 1102877 = 413579) (by norm_num)
theorem B1659941 : Blo 734326 1659941 := bbase (se 4 (by rfl) ⟨155619, by rfl⟩ : syracuseStep 1659941 = 311239) (by norm_num)
theorem B1102901 : Blo 734326 1102901 := bbase (se 5 (by rfl) ⟨51698, by rfl⟩ : syracuseStep 1102901 = 103397) (by norm_num)
theorem B1102925 : Blo 734326 1102925 := bbase (se 3 (by rfl) ⟨206798, by rfl⟩ : syracuseStep 1102925 = 413597) (by norm_num)
theorem B1102949 : Blo 734326 1102949 := bbase (se 4 (by rfl) ⟨103401, by rfl⟩ : syracuseStep 1102949 = 206803) (by norm_num)
theorem B1660013 : Blo 734326 1660013 := bbase (se 3 (by rfl) ⟨311252, by rfl⟩ : syracuseStep 1660013 = 622505) (by norm_num)
theorem B1102973 : Blo 734326 1102973 := bbase (se 3 (by rfl) ⟨206807, by rfl⟩ : syracuseStep 1102973 = 413615) (by norm_num)
theorem B1102997 : Blo 734326 1102997 := bbase (se 6 (by rfl) ⟨25851, by rfl⟩ : syracuseStep 1102997 = 51703) (by norm_num)
theorem B1103021 : Blo 734326 1103021 := bbase (se 3 (by rfl) ⟨206816, by rfl⟩ : syracuseStep 1103021 = 413633) (by norm_num)
theorem B1660085 : Blo 734326 1660085 := bbase (se 5 (by rfl) ⟨77816, by rfl⟩ : syracuseStep 1660085 = 155633) (by norm_num)
theorem B2479301 : Blo 734326 2479301 := bbase (se 4 (by rfl) ⟨232434, by rfl⟩ : syracuseStep 2479301 = 464869) (by norm_num)
theorem B1103045 : Blo 734326 1103045 := bbase (se 4 (by rfl) ⟨103410, by rfl⟩ : syracuseStep 1103045 = 206821) (by norm_num)
theorem B1103069 : Blo 734326 1103069 := bbase (se 3 (by rfl) ⟨206825, by rfl⟩ : syracuseStep 1103069 = 413651) (by norm_num)
theorem B1103093 : Blo 734326 1103093 := bbase (se 5 (by rfl) ⟨51707, by rfl⟩ : syracuseStep 1103093 = 103415) (by norm_num)
theorem B1660157 : Blo 734326 1660157 := bbase (se 3 (by rfl) ⟨311279, by rfl⟩ : syracuseStep 1660157 = 622559) (by norm_num)
theorem B1103117 : Blo 734326 1103117 := bbase (se 3 (by rfl) ⟨206834, by rfl⟩ : syracuseStep 1103117 = 413669) (by norm_num)
theorem B1103141 : Blo 734326 1103141 := bbase (se 4 (by rfl) ⟨103419, by rfl⟩ : syracuseStep 1103141 = 206839) (by norm_num)
theorem B3626293 : Blo 734326 3626293 := bbase (se 5 (by rfl) ⟨169982, by rfl⟩ : syracuseStep 3626293 = 339965) (by norm_num)
theorem B1103165 : Blo 734326 1103165 := bbase (se 3 (by rfl) ⟨206843, by rfl⟩ : syracuseStep 1103165 = 413687) (by norm_num)
theorem B1660229 : Blo 734326 1660229 := bbase (se 4 (by rfl) ⟨155646, by rfl⟩ : syracuseStep 1660229 = 311293) (by norm_num)
theorem B1103189 : Blo 734326 1103189 := bbase (se 15 (by rfl) ⟨50, by rfl⟩ : syracuseStep 1103189 = 101) (by norm_num)
theorem B1103213 : Blo 734326 1103213 := bbase (se 3 (by rfl) ⟨206852, by rfl⟩ : syracuseStep 1103213 = 413705) (by norm_num)
theorem B1103237 : Blo 734326 1103237 := bbase (se 4 (by rfl) ⟨103428, by rfl⟩ : syracuseStep 1103237 = 206857) (by norm_num)
theorem B1660301 : Blo 734326 1660301 := bbase (se 3 (by rfl) ⟨311306, by rfl⟩ : syracuseStep 1660301 = 622613) (by norm_num)
theorem B1103261 : Blo 734326 1103261 := bbase (se 3 (by rfl) ⟨206861, by rfl⟩ : syracuseStep 1103261 = 413723) (by norm_num)
theorem B2512309 : Blo 734326 2512309 := bbase (se 5 (by rfl) ⟨117764, by rfl⟩ : syracuseStep 2512309 = 235529) (by norm_num)
theorem B1103285 : Blo 734326 1103285 := bbase (se 5 (by rfl) ⟨51716, by rfl⟩ : syracuseStep 1103285 = 103433) (by norm_num)
theorem B1103309 : Blo 734326 1103309 := bbase (se 3 (by rfl) ⟨206870, by rfl⟩ : syracuseStep 1103309 = 413741) (by norm_num)
theorem B1660373 : Blo 734326 1660373 := bbase (se 7 (by rfl) ⟨19457, by rfl⟩ : syracuseStep 1660373 = 38915) (by norm_num)
theorem B1103333 : Blo 734326 1103333 := bbase (se 4 (by rfl) ⟨103437, by rfl⟩ : syracuseStep 1103333 = 206875) (by norm_num)
theorem B3364325 : Blo 734326 3364325 := bbase (se 4 (by rfl) ⟨315405, by rfl⟩ : syracuseStep 3364325 = 630811) (by norm_num)
theorem B1103357 : Blo 734326 1103357 := bbase (se 3 (by rfl) ⟨206879, by rfl⟩ : syracuseStep 1103357 = 413759) (by norm_num)
theorem B1103381 : Blo 734326 1103381 := bbase (se 6 (by rfl) ⟨25860, by rfl⟩ : syracuseStep 1103381 = 51721) (by norm_num)
theorem B1660445 : Blo 734326 1660445 := bbase (se 3 (by rfl) ⟨311333, by rfl⟩ : syracuseStep 1660445 = 622667) (by norm_num)
theorem B1791533 : Blo 734326 1791533 := bbase (se 3 (by rfl) ⟨335912, by rfl⟩ : syracuseStep 1791533 = 671825) (by norm_num)
theorem B1103405 : Blo 734326 1103405 := bbase (se 3 (by rfl) ⟨206888, by rfl⟩ : syracuseStep 1103405 = 413777) (by norm_num)
theorem B1103429 : Blo 734326 1103429 := bbase (se 4 (by rfl) ⟨103446, by rfl⟩ : syracuseStep 1103429 = 206893) (by norm_num)
theorem B1103453 : Blo 734326 1103453 := bbase (se 3 (by rfl) ⟨206897, by rfl⟩ : syracuseStep 1103453 = 413795) (by norm_num)
theorem B1660517 : Blo 734326 1660517 := bbase (se 4 (by rfl) ⟨155673, by rfl⟩ : syracuseStep 1660517 = 311347) (by norm_num)
theorem B2479733 : Blo 734326 2479733 := bbase (se 5 (by rfl) ⟨116237, by rfl⟩ : syracuseStep 2479733 = 232475) (by norm_num)
theorem B1103477 : Blo 734326 1103477 := bbase (se 5 (by rfl) ⟨51725, by rfl⟩ : syracuseStep 1103477 = 103451) (by norm_num)
theorem B1398397 : Blo 734326 1398397 := bbase (se 3 (by rfl) ⟨262199, by rfl⟩ : syracuseStep 1398397 = 524399) (by norm_num)
theorem B1103501 : Blo 734326 1103501 := bbase (se 3 (by rfl) ⟨206906, by rfl⟩ : syracuseStep 1103501 = 413813) (by norm_num)
theorem B1103525 : Blo 734326 1103525 := bbase (se 4 (by rfl) ⟨103455, by rfl⟩ : syracuseStep 1103525 = 206911) (by norm_num)
theorem B1660589 : Blo 734326 1660589 := bbase (se 3 (by rfl) ⟨311360, by rfl⟩ : syracuseStep 1660589 = 622721) (by norm_num)
theorem B1103549 : Blo 734326 1103549 := bbase (se 3 (by rfl) ⟨206915, by rfl⟩ : syracuseStep 1103549 = 413831) (by norm_num)
theorem B1103573 : Blo 734326 1103573 := bbase (se 7 (by rfl) ⟨12932, by rfl⟩ : syracuseStep 1103573 = 25865) (by norm_num)
theorem B1103597 : Blo 734326 1103597 := bbase (se 3 (by rfl) ⟨206924, by rfl⟩ : syracuseStep 1103597 = 413849) (by norm_num)
theorem B1660661 : Blo 734326 1660661 := bbase (se 5 (by rfl) ⟨77843, by rfl⟩ : syracuseStep 1660661 = 155687) (by norm_num)
theorem B1103621 : Blo 734326 1103621 := bbase (se 4 (by rfl) ⟨103464, by rfl⟩ : syracuseStep 1103621 = 206929) (by norm_num)
theorem B1398541 : Blo 734326 1398541 := bbase (se 3 (by rfl) ⟨262226, by rfl⟩ : syracuseStep 1398541 = 524453) (by norm_num)
theorem B1103645 : Blo 734326 1103645 := bbase (se 3 (by rfl) ⟨206933, by rfl⟩ : syracuseStep 1103645 = 413867) (by norm_num)
theorem B1103669 : Blo 734326 1103669 := bbase (se 5 (by rfl) ⟨51734, by rfl⟩ : syracuseStep 1103669 = 103469) (by norm_num)
theorem B1660733 : Blo 734326 1660733 := bbase (se 3 (by rfl) ⟨311387, by rfl⟩ : syracuseStep 1660733 = 622775) (by norm_num)
theorem B1103693 : Blo 734326 1103693 := bbase (se 3 (by rfl) ⟨206942, by rfl⟩ : syracuseStep 1103693 = 413885) (by norm_num)
theorem B1103717 : Blo 734326 1103717 := bbase (se 4 (by rfl) ⟨103473, by rfl⟩ : syracuseStep 1103717 = 206947) (by norm_num)
theorem B1103741 : Blo 734326 1103741 := bbase (se 3 (by rfl) ⟨206951, by rfl⟩ : syracuseStep 1103741 = 413903) (by norm_num)
theorem B3725189 : Blo 734326 3725189 := bbase (se 4 (by rfl) ⟨349236, by rfl⟩ : syracuseStep 3725189 = 698473) (by norm_num)
theorem B1660805 : Blo 734326 1660805 := bbase (se 4 (by rfl) ⟨155700, by rfl⟩ : syracuseStep 1660805 = 311401) (by norm_num)
theorem B1103765 : Blo 734326 1103765 := bbase (se 6 (by rfl) ⟨25869, by rfl⟩ : syracuseStep 1103765 = 51739) (by norm_num)
theorem B1103789 : Blo 734326 1103789 := bbase (se 3 (by rfl) ⟨206960, by rfl⟩ : syracuseStep 1103789 = 413921) (by norm_num)
theorem B1398701 : Blo 734326 1398701 := bbase (se 3 (by rfl) ⟨262256, by rfl⟩ : syracuseStep 1398701 = 524513) (by norm_num)
theorem B1103813 : Blo 734326 1103813 := bbase (se 4 (by rfl) ⟨103482, by rfl⟩ : syracuseStep 1103813 = 206965) (by norm_num)
theorem B1660877 : Blo 734326 1660877 := bbase (se 3 (by rfl) ⟨311414, by rfl⟩ : syracuseStep 1660877 = 622829) (by norm_num)
theorem B1103837 : Blo 734326 1103837 := bbase (se 3 (by rfl) ⟨206969, by rfl⟩ : syracuseStep 1103837 = 413939) (by norm_num)
theorem B1103861 : Blo 734326 1103861 := bbase (se 5 (by rfl) ⟨51743, by rfl⟩ : syracuseStep 1103861 = 103487) (by norm_num)
theorem B1103885 : Blo 734326 1103885 := bbase (se 3 (by rfl) ⟨206978, by rfl⟩ : syracuseStep 1103885 = 413957) (by norm_num)
theorem B1660949 : Blo 734326 1660949 := bbase (se 6 (by rfl) ⟨38928, by rfl⟩ : syracuseStep 1660949 = 77857) (by norm_num)
theorem B2480165 : Blo 734326 2480165 := bbase (se 4 (by rfl) ⟨232515, by rfl⟩ : syracuseStep 2480165 = 465031) (by norm_num)
theorem B1103909 : Blo 734326 1103909 := bbase (se 4 (by rfl) ⟨103491, by rfl⟩ : syracuseStep 1103909 = 206983) (by norm_num)
theorem B1103933 : Blo 734326 1103933 := bbase (se 3 (by rfl) ⟨206987, by rfl⟩ : syracuseStep 1103933 = 413975) (by norm_num)
theorem B1398845 : Blo 734326 1398845 := bbase (se 3 (by rfl) ⟨262283, by rfl⟩ : syracuseStep 1398845 = 524567) (by norm_num)
theorem B1103957 : Blo 734326 1103957 := bbase (se 8 (by rfl) ⟨6468, by rfl⟩ : syracuseStep 1103957 = 12937) (by norm_num)
theorem B1661021 : Blo 734326 1661021 := bbase (se 3 (by rfl) ⟨311441, by rfl⟩ : syracuseStep 1661021 = 622883) (by norm_num)
theorem B1103981 : Blo 734326 1103981 := bbase (se 3 (by rfl) ⟨206996, by rfl⟩ : syracuseStep 1103981 = 413993) (by norm_num)
theorem B1104005 : Blo 734326 1104005 := bbase (se 4 (by rfl) ⟨103500, by rfl⟩ : syracuseStep 1104005 = 207001) (by norm_num)
theorem B1104029 : Blo 734326 1104029 := bbase (se 3 (by rfl) ⟨207005, by rfl⟩ : syracuseStep 1104029 = 414011) (by norm_num)
theorem B1661093 : Blo 734326 1661093 := bbase (se 4 (by rfl) ⟨155727, by rfl⟩ : syracuseStep 1661093 = 311455) (by norm_num)
theorem B809137 : Blo 734326 809137 := bbase (se 2 (by rfl) ⟨303426, by rfl⟩ : syracuseStep 809137 = 606853) (by norm_num)
theorem B1104053 : Blo 734326 1104053 := bbase (se 5 (by rfl) ⟨51752, by rfl⟩ : syracuseStep 1104053 = 103505) (by norm_num)
theorem B1104077 : Blo 734326 1104077 := bbase (se 3 (by rfl) ⟨207014, by rfl⟩ : syracuseStep 1104077 = 414029) (by norm_num)
theorem B1104101 : Blo 734326 1104101 := bbase (se 4 (by rfl) ⟨103509, by rfl⟩ : syracuseStep 1104101 = 207019) (by norm_num)
theorem B1661165 : Blo 734326 1661165 := bbase (se 3 (by rfl) ⟨311468, by rfl⟩ : syracuseStep 1661165 = 622937) (by norm_num)
theorem B1104125 : Blo 734326 1104125 := bbase (se 3 (by rfl) ⟨207023, by rfl⟩ : syracuseStep 1104125 = 414047) (by norm_num)
theorem B1104149 : Blo 734326 1104149 := bbase (se 6 (by rfl) ⟨25878, by rfl⟩ : syracuseStep 1104149 = 51757) (by norm_num)
theorem B1104173 : Blo 734326 1104173 := bbase (se 3 (by rfl) ⟨207032, by rfl⟩ : syracuseStep 1104173 = 414065) (by norm_num)
theorem B1104197 : Blo 734326 1104197 := bbase (se 4 (by rfl) ⟨103518, by rfl⟩ : syracuseStep 1104197 = 207037) (by norm_num)
theorem B1104221 : Blo 734326 1104221 := bbase (se 3 (by rfl) ⟨207041, by rfl⟩ : syracuseStep 1104221 = 414083) (by norm_num)
theorem B1399133 : Blo 734326 1399133 := bbase (se 3 (by rfl) ⟨262337, by rfl⟩ : syracuseStep 1399133 = 524675) (by norm_num)
theorem B1104245 : Blo 734326 1104245 := bbase (se 5 (by rfl) ⟨51761, by rfl⟩ : syracuseStep 1104245 = 103523) (by norm_num)
theorem B1104269 : Blo 734326 1104269 := bbase (se 3 (by rfl) ⟨207050, by rfl⟩ : syracuseStep 1104269 = 414101) (by norm_num)
theorem B3627413 : Blo 734326 3627413 := bbase (se 6 (by rfl) ⟨85017, by rfl⟩ : syracuseStep 3627413 = 170035) (by norm_num)
theorem B1104293 : Blo 734326 1104293 := bbase (se 4 (by rfl) ⟨103527, by rfl⟩ : syracuseStep 1104293 = 207055) (by norm_num)
theorem B1104317 : Blo 734326 1104317 := bbase (se 3 (by rfl) ⟨207059, by rfl⟩ : syracuseStep 1104317 = 414119) (by norm_num)
theorem B2480597 : Blo 734326 2480597 := bbase (se 7 (by rfl) ⟨29069, by rfl⟩ : syracuseStep 2480597 = 58139) (by norm_num)
theorem B1104341 : Blo 734326 1104341 := bbase (se 7 (by rfl) ⟨12941, by rfl⟩ : syracuseStep 1104341 = 25883) (by norm_num)
theorem B1104365 : Blo 734326 1104365 := bbase (se 3 (by rfl) ⟨207068, by rfl⟩ : syracuseStep 1104365 = 414137) (by norm_num)
theorem B4708853 : Blo 734326 4708853 := bbase (se 5 (by rfl) ⟨220727, by rfl⟩ : syracuseStep 4708853 = 441455) (by norm_num)
theorem B1399285 : Blo 734326 1399285 := bbase (se 5 (by rfl) ⟨65591, by rfl⟩ : syracuseStep 1399285 = 131183) (by norm_num)
theorem B1104389 : Blo 734326 1104389 := bbase (se 4 (by rfl) ⟨103536, by rfl⟩ : syracuseStep 1104389 = 207073) (by norm_num)
theorem B1104413 : Blo 734326 1104413 := bbase (se 3 (by rfl) ⟨207077, by rfl⟩ : syracuseStep 1104413 = 414155) (by norm_num)
theorem B1104437 : Blo 734326 1104437 := bbase (se 5 (by rfl) ⟨51770, by rfl⟩ : syracuseStep 1104437 = 103541) (by norm_num)
theorem B1104461 : Blo 734326 1104461 := bbase (se 3 (by rfl) ⟨207086, by rfl⟩ : syracuseStep 1104461 = 414173) (by norm_num)
theorem B1104485 : Blo 734326 1104485 := bbase (se 4 (by rfl) ⟨103545, by rfl⟩ : syracuseStep 1104485 = 207091) (by norm_num)
theorem B1104509 : Blo 734326 1104509 := bbase (se 3 (by rfl) ⟨207095, by rfl⟩ : syracuseStep 1104509 = 414191) (by norm_num)
theorem B1104533 : Blo 734326 1104533 := bbase (se 6 (by rfl) ⟨25887, by rfl⟩ : syracuseStep 1104533 = 51775) (by norm_num)
theorem B1104557 : Blo 734326 1104557 := bbase (se 3 (by rfl) ⟨207104, by rfl⟩ : syracuseStep 1104557 = 414209) (by norm_num)
theorem B1104581 : Blo 734326 1104581 := bbase (se 4 (by rfl) ⟨103554, by rfl⟩ : syracuseStep 1104581 = 207109) (by norm_num)
theorem B1104605 : Blo 734326 1104605 := bbase (se 3 (by rfl) ⟨207113, by rfl⟩ : syracuseStep 1104605 = 414227) (by norm_num)
theorem B1891045 : Blo 734326 1891045 := bbase (se 4 (by rfl) ⟨177285, by rfl⟩ : syracuseStep 1891045 = 354571) (by norm_num)
theorem B1104629 : Blo 734326 1104629 := bbase (se 5 (by rfl) ⟨51779, by rfl⟩ : syracuseStep 1104629 = 103559) (by norm_num)
theorem B1104653 : Blo 734326 1104653 := bbase (se 3 (by rfl) ⟨207122, by rfl⟩ : syracuseStep 1104653 = 414245) (by norm_num)
theorem B1104677 : Blo 734326 1104677 := bbase (se 4 (by rfl) ⟨103563, by rfl⟩ : syracuseStep 1104677 = 207127) (by norm_num)
theorem B1399589 : Blo 734326 1399589 := bbase (se 4 (by rfl) ⟨131211, by rfl⟩ : syracuseStep 1399589 = 262423) (by norm_num)
theorem B1104701 : Blo 734326 1104701 := bbase (se 3 (by rfl) ⟨207131, by rfl⟩ : syracuseStep 1104701 = 414263) (by norm_num)
theorem B1104725 : Blo 734326 1104725 := bbase (se 9 (by rfl) ⟨3236, by rfl⟩ : syracuseStep 1104725 = 6473) (by norm_num)
theorem B1104749 : Blo 734326 1104749 := bbase (se 3 (by rfl) ⟨207140, by rfl⟩ : syracuseStep 1104749 = 414281) (by norm_num)
theorem B1006453 : Blo 734326 1006453 := bbase (se 5 (by rfl) ⟨47177, by rfl⟩ : syracuseStep 1006453 = 94355) (by norm_num)
theorem B1104773 : Blo 734326 1104773 := bbase (se 4 (by rfl) ⟨103572, by rfl⟩ : syracuseStep 1104773 = 207145) (by norm_num)
theorem B2481029 : Blo 734326 2481029 := bbase (se 4 (by rfl) ⟨232596, by rfl⟩ : syracuseStep 2481029 = 465193) (by norm_num)
theorem B1104797 : Blo 734326 1104797 := bbase (se 3 (by rfl) ⟨207149, by rfl⟩ : syracuseStep 1104797 = 414299) (by norm_num)
theorem B1104821 : Blo 734326 1104821 := bbase (se 5 (by rfl) ⟨51788, by rfl⟩ : syracuseStep 1104821 = 103577) (by norm_num)
theorem B1104845 : Blo 734326 1104845 := bbase (se 3 (by rfl) ⟨207158, by rfl⟩ : syracuseStep 1104845 = 414317) (by norm_num)
theorem B1104869 : Blo 734326 1104869 := bbase (se 4 (by rfl) ⟨103581, by rfl⟩ : syracuseStep 1104869 = 207163) (by norm_num)
theorem B1104893 : Blo 734326 1104893 := bbase (se 3 (by rfl) ⟨207167, by rfl⟩ : syracuseStep 1104893 = 414335) (by norm_num)
theorem B1104917 : Blo 734326 1104917 := bbase (se 6 (by rfl) ⟨25896, by rfl⟩ : syracuseStep 1104917 = 51793) (by norm_num)
theorem B1104941 : Blo 734326 1104941 := bbase (se 3 (by rfl) ⟨207176, by rfl⟩ : syracuseStep 1104941 = 414353) (by norm_num)
theorem B1104965 : Blo 734326 1104965 := bbase (se 4 (by rfl) ⟨103590, by rfl⟩ : syracuseStep 1104965 = 207181) (by norm_num)
theorem B1104989 : Blo 734326 1104989 := bbase (se 3 (by rfl) ⟨207185, by rfl⟩ : syracuseStep 1104989 = 414371) (by norm_num)
theorem B1105013 : Blo 734326 1105013 := bbase (se 5 (by rfl) ⟨51797, by rfl⟩ : syracuseStep 1105013 = 103595) (by norm_num)
theorem B1105037 : Blo 734326 1105037 := bbase (se 3 (by rfl) ⟨207194, by rfl⟩ : syracuseStep 1105037 = 414389) (by norm_num)
theorem B3726485 : Blo 734326 3726485 := bbase (se 6 (by rfl) ⟨87339, by rfl⟩ : syracuseStep 3726485 = 174679) (by norm_num)
theorem B1105061 : Blo 734326 1105061 := bbase (se 4 (by rfl) ⟨103599, by rfl⟩ : syracuseStep 1105061 = 207199) (by norm_num)
theorem B3529909 : Blo 734326 3529909 := bbase (se 5 (by rfl) ⟨165464, by rfl⟩ : syracuseStep 3529909 = 330929) (by norm_num)
theorem B1105085 : Blo 734326 1105085 := bbase (se 3 (by rfl) ⟨207203, by rfl⟩ : syracuseStep 1105085 = 414407) (by norm_num)
theorem B1105109 : Blo 734326 1105109 := bbase (se 7 (by rfl) ⟨12950, by rfl⟩ : syracuseStep 1105109 = 25901) (by norm_num)
theorem B1105133 : Blo 734326 1105133 := bbase (se 3 (by rfl) ⟨207212, by rfl⟩ : syracuseStep 1105133 = 414425) (by norm_num)
theorem B1105157 : Blo 734326 1105157 := bbase (se 4 (by rfl) ⟨103608, by rfl⟩ : syracuseStep 1105157 = 207217) (by norm_num)
theorem B1105181 : Blo 734326 1105181 := bbase (se 3 (by rfl) ⟨207221, by rfl⟩ : syracuseStep 1105181 = 414443) (by norm_num)
theorem B2481461 : Blo 734326 2481461 := bbase (se 5 (by rfl) ⟨116318, by rfl⟩ : syracuseStep 2481461 = 232637) (by norm_num)
theorem B1105205 : Blo 734326 1105205 := bbase (se 5 (by rfl) ⟨51806, by rfl⟩ : syracuseStep 1105205 = 103613) (by norm_num)
theorem B1105229 : Blo 734326 1105229 := bbase (se 3 (by rfl) ⟨207230, by rfl⟩ : syracuseStep 1105229 = 414461) (by norm_num)
theorem B1858909 : Blo 734326 1858909 := bbase (se 3 (by rfl) ⟨348545, by rfl⟩ : syracuseStep 1858909 = 697091) (by norm_num)
theorem B1105253 : Blo 734326 1105253 := bbase (se 4 (by rfl) ⟨103617, by rfl⟩ : syracuseStep 1105253 = 207235) (by norm_num)
theorem B1105277 : Blo 734326 1105277 := bbase (se 3 (by rfl) ⟨207239, by rfl⟩ : syracuseStep 1105277 = 414479) (by norm_num)
theorem B1105301 : Blo 734326 1105301 := bbase (se 6 (by rfl) ⟨25905, by rfl⟩ : syracuseStep 1105301 = 51811) (by norm_num)
theorem B1105325 : Blo 734326 1105325 := bbase (se 3 (by rfl) ⟨207248, by rfl⟩ : syracuseStep 1105325 = 414497) (by norm_num)
theorem B1105349 : Blo 734326 1105349 := bbase (se 4 (by rfl) ⟨103626, by rfl⟩ : syracuseStep 1105349 = 207253) (by norm_num)
theorem B1859021 : Blo 734326 1859021 := bbase (se 3 (by rfl) ⟨348566, by rfl⟩ : syracuseStep 1859021 = 697133) (by norm_num)
theorem B1105373 : Blo 734326 1105373 := bbase (se 3 (by rfl) ⟨207257, by rfl⟩ : syracuseStep 1105373 = 414515) (by norm_num)
theorem B1105397 : Blo 734326 1105397 := bbase (se 5 (by rfl) ⟨51815, by rfl⟩ : syracuseStep 1105397 = 103631) (by norm_num)
theorem B1105421 : Blo 734326 1105421 := bbase (se 3 (by rfl) ⟨207266, by rfl⟩ : syracuseStep 1105421 = 414533) (by norm_num)
theorem B1400341 : Blo 734326 1400341 := bbase (se 6 (by rfl) ⟨32820, by rfl⟩ : syracuseStep 1400341 = 65641) (by norm_num)
theorem B1105445 : Blo 734326 1105445 := bbase (se 4 (by rfl) ⟨103635, by rfl⟩ : syracuseStep 1105445 = 207271) (by norm_num)
theorem B2514485 : Blo 734326 2514485 := bbase (se 5 (by rfl) ⟨117866, by rfl⟩ : syracuseStep 2514485 = 235733) (by norm_num)
theorem B1105469 : Blo 734326 1105469 := bbase (se 3 (by rfl) ⟨207275, by rfl⟩ : syracuseStep 1105469 = 414551) (by norm_num)
theorem B1105493 : Blo 734326 1105493 := bbase (se 8 (by rfl) ⟨6477, by rfl⟩ : syracuseStep 1105493 = 12955) (by norm_num)
theorem B1105517 : Blo 734326 1105517 := bbase (se 3 (by rfl) ⟨207284, by rfl⟩ : syracuseStep 1105517 = 414569) (by norm_num)
theorem B1105541 : Blo 734326 1105541 := bbase (se 4 (by rfl) ⟨103644, by rfl⟩ : syracuseStep 1105541 = 207289) (by norm_num)
theorem B1859213 : Blo 734326 1859213 := bbase (se 3 (by rfl) ⟨348602, by rfl⟩ : syracuseStep 1859213 = 697205) (by norm_num)
theorem B1105565 : Blo 734326 1105565 := bbase (se 3 (by rfl) ⟨207293, by rfl⟩ : syracuseStep 1105565 = 414587) (by norm_num)
theorem B1400485 : Blo 734326 1400485 := bbase (se 4 (by rfl) ⟨131295, by rfl⟩ : syracuseStep 1400485 = 262591) (by norm_num)
theorem B1105589 : Blo 734326 1105589 := bbase (se 5 (by rfl) ⟨51824, by rfl⟩ : syracuseStep 1105589 = 103649) (by norm_num)
theorem B1105613 : Blo 734326 1105613 := bbase (se 3 (by rfl) ⟨207302, by rfl⟩ : syracuseStep 1105613 = 414605) (by norm_num)
theorem B3137237 : Blo 734326 3137237 := bbase (se 7 (by rfl) ⟨36764, by rfl⟩ : syracuseStep 3137237 = 73529) (by norm_num)
theorem B2481893 : Blo 734326 2481893 := bbase (se 4 (by rfl) ⟨232677, by rfl⟩ : syracuseStep 2481893 = 465355) (by norm_num)
theorem B1105637 : Blo 734326 1105637 := bbase (se 4 (by rfl) ⟨103653, by rfl⟩ : syracuseStep 1105637 = 207307) (by norm_num)
theorem B1105661 : Blo 734326 1105661 := bbase (se 3 (by rfl) ⟨207311, by rfl⟩ : syracuseStep 1105661 = 414623) (by norm_num)
theorem B1105685 : Blo 734326 1105685 := bbase (se 6 (by rfl) ⟨25914, by rfl⟩ : syracuseStep 1105685 = 51829) (by norm_num)
theorem B1105709 : Blo 734326 1105709 := bbase (se 3 (by rfl) ⟨207320, by rfl⟩ : syracuseStep 1105709 = 414641) (by norm_num)
theorem B1105733 : Blo 734326 1105733 := bbase (se 4 (by rfl) ⟨103662, by rfl⟩ : syracuseStep 1105733 = 207325) (by norm_num)
theorem B1400645 : Blo 734326 1400645 := bbase (se 4 (by rfl) ⟨131310, by rfl⟩ : syracuseStep 1400645 = 262621) (by norm_num)
theorem B2514773 : Blo 734326 2514773 := bbase (se 9 (by rfl) ⟨7367, by rfl⟩ : syracuseStep 2514773 = 14735) (by norm_num)
theorem B5103445 : Blo 734326 5103445 := bbase (se 9 (by rfl) ⟨14951, by rfl⟩ : syracuseStep 5103445 = 29903) (by norm_num)
theorem B1105757 : Blo 734326 1105757 := bbase (se 3 (by rfl) ⟨207329, by rfl⟩ : syracuseStep 1105757 = 414659) (by norm_num)
theorem B1007461 : Blo 734326 1007461 := bbase (se 4 (by rfl) ⟨94449, by rfl⟩ : syracuseStep 1007461 = 188899) (by norm_num)
theorem B1105781 : Blo 734326 1105781 := bbase (se 5 (by rfl) ⟨51833, by rfl⟩ : syracuseStep 1105781 = 103667) (by norm_num)
theorem B1105805 : Blo 734326 1105805 := bbase (se 3 (by rfl) ⟨207338, by rfl⟩ : syracuseStep 1105805 = 414677) (by norm_num)
theorem B1105829 : Blo 734326 1105829 := bbase (se 4 (by rfl) ⟨103671, by rfl⟩ : syracuseStep 1105829 = 207343) (by norm_num)
theorem B1105853 : Blo 734326 1105853 := bbase (se 3 (by rfl) ⟨207347, by rfl⟩ : syracuseStep 1105853 = 414695) (by norm_num)
theorem B1105877 : Blo 734326 1105877 := bbase (se 7 (by rfl) ⟨12959, by rfl⟩ : syracuseStep 1105877 = 25919) (by norm_num)
theorem B1400789 : Blo 734326 1400789 := bbase (se 7 (by rfl) ⟨16415, by rfl⟩ : syracuseStep 1400789 = 32831) (by norm_num)
theorem B1859557 : Blo 734326 1859557 := bbase (se 4 (by rfl) ⟨174333, by rfl⟩ : syracuseStep 1859557 = 348667) (by norm_num)
theorem B1105901 : Blo 734326 1105901 := bbase (se 3 (by rfl) ⟨207356, by rfl⟩ : syracuseStep 1105901 = 414713) (by norm_num)
theorem B3137525 : Blo 734326 3137525 := bbase (se 5 (by rfl) ⟨147071, by rfl⟩ : syracuseStep 3137525 = 294143) (by norm_num)
theorem B1105925 : Blo 734326 1105925 := bbase (se 4 (by rfl) ⟨103680, by rfl⟩ : syracuseStep 1105925 = 207361) (by norm_num)
theorem B1105949 : Blo 734326 1105949 := bbase (se 3 (by rfl) ⟨207365, by rfl⟩ : syracuseStep 1105949 = 414731) (by norm_num)
theorem B2154533 : Blo 734326 2154533 := bbase (se 4 (by rfl) ⟨201987, by rfl⟩ : syracuseStep 2154533 = 403975) (by norm_num)
theorem B1105973 : Blo 734326 1105973 := bbase (se 5 (by rfl) ⟨51842, by rfl⟩ : syracuseStep 1105973 = 103685) (by norm_num)
theorem B1105997 : Blo 734326 1105997 := bbase (se 3 (by rfl) ⟨207374, by rfl⟩ : syracuseStep 1105997 = 414749) (by norm_num)
theorem B1859669 : Blo 734326 1859669 := bbase (se 8 (by rfl) ⟨10896, by rfl⟩ : syracuseStep 1859669 = 21793) (by norm_num)
theorem B1106021 : Blo 734326 1106021 := bbase (se 4 (by rfl) ⟨103689, by rfl⟩ : syracuseStep 1106021 = 207379) (by norm_num)
theorem B1106045 : Blo 734326 1106045 := bbase (se 3 (by rfl) ⟨207383, by rfl⟩ : syracuseStep 1106045 = 414767) (by norm_num)
theorem B1597573 : Blo 734326 1597573 := bbase (se 4 (by rfl) ⟨149772, by rfl⟩ : syracuseStep 1597573 = 299545) (by norm_num)
theorem B2482325 : Blo 734326 2482325 := bbase (se 6 (by rfl) ⟨58179, by rfl⟩ : syracuseStep 2482325 = 116359) (by norm_num)
theorem B1106069 : Blo 734326 1106069 := bbase (se 6 (by rfl) ⟨25923, by rfl⟩ : syracuseStep 1106069 = 51847) (by norm_num)
theorem B1106093 : Blo 734326 1106093 := bbase (se 3 (by rfl) ⟨207392, by rfl⟩ : syracuseStep 1106093 = 414785) (by norm_num)
theorem B5595317 : Blo 734326 5595317 := bbase (se 5 (by rfl) ⟨262280, by rfl⟩ : syracuseStep 5595317 = 524561) (by norm_num)
theorem B1106117 : Blo 734326 1106117 := bbase (se 4 (by rfl) ⟨103698, by rfl⟩ : syracuseStep 1106117 = 207397) (by norm_num)
theorem B1106141 : Blo 734326 1106141 := bbase (se 3 (by rfl) ⟨207401, by rfl⟩ : syracuseStep 1106141 = 414803) (by norm_num)
theorem B1106165 : Blo 734326 1106165 := bbase (se 5 (by rfl) ⟨51851, by rfl⟩ : syracuseStep 1106165 = 103703) (by norm_num)
theorem B1401077 : Blo 734326 1401077 := bbase (se 5 (by rfl) ⟨65675, by rfl⟩ : syracuseStep 1401077 = 131351) (by norm_num)
theorem B1106189 : Blo 734326 1106189 := bbase (se 3 (by rfl) ⟨207410, by rfl⟩ : syracuseStep 1106189 = 414821) (by norm_num)
theorem B1859861 : Blo 734326 1859861 := bbase (se 6 (by rfl) ⟨43590, by rfl⟩ : syracuseStep 1859861 = 87181) (by norm_num)
theorem B1106213 : Blo 734326 1106213 := bbase (se 4 (by rfl) ⟨103707, by rfl⟩ : syracuseStep 1106213 = 207415) (by norm_num)
theorem B1106237 : Blo 734326 1106237 := bbase (se 3 (by rfl) ⟨207419, by rfl⟩ : syracuseStep 1106237 = 414839) (by norm_num)
theorem B1106261 : Blo 734326 1106261 := bbase (se 10 (by rfl) ⟨1620, by rfl⟩ : syracuseStep 1106261 = 3241) (by norm_num)
theorem B942445 : Blo 734326 942445 := bbase (se 3 (by rfl) ⟨176708, by rfl⟩ : syracuseStep 942445 = 353417) (by norm_num)
theorem B1106285 : Blo 734326 1106285 := bbase (se 3 (by rfl) ⟨207428, by rfl⟩ : syracuseStep 1106285 = 414857) (by norm_num)
theorem B1106309 : Blo 734326 1106309 := bbase (se 4 (by rfl) ⟨103716, by rfl⟩ : syracuseStep 1106309 = 207433) (by norm_num)
theorem B1401229 : Blo 734326 1401229 := bbase (se 3 (by rfl) ⟨262730, by rfl⟩ : syracuseStep 1401229 = 525461) (by norm_num)
theorem B1106333 : Blo 734326 1106333 := bbase (se 3 (by rfl) ⟨207437, by rfl⟩ : syracuseStep 1106333 = 414875) (by norm_num)
theorem B3727781 : Blo 734326 3727781 := bbase (se 4 (by rfl) ⟨349479, by rfl⟩ : syracuseStep 3727781 = 698959) (by norm_num)
theorem B1106357 : Blo 734326 1106357 := bbase (se 5 (by rfl) ⟨51860, by rfl⟩ : syracuseStep 1106357 = 103721) (by norm_num)
theorem B1106381 : Blo 734326 1106381 := bbase (se 3 (by rfl) ⟨207446, by rfl⟩ : syracuseStep 1106381 = 414893) (by norm_num)
theorem B1106405 : Blo 734326 1106405 := bbase (se 4 (by rfl) ⟨103725, by rfl⟩ : syracuseStep 1106405 = 207451) (by norm_num)
theorem B1106429 : Blo 734326 1106429 := bbase (se 3 (by rfl) ⟨207455, by rfl⟩ : syracuseStep 1106429 = 414911) (by norm_num)
theorem B1106453 : Blo 734326 1106453 := bbase (se 6 (by rfl) ⟨25932, by rfl⟩ : syracuseStep 1106453 = 51865) (by norm_num)
theorem B1106477 : Blo 734326 1106477 := bbase (se 3 (by rfl) ⟨207464, by rfl⟩ : syracuseStep 1106477 = 414929) (by norm_num)
theorem B2482757 : Blo 734326 2482757 := bbase (se 4 (by rfl) ⟨232758, by rfl⟩ : syracuseStep 2482757 = 465517) (by norm_num)
theorem B1106501 : Blo 734326 1106501 := bbase (se 4 (by rfl) ⟨103734, by rfl⟩ : syracuseStep 1106501 = 207469) (by norm_num)
theorem B1106525 : Blo 734326 1106525 := bbase (se 3 (by rfl) ⟨207473, by rfl⟩ : syracuseStep 1106525 = 414947) (by norm_num)
theorem B1860205 : Blo 734326 1860205 := bbase (se 3 (by rfl) ⟨348788, by rfl⟩ : syracuseStep 1860205 = 697577) (by norm_num)
theorem B1106549 : Blo 734326 1106549 := bbase (se 5 (by rfl) ⟨51869, by rfl⟩ : syracuseStep 1106549 = 103739) (by norm_num)
theorem B1106573 : Blo 734326 1106573 := bbase (se 3 (by rfl) ⟨207482, by rfl⟩ : syracuseStep 1106573 = 414965) (by norm_num)
theorem B1106597 : Blo 734326 1106597 := bbase (se 4 (by rfl) ⟨103743, by rfl⟩ : syracuseStep 1106597 = 207487) (by norm_num)
theorem B1106621 : Blo 734326 1106621 := bbase (se 3 (by rfl) ⟨207491, by rfl⟩ : syracuseStep 1106621 = 414983) (by norm_num)
theorem B1401533 : Blo 734326 1401533 := bbase (se 3 (by rfl) ⟨262787, by rfl⟩ : syracuseStep 1401533 = 525575) (by norm_num)
theorem B1106645 : Blo 734326 1106645 := bbase (se 7 (by rfl) ⟨12968, by rfl⟩ : syracuseStep 1106645 = 25937) (by norm_num)
theorem B1860317 : Blo 734326 1860317 := bbase (se 3 (by rfl) ⟨348809, by rfl⟩ : syracuseStep 1860317 = 697619) (by norm_num)
theorem B3138277 : Blo 734326 3138277 := bbase (se 4 (by rfl) ⟨294213, by rfl⟩ : syracuseStep 3138277 = 588427) (by norm_num)
theorem B1106669 : Blo 734326 1106669 := bbase (se 3 (by rfl) ⟨207500, by rfl⟩ : syracuseStep 1106669 = 415001) (by norm_num)
theorem B1106693 : Blo 734326 1106693 := bbase (se 4 (by rfl) ⟨103752, by rfl⟩ : syracuseStep 1106693 = 207505) (by norm_num)
theorem B1106717 : Blo 734326 1106717 := bbase (se 3 (by rfl) ⟨207509, by rfl⟩ : syracuseStep 1106717 = 415019) (by norm_num)
theorem B1106741 : Blo 734326 1106741 := bbase (se 5 (by rfl) ⟨51878, by rfl⟩ : syracuseStep 1106741 = 103757) (by norm_num)
theorem B1106765 : Blo 734326 1106765 := bbase (se 3 (by rfl) ⟨207518, by rfl⟩ : syracuseStep 1106765 = 415037) (by norm_num)
theorem B1794901 : Blo 734326 1794901 := bbase (se 9 (by rfl) ⟨5258, by rfl⟩ : syracuseStep 1794901 = 10517) (by norm_num)
theorem B1106789 : Blo 734326 1106789 := bbase (se 4 (by rfl) ⟨103761, by rfl⟩ : syracuseStep 1106789 = 207523) (by norm_num)
theorem B1106813 : Blo 734326 1106813 := bbase (se 3 (by rfl) ⟨207527, by rfl⟩ : syracuseStep 1106813 = 415055) (by norm_num)
theorem B1598341 : Blo 734326 1598341 := bbase (se 4 (by rfl) ⟨149844, by rfl⟩ : syracuseStep 1598341 = 299689) (by norm_num)
theorem B1106837 : Blo 734326 1106837 := bbase (se 6 (by rfl) ⟨25941, by rfl⟩ : syracuseStep 1106837 = 51883) (by norm_num)
theorem B1860509 : Blo 734326 1860509 := bbase (se 3 (by rfl) ⟨348845, by rfl⟩ : syracuseStep 1860509 = 697691) (by norm_num)
theorem B1106861 : Blo 734326 1106861 := bbase (se 3 (by rfl) ⟨207536, by rfl⟩ : syracuseStep 1106861 = 415073) (by norm_num)
theorem B1106885 : Blo 734326 1106885 := bbase (se 4 (by rfl) ⟨103770, by rfl⟩ : syracuseStep 1106885 = 207541) (by norm_num)
theorem B1106909 : Blo 734326 1106909 := bbase (se 3 (by rfl) ⟨207545, by rfl⟩ : syracuseStep 1106909 = 415091) (by norm_num)
theorem B2483189 : Blo 734326 2483189 := bbase (se 5 (by rfl) ⟨116399, by rfl⟩ : syracuseStep 2483189 = 232799) (by norm_num)
theorem B1106933 : Blo 734326 1106933 := bbase (se 5 (by rfl) ⟨51887, by rfl⟩ : syracuseStep 1106933 = 103775) (by norm_num)
theorem B1106957 : Blo 734326 1106957 := bbase (se 3 (by rfl) ⟨207554, by rfl⟩ : syracuseStep 1106957 = 415109) (by norm_num)
theorem B1106981 : Blo 734326 1106981 := bbase (se 4 (by rfl) ⟨103779, by rfl⟩ : syracuseStep 1106981 = 207559) (by norm_num)
theorem B1107005 : Blo 734326 1107005 := bbase (se 3 (by rfl) ⟨207563, by rfl⟩ : syracuseStep 1107005 = 415127) (by norm_num)
theorem B1107029 : Blo 734326 1107029 := bbase (se 8 (by rfl) ⟨6486, by rfl⟩ : syracuseStep 1107029 = 12973) (by norm_num)
theorem B1107053 : Blo 734326 1107053 := bbase (se 3 (by rfl) ⟨207572, by rfl⟩ : syracuseStep 1107053 = 415145) (by norm_num)
theorem B1893509 : Blo 734326 1893509 := bbase (se 4 (by rfl) ⟨177516, by rfl⟩ : syracuseStep 1893509 = 355033) (by norm_num)
theorem B1107077 : Blo 734326 1107077 := bbase (se 4 (by rfl) ⟨103788, by rfl⟩ : syracuseStep 1107077 = 207577) (by norm_num)
theorem B4187285 : Blo 734326 4187285 := bbase (se 6 (by rfl) ⟨98139, by rfl⟩ : syracuseStep 4187285 = 196279) (by norm_num)
theorem B1107101 : Blo 734326 1107101 := bbase (se 3 (by rfl) ⟨207581, by rfl⟩ : syracuseStep 1107101 = 415163) (by norm_num)
theorem B1107125 : Blo 734326 1107125 := bbase (se 5 (by rfl) ⟨51896, by rfl⟩ : syracuseStep 1107125 = 103793) (by norm_num)
theorem B1107149 : Blo 734326 1107149 := bbase (se 3 (by rfl) ⟨207590, by rfl⟩ : syracuseStep 1107149 = 415181) (by norm_num)
theorem B1107173 : Blo 734326 1107173 := bbase (se 4 (by rfl) ⟨103797, by rfl⟩ : syracuseStep 1107173 = 207595) (by norm_num)
theorem B1860853 : Blo 734326 1860853 := bbase (se 5 (by rfl) ⟨87227, by rfl⟩ : syracuseStep 1860853 = 174455) (by norm_num)
theorem B1107197 : Blo 734326 1107197 := bbase (se 3 (by rfl) ⟨207599, by rfl⟩ : syracuseStep 1107197 = 415199) (by norm_num)
theorem B1107221 : Blo 734326 1107221 := bbase (se 6 (by rfl) ⟨25950, by rfl⟩ : syracuseStep 1107221 = 51901) (by norm_num)
theorem B1107245 : Blo 734326 1107245 := bbase (se 3 (by rfl) ⟨207608, by rfl⟩ : syracuseStep 1107245 = 415217) (by norm_num)
theorem B1107269 : Blo 734326 1107269 := bbase (se 4 (by rfl) ⟨103806, by rfl⟩ : syracuseStep 1107269 = 207613) (by norm_num)
theorem B1107293 : Blo 734326 1107293 := bbase (se 3 (by rfl) ⟨207617, by rfl⟩ : syracuseStep 1107293 = 415235) (by norm_num)
theorem B1860965 : Blo 734326 1860965 := bbase (se 4 (by rfl) ⟨174465, by rfl⟩ : syracuseStep 1860965 = 348931) (by norm_num)
theorem B1107317 : Blo 734326 1107317 := bbase (se 5 (by rfl) ⟨51905, by rfl⟩ : syracuseStep 1107317 = 103811) (by norm_num)
theorem B1107341 : Blo 734326 1107341 := bbase (se 3 (by rfl) ⟨207626, by rfl⟩ : syracuseStep 1107341 = 415253) (by norm_num)
theorem B2483621 : Blo 734326 2483621 := bbase (se 4 (by rfl) ⟨232839, by rfl⟩ : syracuseStep 2483621 = 465679) (by norm_num)
theorem B1107365 : Blo 734326 1107365 := bbase (se 4 (by rfl) ⟨103815, by rfl⟩ : syracuseStep 1107365 = 207631) (by norm_num)
theorem B1107389 : Blo 734326 1107389 := bbase (se 3 (by rfl) ⟨207635, by rfl⟩ : syracuseStep 1107389 = 415271) (by norm_num)
theorem B3139013 : Blo 734326 3139013 := bbase (se 4 (by rfl) ⟨294282, by rfl⟩ : syracuseStep 3139013 = 588565) (by norm_num)
theorem B1107413 : Blo 734326 1107413 := bbase (se 7 (by rfl) ⟨12977, by rfl⟩ : syracuseStep 1107413 = 25955) (by norm_num)
theorem B1107437 : Blo 734326 1107437 := bbase (se 3 (by rfl) ⟨207644, by rfl⟩ : syracuseStep 1107437 = 415289) (by norm_num)
theorem B1107461 : Blo 734326 1107461 := bbase (se 4 (by rfl) ⟨103824, by rfl⟩ : syracuseStep 1107461 = 207649) (by norm_num)
theorem B1107485 : Blo 734326 1107485 := bbase (se 3 (by rfl) ⟨207653, by rfl⟩ : syracuseStep 1107485 = 415307) (by norm_num)
theorem B1861157 : Blo 734326 1861157 := bbase (se 4 (by rfl) ⟨174483, by rfl⟩ : syracuseStep 1861157 = 348967) (by norm_num)
theorem B3729077 : Blo 734326 3729077 := bbase (se 5 (by rfl) ⟨174800, by rfl⟩ : syracuseStep 3729077 = 349601) (by norm_num)
theorem B943861 : Blo 734326 943861 := bbase (se 5 (by rfl) ⟨44243, by rfl⟩ : syracuseStep 943861 = 88487) (by norm_num)
theorem B2484053 : Blo 734326 2484053 := bbase (se 9 (by rfl) ⟨7277, by rfl⟩ : syracuseStep 2484053 = 14555) (by norm_num)
theorem B1861501 : Blo 734326 1861501 := bbase (se 3 (by rfl) ⟨349031, by rfl⟩ : syracuseStep 1861501 = 698063) (by norm_num)
theorem B747433 : Blo 734326 747433 := bbase (se 2 (by rfl) ⟨280287, by rfl⟩ : syracuseStep 747433 = 560575) (by norm_num)
theorem B1861613 : Blo 734326 1861613 := bbase (se 3 (by rfl) ⟨349052, by rfl⟩ : syracuseStep 1861613 = 698105) (by norm_num)
theorem B1239205 : Blo 734326 1239205 := bbase (se 4 (by rfl) ⟨116175, by rfl⟩ : syracuseStep 1239205 = 232351) (by norm_num)
theorem B1861805 : Blo 734326 1861805 := bbase (se 3 (by rfl) ⟨349088, by rfl⟩ : syracuseStep 1861805 = 698177) (by norm_num)
theorem B2353349 : Blo 734326 2353349 := bbase (se 4 (by rfl) ⟨220626, by rfl⟩ : syracuseStep 2353349 = 441253) (by norm_num)
theorem B1239293 : Blo 734326 1239293 := bbase (se 3 (by rfl) ⟨232367, by rfl⟩ : syracuseStep 1239293 = 464735) (by norm_num)
theorem B2484485 : Blo 734326 2484485 := bbase (se 4 (by rfl) ⟨232920, by rfl⟩ : syracuseStep 2484485 = 465841) (by norm_num)
theorem B4188469 : Blo 734326 4188469 := bbase (se 5 (by rfl) ⟨196334, by rfl⟩ : syracuseStep 4188469 = 392669) (by norm_num)
theorem B2091365 : Blo 734326 2091365 := bbase (se 4 (by rfl) ⟨196065, by rfl⟩ : syracuseStep 2091365 = 392131) (by norm_num)
theorem B1239421 : Blo 734326 1239421 := bbase (se 3 (by rfl) ⟨232391, by rfl⟩ : syracuseStep 1239421 = 464783) (by norm_num)
theorem B1239509 : Blo 734326 1239509 := bbase (se 7 (by rfl) ⟨14525, by rfl⟩ : syracuseStep 1239509 = 29051) (by norm_num)
theorem B1862149 : Blo 734326 1862149 := bbase (se 4 (by rfl) ⟨174576, by rfl⟩ : syracuseStep 1862149 = 349153) (by norm_num)
theorem B1239637 : Blo 734326 1239637 := bbase (se 8 (by rfl) ⟨7263, by rfl⟩ : syracuseStep 1239637 = 14527) (by norm_num)
theorem B1862261 : Blo 734326 1862261 := bbase (se 5 (by rfl) ⟨87293, by rfl⟩ : syracuseStep 1862261 = 174587) (by norm_num)
theorem B1239725 : Blo 734326 1239725 := bbase (se 3 (by rfl) ⟨232448, by rfl⟩ : syracuseStep 1239725 = 464897) (by norm_num)
theorem B2484917 : Blo 734326 2484917 := bbase (se 5 (by rfl) ⟨116480, by rfl⟩ : syracuseStep 2484917 = 232961) (by norm_num)
theorem B1239853 : Blo 734326 1239853 := bbase (se 3 (by rfl) ⟨232472, by rfl⟩ : syracuseStep 1239853 = 464945) (by norm_num)
theorem B1862453 : Blo 734326 1862453 := bbase (se 5 (by rfl) ⟨87302, by rfl⟩ : syracuseStep 1862453 = 174605) (by norm_num)
theorem B1239941 : Blo 734326 1239941 := bbase (se 4 (by rfl) ⟨116244, by rfl⟩ : syracuseStep 1239941 = 232489) (by norm_num)
theorem B3730373 : Blo 734326 3730373 := bbase (se 4 (by rfl) ⟨349722, by rfl⟩ : syracuseStep 3730373 = 699445) (by norm_num)
theorem B1240069 : Blo 734326 1240069 := bbase (se 4 (by rfl) ⟨116256, by rfl⟩ : syracuseStep 1240069 = 232513) (by norm_num)
theorem B1240157 : Blo 734326 1240157 := bbase (se 3 (by rfl) ⟨232529, by rfl⟩ : syracuseStep 1240157 = 465059) (by norm_num)
theorem B2485349 : Blo 734326 2485349 := bbase (se 4 (by rfl) ⟨233001, by rfl⟩ : syracuseStep 2485349 = 466003) (by norm_num)
theorem B1862797 : Blo 734326 1862797 := bbase (se 3 (by rfl) ⟨349274, by rfl⟩ : syracuseStep 1862797 = 698549) (by norm_num)
theorem B945329 : Blo 734326 945329 := bbase (se 2 (by rfl) ⟨354498, by rfl⟩ : syracuseStep 945329 = 708997) (by norm_num)
theorem B1240285 : Blo 734326 1240285 := bbase (se 3 (by rfl) ⟨232553, by rfl⟩ : syracuseStep 1240285 = 465107) (by norm_num)
theorem B1862909 : Blo 734326 1862909 := bbase (se 3 (by rfl) ⟨349295, by rfl⟩ : syracuseStep 1862909 = 698591) (by norm_num)
theorem B1764629 : Blo 734326 1764629 := bbase (se 6 (by rfl) ⟨41358, by rfl⟩ : syracuseStep 1764629 = 82717) (by norm_num)
theorem B3534101 : Blo 734326 3534101 := bbase (se 6 (by rfl) ⟨82830, by rfl⟩ : syracuseStep 3534101 = 165661) (by norm_num)
theorem B1994021 : Blo 734326 1994021 := bbase (se 4 (by rfl) ⟨186939, by rfl⟩ : syracuseStep 1994021 = 373879) (by norm_num)
theorem B1240373 : Blo 734326 1240373 := bbase (se 5 (by rfl) ⟨58142, by rfl⟩ : syracuseStep 1240373 = 116285) (by norm_num)
theorem B1240501 : Blo 734326 1240501 := bbase (se 5 (by rfl) ⟨58148, by rfl⟩ : syracuseStep 1240501 = 116297) (by norm_num)
theorem B1863101 : Blo 734326 1863101 := bbase (se 3 (by rfl) ⟨349331, by rfl⟩ : syracuseStep 1863101 = 698663) (by norm_num)
theorem B1535429 : Blo 734326 1535429 := bbase (se 4 (by rfl) ⟨143946, by rfl⟩ : syracuseStep 1535429 = 287893) (by norm_num)
theorem B1764821 : Blo 734326 1764821 := bbase (se 7 (by rfl) ⟨20681, by rfl⟩ : syracuseStep 1764821 = 41363) (by norm_num)
theorem B6286805 : Blo 734326 6286805 := bbase (se 7 (by rfl) ⟨73673, by rfl⟩ : syracuseStep 6286805 = 147347) (by norm_num)
theorem B2092549 : Blo 734326 2092549 := bbase (se 4 (by rfl) ⟨196176, by rfl⟩ : syracuseStep 2092549 = 392353) (by norm_num)
theorem B1240589 : Blo 734326 1240589 := bbase (se 3 (by rfl) ⟨232610, by rfl⟩ : syracuseStep 1240589 = 465221) (by norm_num)
theorem B2485781 : Blo 734326 2485781 := bbase (se 6 (by rfl) ⟨58260, by rfl⟩ : syracuseStep 2485781 = 116521) (by norm_num)
theorem B1240717 : Blo 734326 1240717 := bbase (se 3 (by rfl) ⟨232634, by rfl⟩ : syracuseStep 1240717 = 465269) (by norm_num)
theorem B1568413 : Blo 734326 1568413 := bbase (se 3 (by rfl) ⟨294077, by rfl⟩ : syracuseStep 1568413 = 588155) (by norm_num)
theorem B2092709 : Blo 734326 2092709 := bbase (se 4 (by rfl) ⟨196191, by rfl⟩ : syracuseStep 2092709 = 392383) (by norm_num)
theorem B1240805 : Blo 734326 1240805 := bbase (se 4 (by rfl) ⟨116325, by rfl⟩ : syracuseStep 1240805 = 232651) (by norm_num)
theorem B1863445 : Blo 734326 1863445 := bbase (se 6 (by rfl) ⟨43674, by rfl⟩ : syracuseStep 1863445 = 87349) (by norm_num)
theorem B2649941 : Blo 734326 2649941 := bbase (se 9 (by rfl) ⟨7763, by rfl⟩ : syracuseStep 2649941 = 15527) (by norm_num)
theorem B5304149 : Blo 734326 5304149 := bbase (se 9 (by rfl) ⟨15539, by rfl⟩ : syracuseStep 5304149 = 31079) (by norm_num)
theorem B1240933 : Blo 734326 1240933 := bbase (se 4 (by rfl) ⟨116337, by rfl⟩ : syracuseStep 1240933 = 232675) (by norm_num)
theorem B1863557 : Blo 734326 1863557 := bbase (se 4 (by rfl) ⟨174708, by rfl⟩ : syracuseStep 1863557 = 349417) (by norm_num)
theorem B2092949 : Blo 734326 2092949 := bbase (se 6 (by rfl) ⟨49053, by rfl⟩ : syracuseStep 2092949 = 98107) (by norm_num)
theorem B1241021 : Blo 734326 1241021 := bbase (se 3 (by rfl) ⟨232691, by rfl⟩ : syracuseStep 1241021 = 465383) (by norm_num)
theorem B2486213 : Blo 734326 2486213 := bbase (se 4 (by rfl) ⟨233082, by rfl⟩ : syracuseStep 2486213 = 466165) (by norm_num)
theorem B1765397 : Blo 734326 1765397 := bbase (se 6 (by rfl) ⟨41376, by rfl⟩ : syracuseStep 1765397 = 82753) (by norm_num)
theorem B1241149 : Blo 734326 1241149 := bbase (se 3 (by rfl) ⟨232715, by rfl⟩ : syracuseStep 1241149 = 465431) (by norm_num)
theorem B1863749 : Blo 734326 1863749 := bbase (se 4 (by rfl) ⟨174726, by rfl⟩ : syracuseStep 1863749 = 349453) (by norm_num)
theorem B2093141 : Blo 734326 2093141 := bbase (se 8 (by rfl) ⟨12264, by rfl⟩ : syracuseStep 2093141 = 24529) (by norm_num)
theorem B946273 : Blo 734326 946273 := bbase (se 2 (by rfl) ⟨354852, by rfl⟩ : syracuseStep 946273 = 709705) (by norm_num)
theorem B2650229 : Blo 734326 2650229 := bbase (se 5 (by rfl) ⟨124229, by rfl⟩ : syracuseStep 2650229 = 248459) (by norm_num)
theorem B1241237 : Blo 734326 1241237 := bbase (se 6 (by rfl) ⟨29091, by rfl⟩ : syracuseStep 1241237 = 58183) (by norm_num)
theorem B3731669 : Blo 734326 3731669 := bbase (se 7 (by rfl) ⟨43730, by rfl⟩ : syracuseStep 3731669 = 87461) (by norm_num)
theorem B4190453 : Blo 734326 4190453 := bbase (se 5 (by rfl) ⟨196427, by rfl⟩ : syracuseStep 4190453 = 392855) (by norm_num)
theorem B1241365 : Blo 734326 1241365 := bbase (se 6 (by rfl) ⟨29094, by rfl⟩ : syracuseStep 1241365 = 58189) (by norm_num)
theorem B1241453 : Blo 734326 1241453 := bbase (se 3 (by rfl) ⟨232772, by rfl⟩ : syracuseStep 1241453 = 465545) (by norm_num)
theorem B2486645 : Blo 734326 2486645 := bbase (se 5 (by rfl) ⟨116561, by rfl⟩ : syracuseStep 2486645 = 233123) (by norm_num)
theorem B1765781 : Blo 734326 1765781 := bbase (se 6 (by rfl) ⟨41385, by rfl⟩ : syracuseStep 1765781 = 82771) (by norm_num)
theorem B2355605 : Blo 734326 2355605 := bbase (se 6 (by rfl) ⟨55209, by rfl⟩ : syracuseStep 2355605 = 110419) (by norm_num)
theorem B1864093 : Blo 734326 1864093 := bbase (se 3 (by rfl) ⟨349517, by rfl⟩ : syracuseStep 1864093 = 699035) (by norm_num)
theorem B1241581 : Blo 734326 1241581 := bbase (se 3 (by rfl) ⟨232796, by rfl⟩ : syracuseStep 1241581 = 465593) (by norm_num)
theorem B1864205 : Blo 734326 1864205 := bbase (se 3 (by rfl) ⟨349538, by rfl⟩ : syracuseStep 1864205 = 699077) (by norm_num)
theorem B2355733 : Blo 734326 2355733 := bbase (se 6 (by rfl) ⟨55212, by rfl⟩ : syracuseStep 2355733 = 110425) (by norm_num)
theorem B1241669 : Blo 734326 1241669 := bbase (se 4 (by rfl) ⟨116406, by rfl⟩ : syracuseStep 1241669 = 232813) (by norm_num)
theorem B3142309 : Blo 734326 3142309 := bbase (se 4 (by rfl) ⟨294591, by rfl⟩ : syracuseStep 3142309 = 589183) (by norm_num)
theorem B946873 : Blo 734326 946873 := bbase (se 2 (by rfl) ⟨355077, by rfl⟩ : syracuseStep 946873 = 710155) (by norm_num)
theorem B1241797 : Blo 734326 1241797 := bbase (se 4 (by rfl) ⟨116418, by rfl⟩ : syracuseStep 1241797 = 232837) (by norm_num)
theorem B1864397 : Blo 734326 1864397 := bbase (se 3 (by rfl) ⟨349574, by rfl⟩ : syracuseStep 1864397 = 699149) (by norm_num)
theorem B1241885 : Blo 734326 1241885 := bbase (se 3 (by rfl) ⟨232853, by rfl⟩ : syracuseStep 1241885 = 465707) (by norm_num)
theorem B2487077 : Blo 734326 2487077 := bbase (se 4 (by rfl) ⟨233163, by rfl⟩ : syracuseStep 2487077 = 466327) (by norm_num)
theorem B1242013 : Blo 734326 1242013 := bbase (se 3 (by rfl) ⟨232877, by rfl⟩ : syracuseStep 1242013 = 465755) (by norm_num)
theorem B1242101 : Blo 734326 1242101 := bbase (se 5 (by rfl) ⟨58223, by rfl⟩ : syracuseStep 1242101 = 116447) (by norm_num)
theorem B1864741 : Blo 734326 1864741 := bbase (se 4 (by rfl) ⟨174819, by rfl⟩ : syracuseStep 1864741 = 349639) (by norm_num)
theorem B2094133 : Blo 734326 2094133 := bbase (se 5 (by rfl) ⟨98162, by rfl⟩ : syracuseStep 2094133 = 196325) (by norm_num)
theorem B1242229 : Blo 734326 1242229 := bbase (se 5 (by rfl) ⟨58229, by rfl⟩ : syracuseStep 1242229 = 116459) (by norm_num)
theorem B1569917 : Blo 734326 1569917 := bbase (se 3 (by rfl) ⟨294359, by rfl⟩ : syracuseStep 1569917 = 588719) (by norm_num)
theorem B1864853 : Blo 734326 1864853 := bbase (se 6 (by rfl) ⟨43707, by rfl⟩ : syracuseStep 1864853 = 87415) (by norm_num)
theorem B1242317 : Blo 734326 1242317 := bbase (se 3 (by rfl) ⟨232934, by rfl⟩ : syracuseStep 1242317 = 465869) (by norm_num)
theorem B2487509 : Blo 734326 2487509 := bbase (se 7 (by rfl) ⟨29150, by rfl⟩ : syracuseStep 2487509 = 58301) (by norm_num)
theorem B1570061 : Blo 734326 1570061 := bbase (se 3 (by rfl) ⟨294386, by rfl⟩ : syracuseStep 1570061 = 588773) (by norm_num)
theorem B1242445 : Blo 734326 1242445 := bbase (se 3 (by rfl) ⟨232958, by rfl⟩ : syracuseStep 1242445 = 465917) (by norm_num)
theorem B1865045 : Blo 734326 1865045 := bbase (se 13 (by rfl) ⟨341, by rfl⟩ : syracuseStep 1865045 = 683) (by norm_num)
theorem B1176925 : Blo 734326 1176925 := bbase (se 3 (by rfl) ⟨220673, by rfl⟩ : syracuseStep 1176925 = 441347) (by norm_num)
theorem B1275229 : Blo 734326 1275229 := bbase (se 3 (by rfl) ⟨239105, by rfl⟩ : syracuseStep 1275229 = 478211) (by norm_num)
theorem B2979173 : Blo 734326 2979173 := bbase (se 4 (by rfl) ⟨279297, by rfl⟩ : syracuseStep 2979173 = 558595) (by norm_num)
theorem B1242533 : Blo 734326 1242533 := bbase (se 4 (by rfl) ⟨116487, by rfl⟩ : syracuseStep 1242533 = 232975) (by norm_num)
theorem B1045973 : Blo 734326 1045973 := bbase (se 7 (by rfl) ⟨12257, by rfl⟩ : syracuseStep 1045973 = 24515) (by norm_num)
theorem B3732965 : Blo 734326 3732965 := bbase (se 4 (by rfl) ⟨349965, by rfl⟩ : syracuseStep 3732965 = 699931) (by norm_num)
theorem B1242661 : Blo 734326 1242661 := bbase (se 4 (by rfl) ⟨116499, by rfl⟩ : syracuseStep 1242661 = 232999) (by norm_num)
theorem B1570421 : Blo 734326 1570421 := bbase (se 5 (by rfl) ⟨73613, by rfl⟩ : syracuseStep 1570421 = 147227) (by norm_num)
theorem B1242749 : Blo 734326 1242749 := bbase (se 3 (by rfl) ⟨233015, by rfl⟩ : syracuseStep 1242749 = 466031) (by norm_num)
theorem B2487941 : Blo 734326 2487941 := bbase (se 4 (by rfl) ⟨233244, by rfl⟩ : syracuseStep 2487941 = 466489) (by norm_num)
theorem B1865389 : Blo 734326 1865389 := bbase (se 3 (by rfl) ⟨349760, by rfl⟩ : syracuseStep 1865389 = 699521) (by norm_num)
theorem B5961397 : Blo 734326 5961397 := bbase (se 5 (by rfl) ⟨279440, by rfl⟩ : syracuseStep 5961397 = 558881) (by norm_num)
theorem B1242877 : Blo 734326 1242877 := bbase (se 3 (by rfl) ⟨233039, by rfl⟩ : syracuseStep 1242877 = 466079) (by norm_num)
theorem B1865501 : Blo 734326 1865501 := bbase (se 3 (by rfl) ⟨349781, by rfl⟩ : syracuseStep 1865501 = 699563) (by norm_num)
theorem B1242965 : Blo 734326 1242965 := bbase (se 9 (by rfl) ⟨3641, by rfl⟩ : syracuseStep 1242965 = 7283) (by norm_num)
theorem B3536789 : Blo 734326 3536789 := bbase (se 6 (by rfl) ⟨82893, by rfl⟩ : syracuseStep 3536789 = 165787) (by norm_num)
theorem B1243093 : Blo 734326 1243093 := bbase (se 7 (by rfl) ⟨14567, by rfl⟩ : syracuseStep 1243093 = 29135) (by norm_num)
theorem B1865693 : Blo 734326 1865693 := bbase (se 3 (by rfl) ⟨349817, by rfl⟩ : syracuseStep 1865693 = 699635) (by norm_num)
theorem B1046525 : Blo 734326 1046525 := bbase (se 3 (by rfl) ⟨196223, by rfl⟩ : syracuseStep 1046525 = 392447) (by norm_num)
theorem B1177597 : Blo 734326 1177597 := bbase (se 3 (by rfl) ⟨220799, by rfl⟩ : syracuseStep 1177597 = 441599) (by norm_num)
theorem B1243181 : Blo 734326 1243181 := bbase (se 3 (by rfl) ⟨233096, by rfl⟩ : syracuseStep 1243181 = 466193) (by norm_num)
theorem B2488373 : Blo 734326 2488373 := bbase (se 5 (by rfl) ⟨116642, by rfl⟩ : syracuseStep 2488373 = 233285) (by norm_num)
theorem B1439837 : Blo 734326 1439837 := bbase (se 3 (by rfl) ⟨269969, by rfl⟩ : syracuseStep 1439837 = 539939) (by norm_num)
theorem B882785 : Blo 734326 882785 := bbase (se 2 (by rfl) ⟨331044, by rfl⟩ : syracuseStep 882785 = 662089) (by norm_num)
theorem B1767541 : Blo 734326 1767541 := bbase (se 5 (by rfl) ⟨82853, by rfl⟩ : syracuseStep 1767541 = 165707) (by norm_num)
theorem B2652277 : Blo 734326 2652277 := bbase (se 5 (by rfl) ⟨124325, by rfl⟩ : syracuseStep 2652277 = 248651) (by norm_num)
theorem B2095237 : Blo 734326 2095237 := bbase (se 4 (by rfl) ⟨196428, by rfl⟩ : syracuseStep 2095237 = 392857) (by norm_num)
theorem B1243309 : Blo 734326 1243309 := bbase (se 3 (by rfl) ⟨233120, by rfl⟩ : syracuseStep 1243309 = 466241) (by norm_num)
theorem B784561 : Blo 734326 784561 := bbase (se 2 (by rfl) ⟨294210, by rfl⟩ : syracuseStep 784561 = 588421) (by norm_num)
theorem B2652421 : Blo 734326 2652421 := bbase (se 4 (by rfl) ⟨248664, by rfl⟩ : syracuseStep 2652421 = 497329) (by norm_num)
theorem B1243397 : Blo 734326 1243397 := bbase (se 4 (by rfl) ⟨116568, by rfl⟩ : syracuseStep 1243397 = 233137) (by norm_num)
theorem B784685 : Blo 734326 784685 := bbase (se 3 (by rfl) ⟨147128, by rfl⟩ : syracuseStep 784685 = 294257) (by norm_num)
theorem B1866037 : Blo 734326 1866037 := bbase (se 5 (by rfl) ⟨87470, by rfl⟩ : syracuseStep 1866037 = 174941) (by norm_num)
theorem B1243525 : Blo 734326 1243525 := bbase (se 4 (by rfl) ⟨116580, by rfl⟩ : syracuseStep 1243525 = 233161) (by norm_num)
theorem B4192661 : Blo 734326 4192661 := bbase (se 6 (by rfl) ⟨98265, by rfl⟩ : syracuseStep 4192661 = 196531) (by norm_num)
theorem B4716949 : Blo 734326 4716949 := bbase (se 6 (by rfl) ⟨110553, by rfl⟩ : syracuseStep 4716949 = 221107) (by norm_num)
theorem B2652581 : Blo 734326 2652581 := bbase (se 4 (by rfl) ⟨248679, by rfl⟩ : syracuseStep 2652581 = 497359) (by norm_num)
theorem B1866149 : Blo 734326 1866149 := bbase (se 4 (by rfl) ⟨174951, by rfl⟩ : syracuseStep 1866149 = 349903) (by norm_num)
theorem B883121 : Blo 734326 883121 := bbase (se 2 (by rfl) ⟨331170, by rfl⟩ : syracuseStep 883121 = 662341) (by norm_num)
theorem B1243613 : Blo 734326 1243613 := bbase (se 3 (by rfl) ⟨233177, by rfl⟩ : syracuseStep 1243613 = 466355) (by norm_num)
theorem B2488805 : Blo 734326 2488805 := bbase (se 4 (by rfl) ⟨233325, by rfl⟩ : syracuseStep 2488805 = 466651) (by norm_num)
theorem B1571309 : Blo 734326 1571309 := bbase (se 3 (by rfl) ⟨294620, by rfl⟩ : syracuseStep 1571309 = 589241) (by norm_num)
theorem B883237 : Blo 734326 883237 := bbase (se 4 (by rfl) ⟨82803, by rfl⟩ : syracuseStep 883237 = 165607) (by norm_num)
theorem B2652709 : Blo 734326 2652709 := bbase (se 4 (by rfl) ⟨248691, by rfl⟩ : syracuseStep 2652709 = 497383) (by norm_num)
theorem B784937 : Blo 734326 784937 := bbase (se 2 (by rfl) ⟨294351, by rfl⟩ : syracuseStep 784937 = 588703) (by norm_num)
theorem B1243741 : Blo 734326 1243741 := bbase (se 3 (by rfl) ⟨233201, by rfl⟩ : syracuseStep 1243741 = 466403) (by norm_num)
theorem B1866341 : Blo 734326 1866341 := bbase (se 4 (by rfl) ⟨174969, by rfl⟩ : syracuseStep 1866341 = 349939) (by norm_num)
theorem B883309 : Blo 734326 883309 := bbase (se 3 (by rfl) ⟨165620, by rfl⟩ : syracuseStep 883309 = 331241) (by norm_num)
theorem B883333 : Blo 734326 883333 := bbase (se 4 (by rfl) ⟨82812, by rfl⟩ : syracuseStep 883333 = 165625) (by norm_num)
theorem B1243829 : Blo 734326 1243829 := bbase (se 5 (by rfl) ⟨58304, by rfl⟩ : syracuseStep 1243829 = 116609) (by norm_num)
theorem B1571557 : Blo 734326 1571557 := bbase (se 4 (by rfl) ⟨147333, by rfl⟩ : syracuseStep 1571557 = 294667) (by norm_num)
theorem B1047277 : Blo 734326 1047277 := bbase (se 3 (by rfl) ⟨196364, by rfl⟩ : syracuseStep 1047277 = 392729) (by norm_num)
theorem B3734261 : Blo 734326 3734261 := bbase (se 5 (by rfl) ⟨175043, by rfl⟩ : syracuseStep 3734261 = 350087) (by norm_num)
theorem B4193045 : Blo 734326 4193045 := bbase (se 6 (by rfl) ⟨98274, by rfl⟩ : syracuseStep 4193045 = 196549) (by norm_num)
theorem B883477 : Blo 734326 883477 := bbase (se 6 (by rfl) ⟨20706, by rfl⟩ : syracuseStep 883477 = 41413) (by norm_num)
theorem B1243957 : Blo 734326 1243957 := bbase (se 5 (by rfl) ⟨58310, by rfl⟩ : syracuseStep 1243957 = 116621) (by norm_num)
theorem B3406693 : Blo 734326 3406693 := bbase (se 4 (by rfl) ⟨319377, by rfl⟩ : syracuseStep 3406693 = 638755) (by norm_num)
theorem B1244045 : Blo 734326 1244045 := bbase (se 3 (by rfl) ⟨233258, by rfl⟩ : syracuseStep 1244045 = 466517) (by norm_num)
theorem B2489237 : Blo 734326 2489237 := bbase (se 6 (by rfl) ⟨58341, by rfl⟩ : syracuseStep 2489237 = 116683) (by norm_num)
theorem B1866685 : Blo 734326 1866685 := bbase (se 3 (by rfl) ⟨350003, by rfl⟩ : syracuseStep 1866685 = 700007) (by norm_num)
theorem B785381 : Blo 734326 785381 := bbase (se 4 (by rfl) ⟨73629, by rfl⟩ : syracuseStep 785381 = 147259) (by norm_num)
theorem B1178597 : Blo 734326 1178597 := bbase (se 4 (by rfl) ⟨110493, by rfl⟩ : syracuseStep 1178597 = 220987) (by norm_num)
theorem B1244173 : Blo 734326 1244173 := bbase (se 3 (by rfl) ⟨233282, by rfl⟩ : syracuseStep 1244173 = 466565) (by norm_num)
theorem B1866797 : Blo 734326 1866797 := bbase (se 3 (by rfl) ⟨350024, by rfl⟩ : syracuseStep 1866797 = 700049) (by norm_num)
theorem B1768549 : Blo 734326 1768549 := bbase (se 4 (by rfl) ⟨165801, by rfl⟩ : syracuseStep 1768549 = 331603) (by norm_num)
theorem B1244261 : Blo 734326 1244261 := bbase (se 4 (by rfl) ⟨116649, by rfl⟩ : syracuseStep 1244261 = 233299) (by norm_num)
theorem B2522261 : Blo 734326 2522261 := bbase (se 6 (by rfl) ⟨59115, by rfl⟩ : syracuseStep 2522261 = 118231) (by norm_num)
theorem B1768645 : Blo 734326 1768645 := bbase (se 4 (by rfl) ⟨165810, by rfl⟩ : syracuseStep 1768645 = 331621) (by norm_num)
theorem B785629 : Blo 734326 785629 := bbase (se 3 (by rfl) ⟨147305, by rfl⟩ : syracuseStep 785629 = 294611) (by norm_num)
theorem B1572061 : Blo 734326 1572061 := bbase (se 3 (by rfl) ⟨294761, by rfl⟩ : syracuseStep 1572061 = 589523) (by norm_num)
theorem B1244389 : Blo 734326 1244389 := bbase (se 4 (by rfl) ⟨116661, by rfl⟩ : syracuseStep 1244389 = 233323) (by norm_num)
theorem B1866989 : Blo 734326 1866989 := bbase (se 3 (by rfl) ⟨350060, by rfl⟩ : syracuseStep 1866989 = 700121) (by norm_num)
theorem B1244477 : Blo 734326 1244477 := bbase (se 3 (by rfl) ⟨233339, by rfl⟩ : syracuseStep 1244477 = 466679) (by norm_num)
theorem B2489669 : Blo 734326 2489669 := bbase (se 4 (by rfl) ⟨233406, by rfl⟩ : syracuseStep 2489669 = 466813) (by norm_num)
theorem B2358629 : Blo 734326 2358629 := bbase (se 4 (by rfl) ⟨221121, by rfl⟩ : syracuseStep 2358629 = 442243) (by norm_num)
theorem B7077269 : Blo 734326 7077269 := bbase (se 6 (by rfl) ⟨165873, by rfl⟩ : syracuseStep 7077269 = 331747) (by norm_num)
theorem B1244605 : Blo 734326 1244605 := bbase (se 3 (by rfl) ⟨233363, by rfl⟩ : syracuseStep 1244605 = 466727) (by norm_num)
theorem B4259285 : Blo 734326 4259285 := bbase (se 7 (by rfl) ⟨49913, by rfl⟩ : syracuseStep 4259285 = 99827) (by norm_num)
theorem B1048069 : Blo 734326 1048069 := bbase (se 4 (by rfl) ⟨98256, by rfl⟩ : syracuseStep 1048069 = 196513) (by norm_num)
theorem B1244693 : Blo 734326 1244693 := bbase (se 6 (by rfl) ⟨29172, by rfl⟩ : syracuseStep 1244693 = 58345) (by norm_num)
theorem B1867333 : Blo 734326 1867333 := bbase (se 4 (by rfl) ⟨175062, by rfl⟩ : syracuseStep 1867333 = 350125) (by norm_num)
theorem B3145301 : Blo 734326 3145301 := bbase (se 8 (by rfl) ⟨18429, by rfl⟩ : syracuseStep 3145301 = 36859) (by norm_num)
theorem B2096741 : Blo 734326 2096741 := bbase (se 4 (by rfl) ⟨196569, by rfl⟩ : syracuseStep 2096741 = 393139) (by norm_num)
theorem B1244821 : Blo 734326 1244821 := bbase (se 6 (by rfl) ⟨29175, by rfl⟩ : syracuseStep 1244821 = 58351) (by norm_num)
theorem B786073 : Blo 734326 786073 := bbase (se 2 (by rfl) ⟨294777, by rfl⟩ : syracuseStep 786073 = 589555) (by norm_num)
theorem B1867445 : Blo 734326 1867445 := bbase (se 5 (by rfl) ⟨87536, by rfl⟩ : syracuseStep 1867445 = 175073) (by norm_num)
theorem B2981573 : Blo 734326 2981573 := bbase (se 4 (by rfl) ⟨279522, by rfl⟩ : syracuseStep 2981573 = 559045) (by norm_num)
theorem B1769165 : Blo 734326 1769165 := bbase (se 3 (by rfl) ⟨331718, by rfl⟩ : syracuseStep 1769165 = 663437) (by norm_num)
theorem B786133 : Blo 734326 786133 := bbase (se 7 (by rfl) ⟨9212, by rfl⟩ : syracuseStep 786133 = 18425) (by norm_num)
theorem B1244909 : Blo 734326 1244909 := bbase (se 3 (by rfl) ⟨233420, by rfl⟩ : syracuseStep 1244909 = 466841) (by norm_num)
theorem B2490101 : Blo 734326 2490101 := bbase (se 5 (by rfl) ⟨116723, by rfl⟩ : syracuseStep 2490101 = 233447) (by norm_num)
theorem B5603093 : Blo 734326 5603093 := bbase (se 6 (by rfl) ⟨131322, by rfl⟩ : syracuseStep 5603093 = 262645) (by norm_num)
theorem B1703717 : Blo 734326 1703717 := bbase (se 4 (by rfl) ⟨159723, by rfl⟩ : syracuseStep 1703717 = 319447) (by norm_num)
theorem B1048405 : Blo 734326 1048405 := bbase (se 9 (by rfl) ⟨3071, by rfl⟩ : syracuseStep 1048405 = 6143) (by norm_num)
theorem B1245037 : Blo 734326 1245037 := bbase (se 3 (by rfl) ⟨233444, by rfl⟩ : syracuseStep 1245037 = 466889) (by norm_num)
theorem B1867637 : Blo 734326 1867637 := bbase (se 5 (by rfl) ⟨87545, by rfl⟩ : syracuseStep 1867637 = 175091) (by norm_num)
theorem B1245125 : Blo 734326 1245125 := bbase (se 4 (by rfl) ⟨116730, by rfl⟩ : syracuseStep 1245125 = 233461) (by norm_num)
theorem B884693 : Blo 734326 884693 := bbase (se 7 (by rfl) ⟨10367, by rfl⟩ : syracuseStep 884693 = 20735) (by norm_num)
theorem B2490371 : Blo 734326 2490371 := bstep (se 1 (by rfl) ⟨1867778, by rfl⟩ : syracuseStep 2490371 = 3735557) B3735557
theorem B2097197 : Blo 734326 2097197 := bstep (se 3 (by rfl) ⟨393224, by rfl⟩ : syracuseStep 2097197 = 786449) B786449
theorem B1245233 : Blo 734326 1245233 := bstep (se 2 (by rfl) ⟨466962, by rfl⟩ : syracuseStep 1245233 = 933925) B933925
theorem B2097265 : Blo 734326 2097265 := bstep (se 2 (by rfl) ⟨786474, by rfl⟩ : syracuseStep 2097265 = 1572949) B1572949
theorem B1769617 : Blo 734326 1769617 := bstep (se 2 (by rfl) ⟨663606, by rfl⟩ : syracuseStep 1769617 = 1327213) B1327213
theorem B2130097 : Blo 734326 2130097 := bstep (se 2 (by rfl) ⟨798786, by rfl⟩ : syracuseStep 2130097 = 1597573) B1597573
theorem B1245361 : Blo 734326 1245361 := bstep (se 2 (by rfl) ⟨467010, by rfl⟩ : syracuseStep 1245361 = 934021) B934021
theorem B1245395 : Blo 734326 1245395 := bstep (se 1 (by rfl) ⟨934046, by rfl⟩ : syracuseStep 1245395 = 1868093) B1868093
theorem B2490641 : Blo 734326 2490641 := bstep (se 2 (by rfl) ⟨933990, by rfl⟩ : syracuseStep 2490641 = 1867981) B1867981
theorem B1179955 : Blo 734326 1179955 := bstep (se 1 (by rfl) ⟨884966, by rfl⟩ : syracuseStep 1179955 = 1769933) B1769933
theorem B1245523 : Blo 734326 1245523 := bstep (se 1 (by rfl) ⟨934142, by rfl⟩ : syracuseStep 1245523 = 1868285) B1868285
theorem B1180001 : Blo 734326 1180001 := bstep (se 2 (by rfl) ⟨442500, by rfl⟩ : syracuseStep 1180001 = 885001) B885001
theorem B2097539 : Blo 734326 2097539 := bstep (se 1 (by rfl) ⟨1573154, by rfl⟩ : syracuseStep 2097539 = 3146309) B3146309
theorem B1048963 : Blo 734326 1048963 := bstep (se 1 (by rfl) ⟨786722, by rfl⟩ : syracuseStep 1048963 = 1573445) B1573445
theorem B2425265 : Blo 734326 2425265 := bstep (se 2 (by rfl) ⟨909474, by rfl⟩ : syracuseStep 2425265 = 1818949) B1818949
theorem B2654669 : Blo 734326 2654669 := bstep (se 3 (by rfl) ⟨497750, by rfl⟩ : syracuseStep 2654669 = 995501) B995501
theorem B1245665 : Blo 734326 1245665 := bstep (se 2 (by rfl) ⟨467124, by rfl⟩ : syracuseStep 1245665 = 934249) B934249
theorem B1868305 : Blo 734326 1868305 := bstep (se 2 (by rfl) ⟨700614, by rfl⟩ : syracuseStep 1868305 = 1401229) B1401229
theorem B4719181 : Blo 734326 4719181 := bstep (se 3 (by rfl) ⟨884846, by rfl⟩ : syracuseStep 4719181 = 1769693) B1769693
theorem B1245793 : Blo 734326 1245793 := bstep (se 2 (by rfl) ⟨467172, by rfl⟩ : syracuseStep 1245793 = 934345) B934345
theorem B9437795 : Blo 734326 9437795 := bstep (se 1 (by rfl) ⟨7078346, by rfl⟩ : syracuseStep 9437795 = 14156693) B14156693
theorem B7078499 : Blo 734326 7078499 := bstep (se 1 (by rfl) ⟨5308874, by rfl⟩ : syracuseStep 7078499 = 10617749) B10617749
theorem B787043 : Blo 734326 787043 := bstep (se 1 (by rfl) ⟨590282, by rfl⟩ : syracuseStep 787043 = 1180565) B1180565
theorem B1245827 : Blo 734326 1245827 := bstep (se 1 (by rfl) ⟨934370, by rfl⟩ : syracuseStep 1245827 = 1868741) B1868741
theorem B3736205 : Blo 734326 3736205 := bstep (se 3 (by rfl) ⟨700538, by rfl⟩ : syracuseStep 3736205 = 1401077) B1401077
theorem B885539 : Blo 734326 885539 := bstep (se 1 (by rfl) ⟨664154, by rfl⟩ : syracuseStep 885539 = 1328309) B1328309
theorem B1868579 : Blo 734326 1868579 := bstep (se 1 (by rfl) ⟨1401434, by rfl⟩ : syracuseStep 1868579 = 2802869) B2802869
theorem B2491181 : Blo 734326 2491181 := bstep (se 3 (by rfl) ⟨467096, by rfl⟩ : syracuseStep 2491181 = 934193) B934193
theorem B1049441 : Blo 734326 1049441 := bstep (se 2 (by rfl) ⟨393540, by rfl⟩ : syracuseStep 1049441 = 787081) B787081
theorem B2491235 : Blo 734326 2491235 := bstep (se 1 (by rfl) ⟨1868426, by rfl⟩ : syracuseStep 2491235 = 3736853) B3736853
theorem B2360269 : Blo 734326 2360269 := bstep (se 3 (by rfl) ⟨442550, by rfl⟩ : syracuseStep 2360269 = 885101) B885101
theorem B1049555 : Blo 734326 1049555 := bstep (se 1 (by rfl) ⟨787166, by rfl⟩ : syracuseStep 1049555 = 1574333) B1574333
theorem B1868771 : Blo 734326 1868771 := bstep (se 1 (by rfl) ⟨1401578, by rfl⟩ : syracuseStep 1868771 = 2803157) B2803157
theorem B1213427 : Blo 734326 1213427 := bstep (se 1 (by rfl) ⟨910070, by rfl⟩ : syracuseStep 1213427 = 1820141) B1820141
theorem B1180673 : Blo 734326 1180673 := bstep (se 2 (by rfl) ⟨442752, by rfl⟩ : syracuseStep 1180673 = 885505) B885505
theorem B1049635 : Blo 734326 1049635 := bstep (se 1 (by rfl) ⟨787226, by rfl⟩ : syracuseStep 1049635 = 1574453) B1574453
theorem B2589763 : Blo 734326 2589763 := bstep (se 1 (by rfl) ⟨1942322, by rfl⟩ : syracuseStep 2589763 = 3884645) B3884645
theorem B2393201 : Blo 734326 2393201 := bstep (se 2 (by rfl) ⟨897450, by rfl⟩ : syracuseStep 2393201 = 1794901) B1794901
theorem B2491505 : Blo 734326 2491505 := bstep (se 2 (by rfl) ⟨934314, by rfl⟩ : syracuseStep 2491505 = 1868629) B1868629
theorem B2131121 : Blo 734326 2131121 := bstep (se 2 (by rfl) ⟨799170, by rfl⟩ : syracuseStep 2131121 = 1598341) B1598341
theorem B3146957 : Blo 734326 3146957 := bstep (se 3 (by rfl) ⟨590054, by rfl⟩ : syracuseStep 3146957 = 1180109) B1180109
theorem B2098381 : Blo 734326 2098381 := bstep (se 3 (by rfl) ⟨393446, by rfl⟩ : syracuseStep 2098381 = 786893) B786893
theorem B2098541 : Blo 734326 2098541 := bstep (se 3 (by rfl) ⟨393476, by rfl⟩ : syracuseStep 2098541 = 786953) B786953
theorem B1181185 : Blo 734326 1181185 := bstep (se 2 (by rfl) ⟨442944, by rfl⟩ : syracuseStep 1181185 = 885889) B885889
theorem B3147299 : Blo 734326 3147299 := bstep (se 1 (by rfl) ⟨2360474, by rfl⟩ : syracuseStep 3147299 = 4720949) B4720949
theorem B2098723 : Blo 734326 2098723 := bstep (se 1 (by rfl) ⟨1574042, by rfl⟩ : syracuseStep 2098723 = 3148085) B3148085
theorem B1574435 : Blo 734326 1574435 := bstep (se 1 (by rfl) ⟨1180826, by rfl⟩ : syracuseStep 1574435 = 2361653) B2361653
theorem B1050193 : Blo 734326 1050193 := bstep (se 2 (by rfl) ⟨393822, by rfl⟩ : syracuseStep 1050193 = 787645) B787645
theorem B3147761 : Blo 734326 3147761 := bstep (se 2 (by rfl) ⟨1180410, by rfl⟩ : syracuseStep 3147761 = 2360821) B2360821
theorem B1050899 : Blo 734326 1050899 := bstep (se 1 (by rfl) ⟨788174, by rfl⟩ : syracuseStep 1050899 = 1576349) B1576349
theorem B1116595 : Blo 734326 1116595 := bstep (se 1 (by rfl) ⟨837446, by rfl⟩ : syracuseStep 1116595 = 1674893) B1674893
theorem B2362051 : Blo 734326 2362051 := bstep (se 1 (by rfl) ⟨1771538, by rfl⟩ : syracuseStep 2362051 = 3543077) B3543077
theorem B2362115 : Blo 734326 2362115 := bstep (se 1 (by rfl) ⟨1771586, by rfl⟩ : syracuseStep 2362115 = 3543173) B3543173
theorem B1575683 : Blo 734326 1575683 := bstep (se 1 (by rfl) ⟨1181762, by rfl⟩ : syracuseStep 1575683 = 2363525) B2363525
theorem B1182467 : Blo 734326 1182467 := bstep (se 1 (by rfl) ⟨886850, by rfl⟩ : syracuseStep 1182467 = 1773701) B1773701
theorem B2362193 : Blo 734326 2362193 := bstep (se 2 (by rfl) ⟨885822, by rfl⟩ : syracuseStep 2362193 = 1771645) B1771645
theorem B1182595 : Blo 734326 1182595 := bstep (se 1 (by rfl) ⟨886946, by rfl⟩ : syracuseStep 1182595 = 1773893) B1773893
theorem B2100113 : Blo 734326 2100113 := bstep (se 2 (by rfl) ⟨787542, by rfl⟩ : syracuseStep 2100113 = 1575085) B1575085
theorem B1576273 : Blo 734326 1576273 := bstep (se 2 (by rfl) ⟨591102, by rfl⟩ : syracuseStep 1576273 = 1182205) B1182205
theorem B5049989 : Blo 734326 5049989 := bstep (se 4 (by rfl) ⟨473436, by rfl⟩ : syracuseStep 5049989 = 946873) B946873
theorem B1117891 : Blo 734326 1117891 := bstep (se 1 (by rfl) ⟨838418, by rfl⟩ : syracuseStep 1117891 = 1676837) B1676837
theorem B2101069 : Blo 734326 2101069 := bstep (se 3 (by rfl) ⟨393950, by rfl⟩ : syracuseStep 2101069 = 787901) B787901
theorem B2789261 : Blo 734326 2789261 := bstep (se 3 (by rfl) ⟨522986, by rfl⟩ : syracuseStep 2789261 = 1045973) B1045973
theorem B1773539 : Blo 734326 1773539 := bstep (se 1 (by rfl) ⟨1330154, by rfl⟩ : syracuseStep 1773539 = 2660309) B2660309
theorem B2101297 : Blo 734326 2101297 := bstep (se 2 (by rfl) ⟨787986, by rfl⟩ : syracuseStep 2101297 = 1575973) B1575973
theorem B2101457 : Blo 734326 2101457 := bstep (se 2 (by rfl) ⟨788046, by rfl⟩ : syracuseStep 2101457 = 1576093) B1576093
theorem B5050673 : Blo 734326 5050673 := bstep (se 2 (by rfl) ⟨1894002, by rfl⟩ : syracuseStep 5050673 = 3788005) B3788005
theorem B2101571 : Blo 734326 2101571 := bstep (se 1 (by rfl) ⟨1576178, by rfl⟩ : syracuseStep 2101571 = 3152357) B3152357
theorem B14127473 : Blo 734326 14127473 := bstep (se 2 (by rfl) ⟨5297802, by rfl⟩ : syracuseStep 14127473 = 10595605) B10595605
theorem B5739121 : Blo 734326 5739121 := bstep (se 2 (by rfl) ⟨2152170, by rfl⟩ : syracuseStep 5739121 = 4304341) B4304341
theorem B2790065 : Blo 734326 2790065 := bstep (se 2 (by rfl) ⟨1046274, by rfl⟩ : syracuseStep 2790065 = 2092549) B2092549
theorem B2364113 : Blo 734326 2364113 := bstep (se 2 (by rfl) ⟨886542, by rfl⟩ : syracuseStep 2364113 = 1773085) B1773085
theorem B4723525 : Blo 734326 4723525 := bstep (se 4 (by rfl) ⟨442830, by rfl⟩ : syracuseStep 4723525 = 885661) B885661
theorem B2233261 : Blo 734326 2233261 := bstep (se 3 (by rfl) ⟨418736, by rfl⟩ : syracuseStep 2233261 = 837473) B837473
theorem B2987021 : Blo 734326 2987021 := bstep (se 3 (by rfl) ⟨560066, by rfl⟩ : syracuseStep 2987021 = 1120133) B1120133
theorem B1676323 : Blo 734326 1676323 := bstep (se 1 (by rfl) ⟨1257242, by rfl⟩ : syracuseStep 1676323 = 2514485) B2514485
theorem B1676497 : Blo 734326 1676497 := bstep (se 2 (by rfl) ⟨628686, by rfl⟩ : syracuseStep 1676497 = 1257373) B1257373
theorem B2364653 : Blo 734326 2364653 := bstep (se 3 (by rfl) ⟨443372, by rfl⟩ : syracuseStep 2364653 = 886745) B886745
theorem B2790733 : Blo 734326 2790733 := bstep (se 3 (by rfl) ⟨523262, by rfl⟩ : syracuseStep 2790733 = 1046525) B1046525
theorem B3151331 : Blo 734326 3151331 := bstep (se 1 (by rfl) ⟨2363498, by rfl⟩ : syracuseStep 3151331 = 4726997) B4726997
theorem B4200133 : Blo 734326 4200133 := bstep (se 4 (by rfl) ⟨393762, by rfl⟩ : syracuseStep 4200133 = 787525) B787525
theorem B7870193 : Blo 734326 7870193 := bstep (se 2 (by rfl) ⟨2951322, by rfl⟩ : syracuseStep 7870193 = 5902645) B5902645
theorem B14718773 : Blo 734326 14718773 := bstep (se 5 (by rfl) ⟨689942, by rfl⟩ : syracuseStep 14718773 = 1379885) B1379885
theorem B2791523 : Blo 734326 2791523 := bstep (se 1 (by rfl) ⟨2093642, by rfl⟩ : syracuseStep 2791523 = 4187285) B4187285
theorem B2792177 : Blo 734326 2792177 := bstep (se 2 (by rfl) ⟨1047066, by rfl⟩ : syracuseStep 2792177 = 2094133) B2094133
theorem B4725539 : Blo 734326 4725539 := bstep (se 1 (by rfl) ⟨3544154, by rfl⟩ : syracuseStep 4725539 = 7088309) B7088309
theorem B826195 : Blo 734326 826195 := bstep (se 1 (by rfl) ⟨619646, by rfl⟩ : syracuseStep 826195 = 1239293) B1239293
theorem B826339 : Blo 734326 826339 := bstep (se 1 (by rfl) ⟨619754, by rfl⟩ : syracuseStep 826339 = 1239509) B1239509
theorem B826483 : Blo 734326 826483 := bstep (se 1 (by rfl) ⟨619862, by rfl⟩ : syracuseStep 826483 = 1239725) B1239725
theorem B3349745 : Blo 734326 3349745 := bstep (se 2 (by rfl) ⟨1256154, by rfl⟩ : syracuseStep 3349745 = 2512309) B2512309
theorem B826627 : Blo 734326 826627 := bstep (se 1 (by rfl) ⟨619970, by rfl⟩ : syracuseStep 826627 = 1239941) B1239941
theorem B826771 : Blo 734326 826771 := bstep (se 1 (by rfl) ⟨620078, by rfl⟩ : syracuseStep 826771 = 1240157) B1240157
theorem B826915 : Blo 734326 826915 := bstep (se 1 (by rfl) ⟨620186, by rfl⟩ : syracuseStep 826915 = 1240373) B1240373
theorem B1023619 : Blo 734326 1023619 := bstep (se 1 (by rfl) ⟨767714, by rfl⟩ : syracuseStep 1023619 = 1535429) B1535429
theorem B4202117 : Blo 734326 4202117 := bstep (se 4 (by rfl) ⟨393948, by rfl⟩ : syracuseStep 4202117 = 787897) B787897
theorem B827059 : Blo 734326 827059 := bstep (se 1 (by rfl) ⟨620294, by rfl⟩ : syracuseStep 827059 = 1240589) B1240589
theorem B1417009 : Blo 734326 1417009 := bstep (se 2 (by rfl) ⟨531378, by rfl⟩ : syracuseStep 1417009 = 1062757) B1062757
theorem B827203 : Blo 734326 827203 := bstep (se 1 (by rfl) ⟨620402, by rfl⟩ : syracuseStep 827203 = 1240805) B1240805
theorem B1515395 : Blo 734326 1515395 := bstep (se 1 (by rfl) ⟨1136546, by rfl⟩ : syracuseStep 1515395 = 2273093) B2273093
theorem B827347 : Blo 734326 827347 := bstep (se 1 (by rfl) ⟨620510, by rfl⟩ : syracuseStep 827347 = 1241021) B1241021
theorem B1122275 : Blo 734326 1122275 := bstep (se 1 (by rfl) ⟨841706, by rfl⟩ : syracuseStep 1122275 = 1683413) B1683413
theorem B827491 : Blo 734326 827491 := bstep (se 1 (by rfl) ⟨620618, by rfl⟩ : syracuseStep 827491 = 1241237) B1241237
theorem B2793635 : Blo 734326 2793635 := bstep (se 1 (by rfl) ⟨2095226, by rfl⟩ : syracuseStep 2793635 = 4190453) B4190453
theorem B2793649 : Blo 734326 2793649 := bstep (se 2 (by rfl) ⟨1047618, by rfl⟩ : syracuseStep 2793649 = 2095237) B2095237
theorem B827635 : Blo 734326 827635 := bstep (se 1 (by rfl) ⟨620726, by rfl⟩ : syracuseStep 827635 = 1241453) B1241453
theorem B827779 : Blo 734326 827779 := bstep (se 1 (by rfl) ⟨620834, by rfl⟩ : syracuseStep 827779 = 1241669) B1241669
theorem B827923 : Blo 734326 827923 := bstep (se 1 (by rfl) ⟨620942, by rfl⟩ : syracuseStep 827923 = 1241885) B1241885
theorem B828067 : Blo 734326 828067 := bstep (se 1 (by rfl) ⟨621050, by rfl⟩ : syracuseStep 828067 = 1242101) B1242101
theorem B828211 : Blo 734326 828211 := bstep (se 1 (by rfl) ⟨621158, by rfl⟩ : syracuseStep 828211 = 1242317) B1242317
theorem B828355 : Blo 734326 828355 := bstep (se 1 (by rfl) ⟨621266, by rfl⟩ : syracuseStep 828355 = 1242533) B1242533
theorem B828499 : Blo 734326 828499 := bstep (se 1 (by rfl) ⟨621374, by rfl⟩ : syracuseStep 828499 = 1242749) B1242749
theorem B828643 : Blo 734326 828643 := bstep (se 1 (by rfl) ⟨621482, by rfl⟩ : syracuseStep 828643 = 1242965) B1242965
theorem B5317987 : Blo 734326 5317987 := bstep (se 1 (by rfl) ⟨3988490, by rfl⟩ : syracuseStep 5317987 = 7976981) B7976981
theorem B828787 : Blo 734326 828787 := bstep (se 1 (by rfl) ⟨621590, by rfl⟩ : syracuseStep 828787 = 1243181) B1243181
theorem B959891 : Blo 734326 959891 := bstep (se 1 (by rfl) ⟨719918, by rfl⟩ : syracuseStep 959891 = 1439837) B1439837
theorem B828931 : Blo 734326 828931 := bstep (se 1 (by rfl) ⟨621698, by rfl⟩ : syracuseStep 828931 = 1243397) B1243397
theorem B2991629 : Blo 734326 2991629 := bstep (se 3 (by rfl) ⟨560930, by rfl⟩ : syracuseStep 2991629 = 1121861) B1121861
theorem B2795107 : Blo 734326 2795107 := bstep (se 1 (by rfl) ⟨2096330, by rfl⟩ : syracuseStep 2795107 = 4192661) B4192661
theorem B829075 : Blo 734326 829075 := bstep (se 1 (by rfl) ⟨621806, by rfl⟩ : syracuseStep 829075 = 1243613) B1243613
theorem B1418993 : Blo 734326 1418993 := bstep (se 2 (by rfl) ⟨532122, by rfl⟩ : syracuseStep 1418993 = 1064245) B1064245
theorem B2238211 : Blo 734326 2238211 := bstep (se 1 (by rfl) ⟨1678658, by rfl⟩ : syracuseStep 2238211 = 3357317) B3357317
theorem B829219 : Blo 734326 829219 := bstep (se 1 (by rfl) ⟨621914, by rfl⟩ : syracuseStep 829219 = 1243829) B1243829
theorem B2795363 : Blo 734326 2795363 := bstep (se 1 (by rfl) ⟨2096522, by rfl⟩ : syracuseStep 2795363 = 4193045) B4193045
theorem B4728689 : Blo 734326 4728689 := bstep (se 2 (by rfl) ⟨1773258, by rfl⟩ : syracuseStep 4728689 = 3546517) B3546517
theorem B4728739 : Blo 734326 4728739 := bstep (se 1 (by rfl) ⟨3546554, by rfl⟩ : syracuseStep 4728739 = 7093109) B7093109
theorem B829363 : Blo 734326 829363 := bstep (se 1 (by rfl) ⟨622022, by rfl⟩ : syracuseStep 829363 = 1244045) B1244045
theorem B6301637 : Blo 734326 6301637 := bstep (se 4 (by rfl) ⟨590778, by rfl⟩ : syracuseStep 6301637 = 1181557) B1181557
theorem B829507 : Blo 734326 829507 := bstep (se 1 (by rfl) ⟨622130, by rfl⟩ : syracuseStep 829507 = 1244261) B1244261
theorem B4466765 : Blo 734326 4466765 := bstep (se 3 (by rfl) ⟨837518, by rfl⟩ : syracuseStep 4466765 = 1675037) B1675037
theorem B1681507 : Blo 734326 1681507 := bstep (se 1 (by rfl) ⟨1261130, by rfl⟩ : syracuseStep 1681507 = 2522261) B2522261
theorem B829651 : Blo 734326 829651 := bstep (se 1 (by rfl) ⟨622238, by rfl⟩ : syracuseStep 829651 = 1244477) B1244477
theorem B829795 : Blo 734326 829795 := bstep (se 1 (by rfl) ⟨622346, by rfl⟩ : syracuseStep 829795 = 1244693) B1244693
theorem B829939 : Blo 734326 829939 := bstep (se 1 (by rfl) ⟨622454, by rfl⟩ : syracuseStep 829939 = 1244909) B1244909
theorem B830083 : Blo 734326 830083 := bstep (se 1 (by rfl) ⟨622562, by rfl⟩ : syracuseStep 830083 = 1245125) B1245125
theorem B5745421 : Blo 734326 5745421 := bstep (se 3 (by rfl) ⟨1077266, by rfl⟩ : syracuseStep 5745421 = 2154533) B2154533
theorem B830227 : Blo 734326 830227 := bstep (se 1 (by rfl) ⟨622670, by rfl⟩ : syracuseStep 830227 = 1245341) B1245341
theorem B5581709 : Blo 734326 5581709 := bstep (se 3 (by rfl) ⟨1046570, by rfl⟩ : syracuseStep 5581709 = 2093141) B2093141
theorem B830371 : Blo 734326 830371 := bstep (se 1 (by rfl) ⟨622778, by rfl⟩ : syracuseStep 830371 = 1245557) B1245557
theorem B830515 : Blo 734326 830515 := bstep (se 1 (by rfl) ⟨622886, by rfl⟩ : syracuseStep 830515 = 1245773) B1245773
theorem B1256593 : Blo 734326 1256593 := bstep (se 2 (by rfl) ⟨471222, by rfl⟩ : syracuseStep 1256593 = 942445) B942445
theorem B1617059 : Blo 734326 1617059 := bstep (se 1 (by rfl) ⟨1212794, by rfl⟩ : syracuseStep 1617059 = 2425589) B2425589
theorem B896243 : Blo 734326 896243 := bstep (se 1 (by rfl) ⟨672182, by rfl⟩ : syracuseStep 896243 = 1344365) B1344365
theorem B1420625 : Blo 734326 1420625 := bstep (se 2 (by rfl) ⟨532734, by rfl⟩ : syracuseStep 1420625 = 1065469) B1065469
theorem B2797325 : Blo 734326 2797325 := bstep (se 3 (by rfl) ⟨524498, by rfl⟩ : syracuseStep 2797325 = 1048997) B1048997
theorem B995107 : Blo 734326 995107 := bstep (se 1 (by rfl) ⟨746330, by rfl⟩ : syracuseStep 995107 = 1492661) B1492661
theorem B9416675 : Blo 734326 9416675 := bstep (se 1 (by rfl) ⟨7062506, by rfl⟩ : syracuseStep 9416675 = 14125013) B14125013
theorem B929875 : Blo 734326 929875 := bstep (se 1 (by rfl) ⟨697406, by rfl⟩ : syracuseStep 929875 = 1394813) B1394813
theorem B8400995 : Blo 734326 8400995 := bstep (se 1 (by rfl) ⟨6300746, by rfl⟩ : syracuseStep 8400995 = 12601493) B12601493
theorem B929971 : Blo 734326 929971 := bstep (se 1 (by rfl) ⟨697478, by rfl⟩ : syracuseStep 929971 = 1394957) B1394957
theorem B995555 : Blo 734326 995555 := bstep (se 1 (by rfl) ⟨746666, by rfl⟩ : syracuseStep 995555 = 1493333) B1493333
theorem B930467 : Blo 734326 930467 := bstep (se 1 (by rfl) ⟨697850, by rfl⟩ : syracuseStep 930467 = 1395701) B1395701
theorem B1815313 : Blo 734326 1815313 := bstep (se 2 (by rfl) ⟨680742, by rfl⟩ : syracuseStep 1815313 = 1361485) B1361485
theorem B2241325 : Blo 734326 2241325 := bstep (se 3 (by rfl) ⟨420248, by rfl⟩ : syracuseStep 2241325 = 840497) B840497
theorem B1258481 : Blo 734326 1258481 := bstep (se 2 (by rfl) ⟨471930, by rfl⟩ : syracuseStep 1258481 = 943861) B943861
theorem B734339 : Blo 734326 734339 := bstep (se 1 (by rfl) ⟨550754, by rfl⟩ : syracuseStep 734339 = 1101509) B1101509
theorem B734355 : Blo 734326 734355 := bstep (se 1 (by rfl) ⟨550766, by rfl⟩ : syracuseStep 734355 = 1101533) B1101533
theorem B734371 : Blo 734326 734371 := bstep (se 1 (by rfl) ⟨550778, by rfl⟩ : syracuseStep 734371 = 1101557) B1101557
theorem B734387 : Blo 734326 734387 := bstep (se 1 (by rfl) ⟨550790, by rfl⟩ : syracuseStep 734387 = 1101581) B1101581
theorem B734403 : Blo 734326 734403 := bstep (se 1 (by rfl) ⟨550802, by rfl⟩ : syracuseStep 734403 = 1101605) B1101605
theorem B734419 : Blo 734326 734419 := bstep (se 1 (by rfl) ⟨550814, by rfl⟩ : syracuseStep 734419 = 1101629) B1101629
theorem B734435 : Blo 734326 734435 := bstep (se 1 (by rfl) ⟨550826, by rfl⟩ : syracuseStep 734435 = 1101653) B1101653
theorem B10073315 : Blo 734326 10073315 := bstep (se 1 (by rfl) ⟨7554986, by rfl⟩ : syracuseStep 10073315 = 15109973) B15109973
theorem B734451 : Blo 734326 734451 := bstep (se 1 (by rfl) ⟨550838, by rfl⟩ : syracuseStep 734451 = 1101677) B1101677
theorem B734467 : Blo 734326 734467 := bstep (se 1 (by rfl) ⟨550850, by rfl⟩ : syracuseStep 734467 = 1101701) B1101701
theorem B734483 : Blo 734326 734483 := bstep (se 1 (by rfl) ⟨550862, by rfl⟩ : syracuseStep 734483 = 1101725) B1101725
theorem B734499 : Blo 734326 734499 := bstep (se 1 (by rfl) ⟨550874, by rfl⟩ : syracuseStep 734499 = 1101749) B1101749
theorem B734515 : Blo 734326 734515 := bstep (se 1 (by rfl) ⟨550886, by rfl⟩ : syracuseStep 734515 = 1101773) B1101773
theorem B734531 : Blo 734326 734531 := bstep (se 1 (by rfl) ⟨550898, by rfl⟩ : syracuseStep 734531 = 1101797) B1101797
theorem B734547 : Blo 734326 734547 := bstep (se 1 (by rfl) ⟨550910, by rfl⟩ : syracuseStep 734547 = 1101821) B1101821
theorem B734563 : Blo 734326 734563 := bstep (se 1 (by rfl) ⟨550922, by rfl⟩ : syracuseStep 734563 = 1101845) B1101845
theorem B931171 : Blo 734326 931171 := bstep (se 1 (by rfl) ⟨698378, by rfl⟩ : syracuseStep 931171 = 1396757) B1396757
theorem B734579 : Blo 734326 734579 := bstep (se 1 (by rfl) ⟨550934, by rfl⟩ : syracuseStep 734579 = 1101869) B1101869
theorem B734595 : Blo 734326 734595 := bstep (se 1 (by rfl) ⟨550946, by rfl⟩ : syracuseStep 734595 = 1101893) B1101893
theorem B734611 : Blo 734326 734611 := bstep (se 1 (by rfl) ⟨550958, by rfl⟩ : syracuseStep 734611 = 1101917) B1101917
theorem B734627 : Blo 734326 734627 := bstep (se 1 (by rfl) ⟨550970, by rfl⟩ : syracuseStep 734627 = 1101941) B1101941
theorem B734643 : Blo 734326 734643 := bstep (se 1 (by rfl) ⟨550982, by rfl⟩ : syracuseStep 734643 = 1101965) B1101965
theorem B734659 : Blo 734326 734659 := bstep (se 1 (by rfl) ⟨550994, by rfl⟩ : syracuseStep 734659 = 1101989) B1101989
theorem B931267 : Blo 734326 931267 := bstep (se 1 (by rfl) ⟨698450, by rfl⟩ : syracuseStep 931267 = 1396901) B1396901
theorem B734675 : Blo 734326 734675 := bstep (se 1 (by rfl) ⟨551006, by rfl⟩ : syracuseStep 734675 = 1102013) B1102013
theorem B734691 : Blo 734326 734691 := bstep (se 1 (by rfl) ⟨551018, by rfl⟩ : syracuseStep 734691 = 1102037) B1102037
theorem B734707 : Blo 734326 734707 := bstep (se 1 (by rfl) ⟨551030, by rfl⟩ : syracuseStep 734707 = 1102061) B1102061
theorem B734723 : Blo 734326 734723 := bstep (se 1 (by rfl) ⟨551042, by rfl⟩ : syracuseStep 734723 = 1102085) B1102085
theorem B734739 : Blo 734326 734739 := bstep (se 1 (by rfl) ⟨551054, by rfl⟩ : syracuseStep 734739 = 1102109) B1102109
theorem B734755 : Blo 734326 734755 := bstep (se 1 (by rfl) ⟨551066, by rfl⟩ : syracuseStep 734755 = 1102133) B1102133
theorem B1652273 : Blo 734326 1652273 := bstep (se 2 (by rfl) ⟨619602, by rfl⟩ : syracuseStep 1652273 = 1239205) B1239205
theorem B734771 : Blo 734326 734771 := bstep (se 1 (by rfl) ⟨551078, by rfl⟩ : syracuseStep 734771 = 1102157) B1102157
theorem B1652291 : Blo 734326 1652291 := bstep (se 1 (by rfl) ⟨1239218, by rfl⟩ : syracuseStep 1652291 = 2478437) B2478437
theorem B734787 : Blo 734326 734787 := bstep (se 1 (by rfl) ⟨551090, by rfl⟩ : syracuseStep 734787 = 1102181) B1102181
theorem B734803 : Blo 734326 734803 := bstep (se 1 (by rfl) ⟨551102, by rfl⟩ : syracuseStep 734803 = 1102205) B1102205
theorem B734819 : Blo 734326 734819 := bstep (se 1 (by rfl) ⟨551114, by rfl⟩ : syracuseStep 734819 = 1102229) B1102229
theorem B8500835 : Blo 734326 8500835 := bstep (se 1 (by rfl) ⟨6375626, by rfl⟩ : syracuseStep 8500835 = 12751253) B12751253
theorem B734835 : Blo 734326 734835 := bstep (se 1 (by rfl) ⟨551126, by rfl⟩ : syracuseStep 734835 = 1102253) B1102253
theorem B734851 : Blo 734326 734851 := bstep (se 1 (by rfl) ⟨551138, by rfl⟩ : syracuseStep 734851 = 1102277) B1102277
theorem B734867 : Blo 734326 734867 := bstep (se 1 (by rfl) ⟨551150, by rfl⟩ : syracuseStep 734867 = 1102301) B1102301
theorem B734883 : Blo 734326 734883 := bstep (se 1 (by rfl) ⟨551162, by rfl⟩ : syracuseStep 734883 = 1102325) B1102325
theorem B734899 : Blo 734326 734899 := bstep (se 1 (by rfl) ⟨551174, by rfl⟩ : syracuseStep 734899 = 1102349) B1102349
theorem B734915 : Blo 734326 734915 := bstep (se 1 (by rfl) ⟨551186, by rfl⟩ : syracuseStep 734915 = 1102373) B1102373
theorem B734931 : Blo 734326 734931 := bstep (se 1 (by rfl) ⟨551198, by rfl⟩ : syracuseStep 734931 = 1102397) B1102397
theorem B734947 : Blo 734326 734947 := bstep (se 1 (by rfl) ⟨551210, by rfl⟩ : syracuseStep 734947 = 1102421) B1102421
theorem B5584625 : Blo 734326 5584625 := bstep (se 2 (by rfl) ⟨2094234, by rfl⟩ : syracuseStep 5584625 = 4188469) B4188469
theorem B734963 : Blo 734326 734963 := bstep (se 1 (by rfl) ⟨551222, by rfl⟩ : syracuseStep 734963 = 1102445) B1102445
theorem B734979 : Blo 734326 734979 := bstep (se 1 (by rfl) ⟨551234, by rfl⟩ : syracuseStep 734979 = 1102469) B1102469
theorem B734995 : Blo 734326 734995 := bstep (se 1 (by rfl) ⟨551246, by rfl⟩ : syracuseStep 734995 = 1102493) B1102493
theorem B735011 : Blo 734326 735011 := bstep (se 1 (by rfl) ⟨551258, by rfl⟩ : syracuseStep 735011 = 1102517) B1102517
theorem B735027 : Blo 734326 735027 := bstep (se 1 (by rfl) ⟨551270, by rfl⟩ : syracuseStep 735027 = 1102541) B1102541
theorem B735043 : Blo 734326 735043 := bstep (se 1 (by rfl) ⟨551282, by rfl⟩ : syracuseStep 735043 = 1102565) B1102565
theorem B1652561 : Blo 734326 1652561 := bstep (se 2 (by rfl) ⟨619710, by rfl⟩ : syracuseStep 1652561 = 1239421) B1239421
theorem B735059 : Blo 734326 735059 := bstep (se 1 (by rfl) ⟨551294, by rfl⟩ : syracuseStep 735059 = 1102589) B1102589
theorem B1652579 : Blo 734326 1652579 := bstep (se 1 (by rfl) ⟨1239434, by rfl⟩ : syracuseStep 1652579 = 2478869) B2478869
theorem B735075 : Blo 734326 735075 := bstep (se 1 (by rfl) ⟨551306, by rfl⟩ : syracuseStep 735075 = 1102613) B1102613
theorem B735091 : Blo 734326 735091 := bstep (se 1 (by rfl) ⟨551318, by rfl⟩ : syracuseStep 735091 = 1102637) B1102637
theorem B735107 : Blo 734326 735107 := bstep (se 1 (by rfl) ⟨551330, by rfl⟩ : syracuseStep 735107 = 1102661) B1102661
theorem B735123 : Blo 734326 735123 := bstep (se 1 (by rfl) ⟨551342, by rfl⟩ : syracuseStep 735123 = 1102685) B1102685
theorem B735139 : Blo 734326 735139 := bstep (se 1 (by rfl) ⟨551354, by rfl⟩ : syracuseStep 735139 = 1102709) B1102709
theorem B735155 : Blo 734326 735155 := bstep (se 1 (by rfl) ⟨551366, by rfl⟩ : syracuseStep 735155 = 1102733) B1102733
theorem B931763 : Blo 734326 931763 := bstep (se 1 (by rfl) ⟨698822, by rfl⟩ : syracuseStep 931763 = 1397645) B1397645
theorem B735171 : Blo 734326 735171 := bstep (se 1 (by rfl) ⟨551378, by rfl⟩ : syracuseStep 735171 = 1102757) B1102757
theorem B735187 : Blo 734326 735187 := bstep (se 1 (by rfl) ⟨551390, by rfl⟩ : syracuseStep 735187 = 1102781) B1102781
theorem B735203 : Blo 734326 735203 := bstep (se 1 (by rfl) ⟨551402, by rfl⟩ : syracuseStep 735203 = 1102805) B1102805
theorem B735219 : Blo 734326 735219 := bstep (se 1 (by rfl) ⟨551414, by rfl⟩ : syracuseStep 735219 = 1102829) B1102829
theorem B735235 : Blo 734326 735235 := bstep (se 1 (by rfl) ⟨551426, by rfl⟩ : syracuseStep 735235 = 1102853) B1102853
theorem B735251 : Blo 734326 735251 := bstep (se 1 (by rfl) ⟨551438, by rfl⟩ : syracuseStep 735251 = 1102877) B1102877
theorem B735267 : Blo 734326 735267 := bstep (se 1 (by rfl) ⟨551450, by rfl⟩ : syracuseStep 735267 = 1102901) B1102901
theorem B735283 : Blo 734326 735283 := bstep (se 1 (by rfl) ⟨551462, by rfl⟩ : syracuseStep 735283 = 1102925) B1102925
theorem B735299 : Blo 734326 735299 := bstep (se 1 (by rfl) ⟨551474, by rfl⟩ : syracuseStep 735299 = 1102949) B1102949
theorem B735315 : Blo 734326 735315 := bstep (se 1 (by rfl) ⟨551486, by rfl⟩ : syracuseStep 735315 = 1102973) B1102973
theorem B735331 : Blo 734326 735331 := bstep (se 1 (by rfl) ⟨551498, by rfl⟩ : syracuseStep 735331 = 1102997) B1102997
theorem B1652849 : Blo 734326 1652849 := bstep (se 2 (by rfl) ⟨619818, by rfl⟩ : syracuseStep 1652849 = 1239637) B1239637
theorem B735347 : Blo 734326 735347 := bstep (se 1 (by rfl) ⟨551510, by rfl⟩ : syracuseStep 735347 = 1103021) B1103021
theorem B1489027 : Blo 734326 1489027 := bstep (se 1 (by rfl) ⟨1116770, by rfl⟩ : syracuseStep 1489027 = 2233541) B2233541
theorem B1652867 : Blo 734326 1652867 := bstep (se 1 (by rfl) ⟨1239650, by rfl⟩ : syracuseStep 1652867 = 2479301) B2479301
theorem B735363 : Blo 734326 735363 := bstep (se 1 (by rfl) ⟨551522, by rfl⟩ : syracuseStep 735363 = 1103045) B1103045
theorem B735379 : Blo 734326 735379 := bstep (se 1 (by rfl) ⟨551534, by rfl⟩ : syracuseStep 735379 = 1103069) B1103069
theorem B735395 : Blo 734326 735395 := bstep (se 1 (by rfl) ⟨551546, by rfl⟩ : syracuseStep 735395 = 1103093) B1103093
theorem B735411 : Blo 734326 735411 := bstep (se 1 (by rfl) ⟨551558, by rfl⟩ : syracuseStep 735411 = 1103117) B1103117
theorem B735427 : Blo 734326 735427 := bstep (se 1 (by rfl) ⟨551570, by rfl⟩ : syracuseStep 735427 = 1103141) B1103141
theorem B735443 : Blo 734326 735443 := bstep (se 1 (by rfl) ⟨551582, by rfl⟩ : syracuseStep 735443 = 1103165) B1103165
theorem B735459 : Blo 734326 735459 := bstep (se 1 (by rfl) ⟨551594, by rfl⟩ : syracuseStep 735459 = 1103189) B1103189
theorem B735475 : Blo 734326 735475 := bstep (se 1 (by rfl) ⟨551606, by rfl⟩ : syracuseStep 735475 = 1103213) B1103213
theorem B735491 : Blo 734326 735491 := bstep (se 1 (by rfl) ⟨551618, by rfl⟩ : syracuseStep 735491 = 1103237) B1103237
theorem B735507 : Blo 734326 735507 := bstep (se 1 (by rfl) ⟨551630, by rfl⟩ : syracuseStep 735507 = 1103261) B1103261
theorem B735523 : Blo 734326 735523 := bstep (se 1 (by rfl) ⟨551642, by rfl⟩ : syracuseStep 735523 = 1103285) B1103285
theorem B735539 : Blo 734326 735539 := bstep (se 1 (by rfl) ⟨551654, by rfl⟩ : syracuseStep 735539 = 1103309) B1103309
theorem B735555 : Blo 734326 735555 := bstep (se 1 (by rfl) ⟨551666, by rfl⟩ : syracuseStep 735555 = 1103333) B1103333
theorem B2242883 : Blo 734326 2242883 := bstep (se 1 (by rfl) ⟨1682162, by rfl⟩ : syracuseStep 2242883 = 3364325) B3364325
theorem B735571 : Blo 734326 735571 := bstep (se 1 (by rfl) ⟨551678, by rfl⟩ : syracuseStep 735571 = 1103357) B1103357
theorem B735587 : Blo 734326 735587 := bstep (se 1 (by rfl) ⟨551690, by rfl⟩ : syracuseStep 735587 = 1103381) B1103381
theorem B1325425 : Blo 734326 1325425 := bstep (se 2 (by rfl) ⟨497034, by rfl⟩ : syracuseStep 1325425 = 994069) B994069
theorem B1194355 : Blo 734326 1194355 := bstep (se 1 (by rfl) ⟨895766, by rfl⟩ : syracuseStep 1194355 = 1791533) B1791533
theorem B735603 : Blo 734326 735603 := bstep (se 1 (by rfl) ⟨551702, by rfl⟩ : syracuseStep 735603 = 1103405) B1103405
theorem B735619 : Blo 734326 735619 := bstep (se 1 (by rfl) ⟨551714, by rfl⟩ : syracuseStep 735619 = 1103429) B1103429
theorem B1653137 : Blo 734326 1653137 := bstep (se 2 (by rfl) ⟨619926, by rfl⟩ : syracuseStep 1653137 = 1239853) B1239853
theorem B735635 : Blo 734326 735635 := bstep (se 1 (by rfl) ⟨551726, by rfl⟩ : syracuseStep 735635 = 1103453) B1103453
theorem B1653155 : Blo 734326 1653155 := bstep (se 1 (by rfl) ⟨1239866, by rfl⟩ : syracuseStep 1653155 = 2479733) B2479733
theorem B735651 : Blo 734326 735651 := bstep (se 1 (by rfl) ⟨551738, by rfl⟩ : syracuseStep 735651 = 1103477) B1103477
theorem B1325489 : Blo 734326 1325489 := bstep (se 2 (by rfl) ⟨497058, by rfl⟩ : syracuseStep 1325489 = 994117) B994117
theorem B735667 : Blo 734326 735667 := bstep (se 1 (by rfl) ⟨551750, by rfl⟩ : syracuseStep 735667 = 1103501) B1103501
theorem B735683 : Blo 734326 735683 := bstep (se 1 (by rfl) ⟨551762, by rfl⟩ : syracuseStep 735683 = 1103525) B1103525
theorem B735699 : Blo 734326 735699 := bstep (se 1 (by rfl) ⟨551774, by rfl⟩ : syracuseStep 735699 = 1103549) B1103549
theorem B735715 : Blo 734326 735715 := bstep (se 1 (by rfl) ⟨551786, by rfl⟩ : syracuseStep 735715 = 1103573) B1103573
theorem B735731 : Blo 734326 735731 := bstep (se 1 (by rfl) ⟨551798, by rfl⟩ : syracuseStep 735731 = 1103597) B1103597
theorem B735747 : Blo 734326 735747 := bstep (se 1 (by rfl) ⟨551810, by rfl⟩ : syracuseStep 735747 = 1103621) B1103621
theorem B735763 : Blo 734326 735763 := bstep (se 1 (by rfl) ⟨551822, by rfl⟩ : syracuseStep 735763 = 1103645) B1103645
theorem B735779 : Blo 734326 735779 := bstep (se 1 (by rfl) ⟨551834, by rfl⟩ : syracuseStep 735779 = 1103669) B1103669
theorem B735795 : Blo 734326 735795 := bstep (se 1 (by rfl) ⟨551846, by rfl⟩ : syracuseStep 735795 = 1103693) B1103693
theorem B735811 : Blo 734326 735811 := bstep (se 1 (by rfl) ⟨551858, by rfl⟩ : syracuseStep 735811 = 1103717) B1103717
theorem B735827 : Blo 734326 735827 := bstep (se 1 (by rfl) ⟨551870, by rfl⟩ : syracuseStep 735827 = 1103741) B1103741
theorem B735843 : Blo 734326 735843 := bstep (se 1 (by rfl) ⟨551882, by rfl⟩ : syracuseStep 735843 = 1103765) B1103765
theorem B2800241 : Blo 734326 2800241 := bstep (se 2 (by rfl) ⟨1050090, by rfl⟩ : syracuseStep 2800241 = 2100181) B2100181
theorem B735859 : Blo 734326 735859 := bstep (se 1 (by rfl) ⟨551894, by rfl⟩ : syracuseStep 735859 = 1103789) B1103789
theorem B932467 : Blo 734326 932467 := bstep (se 1 (by rfl) ⟨699350, by rfl⟩ : syracuseStep 932467 = 1398701) B1398701
theorem B735875 : Blo 734326 735875 := bstep (se 1 (by rfl) ⟨551906, by rfl⟩ : syracuseStep 735875 = 1103813) B1103813
theorem B735891 : Blo 734326 735891 := bstep (se 1 (by rfl) ⟨551918, by rfl⟩ : syracuseStep 735891 = 1103837) B1103837
theorem B735907 : Blo 734326 735907 := bstep (se 1 (by rfl) ⟨551930, by rfl⟩ : syracuseStep 735907 = 1103861) B1103861
theorem B1653425 : Blo 734326 1653425 := bstep (se 2 (by rfl) ⟨620034, by rfl⟩ : syracuseStep 1653425 = 1240069) B1240069
theorem B735923 : Blo 734326 735923 := bstep (se 1 (by rfl) ⟨551942, by rfl⟩ : syracuseStep 735923 = 1103885) B1103885
theorem B1653443 : Blo 734326 1653443 := bstep (se 1 (by rfl) ⟨1240082, by rfl⟩ : syracuseStep 1653443 = 2480165) B2480165
theorem B735939 : Blo 734326 735939 := bstep (se 1 (by rfl) ⟨551954, by rfl⟩ : syracuseStep 735939 = 1103909) B1103909
theorem B735955 : Blo 734326 735955 := bstep (se 1 (by rfl) ⟨551966, by rfl⟩ : syracuseStep 735955 = 1103933) B1103933
theorem B932563 : Blo 734326 932563 := bstep (se 1 (by rfl) ⟨699422, by rfl⟩ : syracuseStep 932563 = 1398845) B1398845
theorem B735971 : Blo 734326 735971 := bstep (se 1 (by rfl) ⟨551978, by rfl⟩ : syracuseStep 735971 = 1103957) B1103957
theorem B735987 : Blo 734326 735987 := bstep (se 1 (by rfl) ⟨551990, by rfl⟩ : syracuseStep 735987 = 1103981) B1103981
theorem B736003 : Blo 734326 736003 := bstep (se 1 (by rfl) ⟨552002, by rfl⟩ : syracuseStep 736003 = 1104005) B1104005
theorem B736019 : Blo 734326 736019 := bstep (se 1 (by rfl) ⟨552014, by rfl⟩ : syracuseStep 736019 = 1104029) B1104029
theorem B736035 : Blo 734326 736035 := bstep (se 1 (by rfl) ⟨552026, by rfl⟩ : syracuseStep 736035 = 1104053) B1104053
theorem B736051 : Blo 734326 736051 := bstep (se 1 (by rfl) ⟨552038, by rfl⟩ : syracuseStep 736051 = 1104077) B1104077
theorem B736067 : Blo 734326 736067 := bstep (se 1 (by rfl) ⟨552050, by rfl⟩ : syracuseStep 736067 = 1104101) B1104101
theorem B736083 : Blo 734326 736083 := bstep (se 1 (by rfl) ⟨552062, by rfl⟩ : syracuseStep 736083 = 1104125) B1104125
theorem B736099 : Blo 734326 736099 := bstep (se 1 (by rfl) ⟨552074, by rfl⟩ : syracuseStep 736099 = 1104149) B1104149
theorem B736115 : Blo 734326 736115 := bstep (se 1 (by rfl) ⟨552086, by rfl⟩ : syracuseStep 736115 = 1104173) B1104173
theorem B736131 : Blo 734326 736131 := bstep (se 1 (by rfl) ⟨552098, by rfl⟩ : syracuseStep 736131 = 1104197) B1104197
theorem B736147 : Blo 734326 736147 := bstep (se 1 (by rfl) ⟨552110, by rfl⟩ : syracuseStep 736147 = 1104221) B1104221
theorem B736163 : Blo 734326 736163 := bstep (se 1 (by rfl) ⟨552122, by rfl⟩ : syracuseStep 736163 = 1104245) B1104245
theorem B736179 : Blo 734326 736179 := bstep (se 1 (by rfl) ⟨552134, by rfl⟩ : syracuseStep 736179 = 1104269) B1104269
theorem B736195 : Blo 734326 736195 := bstep (se 1 (by rfl) ⟨552146, by rfl⟩ : syracuseStep 736195 = 1104293) B1104293
theorem B1653713 : Blo 734326 1653713 := bstep (se 2 (by rfl) ⟨620142, by rfl⟩ : syracuseStep 1653713 = 1240285) B1240285
theorem B736211 : Blo 734326 736211 := bstep (se 1 (by rfl) ⟨552158, by rfl⟩ : syracuseStep 736211 = 1104317) B1104317
theorem B1653731 : Blo 734326 1653731 := bstep (se 1 (by rfl) ⟨1240298, by rfl⟩ : syracuseStep 1653731 = 2480597) B2480597
theorem B736227 : Blo 734326 736227 := bstep (se 1 (by rfl) ⟨552170, by rfl⟩ : syracuseStep 736227 = 1104341) B1104341
theorem B736243 : Blo 734326 736243 := bstep (se 1 (by rfl) ⟨552182, by rfl⟩ : syracuseStep 736243 = 1104365) B1104365
theorem B736259 : Blo 734326 736259 := bstep (se 1 (by rfl) ⟨552194, by rfl⟩ : syracuseStep 736259 = 1104389) B1104389
theorem B7093261 : Blo 734326 7093261 := bstep (se 3 (by rfl) ⟨1329986, by rfl⟩ : syracuseStep 7093261 = 2659973) B2659973
theorem B736275 : Blo 734326 736275 := bstep (se 1 (by rfl) ⟨552206, by rfl⟩ : syracuseStep 736275 = 1104413) B1104413
theorem B736291 : Blo 734326 736291 := bstep (se 1 (by rfl) ⟨552218, by rfl⟩ : syracuseStep 736291 = 1104437) B1104437
theorem B736307 : Blo 734326 736307 := bstep (se 1 (by rfl) ⟨552230, by rfl⟩ : syracuseStep 736307 = 1104461) B1104461
theorem B736323 : Blo 734326 736323 := bstep (se 1 (by rfl) ⟨552242, by rfl⟩ : syracuseStep 736323 = 1104485) B1104485
theorem B736339 : Blo 734326 736339 := bstep (se 1 (by rfl) ⟨552254, by rfl⟩ : syracuseStep 736339 = 1104509) B1104509
theorem B736355 : Blo 734326 736355 := bstep (se 1 (by rfl) ⟨552266, by rfl⟩ : syracuseStep 736355 = 1104533) B1104533
theorem B736371 : Blo 734326 736371 := bstep (se 1 (by rfl) ⟨552278, by rfl⟩ : syracuseStep 736371 = 1104557) B1104557
theorem B736387 : Blo 734326 736387 := bstep (se 1 (by rfl) ⟨552290, by rfl⟩ : syracuseStep 736387 = 1104581) B1104581
theorem B736403 : Blo 734326 736403 := bstep (se 1 (by rfl) ⟨552302, by rfl⟩ : syracuseStep 736403 = 1104605) B1104605
theorem B736419 : Blo 734326 736419 := bstep (se 1 (by rfl) ⟨552314, by rfl⟩ : syracuseStep 736419 = 1104629) B1104629
theorem B736435 : Blo 734326 736435 := bstep (se 1 (by rfl) ⟨552326, by rfl⟩ : syracuseStep 736435 = 1104653) B1104653
theorem B736451 : Blo 734326 736451 := bstep (se 1 (by rfl) ⟨552338, by rfl⟩ : syracuseStep 736451 = 1104677) B1104677
theorem B933059 : Blo 734326 933059 := bstep (se 1 (by rfl) ⟨699794, by rfl⟩ : syracuseStep 933059 = 1399589) B1399589
theorem B736467 : Blo 734326 736467 := bstep (se 1 (by rfl) ⟨552350, by rfl⟩ : syracuseStep 736467 = 1104701) B1104701
theorem B736483 : Blo 734326 736483 := bstep (se 1 (by rfl) ⟨552362, by rfl⟩ : syracuseStep 736483 = 1104725) B1104725
theorem B3718385 : Blo 734326 3718385 := bstep (se 2 (by rfl) ⟨1394394, by rfl⟩ : syracuseStep 3718385 = 2788789) B2788789
theorem B1654001 : Blo 734326 1654001 := bstep (se 2 (by rfl) ⟨620250, by rfl⟩ : syracuseStep 1654001 = 1240501) B1240501
theorem B736499 : Blo 734326 736499 := bstep (se 1 (by rfl) ⟨552374, by rfl⟩ : syracuseStep 736499 = 1104749) B1104749
theorem B1654019 : Blo 734326 1654019 := bstep (se 1 (by rfl) ⟨1240514, by rfl⟩ : syracuseStep 1654019 = 2481029) B2481029
theorem B736515 : Blo 734326 736515 := bstep (se 1 (by rfl) ⟨552386, by rfl⟩ : syracuseStep 736515 = 1104773) B1104773
theorem B2243857 : Blo 734326 2243857 := bstep (se 2 (by rfl) ⟨841446, by rfl⟩ : syracuseStep 2243857 = 1682893) B1682893
theorem B736531 : Blo 734326 736531 := bstep (se 1 (by rfl) ⟨552398, by rfl⟩ : syracuseStep 736531 = 1104797) B1104797
theorem B736547 : Blo 734326 736547 := bstep (se 1 (by rfl) ⟨552410, by rfl⟩ : syracuseStep 736547 = 1104821) B1104821
theorem B736563 : Blo 734326 736563 := bstep (se 1 (by rfl) ⟨552422, by rfl⟩ : syracuseStep 736563 = 1104845) B1104845
theorem B736579 : Blo 734326 736579 := bstep (se 1 (by rfl) ⟨552434, by rfl⟩ : syracuseStep 736579 = 1104869) B1104869
theorem B736595 : Blo 734326 736595 := bstep (se 1 (by rfl) ⟨552446, by rfl⟩ : syracuseStep 736595 = 1104893) B1104893
theorem B736611 : Blo 734326 736611 := bstep (se 1 (by rfl) ⟨552458, by rfl⟩ : syracuseStep 736611 = 1104917) B1104917
theorem B736627 : Blo 734326 736627 := bstep (se 1 (by rfl) ⟨552470, by rfl⟩ : syracuseStep 736627 = 1104941) B1104941
theorem B736643 : Blo 734326 736643 := bstep (se 1 (by rfl) ⟨552482, by rfl⟩ : syracuseStep 736643 = 1104965) B1104965
theorem B736659 : Blo 734326 736659 := bstep (se 1 (by rfl) ⟨552494, by rfl⟩ : syracuseStep 736659 = 1104989) B1104989
theorem B736675 : Blo 734326 736675 := bstep (se 1 (by rfl) ⟨552506, by rfl⟩ : syracuseStep 736675 = 1105013) B1105013
theorem B736691 : Blo 734326 736691 := bstep (se 1 (by rfl) ⟨552518, by rfl⟩ : syracuseStep 736691 = 1105037) B1105037
theorem B736707 : Blo 734326 736707 := bstep (se 1 (by rfl) ⟨552530, by rfl⟩ : syracuseStep 736707 = 1105061) B1105061
theorem B736723 : Blo 734326 736723 := bstep (se 1 (by rfl) ⟨552542, by rfl⟩ : syracuseStep 736723 = 1105085) B1105085
theorem B736739 : Blo 734326 736739 := bstep (se 1 (by rfl) ⟨552554, by rfl⟩ : syracuseStep 736739 = 1105109) B1105109
theorem B736755 : Blo 734326 736755 := bstep (se 1 (by rfl) ⟨552566, by rfl⟩ : syracuseStep 736755 = 1105133) B1105133
theorem B736771 : Blo 734326 736771 := bstep (se 1 (by rfl) ⟨552578, by rfl⟩ : syracuseStep 736771 = 1105157) B1105157
theorem B1654289 : Blo 734326 1654289 := bstep (se 2 (by rfl) ⟨620358, by rfl⟩ : syracuseStep 1654289 = 1240717) B1240717
theorem B736787 : Blo 734326 736787 := bstep (se 1 (by rfl) ⟨552590, by rfl⟩ : syracuseStep 736787 = 1105181) B1105181
theorem B1654307 : Blo 734326 1654307 := bstep (se 1 (by rfl) ⟨1240730, by rfl⟩ : syracuseStep 1654307 = 2481461) B2481461
theorem B736803 : Blo 734326 736803 := bstep (se 1 (by rfl) ⟨552602, by rfl⟩ : syracuseStep 736803 = 1105205) B1105205
theorem B736819 : Blo 734326 736819 := bstep (se 1 (by rfl) ⟨552614, by rfl⟩ : syracuseStep 736819 = 1105229) B1105229
theorem B45432373 : Blo 734326 45432373 := bstep (se 5 (by rfl) ⟨2129642, by rfl⟩ : syracuseStep 45432373 = 4259285) B4259285
theorem B736835 : Blo 734326 736835 := bstep (se 1 (by rfl) ⟨552626, by rfl⟩ : syracuseStep 736835 = 1105253) B1105253
theorem B736851 : Blo 734326 736851 := bstep (se 1 (by rfl) ⟨552638, by rfl⟩ : syracuseStep 736851 = 1105277) B1105277
theorem B1064545 : Blo 734326 1064545 := bstep (se 2 (by rfl) ⟨399204, by rfl⟩ : syracuseStep 1064545 = 798409) B798409
theorem B736867 : Blo 734326 736867 := bstep (se 1 (by rfl) ⟨552650, by rfl⟩ : syracuseStep 736867 = 1105301) B1105301
theorem B736883 : Blo 734326 736883 := bstep (se 1 (by rfl) ⟨552662, by rfl⟩ : syracuseStep 736883 = 1105325) B1105325
theorem B736899 : Blo 734326 736899 := bstep (se 1 (by rfl) ⟨552674, by rfl⟩ : syracuseStep 736899 = 1105349) B1105349
theorem B736915 : Blo 734326 736915 := bstep (se 1 (by rfl) ⟨552686, by rfl⟩ : syracuseStep 736915 = 1105373) B1105373
theorem B736931 : Blo 734326 736931 := bstep (se 1 (by rfl) ⟨552698, by rfl⟩ : syracuseStep 736931 = 1105397) B1105397
theorem B736947 : Blo 734326 736947 := bstep (se 1 (by rfl) ⟨552710, by rfl⟩ : syracuseStep 736947 = 1105421) B1105421
theorem B736963 : Blo 734326 736963 := bstep (se 1 (by rfl) ⟨552722, by rfl⟩ : syracuseStep 736963 = 1105445) B1105445
theorem B736979 : Blo 734326 736979 := bstep (se 1 (by rfl) ⟨552734, by rfl⟩ : syracuseStep 736979 = 1105469) B1105469
theorem B736995 : Blo 734326 736995 := bstep (se 1 (by rfl) ⟨552746, by rfl⟩ : syracuseStep 736995 = 1105493) B1105493
theorem B737011 : Blo 734326 737011 := bstep (se 1 (by rfl) ⟨552758, by rfl⟩ : syracuseStep 737011 = 1105517) B1105517
theorem B737027 : Blo 734326 737027 := bstep (se 1 (by rfl) ⟨552770, by rfl⟩ : syracuseStep 737027 = 1105541) B1105541
theorem B737043 : Blo 734326 737043 := bstep (se 1 (by rfl) ⟨552782, by rfl⟩ : syracuseStep 737043 = 1105565) B1105565
theorem B737059 : Blo 734326 737059 := bstep (se 1 (by rfl) ⟨552794, by rfl⟩ : syracuseStep 737059 = 1105589) B1105589
theorem B1654577 : Blo 734326 1654577 := bstep (se 2 (by rfl) ⟨620466, by rfl⟩ : syracuseStep 1654577 = 1240933) B1240933
theorem B737075 : Blo 734326 737075 := bstep (se 1 (by rfl) ⟨552806, by rfl⟩ : syracuseStep 737075 = 1105613) B1105613
theorem B1654595 : Blo 734326 1654595 := bstep (se 1 (by rfl) ⟨1240946, by rfl⟩ : syracuseStep 1654595 = 2481893) B2481893
theorem B737091 : Blo 734326 737091 := bstep (se 1 (by rfl) ⟨552818, by rfl⟩ : syracuseStep 737091 = 1105637) B1105637
theorem B737107 : Blo 734326 737107 := bstep (se 1 (by rfl) ⟨552830, by rfl⟩ : syracuseStep 737107 = 1105661) B1105661
theorem B737123 : Blo 734326 737123 := bstep (se 1 (by rfl) ⟨552842, by rfl⟩ : syracuseStep 737123 = 1105685) B1105685
theorem B737139 : Blo 734326 737139 := bstep (se 1 (by rfl) ⟨552854, by rfl⟩ : syracuseStep 737139 = 1105709) B1105709
theorem B737155 : Blo 734326 737155 := bstep (se 1 (by rfl) ⟨552866, by rfl⟩ : syracuseStep 737155 = 1105733) B1105733
theorem B933763 : Blo 734326 933763 := bstep (se 1 (by rfl) ⟨700322, by rfl⟩ : syracuseStep 933763 = 1400645) B1400645
theorem B737171 : Blo 734326 737171 := bstep (se 1 (by rfl) ⟨552878, by rfl⟩ : syracuseStep 737171 = 1105757) B1105757
theorem B737187 : Blo 734326 737187 := bstep (se 1 (by rfl) ⟨552890, by rfl⟩ : syracuseStep 737187 = 1105781) B1105781
theorem B737203 : Blo 734326 737203 := bstep (se 1 (by rfl) ⟨552902, by rfl⟩ : syracuseStep 737203 = 1105805) B1105805
theorem B737219 : Blo 734326 737219 := bstep (se 1 (by rfl) ⟨552914, by rfl⟩ : syracuseStep 737219 = 1105829) B1105829
theorem B737235 : Blo 734326 737235 := bstep (se 1 (by rfl) ⟨552926, by rfl⟩ : syracuseStep 737235 = 1105853) B1105853
theorem B737251 : Blo 734326 737251 := bstep (se 1 (by rfl) ⟨552938, by rfl⟩ : syracuseStep 737251 = 1105877) B1105877
theorem B933859 : Blo 734326 933859 := bstep (se 1 (by rfl) ⟨700394, by rfl⟩ : syracuseStep 933859 = 1400789) B1400789
theorem B1294321 : Blo 734326 1294321 := bstep (se 2 (by rfl) ⟨485370, by rfl⟩ : syracuseStep 1294321 = 970741) B970741
theorem B737267 : Blo 734326 737267 := bstep (se 1 (by rfl) ⟨552950, by rfl⟩ : syracuseStep 737267 = 1105901) B1105901
theorem B737283 : Blo 734326 737283 := bstep (se 1 (by rfl) ⟨552962, by rfl⟩ : syracuseStep 737283 = 1105925) B1105925
theorem B9453581 : Blo 734326 9453581 := bstep (se 3 (by rfl) ⟨1772546, by rfl⟩ : syracuseStep 9453581 = 3545093) B3545093
theorem B737299 : Blo 734326 737299 := bstep (se 1 (by rfl) ⟨552974, by rfl⟩ : syracuseStep 737299 = 1105949) B1105949
theorem B737315 : Blo 734326 737315 := bstep (se 1 (by rfl) ⟨552986, by rfl⟩ : syracuseStep 737315 = 1105973) B1105973
theorem B2801699 : Blo 734326 2801699 := bstep (se 1 (by rfl) ⟨2101274, by rfl⟩ : syracuseStep 2801699 = 4202549) B4202549
theorem B737331 : Blo 734326 737331 := bstep (se 1 (by rfl) ⟨552998, by rfl⟩ : syracuseStep 737331 = 1105997) B1105997
theorem B737347 : Blo 734326 737347 := bstep (se 1 (by rfl) ⟨553010, by rfl⟩ : syracuseStep 737347 = 1106021) B1106021
theorem B1654865 : Blo 734326 1654865 := bstep (se 2 (by rfl) ⟨620574, by rfl⟩ : syracuseStep 1654865 = 1241149) B1241149
theorem B737363 : Blo 734326 737363 := bstep (se 1 (by rfl) ⟨553022, by rfl⟩ : syracuseStep 737363 = 1106045) B1106045
theorem B1654883 : Blo 734326 1654883 := bstep (se 1 (by rfl) ⟨1241162, by rfl⟩ : syracuseStep 1654883 = 2482325) B2482325
theorem B737379 : Blo 734326 737379 := bstep (se 1 (by rfl) ⟨553034, by rfl⟩ : syracuseStep 737379 = 1106069) B1106069
theorem B737395 : Blo 734326 737395 := bstep (se 1 (by rfl) ⟨553046, by rfl⟩ : syracuseStep 737395 = 1106093) B1106093
theorem B1261697 : Blo 734326 1261697 := bstep (se 2 (by rfl) ⟨473136, by rfl⟩ : syracuseStep 1261697 = 946273) B946273
theorem B737411 : Blo 734326 737411 := bstep (se 1 (by rfl) ⟨553058, by rfl⟩ : syracuseStep 737411 = 1106117) B1106117
theorem B737427 : Blo 734326 737427 := bstep (se 1 (by rfl) ⟨553070, by rfl⟩ : syracuseStep 737427 = 1106141) B1106141
theorem B737443 : Blo 734326 737443 := bstep (se 1 (by rfl) ⟨553082, by rfl⟩ : syracuseStep 737443 = 1106165) B1106165
theorem B737459 : Blo 734326 737459 := bstep (se 1 (by rfl) ⟨553094, by rfl⟩ : syracuseStep 737459 = 1106189) B1106189
theorem B737475 : Blo 734326 737475 := bstep (se 1 (by rfl) ⟨553106, by rfl⟩ : syracuseStep 737475 = 1106213) B1106213
theorem B737491 : Blo 734326 737491 := bstep (se 1 (by rfl) ⟨553118, by rfl⟩ : syracuseStep 737491 = 1106237) B1106237
theorem B737507 : Blo 734326 737507 := bstep (se 1 (by rfl) ⟨553130, by rfl⟩ : syracuseStep 737507 = 1106261) B1106261
theorem B737523 : Blo 734326 737523 := bstep (se 1 (by rfl) ⟨553142, by rfl⟩ : syracuseStep 737523 = 1106285) B1106285
theorem B737539 : Blo 734326 737539 := bstep (se 1 (by rfl) ⟨553154, by rfl⟩ : syracuseStep 737539 = 1106309) B1106309
theorem B737555 : Blo 734326 737555 := bstep (se 1 (by rfl) ⟨553166, by rfl⟩ : syracuseStep 737555 = 1106333) B1106333
theorem B737571 : Blo 734326 737571 := bstep (se 1 (by rfl) ⟨553178, by rfl⟩ : syracuseStep 737571 = 1106357) B1106357
theorem B4473137 : Blo 734326 4473137 := bstep (se 2 (by rfl) ⟨1677426, by rfl⟩ : syracuseStep 4473137 = 3354853) B3354853
theorem B737587 : Blo 734326 737587 := bstep (se 1 (by rfl) ⟨553190, by rfl⟩ : syracuseStep 737587 = 1106381) B1106381
theorem B737603 : Blo 734326 737603 := bstep (se 1 (by rfl) ⟨553202, by rfl⟩ : syracuseStep 737603 = 1106405) B1106405
theorem B737619 : Blo 734326 737619 := bstep (se 1 (by rfl) ⟨553214, by rfl⟩ : syracuseStep 737619 = 1106429) B1106429
theorem B737635 : Blo 734326 737635 := bstep (se 1 (by rfl) ⟨553226, by rfl⟩ : syracuseStep 737635 = 1106453) B1106453
theorem B1655153 : Blo 734326 1655153 := bstep (se 2 (by rfl) ⟨620682, by rfl⟩ : syracuseStep 1655153 = 1241365) B1241365
theorem B737651 : Blo 734326 737651 := bstep (se 1 (by rfl) ⟨553238, by rfl⟩ : syracuseStep 737651 = 1106477) B1106477
theorem B1655171 : Blo 734326 1655171 := bstep (se 1 (by rfl) ⟨1241378, by rfl⟩ : syracuseStep 1655171 = 2482757) B2482757
theorem B737667 : Blo 734326 737667 := bstep (se 1 (by rfl) ⟨553250, by rfl⟩ : syracuseStep 737667 = 1106501) B1106501
theorem B737683 : Blo 734326 737683 := bstep (se 1 (by rfl) ⟨553262, by rfl⟩ : syracuseStep 737683 = 1106525) B1106525
theorem B737699 : Blo 734326 737699 := bstep (se 1 (by rfl) ⟨553274, by rfl⟩ : syracuseStep 737699 = 1106549) B1106549
theorem B737715 : Blo 734326 737715 := bstep (se 1 (by rfl) ⟨553286, by rfl⟩ : syracuseStep 737715 = 1106573) B1106573
theorem B737731 : Blo 734326 737731 := bstep (se 1 (by rfl) ⟨553298, by rfl⟩ : syracuseStep 737731 = 1106597) B1106597
theorem B737747 : Blo 734326 737747 := bstep (se 1 (by rfl) ⟨553310, by rfl⟩ : syracuseStep 737747 = 1106621) B1106621
theorem B934355 : Blo 734326 934355 := bstep (se 1 (by rfl) ⟨700766, by rfl⟩ : syracuseStep 934355 = 1401533) B1401533
theorem B737763 : Blo 734326 737763 := bstep (se 1 (by rfl) ⟨553322, by rfl⟩ : syracuseStep 737763 = 1106645) B1106645
theorem B737779 : Blo 734326 737779 := bstep (se 1 (by rfl) ⟨553334, by rfl⟩ : syracuseStep 737779 = 1106669) B1106669
theorem B737795 : Blo 734326 737795 := bstep (se 1 (by rfl) ⟨553346, by rfl⟩ : syracuseStep 737795 = 1106693) B1106693
theorem B737811 : Blo 734326 737811 := bstep (se 1 (by rfl) ⟨553358, by rfl⟩ : syracuseStep 737811 = 1106717) B1106717
theorem B737827 : Blo 734326 737827 := bstep (se 1 (by rfl) ⟨553370, by rfl⟩ : syracuseStep 737827 = 1106741) B1106741
theorem B737843 : Blo 734326 737843 := bstep (se 1 (by rfl) ⟨553382, by rfl⟩ : syracuseStep 737843 = 1106765) B1106765
theorem B737859 : Blo 734326 737859 := bstep (se 1 (by rfl) ⟨553394, by rfl⟩ : syracuseStep 737859 = 1106789) B1106789
theorem B737875 : Blo 734326 737875 := bstep (se 1 (by rfl) ⟨553406, by rfl⟩ : syracuseStep 737875 = 1106813) B1106813
theorem B737891 : Blo 734326 737891 := bstep (se 1 (by rfl) ⟨553418, by rfl⟩ : syracuseStep 737891 = 1106837) B1106837
theorem B737907 : Blo 734326 737907 := bstep (se 1 (by rfl) ⟨553430, by rfl⟩ : syracuseStep 737907 = 1106861) B1106861
theorem B737923 : Blo 734326 737923 := bstep (se 1 (by rfl) ⟨553442, by rfl⟩ : syracuseStep 737923 = 1106885) B1106885
theorem B1655441 : Blo 734326 1655441 := bstep (se 2 (by rfl) ⟨620790, by rfl⟩ : syracuseStep 1655441 = 1241581) B1241581
theorem B737939 : Blo 734326 737939 := bstep (se 1 (by rfl) ⟨553454, by rfl⟩ : syracuseStep 737939 = 1106909) B1106909
theorem B3719843 : Blo 734326 3719843 := bstep (se 1 (by rfl) ⟨2789882, by rfl⟩ : syracuseStep 3719843 = 5579765) B5579765
theorem B1655459 : Blo 734326 1655459 := bstep (se 1 (by rfl) ⟨1241594, by rfl⟩ : syracuseStep 1655459 = 2483189) B2483189
theorem B737955 : Blo 734326 737955 := bstep (se 1 (by rfl) ⟨553466, by rfl⟩ : syracuseStep 737955 = 1106933) B1106933
theorem B737971 : Blo 734326 737971 := bstep (se 1 (by rfl) ⟨553478, by rfl⟩ : syracuseStep 737971 = 1106957) B1106957
theorem B737987 : Blo 734326 737987 := bstep (se 1 (by rfl) ⟨553490, by rfl⟩ : syracuseStep 737987 = 1106981) B1106981
theorem B738003 : Blo 734326 738003 := bstep (se 1 (by rfl) ⟨553502, by rfl⟩ : syracuseStep 738003 = 1107005) B1107005
theorem B738019 : Blo 734326 738019 := bstep (se 1 (by rfl) ⟨553514, by rfl⟩ : syracuseStep 738019 = 1107029) B1107029
theorem B738035 : Blo 734326 738035 := bstep (se 1 (by rfl) ⟨553526, by rfl⟩ : syracuseStep 738035 = 1107053) B1107053
theorem B1262339 : Blo 734326 1262339 := bstep (se 1 (by rfl) ⟨946754, by rfl⟩ : syracuseStep 1262339 = 1893509) B1893509
theorem B738051 : Blo 734326 738051 := bstep (se 1 (by rfl) ⟨553538, by rfl⟩ : syracuseStep 738051 = 1107077) B1107077
theorem B738067 : Blo 734326 738067 := bstep (se 1 (by rfl) ⟨553550, by rfl⟩ : syracuseStep 738067 = 1107101) B1107101
theorem B738083 : Blo 734326 738083 := bstep (se 1 (by rfl) ⟨553562, by rfl⟩ : syracuseStep 738083 = 1107125) B1107125
theorem B738099 : Blo 734326 738099 := bstep (se 1 (by rfl) ⟨553574, by rfl⟩ : syracuseStep 738099 = 1107149) B1107149
theorem B738115 : Blo 734326 738115 := bstep (se 1 (by rfl) ⟨553586, by rfl⟩ : syracuseStep 738115 = 1107173) B1107173
theorem B738131 : Blo 734326 738131 := bstep (se 1 (by rfl) ⟨553598, by rfl⟩ : syracuseStep 738131 = 1107197) B1107197
theorem B738147 : Blo 734326 738147 := bstep (se 1 (by rfl) ⟨553610, by rfl⟩ : syracuseStep 738147 = 1107221) B1107221
theorem B738163 : Blo 734326 738163 := bstep (se 1 (by rfl) ⟨553622, by rfl⟩ : syracuseStep 738163 = 1107245) B1107245
theorem B738179 : Blo 734326 738179 := bstep (se 1 (by rfl) ⟨553634, by rfl⟩ : syracuseStep 738179 = 1107269) B1107269
theorem B53855117 : Blo 734326 53855117 := bstep (se 3 (by rfl) ⟨10097834, by rfl⟩ : syracuseStep 53855117 = 20195669) B20195669
theorem B738195 : Blo 734326 738195 := bstep (se 1 (by rfl) ⟨553646, by rfl⟩ : syracuseStep 738195 = 1107293) B1107293
theorem B738211 : Blo 734326 738211 := bstep (se 1 (by rfl) ⟨553658, by rfl⟩ : syracuseStep 738211 = 1107317) B1107317
theorem B1655729 : Blo 734326 1655729 := bstep (se 2 (by rfl) ⟨620898, by rfl⟩ : syracuseStep 1655729 = 1241797) B1241797
theorem B738227 : Blo 734326 738227 := bstep (se 1 (by rfl) ⟨553670, by rfl⟩ : syracuseStep 738227 = 1107341) B1107341
theorem B1655747 : Blo 734326 1655747 := bstep (se 1 (by rfl) ⟨1241810, by rfl⟩ : syracuseStep 1655747 = 2483621) B2483621
theorem B738243 : Blo 734326 738243 := bstep (se 1 (by rfl) ⟨553682, by rfl⟩ : syracuseStep 738243 = 1107365) B1107365
theorem B738259 : Blo 734326 738259 := bstep (se 1 (by rfl) ⟨553694, by rfl⟩ : syracuseStep 738259 = 1107389) B1107389
theorem B738275 : Blo 734326 738275 := bstep (se 1 (by rfl) ⟨553706, by rfl⟩ : syracuseStep 738275 = 1107413) B1107413
theorem B1328113 : Blo 734326 1328113 := bstep (se 2 (by rfl) ⟨498042, by rfl⟩ : syracuseStep 1328113 = 996085) B996085
theorem B738291 : Blo 734326 738291 := bstep (se 1 (by rfl) ⟨553718, by rfl⟩ : syracuseStep 738291 = 1107437) B1107437
theorem B738307 : Blo 734326 738307 := bstep (se 1 (by rfl) ⟨553730, by rfl⟩ : syracuseStep 738307 = 1107461) B1107461
theorem B2802701 : Blo 734326 2802701 := bstep (se 3 (by rfl) ⟨525506, by rfl⟩ : syracuseStep 2802701 = 1051013) B1051013
theorem B738323 : Blo 734326 738323 := bstep (se 1 (by rfl) ⟨553742, by rfl⟩ : syracuseStep 738323 = 1107485) B1107485
theorem B1656017 : Blo 734326 1656017 := bstep (se 2 (by rfl) ⟨621006, by rfl⟩ : syracuseStep 1656017 = 1242013) B1242013
theorem B1656035 : Blo 734326 1656035 := bstep (se 1 (by rfl) ⟨1242026, by rfl⟩ : syracuseStep 1656035 = 2484053) B2484053
theorem B3720653 : Blo 734326 3720653 := bstep (se 3 (by rfl) ⟨697622, by rfl⟩ : syracuseStep 3720653 = 1395245) B1395245
theorem B1656305 : Blo 734326 1656305 := bstep (se 2 (by rfl) ⟨621114, by rfl⟩ : syracuseStep 1656305 = 1242229) B1242229
theorem B1656323 : Blo 734326 1656323 := bstep (se 1 (by rfl) ⟨1242242, by rfl⟩ : syracuseStep 1656323 = 2484485) B2484485
theorem B1394243 : Blo 734326 1394243 := bstep (se 1 (by rfl) ⟨1045682, by rfl⟩ : syracuseStep 1394243 = 2091365) B2091365
theorem B1590929 : Blo 734326 1590929 := bstep (se 2 (by rfl) ⟨596598, by rfl⟩ : syracuseStep 1590929 = 1193197) B1193197
theorem B4835057 : Blo 734326 4835057 := bstep (se 2 (by rfl) ⟨1813146, by rfl⟩ : syracuseStep 4835057 = 3626293) B3626293
theorem B1656593 : Blo 734326 1656593 := bstep (se 2 (by rfl) ⟨621222, by rfl⟩ : syracuseStep 1656593 = 1242445) B1242445
theorem B1656611 : Blo 734326 1656611 := bstep (se 1 (by rfl) ⟨1242458, by rfl⟩ : syracuseStep 1656611 = 2484917) B2484917
theorem B6801221 : Blo 734326 6801221 := bstep (se 4 (by rfl) ⟨637614, by rfl⟩ : syracuseStep 6801221 = 1275229) B1275229
theorem B1656881 : Blo 734326 1656881 := bstep (se 2 (by rfl) ⟨621330, by rfl⟩ : syracuseStep 1656881 = 1242661) B1242661
theorem B1656899 : Blo 734326 1656899 := bstep (se 1 (by rfl) ⟨1242674, by rfl⟩ : syracuseStep 1656899 = 2485349) B2485349
theorem B1329347 : Blo 734326 1329347 := bstep (se 1 (by rfl) ⟨997010, by rfl⟩ : syracuseStep 1329347 = 1994021) B1994021
theorem B21547235 : Blo 734326 21547235 := bstep (se 1 (by rfl) ⟨16160426, by rfl⟩ : syracuseStep 21547235 = 32320853) B32320853
theorem B7948529 : Blo 734326 7948529 := bstep (se 2 (by rfl) ⟨2980698, by rfl⟩ : syracuseStep 7948529 = 5961397) B5961397
theorem B1657169 : Blo 734326 1657169 := bstep (se 2 (by rfl) ⟨621438, by rfl⟩ : syracuseStep 1657169 = 1242877) B1242877
theorem B1657187 : Blo 734326 1657187 := bstep (se 1 (by rfl) ⟨1242890, by rfl⟩ : syracuseStep 1657187 = 2485781) B2485781
theorem B1395139 : Blo 734326 1395139 := bstep (se 1 (by rfl) ⟨1046354, by rfl⟩ : syracuseStep 1395139 = 2092709) B2092709
theorem B1395299 : Blo 734326 1395299 := bstep (se 1 (by rfl) ⟨1046474, by rfl⟩ : syracuseStep 1395299 = 2092949) B2092949
theorem B1657457 : Blo 734326 1657457 := bstep (se 2 (by rfl) ⟨621546, by rfl⟩ : syracuseStep 1657457 = 1243093) B1243093
theorem B1657475 : Blo 734326 1657475 := bstep (se 1 (by rfl) ⟨1243106, by rfl⟩ : syracuseStep 1657475 = 2486213) B2486213
theorem B2018125 : Blo 734326 2018125 := bstep (se 3 (by rfl) ⟨378398, by rfl⟩ : syracuseStep 2018125 = 756797) B756797
theorem B1657745 : Blo 734326 1657745 := bstep (se 2 (by rfl) ⟨621654, by rfl⟩ : syracuseStep 1657745 = 1243309) B1243309
theorem B1657763 : Blo 734326 1657763 := bstep (se 1 (by rfl) ⟨1243322, by rfl⟩ : syracuseStep 1657763 = 2486645) B2486645
theorem B1985489 : Blo 734326 1985489 := bstep (se 2 (by rfl) ⟨744558, by rfl⟩ : syracuseStep 1985489 = 1489117) B1489117
theorem B1658033 : Blo 734326 1658033 := bstep (se 2 (by rfl) ⟨621762, by rfl⟩ : syracuseStep 1658033 = 1243525) B1243525
theorem B1658051 : Blo 734326 1658051 := bstep (se 1 (by rfl) ⟨1243538, by rfl⟩ : syracuseStep 1658051 = 2487077) B2487077
theorem B1658321 : Blo 734326 1658321 := bstep (se 2 (by rfl) ⟨621870, by rfl⟩ : syracuseStep 1658321 = 1243741) B1243741
theorem B1658339 : Blo 734326 1658339 := bstep (se 1 (by rfl) ⟨1243754, by rfl⟩ : syracuseStep 1658339 = 2487509) B2487509
theorem B1986115 : Blo 734326 1986115 := bstep (se 1 (by rfl) ⟨1489586, by rfl⟩ : syracuseStep 1986115 = 2979173) B2979173
theorem B1396369 : Blo 734326 1396369 := bstep (se 2 (by rfl) ⟨523638, by rfl⟩ : syracuseStep 1396369 = 1047277) B1047277
theorem B1101491 : Blo 734326 1101491 := bstep (se 1 (by rfl) ⟨826118, by rfl⟩ : syracuseStep 1101491 = 1652237) B1652237
theorem B1101521 : Blo 734326 1101521 := bstep (se 2 (by rfl) ⟨413070, by rfl⟩ : syracuseStep 1101521 = 826141) B826141
theorem B1101539 : Blo 734326 1101539 := bstep (se 1 (by rfl) ⟨826154, by rfl⟩ : syracuseStep 1101539 = 1652309) B1652309
theorem B1658609 : Blo 734326 1658609 := bstep (se 2 (by rfl) ⟨621978, by rfl⟩ : syracuseStep 1658609 = 1243957) B1243957
theorem B1101569 : Blo 734326 1101569 := bstep (se 2 (by rfl) ⟨413088, by rfl⟩ : syracuseStep 1101569 = 826177) B826177
theorem B1658627 : Blo 734326 1658627 := bstep (se 1 (by rfl) ⟨1243970, by rfl⟩ : syracuseStep 1658627 = 2487941) B2487941
theorem B1101587 : Blo 734326 1101587 := bstep (se 1 (by rfl) ⟨826190, by rfl⟩ : syracuseStep 1101587 = 1652381) B1652381
theorem B1101617 : Blo 734326 1101617 := bstep (se 2 (by rfl) ⟨413106, by rfl⟩ : syracuseStep 1101617 = 826213) B826213
theorem B4542257 : Blo 734326 4542257 := bstep (se 2 (by rfl) ⟨1703346, by rfl⟩ : syracuseStep 4542257 = 3406693) B3406693
theorem B1101635 : Blo 734326 1101635 := bstep (se 1 (by rfl) ⟨826226, by rfl⟩ : syracuseStep 1101635 = 1652453) B1652453
theorem B1101665 : Blo 734326 1101665 := bstep (se 2 (by rfl) ⟨413124, by rfl⟩ : syracuseStep 1101665 = 826249) B826249
theorem B1101683 : Blo 734326 1101683 := bstep (se 1 (by rfl) ⟨826262, by rfl⟩ : syracuseStep 1101683 = 1652525) B1652525
theorem B1101713 : Blo 734326 1101713 := bstep (se 2 (by rfl) ⟨413142, by rfl⟩ : syracuseStep 1101713 = 826285) B826285
theorem B1101731 : Blo 734326 1101731 := bstep (se 1 (by rfl) ⟨826298, by rfl⟩ : syracuseStep 1101731 = 1652597) B1652597
theorem B1101761 : Blo 734326 1101761 := bstep (se 2 (by rfl) ⟨413160, by rfl⟩ : syracuseStep 1101761 = 826321) B826321
theorem B1101779 : Blo 734326 1101779 := bstep (se 1 (by rfl) ⟨826334, by rfl⟩ : syracuseStep 1101779 = 1652669) B1652669
theorem B1101809 : Blo 734326 1101809 := bstep (se 2 (by rfl) ⟨413178, by rfl⟩ : syracuseStep 1101809 = 826357) B826357
theorem B1101827 : Blo 734326 1101827 := bstep (se 1 (by rfl) ⟨826370, by rfl⟩ : syracuseStep 1101827 = 1652741) B1652741
theorem B1658897 : Blo 734326 1658897 := bstep (se 2 (by rfl) ⟨622086, by rfl⟩ : syracuseStep 1658897 = 1244173) B1244173
theorem B1101857 : Blo 734326 1101857 := bstep (se 2 (by rfl) ⟨413196, by rfl⟩ : syracuseStep 1101857 = 826393) B826393
theorem B1658915 : Blo 734326 1658915 := bstep (se 1 (by rfl) ⟨1244186, by rfl⟩ : syracuseStep 1658915 = 2488373) B2488373
theorem B1101875 : Blo 734326 1101875 := bstep (se 1 (by rfl) ⟨826406, by rfl⟩ : syracuseStep 1101875 = 1652813) B1652813
theorem B1101905 : Blo 734326 1101905 := bstep (se 2 (by rfl) ⟨413214, by rfl⟩ : syracuseStep 1101905 = 826429) B826429
theorem B1101923 : Blo 734326 1101923 := bstep (se 1 (by rfl) ⟨826442, by rfl⟩ : syracuseStep 1101923 = 1652885) B1652885
theorem B1101953 : Blo 734326 1101953 := bstep (se 2 (by rfl) ⟨413232, by rfl⟩ : syracuseStep 1101953 = 826465) B826465
theorem B1101971 : Blo 734326 1101971 := bstep (se 1 (by rfl) ⟨826478, by rfl⟩ : syracuseStep 1101971 = 1652957) B1652957
theorem B1102001 : Blo 734326 1102001 := bstep (se 2 (by rfl) ⟨413250, by rfl⟩ : syracuseStep 1102001 = 826501) B826501
theorem B1102019 : Blo 734326 1102019 := bstep (se 1 (by rfl) ⟨826514, by rfl⟩ : syracuseStep 1102019 = 1653029) B1653029
theorem B1102049 : Blo 734326 1102049 := bstep (se 2 (by rfl) ⟨413268, by rfl⟩ : syracuseStep 1102049 = 826537) B826537
theorem B4706545 : Blo 734326 4706545 := bstep (se 2 (by rfl) ⟨1764954, by rfl⟩ : syracuseStep 4706545 = 3529909) B3529909
theorem B1102067 : Blo 734326 1102067 := bstep (se 1 (by rfl) ⟨826550, by rfl⟩ : syracuseStep 1102067 = 1653101) B1653101
theorem B1102097 : Blo 734326 1102097 := bstep (se 2 (by rfl) ⟨413286, by rfl⟩ : syracuseStep 1102097 = 826573) B826573
theorem B1102115 : Blo 734326 1102115 := bstep (se 1 (by rfl) ⟨826586, by rfl⟩ : syracuseStep 1102115 = 1653173) B1653173
theorem B3723569 : Blo 734326 3723569 := bstep (se 2 (by rfl) ⟨1396338, by rfl⟩ : syracuseStep 3723569 = 2792677) B2792677
theorem B1659185 : Blo 734326 1659185 := bstep (se 2 (by rfl) ⟨622194, by rfl⟩ : syracuseStep 1659185 = 1244389) B1244389
theorem B1102145 : Blo 734326 1102145 := bstep (se 2 (by rfl) ⟨413304, by rfl⟩ : syracuseStep 1102145 = 826609) B826609
theorem B1659203 : Blo 734326 1659203 := bstep (se 1 (by rfl) ⟨1244402, by rfl⟩ : syracuseStep 1659203 = 2488805) B2488805
theorem B1102163 : Blo 734326 1102163 := bstep (se 1 (by rfl) ⟨826622, by rfl⟩ : syracuseStep 1102163 = 1653245) B1653245
theorem B1102193 : Blo 734326 1102193 := bstep (se 2 (by rfl) ⟨413322, by rfl⟩ : syracuseStep 1102193 = 826645) B826645
theorem B1102211 : Blo 734326 1102211 := bstep (se 1 (by rfl) ⟨826658, by rfl⟩ : syracuseStep 1102211 = 1653317) B1653317
theorem B1102241 : Blo 734326 1102241 := bstep (se 2 (by rfl) ⟨413340, by rfl⟩ : syracuseStep 1102241 = 826681) B826681
theorem B1102259 : Blo 734326 1102259 := bstep (se 1 (by rfl) ⟨826694, by rfl⟩ : syracuseStep 1102259 = 1653389) B1653389
theorem B2478545 : Blo 734326 2478545 := bstep (se 2 (by rfl) ⟨929454, by rfl⟩ : syracuseStep 2478545 = 1858909) B1858909
theorem B1102289 : Blo 734326 1102289 := bstep (se 2 (by rfl) ⟨413358, by rfl⟩ : syracuseStep 1102289 = 826717) B826717
theorem B1102307 : Blo 734326 1102307 := bstep (se 1 (by rfl) ⟨826730, by rfl⟩ : syracuseStep 1102307 = 1653461) B1653461
theorem B1495523 : Blo 734326 1495523 := bstep (se 1 (by rfl) ⟨1121642, by rfl⟩ : syracuseStep 1495523 = 2243285) B2243285
theorem B1102337 : Blo 734326 1102337 := bstep (se 2 (by rfl) ⟨413376, by rfl⟩ : syracuseStep 1102337 = 826753) B826753
theorem B1102355 : Blo 734326 1102355 := bstep (se 1 (by rfl) ⟨826766, by rfl⟩ : syracuseStep 1102355 = 1653533) B1653533
theorem B1102385 : Blo 734326 1102385 := bstep (se 2 (by rfl) ⟨413394, by rfl⟩ : syracuseStep 1102385 = 826789) B826789
theorem B1102403 : Blo 734326 1102403 := bstep (se 1 (by rfl) ⟨826802, by rfl⟩ : syracuseStep 1102403 = 1653605) B1653605
theorem B1659473 : Blo 734326 1659473 := bstep (se 2 (by rfl) ⟨622302, by rfl⟩ : syracuseStep 1659473 = 1244605) B1244605
theorem B1102433 : Blo 734326 1102433 := bstep (se 2 (by rfl) ⟨413412, by rfl⟩ : syracuseStep 1102433 = 826825) B826825
theorem B1659491 : Blo 734326 1659491 := bstep (se 1 (by rfl) ⟨1244618, by rfl⟩ : syracuseStep 1659491 = 2489237) B2489237
theorem B1102451 : Blo 734326 1102451 := bstep (se 1 (by rfl) ⟨826838, by rfl⟩ : syracuseStep 1102451 = 1653677) B1653677
theorem B1102481 : Blo 734326 1102481 := bstep (se 2 (by rfl) ⟨413430, by rfl⟩ : syracuseStep 1102481 = 826861) B826861
theorem B1102499 : Blo 734326 1102499 := bstep (se 1 (by rfl) ⟨826874, by rfl⟩ : syracuseStep 1102499 = 1653749) B1653749
theorem B1397425 : Blo 734326 1397425 := bstep (se 2 (by rfl) ⟨524034, by rfl⟩ : syracuseStep 1397425 = 1048069) B1048069
theorem B1102529 : Blo 734326 1102529 := bstep (se 2 (by rfl) ⟨413448, by rfl⟩ : syracuseStep 1102529 = 826897) B826897
theorem B1102547 : Blo 734326 1102547 := bstep (se 1 (by rfl) ⟨826910, by rfl⟩ : syracuseStep 1102547 = 1653821) B1653821
theorem B1102577 : Blo 734326 1102577 := bstep (se 2 (by rfl) ⟨413466, by rfl⟩ : syracuseStep 1102577 = 826933) B826933
theorem B1102595 : Blo 734326 1102595 := bstep (se 1 (by rfl) ⟨826946, by rfl⟩ : syracuseStep 1102595 = 1653893) B1653893
theorem B1102625 : Blo 734326 1102625 := bstep (se 2 (by rfl) ⟨413484, by rfl⟩ : syracuseStep 1102625 = 826969) B826969
theorem B1102643 : Blo 734326 1102643 := bstep (se 1 (by rfl) ⟨826982, by rfl⟩ : syracuseStep 1102643 = 1653965) B1653965
theorem B1102673 : Blo 734326 1102673 := bstep (se 2 (by rfl) ⟨413502, by rfl⟩ : syracuseStep 1102673 = 827005) B827005
theorem B1102691 : Blo 734326 1102691 := bstep (se 1 (by rfl) ⟨827018, by rfl⟩ : syracuseStep 1102691 = 1654037) B1654037
theorem B1659761 : Blo 734326 1659761 := bstep (se 2 (by rfl) ⟨622410, by rfl⟩ : syracuseStep 1659761 = 1244821) B1244821
theorem B1102721 : Blo 734326 1102721 := bstep (se 2 (by rfl) ⟨413520, by rfl⟩ : syracuseStep 1102721 = 827041) B827041
theorem B1659779 : Blo 734326 1659779 := bstep (se 1 (by rfl) ⟨1244834, by rfl⟩ : syracuseStep 1659779 = 2489669) B2489669
theorem B3986309 : Blo 734326 3986309 := bstep (se 4 (by rfl) ⟨373716, by rfl⟩ : syracuseStep 3986309 = 747433) B747433
theorem B6706061 : Blo 734326 6706061 := bstep (se 3 (by rfl) ⟨1257386, by rfl⟩ : syracuseStep 6706061 = 2514773) B2514773
theorem B1102739 : Blo 734326 1102739 := bstep (se 1 (by rfl) ⟨827054, by rfl⟩ : syracuseStep 1102739 = 1654109) B1654109
theorem B1102769 : Blo 734326 1102769 := bstep (se 2 (by rfl) ⟨413538, by rfl⟩ : syracuseStep 1102769 = 827077) B827077
theorem B1102787 : Blo 734326 1102787 := bstep (se 1 (by rfl) ⟨827090, by rfl⟩ : syracuseStep 1102787 = 1654181) B1654181
theorem B1102817 : Blo 734326 1102817 := bstep (se 2 (by rfl) ⟨413556, by rfl⟩ : syracuseStep 1102817 = 827113) B827113
theorem B2479085 : Blo 734326 2479085 := bstep (se 3 (by rfl) ⟨464828, by rfl⟩ : syracuseStep 2479085 = 929657) B929657
theorem B1102835 : Blo 734326 1102835 := bstep (se 1 (by rfl) ⟨827126, by rfl⟩ : syracuseStep 1102835 = 1654253) B1654253
theorem B1102865 : Blo 734326 1102865 := bstep (se 2 (by rfl) ⟨413574, by rfl⟩ : syracuseStep 1102865 = 827149) B827149
theorem B2479139 : Blo 734326 2479139 := bstep (se 1 (by rfl) ⟨1859354, by rfl⟩ : syracuseStep 2479139 = 3718709) B3718709
theorem B1102883 : Blo 734326 1102883 := bstep (se 1 (by rfl) ⟨827162, by rfl⟩ : syracuseStep 1102883 = 1654325) B1654325
theorem B1102913 : Blo 734326 1102913 := bstep (se 2 (by rfl) ⟨413592, by rfl⟩ : syracuseStep 1102913 = 827185) B827185
theorem B1397827 : Blo 734326 1397827 := bstep (se 1 (by rfl) ⟨1048370, by rfl⟩ : syracuseStep 1397827 = 2096741) B2096741
theorem B1102931 : Blo 734326 1102931 := bstep (se 1 (by rfl) ⟨827198, by rfl⟩ : syracuseStep 1102931 = 1654397) B1654397
theorem B1102961 : Blo 734326 1102961 := bstep (se 2 (by rfl) ⟨413610, by rfl⟩ : syracuseStep 1102961 = 827221) B827221
theorem B6804593 : Blo 734326 6804593 := bstep (se 2 (by rfl) ⟨2551722, by rfl⟩ : syracuseStep 6804593 = 5103445) B5103445
theorem B1397873 : Blo 734326 1397873 := bstep (se 2 (by rfl) ⟨524202, by rfl⟩ : syracuseStep 1397873 = 1048405) B1048405
theorem B1102979 : Blo 734326 1102979 := bstep (se 1 (by rfl) ⟨827234, by rfl⟩ : syracuseStep 1102979 = 1654469) B1654469
theorem B1987715 : Blo 734326 1987715 := bstep (se 1 (by rfl) ⟨1490786, by rfl⟩ : syracuseStep 1987715 = 2981573) B2981573
theorem B1660049 : Blo 734326 1660049 := bstep (se 2 (by rfl) ⟨622518, by rfl⟩ : syracuseStep 1660049 = 1245037) B1245037
theorem B1103009 : Blo 734326 1103009 := bstep (se 2 (by rfl) ⟨413628, by rfl⟩ : syracuseStep 1103009 = 827257) B827257
theorem B1660067 : Blo 734326 1660067 := bstep (se 1 (by rfl) ⟨1245050, by rfl⟩ : syracuseStep 1660067 = 2490101) B2490101
theorem B1103027 : Blo 734326 1103027 := bstep (se 1 (by rfl) ⟨827270, by rfl⟩ : syracuseStep 1103027 = 1654541) B1654541
theorem B1135811 : Blo 734326 1135811 := bstep (se 1 (by rfl) ⟨851858, by rfl⟩ : syracuseStep 1135811 = 1703717) B1703717
theorem B1103057 : Blo 734326 1103057 := bstep (se 2 (by rfl) ⟨413646, by rfl⟩ : syracuseStep 1103057 = 827293) B827293
theorem B1103075 : Blo 734326 1103075 := bstep (se 1 (by rfl) ⟨827306, by rfl⟩ : syracuseStep 1103075 = 1654613) B1654613
theorem B1103105 : Blo 734326 1103105 := bstep (se 2 (by rfl) ⟨413664, by rfl⟩ : syracuseStep 1103105 = 827329) B827329
theorem B1103123 : Blo 734326 1103123 := bstep (se 1 (by rfl) ⟨827342, by rfl⟩ : syracuseStep 1103123 = 1654685) B1654685
theorem B2479409 : Blo 734326 2479409 := bstep (se 2 (by rfl) ⟨929778, by rfl⟩ : syracuseStep 2479409 = 1859557) B1859557
theorem B1103153 : Blo 734326 1103153 := bstep (se 2 (by rfl) ⟨413682, by rfl⟩ : syracuseStep 1103153 = 827365) B827365
theorem B1103171 : Blo 734326 1103171 := bstep (se 1 (by rfl) ⟨827378, by rfl⟩ : syracuseStep 1103171 = 1654757) B1654757
theorem B6280517 : Blo 734326 6280517 := bstep (se 4 (by rfl) ⟨588798, by rfl⟩ : syracuseStep 6280517 = 1177597) B1177597
theorem B1103201 : Blo 734326 1103201 := bstep (se 2 (by rfl) ⟨413700, by rfl⟩ : syracuseStep 1103201 = 827401) B827401
theorem B1103219 : Blo 734326 1103219 := bstep (se 1 (by rfl) ⟨827414, by rfl⟩ : syracuseStep 1103219 = 1654829) B1654829
theorem B1103249 : Blo 734326 1103249 := bstep (se 2 (by rfl) ⟨413718, by rfl⟩ : syracuseStep 1103249 = 827437) B827437
theorem B1398161 : Blo 734326 1398161 := bstep (se 2 (by rfl) ⟨524310, by rfl⟩ : syracuseStep 1398161 = 1048621) B1048621
theorem B1103267 : Blo 734326 1103267 := bstep (se 1 (by rfl) ⟨827450, by rfl⟩ : syracuseStep 1103267 = 1654901) B1654901
theorem B1660337 : Blo 734326 1660337 := bstep (se 2 (by rfl) ⟨622626, by rfl⟩ : syracuseStep 1660337 = 1245253) B1245253
theorem B1103297 : Blo 734326 1103297 := bstep (se 2 (by rfl) ⟨413736, by rfl⟩ : syracuseStep 1103297 = 827473) B827473
theorem B1660355 : Blo 734326 1660355 := bstep (se 1 (by rfl) ⟨1245266, by rfl⟩ : syracuseStep 1660355 = 2490533) B2490533
theorem B1103315 : Blo 734326 1103315 := bstep (se 1 (by rfl) ⟨827486, by rfl⟩ : syracuseStep 1103315 = 1654973) B1654973
theorem B1103345 : Blo 734326 1103345 := bstep (se 2 (by rfl) ⟨413754, by rfl⟩ : syracuseStep 1103345 = 827509) B827509
theorem B1103363 : Blo 734326 1103363 := bstep (se 1 (by rfl) ⟨827522, by rfl⟩ : syracuseStep 1103363 = 1655045) B1655045
theorem B1103393 : Blo 734326 1103393 := bstep (se 2 (by rfl) ⟨413772, by rfl⟩ : syracuseStep 1103393 = 827545) B827545
theorem B1103411 : Blo 734326 1103411 := bstep (se 1 (by rfl) ⟨827558, by rfl⟩ : syracuseStep 1103411 = 1655117) B1655117
theorem B1103441 : Blo 734326 1103441 := bstep (se 2 (by rfl) ⟨413790, by rfl⟩ : syracuseStep 1103441 = 827581) B827581
theorem B1103459 : Blo 734326 1103459 := bstep (se 1 (by rfl) ⟨827594, by rfl⟩ : syracuseStep 1103459 = 1655189) B1655189
theorem B5035619 : Blo 734326 5035619 := bstep (se 1 (by rfl) ⟨3776714, by rfl⟩ : syracuseStep 5035619 = 7553429) B7553429
theorem B1103489 : Blo 734326 1103489 := bstep (se 2 (by rfl) ⟨413808, by rfl⟩ : syracuseStep 1103489 = 827617) B827617
theorem B1103507 : Blo 734326 1103507 := bstep (se 1 (by rfl) ⟨827630, by rfl⟩ : syracuseStep 1103507 = 1655261) B1655261
theorem B3987107 : Blo 734326 3987107 := bstep (se 1 (by rfl) ⟨2990330, by rfl⟩ : syracuseStep 3987107 = 5980661) B5980661
theorem B1103537 : Blo 734326 1103537 := bstep (se 2 (by rfl) ⟨413826, by rfl⟩ : syracuseStep 1103537 = 827653) B827653
theorem B1103555 : Blo 734326 1103555 := bstep (se 1 (by rfl) ⟨827666, by rfl⟩ : syracuseStep 1103555 = 1655333) B1655333
theorem B7952069 : Blo 734326 7952069 := bstep (se 4 (by rfl) ⟨745506, by rfl⟩ : syracuseStep 7952069 = 1491013) B1491013
theorem B1660625 : Blo 734326 1660625 := bstep (se 2 (by rfl) ⟨622734, by rfl⟩ : syracuseStep 1660625 = 1245469) B1245469
theorem B1103585 : Blo 734326 1103585 := bstep (se 2 (by rfl) ⟨413844, by rfl⟩ : syracuseStep 1103585 = 827689) B827689
theorem B3725027 : Blo 734326 3725027 := bstep (se 1 (by rfl) ⟨2793770, by rfl⟩ : syracuseStep 3725027 = 5587541) B5587541
theorem B1660643 : Blo 734326 1660643 := bstep (se 1 (by rfl) ⟨1245482, by rfl⟩ : syracuseStep 1660643 = 2490965) B2490965
theorem B1103603 : Blo 734326 1103603 := bstep (se 1 (by rfl) ⟨827702, by rfl⟩ : syracuseStep 1103603 = 1655405) B1655405
theorem B1103633 : Blo 734326 1103633 := bstep (se 2 (by rfl) ⟨413862, by rfl⟩ : syracuseStep 1103633 = 827725) B827725
theorem B1103651 : Blo 734326 1103651 := bstep (se 1 (by rfl) ⟨827738, by rfl⟩ : syracuseStep 1103651 = 1655477) B1655477
theorem B1103681 : Blo 734326 1103681 := bstep (se 2 (by rfl) ⟨413880, by rfl⟩ : syracuseStep 1103681 = 827761) B827761
theorem B2479949 : Blo 734326 2479949 := bstep (se 3 (by rfl) ⟨464990, by rfl⟩ : syracuseStep 2479949 = 929981) B929981
theorem B1103699 : Blo 734326 1103699 := bstep (se 1 (by rfl) ⟨827774, by rfl⟩ : syracuseStep 1103699 = 1655549) B1655549
theorem B1103729 : Blo 734326 1103729 := bstep (se 2 (by rfl) ⟨413898, by rfl⟩ : syracuseStep 1103729 = 827797) B827797
theorem B2480003 : Blo 734326 2480003 := bstep (se 1 (by rfl) ⟨1860002, by rfl⟩ : syracuseStep 2480003 = 3720005) B3720005
theorem B1103747 : Blo 734326 1103747 := bstep (se 1 (by rfl) ⟨827810, by rfl⟩ : syracuseStep 1103747 = 1655621) B1655621
theorem B1103777 : Blo 734326 1103777 := bstep (se 2 (by rfl) ⟨413916, by rfl⟩ : syracuseStep 1103777 = 827833) B827833
theorem B1103795 : Blo 734326 1103795 := bstep (se 1 (by rfl) ⟨827846, by rfl⟩ : syracuseStep 1103795 = 1655693) B1655693
theorem B1103825 : Blo 734326 1103825 := bstep (se 2 (by rfl) ⟨413934, by rfl⟩ : syracuseStep 1103825 = 827869) B827869
theorem B1103843 : Blo 734326 1103843 := bstep (se 1 (by rfl) ⟨827882, by rfl⟩ : syracuseStep 1103843 = 1655765) B1655765
theorem B1660913 : Blo 734326 1660913 := bstep (se 2 (by rfl) ⟨622842, by rfl⟩ : syracuseStep 1660913 = 1245685) B1245685
theorem B1103873 : Blo 734326 1103873 := bstep (se 2 (by rfl) ⟨413952, by rfl⟩ : syracuseStep 1103873 = 827905) B827905
theorem B1660931 : Blo 734326 1660931 := bstep (se 1 (by rfl) ⟨1245698, by rfl⟩ : syracuseStep 1660931 = 2491397) B2491397
theorem B1103891 : Blo 734326 1103891 := bstep (se 1 (by rfl) ⟨827918, by rfl⟩ : syracuseStep 1103891 = 1655837) B1655837
theorem B1103921 : Blo 734326 1103921 := bstep (se 2 (by rfl) ⟨413970, by rfl⟩ : syracuseStep 1103921 = 827941) B827941
theorem B1103939 : Blo 734326 1103939 := bstep (se 1 (by rfl) ⟨827954, by rfl⟩ : syracuseStep 1103939 = 1655909) B1655909
theorem B1103969 : Blo 734326 1103969 := bstep (se 2 (by rfl) ⟨413988, by rfl⟩ : syracuseStep 1103969 = 827977) B827977
theorem B1398883 : Blo 734326 1398883 := bstep (se 1 (by rfl) ⟨1049162, by rfl⟩ : syracuseStep 1398883 = 2098325) B2098325
theorem B1103987 : Blo 734326 1103987 := bstep (se 1 (by rfl) ⟨827990, by rfl⟩ : syracuseStep 1103987 = 1655981) B1655981
theorem B1104017 : Blo 734326 1104017 := bstep (se 2 (by rfl) ⟨414006, by rfl⟩ : syracuseStep 1104017 = 828013) B828013
theorem B2480273 : Blo 734326 2480273 := bstep (se 2 (by rfl) ⟨930102, by rfl⟩ : syracuseStep 2480273 = 1860205) B1860205
theorem B1104035 : Blo 734326 1104035 := bstep (se 1 (by rfl) ⟨828026, by rfl⟩ : syracuseStep 1104035 = 1656053) B1656053
theorem B1104065 : Blo 734326 1104065 := bstep (se 2 (by rfl) ⟨414024, by rfl⟩ : syracuseStep 1104065 = 828049) B828049
theorem B1104083 : Blo 734326 1104083 := bstep (se 1 (by rfl) ⟨828062, by rfl⟩ : syracuseStep 1104083 = 1656125) B1656125
theorem B1104113 : Blo 734326 1104113 := bstep (se 2 (by rfl) ⟨414042, by rfl⟩ : syracuseStep 1104113 = 828085) B828085
theorem B1104131 : Blo 734326 1104131 := bstep (se 1 (by rfl) ⟨828098, by rfl⟩ : syracuseStep 1104131 = 1656197) B1656197
theorem B1661201 : Blo 734326 1661201 := bstep (se 2 (by rfl) ⟨622950, by rfl⟩ : syracuseStep 1661201 = 1245901) B1245901
theorem B1104161 : Blo 734326 1104161 := bstep (se 2 (by rfl) ⟨414060, by rfl⟩ : syracuseStep 1104161 = 828121) B828121
theorem B1661219 : Blo 734326 1661219 := bstep (se 1 (by rfl) ⟨1245914, by rfl⟩ : syracuseStep 1661219 = 2491829) B2491829
theorem B4184369 : Blo 734326 4184369 := bstep (se 2 (by rfl) ⟨1569138, by rfl⟩ : syracuseStep 4184369 = 3138277) B3138277
theorem B1104179 : Blo 734326 1104179 := bstep (se 1 (by rfl) ⟨828134, by rfl⟩ : syracuseStep 1104179 = 1656269) B1656269
theorem B1104209 : Blo 734326 1104209 := bstep (se 2 (by rfl) ⟨414078, by rfl⟩ : syracuseStep 1104209 = 828157) B828157
theorem B1104227 : Blo 734326 1104227 := bstep (se 1 (by rfl) ⟨828170, by rfl⟩ : syracuseStep 1104227 = 1656341) B1656341
theorem B1104257 : Blo 734326 1104257 := bstep (se 2 (by rfl) ⟨414096, by rfl⟩ : syracuseStep 1104257 = 828193) B828193
theorem B1104275 : Blo 734326 1104275 := bstep (se 1 (by rfl) ⟨828206, by rfl⟩ : syracuseStep 1104275 = 1656413) B1656413
theorem B1104305 : Blo 734326 1104305 := bstep (se 2 (by rfl) ⟨414114, by rfl⟩ : syracuseStep 1104305 = 828229) B828229
theorem B1104323 : Blo 734326 1104323 := bstep (se 1 (by rfl) ⟨828242, by rfl⟩ : syracuseStep 1104323 = 1656485) B1656485
theorem B1104353 : Blo 734326 1104353 := bstep (se 2 (by rfl) ⟨414132, by rfl⟩ : syracuseStep 1104353 = 828265) B828265
theorem B1104371 : Blo 734326 1104371 := bstep (se 1 (by rfl) ⟨828278, by rfl⟩ : syracuseStep 1104371 = 1656557) B1656557
theorem B3725837 : Blo 734326 3725837 := bstep (se 3 (by rfl) ⟨698594, by rfl⟩ : syracuseStep 3725837 = 1397189) B1397189
theorem B1104401 : Blo 734326 1104401 := bstep (se 2 (by rfl) ⟨414150, by rfl⟩ : syracuseStep 1104401 = 828301) B828301
theorem B1104419 : Blo 734326 1104419 := bstep (se 1 (by rfl) ⟨828314, by rfl⟩ : syracuseStep 1104419 = 1656629) B1656629
theorem B1399331 : Blo 734326 1399331 := bstep (se 1 (by rfl) ⟨1049498, by rfl⟩ : syracuseStep 1399331 = 2098997) B2098997
theorem B1104449 : Blo 734326 1104449 := bstep (se 2 (by rfl) ⟨414168, by rfl⟩ : syracuseStep 1104449 = 828337) B828337
theorem B1104467 : Blo 734326 1104467 := bstep (se 1 (by rfl) ⟨828350, by rfl⟩ : syracuseStep 1104467 = 1656701) B1656701
theorem B1104497 : Blo 734326 1104497 := bstep (se 2 (by rfl) ⟨414186, by rfl⟩ : syracuseStep 1104497 = 828373) B828373
theorem B1104515 : Blo 734326 1104515 := bstep (se 1 (by rfl) ⟨828386, by rfl⟩ : syracuseStep 1104515 = 1656773) B1656773
theorem B1104545 : Blo 734326 1104545 := bstep (se 2 (by rfl) ⟨414204, by rfl⟩ : syracuseStep 1104545 = 828409) B828409
theorem B2480813 : Blo 734326 2480813 := bstep (se 3 (by rfl) ⟨465152, by rfl⟩ : syracuseStep 2480813 = 930305) B930305
theorem B1104563 : Blo 734326 1104563 := bstep (se 1 (by rfl) ⟨828422, by rfl⟩ : syracuseStep 1104563 = 1656845) B1656845
theorem B1104593 : Blo 734326 1104593 := bstep (se 2 (by rfl) ⟨414222, by rfl⟩ : syracuseStep 1104593 = 828445) B828445
theorem B2480867 : Blo 734326 2480867 := bstep (se 1 (by rfl) ⟨1860650, by rfl⟩ : syracuseStep 2480867 = 3721301) B3721301
theorem B1104611 : Blo 734326 1104611 := bstep (se 1 (by rfl) ⟨828458, by rfl⟩ : syracuseStep 1104611 = 1656917) B1656917
theorem B1104641 : Blo 734326 1104641 := bstep (se 2 (by rfl) ⟨414240, by rfl⟩ : syracuseStep 1104641 = 828481) B828481
theorem B1104659 : Blo 734326 1104659 := bstep (se 1 (by rfl) ⟨828494, by rfl⟩ : syracuseStep 1104659 = 1656989) B1656989
theorem B1104689 : Blo 734326 1104689 := bstep (se 2 (by rfl) ⟨414258, by rfl⟩ : syracuseStep 1104689 = 828517) B828517
theorem B1104707 : Blo 734326 1104707 := bstep (se 1 (by rfl) ⟨828530, by rfl⟩ : syracuseStep 1104707 = 1657061) B1657061
theorem B1399619 : Blo 734326 1399619 := bstep (se 1 (by rfl) ⟨1049714, by rfl⟩ : syracuseStep 1399619 = 2099429) B2099429
theorem B1104737 : Blo 734326 1104737 := bstep (se 2 (by rfl) ⟨414276, by rfl⟩ : syracuseStep 1104737 = 828553) B828553
theorem B1104755 : Blo 734326 1104755 := bstep (se 1 (by rfl) ⟨828566, by rfl⟩ : syracuseStep 1104755 = 1657133) B1657133
theorem B1104785 : Blo 734326 1104785 := bstep (se 2 (by rfl) ⟨414294, by rfl⟩ : syracuseStep 1104785 = 828589) B828589
theorem B744355 : Blo 734326 744355 := bstep (se 1 (by rfl) ⟨558266, by rfl⟩ : syracuseStep 744355 = 1116533) B1116533
theorem B1104803 : Blo 734326 1104803 := bstep (se 1 (by rfl) ⟨828602, by rfl⟩ : syracuseStep 1104803 = 1657205) B1657205
theorem B1104833 : Blo 734326 1104833 := bstep (se 2 (by rfl) ⟨414312, by rfl⟩ : syracuseStep 1104833 = 828625) B828625
theorem B1104851 : Blo 734326 1104851 := bstep (se 1 (by rfl) ⟨828638, by rfl⟩ : syracuseStep 1104851 = 1657277) B1657277
theorem B2481137 : Blo 734326 2481137 := bstep (se 2 (by rfl) ⟨930426, by rfl⟩ : syracuseStep 2481137 = 1860853) B1860853
theorem B1104881 : Blo 734326 1104881 := bstep (se 2 (by rfl) ⟨414330, by rfl⟩ : syracuseStep 1104881 = 828661) B828661
theorem B1104899 : Blo 734326 1104899 := bstep (se 1 (by rfl) ⟨828674, by rfl⟩ : syracuseStep 1104899 = 1657349) B1657349
theorem B1104929 : Blo 734326 1104929 := bstep (se 2 (by rfl) ⟨414348, by rfl⟩ : syracuseStep 1104929 = 828697) B828697
theorem B1104947 : Blo 734326 1104947 := bstep (se 1 (by rfl) ⟨828710, by rfl⟩ : syracuseStep 1104947 = 1657421) B1657421
theorem B1104977 : Blo 734326 1104977 := bstep (se 2 (by rfl) ⟨414366, by rfl⟩ : syracuseStep 1104977 = 828733) B828733
theorem B1104995 : Blo 734326 1104995 := bstep (se 1 (by rfl) ⟨828746, by rfl⟩ : syracuseStep 1104995 = 1657493) B1657493
theorem B1105025 : Blo 734326 1105025 := bstep (se 2 (by rfl) ⟨414384, by rfl⟩ : syracuseStep 1105025 = 828769) B828769
theorem B1105043 : Blo 734326 1105043 := bstep (se 1 (by rfl) ⟨828782, by rfl⟩ : syracuseStep 1105043 = 1657565) B1657565
theorem B1105073 : Blo 734326 1105073 := bstep (se 2 (by rfl) ⟨414402, by rfl⟩ : syracuseStep 1105073 = 828805) B828805
theorem B1596611 : Blo 734326 1596611 := bstep (se 1 (by rfl) ⟨1197458, by rfl⟩ : syracuseStep 1596611 = 2394917) B2394917
theorem B1105091 : Blo 734326 1105091 := bstep (se 1 (by rfl) ⟨828818, by rfl⟩ : syracuseStep 1105091 = 1657637) B1657637
theorem B1105121 : Blo 734326 1105121 := bstep (se 2 (by rfl) ⟨414420, by rfl⟩ : syracuseStep 1105121 = 828841) B828841
theorem B1105139 : Blo 734326 1105139 := bstep (se 1 (by rfl) ⟨828854, by rfl⟩ : syracuseStep 1105139 = 1657709) B1657709
theorem B1105169 : Blo 734326 1105169 := bstep (se 2 (by rfl) ⟨414438, by rfl⟩ : syracuseStep 1105169 = 828877) B828877
theorem B1105187 : Blo 734326 1105187 := bstep (se 1 (by rfl) ⟨828890, by rfl⟩ : syracuseStep 1105187 = 1657781) B1657781
theorem B1105217 : Blo 734326 1105217 := bstep (se 2 (by rfl) ⟨414456, by rfl⟩ : syracuseStep 1105217 = 828913) B828913
theorem B1105235 : Blo 734326 1105235 := bstep (se 1 (by rfl) ⟨828926, by rfl⟩ : syracuseStep 1105235 = 1657853) B1657853
theorem B1105265 : Blo 734326 1105265 := bstep (se 2 (by rfl) ⟨414474, by rfl⟩ : syracuseStep 1105265 = 828949) B828949
theorem B1105283 : Blo 734326 1105283 := bstep (se 1 (by rfl) ⟨828962, by rfl⟩ : syracuseStep 1105283 = 1657925) B1657925
theorem B1105313 : Blo 734326 1105313 := bstep (se 2 (by rfl) ⟨414492, by rfl⟩ : syracuseStep 1105313 = 828985) B828985
theorem B1105331 : Blo 734326 1105331 := bstep (se 1 (by rfl) ⟨828998, by rfl⟩ : syracuseStep 1105331 = 1657997) B1657997
theorem B1105361 : Blo 734326 1105361 := bstep (se 2 (by rfl) ⟨414510, by rfl⟩ : syracuseStep 1105361 = 829021) B829021
theorem B1105379 : Blo 734326 1105379 := bstep (se 1 (by rfl) ⟨829034, by rfl⟩ : syracuseStep 1105379 = 1658069) B1658069
theorem B1990129 : Blo 734326 1990129 := bstep (se 2 (by rfl) ⟨746298, by rfl⟩ : syracuseStep 1990129 = 1492597) B1492597
theorem B1105409 : Blo 734326 1105409 := bstep (se 2 (by rfl) ⟨414528, by rfl⟩ : syracuseStep 1105409 = 829057) B829057
theorem B2481677 : Blo 734326 2481677 := bstep (se 3 (by rfl) ⟨465314, by rfl⟩ : syracuseStep 2481677 = 930629) B930629
theorem B1105427 : Blo 734326 1105427 := bstep (se 1 (by rfl) ⟨829070, by rfl⟩ : syracuseStep 1105427 = 1658141) B1658141
theorem B1105457 : Blo 734326 1105457 := bstep (se 2 (by rfl) ⟨414546, by rfl⟩ : syracuseStep 1105457 = 829093) B829093
theorem B2481731 : Blo 734326 2481731 := bstep (se 1 (by rfl) ⟨1861298, by rfl⟩ : syracuseStep 2481731 = 3722597) B3722597
theorem B1105475 : Blo 734326 1105475 := bstep (se 1 (by rfl) ⟨829106, by rfl⟩ : syracuseStep 1105475 = 1658213) B1658213
theorem B1105505 : Blo 734326 1105505 := bstep (se 2 (by rfl) ⟨414564, by rfl⟩ : syracuseStep 1105505 = 829129) B829129
theorem B1105523 : Blo 734326 1105523 := bstep (se 1 (by rfl) ⟨829142, by rfl⟩ : syracuseStep 1105523 = 1658285) B1658285
theorem B1105553 : Blo 734326 1105553 := bstep (se 2 (by rfl) ⟨414582, by rfl⟩ : syracuseStep 1105553 = 829165) B829165
theorem B1105571 : Blo 734326 1105571 := bstep (se 1 (by rfl) ⟨829178, by rfl⟩ : syracuseStep 1105571 = 1658357) B1658357
theorem B1105601 : Blo 734326 1105601 := bstep (se 2 (by rfl) ⟨414600, by rfl⟩ : syracuseStep 1105601 = 829201) B829201
theorem B1105619 : Blo 734326 1105619 := bstep (se 1 (by rfl) ⟨829214, by rfl⟩ : syracuseStep 1105619 = 1658429) B1658429
theorem B4185827 : Blo 734326 4185827 := bstep (se 1 (by rfl) ⟨3139370, by rfl⟩ : syracuseStep 4185827 = 6278741) B6278741
theorem B1105649 : Blo 734326 1105649 := bstep (se 2 (by rfl) ⟨414618, by rfl⟩ : syracuseStep 1105649 = 829237) B829237
theorem B1400561 : Blo 734326 1400561 := bstep (se 2 (by rfl) ⟨525210, by rfl⟩ : syracuseStep 1400561 = 1050421) B1050421
theorem B1105667 : Blo 734326 1105667 := bstep (se 1 (by rfl) ⟨829250, by rfl⟩ : syracuseStep 1105667 = 1658501) B1658501
theorem B1859345 : Blo 734326 1859345 := bstep (se 2 (by rfl) ⟨697254, by rfl⟩ : syracuseStep 1859345 = 1394509) B1394509
theorem B1105697 : Blo 734326 1105697 := bstep (se 2 (by rfl) ⟨414636, by rfl⟩ : syracuseStep 1105697 = 829273) B829273
theorem B1105715 : Blo 734326 1105715 := bstep (se 1 (by rfl) ⟨829286, by rfl⟩ : syracuseStep 1105715 = 1658573) B1658573
theorem B1859395 : Blo 734326 1859395 := bstep (se 1 (by rfl) ⟨1394546, by rfl⟩ : syracuseStep 1859395 = 2789093) B2789093
theorem B2482001 : Blo 734326 2482001 := bstep (se 2 (by rfl) ⟨930750, by rfl⟩ : syracuseStep 2482001 = 1861501) B1861501
theorem B1105745 : Blo 734326 1105745 := bstep (se 2 (by rfl) ⟨414654, by rfl⟩ : syracuseStep 1105745 = 829309) B829309
theorem B1105763 : Blo 734326 1105763 := bstep (se 1 (by rfl) ⟨829322, by rfl⟩ : syracuseStep 1105763 = 1658645) B1658645
theorem B1105793 : Blo 734326 1105793 := bstep (se 2 (by rfl) ⟨414672, by rfl⟩ : syracuseStep 1105793 = 829345) B829345
theorem B1105811 : Blo 734326 1105811 := bstep (se 1 (by rfl) ⟨829358, by rfl⟩ : syracuseStep 1105811 = 1658717) B1658717
theorem B1105841 : Blo 734326 1105841 := bstep (se 2 (by rfl) ⟨414690, by rfl⟩ : syracuseStep 1105841 = 829381) B829381
theorem B1105859 : Blo 734326 1105859 := bstep (se 1 (by rfl) ⟨829394, by rfl⟩ : syracuseStep 1105859 = 1658789) B1658789
theorem B1859537 : Blo 734326 1859537 := bstep (se 2 (by rfl) ⟨697326, by rfl⟩ : syracuseStep 1859537 = 1394653) B1394653
theorem B1105889 : Blo 734326 1105889 := bstep (se 2 (by rfl) ⟨414708, by rfl⟩ : syracuseStep 1105889 = 829417) B829417
theorem B1105907 : Blo 734326 1105907 := bstep (se 1 (by rfl) ⟨829430, by rfl⟩ : syracuseStep 1105907 = 1658861) B1658861
theorem B1105937 : Blo 734326 1105937 := bstep (se 2 (by rfl) ⟨414726, by rfl⟩ : syracuseStep 1105937 = 829453) B829453
theorem B1105955 : Blo 734326 1105955 := bstep (se 1 (by rfl) ⟨829466, by rfl⟩ : syracuseStep 1105955 = 1658933) B1658933
theorem B1105985 : Blo 734326 1105985 := bstep (se 2 (by rfl) ⟨414744, by rfl⟩ : syracuseStep 1105985 = 829489) B829489
theorem B1106003 : Blo 734326 1106003 := bstep (se 1 (by rfl) ⟨829502, by rfl⟩ : syracuseStep 1106003 = 1659005) B1659005
theorem B1106033 : Blo 734326 1106033 := bstep (se 2 (by rfl) ⟨414762, by rfl⟩ : syracuseStep 1106033 = 829525) B829525
theorem B1106051 : Blo 734326 1106051 := bstep (se 1 (by rfl) ⟨829538, by rfl⟩ : syracuseStep 1106051 = 1659077) B1659077
theorem B1106081 : Blo 734326 1106081 := bstep (se 2 (by rfl) ⟨414780, by rfl⟩ : syracuseStep 1106081 = 829561) B829561
theorem B1106099 : Blo 734326 1106099 := bstep (se 1 (by rfl) ⟨829574, by rfl⟩ : syracuseStep 1106099 = 1659149) B1659149
theorem B1106129 : Blo 734326 1106129 := bstep (se 2 (by rfl) ⟨414798, by rfl⟩ : syracuseStep 1106129 = 829597) B829597
theorem B1106147 : Blo 734326 1106147 := bstep (se 1 (by rfl) ⟨829610, by rfl⟩ : syracuseStep 1106147 = 1659221) B1659221
theorem B1106177 : Blo 734326 1106177 := bstep (se 2 (by rfl) ⟨414816, by rfl⟩ : syracuseStep 1106177 = 829633) B829633
theorem B1106195 : Blo 734326 1106195 := bstep (se 1 (by rfl) ⟨829646, by rfl⟩ : syracuseStep 1106195 = 1659293) B1659293
theorem B1106225 : Blo 734326 1106225 := bstep (se 2 (by rfl) ⟨414834, by rfl⟩ : syracuseStep 1106225 = 829669) B829669
theorem B1106243 : Blo 734326 1106243 := bstep (se 1 (by rfl) ⟨829682, by rfl⟩ : syracuseStep 1106243 = 1659365) B1659365
theorem B1106273 : Blo 734326 1106273 := bstep (se 2 (by rfl) ⟨414852, by rfl⟩ : syracuseStep 1106273 = 829705) B829705
theorem B2482541 : Blo 734326 2482541 := bstep (se 3 (by rfl) ⟨465476, by rfl⟩ : syracuseStep 2482541 = 930953) B930953
theorem B1106291 : Blo 734326 1106291 := bstep (se 1 (by rfl) ⟨829718, by rfl⟩ : syracuseStep 1106291 = 1659437) B1659437
theorem B1106321 : Blo 734326 1106321 := bstep (se 2 (by rfl) ⟨414870, by rfl⟩ : syracuseStep 1106321 = 829741) B829741
theorem B2482595 : Blo 734326 2482595 := bstep (se 1 (by rfl) ⟨1861946, by rfl⟩ : syracuseStep 2482595 = 3723893) B3723893
theorem B1106339 : Blo 734326 1106339 := bstep (se 1 (by rfl) ⟨829754, by rfl⟩ : syracuseStep 1106339 = 1659509) B1659509
theorem B8511925 : Blo 734326 8511925 := bstep (se 5 (by rfl) ⟨398996, by rfl⟩ : syracuseStep 8511925 = 797993) B797993
theorem B1106369 : Blo 734326 1106369 := bstep (se 2 (by rfl) ⟨414888, by rfl⟩ : syracuseStep 1106369 = 829777) B829777
theorem B1106387 : Blo 734326 1106387 := bstep (se 1 (by rfl) ⟨829790, by rfl⟩ : syracuseStep 1106387 = 1659581) B1659581
theorem B1106417 : Blo 734326 1106417 := bstep (se 2 (by rfl) ⟨414906, by rfl⟩ : syracuseStep 1106417 = 829813) B829813
theorem B1106435 : Blo 734326 1106435 := bstep (se 1 (by rfl) ⟨829826, by rfl⟩ : syracuseStep 1106435 = 1659653) B1659653
theorem B1106465 : Blo 734326 1106465 := bstep (se 2 (by rfl) ⟨414924, by rfl⟩ : syracuseStep 1106465 = 829849) B829849
theorem B1106483 : Blo 734326 1106483 := bstep (se 1 (by rfl) ⟨829862, by rfl⟩ : syracuseStep 1106483 = 1659725) B1659725
theorem B1106513 : Blo 734326 1106513 := bstep (se 2 (by rfl) ⟨414942, by rfl⟩ : syracuseStep 1106513 = 829885) B829885
theorem B1106531 : Blo 734326 1106531 := bstep (se 1 (by rfl) ⟨829898, by rfl⟩ : syracuseStep 1106531 = 1659797) B1659797
theorem B1401457 : Blo 734326 1401457 := bstep (se 2 (by rfl) ⟨525546, by rfl⟩ : syracuseStep 1401457 = 1051093) B1051093
theorem B1106561 : Blo 734326 1106561 := bstep (se 2 (by rfl) ⟨414960, by rfl⟩ : syracuseStep 1106561 = 829921) B829921
theorem B1106579 : Blo 734326 1106579 := bstep (se 1 (by rfl) ⟨829934, by rfl⟩ : syracuseStep 1106579 = 1659869) B1659869
theorem B2482865 : Blo 734326 2482865 := bstep (se 2 (by rfl) ⟨931074, by rfl⟩ : syracuseStep 2482865 = 1862149) B1862149
theorem B1106609 : Blo 734326 1106609 := bstep (se 2 (by rfl) ⟨414978, by rfl⟩ : syracuseStep 1106609 = 829957) B829957
theorem B1106627 : Blo 734326 1106627 := bstep (se 1 (by rfl) ⟨829970, by rfl⟩ : syracuseStep 1106627 = 1659941) B1659941
theorem B4186829 : Blo 734326 4186829 := bstep (se 3 (by rfl) ⟨785030, by rfl⟩ : syracuseStep 4186829 = 1570061) B1570061
theorem B1106657 : Blo 734326 1106657 := bstep (se 2 (by rfl) ⟨414996, by rfl⟩ : syracuseStep 1106657 = 829993) B829993
theorem B1106675 : Blo 734326 1106675 := bstep (se 1 (by rfl) ⟨830006, by rfl⟩ : syracuseStep 1106675 = 1660013) B1660013
theorem B1106705 : Blo 734326 1106705 := bstep (se 2 (by rfl) ⟨415014, by rfl⟩ : syracuseStep 1106705 = 830029) B830029
theorem B1401617 : Blo 734326 1401617 := bstep (se 2 (by rfl) ⟨525606, by rfl⟩ : syracuseStep 1401617 = 1051213) B1051213
theorem B1106723 : Blo 734326 1106723 := bstep (se 1 (by rfl) ⟨830042, by rfl⟩ : syracuseStep 1106723 = 1660085) B1660085
theorem B1106753 : Blo 734326 1106753 := bstep (se 2 (by rfl) ⟨415032, by rfl⟩ : syracuseStep 1106753 = 830065) B830065
theorem B1106771 : Blo 734326 1106771 := bstep (se 1 (by rfl) ⟨830078, by rfl⟩ : syracuseStep 1106771 = 1660157) B1660157
theorem B1106801 : Blo 734326 1106801 := bstep (se 2 (by rfl) ⟨415050, by rfl⟩ : syracuseStep 1106801 = 830101) B830101
theorem B1106819 : Blo 734326 1106819 := bstep (se 1 (by rfl) ⟨830114, by rfl⟩ : syracuseStep 1106819 = 1660229) B1660229
theorem B1106849 : Blo 734326 1106849 := bstep (se 2 (by rfl) ⟨415068, by rfl⟩ : syracuseStep 1106849 = 830137) B830137
theorem B1860529 : Blo 734326 1860529 := bstep (se 2 (by rfl) ⟨697698, by rfl⟩ : syracuseStep 1860529 = 1395397) B1395397
theorem B1106867 : Blo 734326 1106867 := bstep (se 1 (by rfl) ⟨830150, by rfl⟩ : syracuseStep 1106867 = 1660301) B1660301
theorem B1106897 : Blo 734326 1106897 := bstep (se 2 (by rfl) ⟨415086, by rfl⟩ : syracuseStep 1106897 = 830173) B830173
theorem B1106915 : Blo 734326 1106915 := bstep (se 1 (by rfl) ⟨830186, by rfl⟩ : syracuseStep 1106915 = 1660373) B1660373
theorem B1106945 : Blo 734326 1106945 := bstep (se 2 (by rfl) ⟨415104, by rfl⟩ : syracuseStep 1106945 = 830209) B830209
theorem B1106963 : Blo 734326 1106963 := bstep (se 1 (by rfl) ⟨830222, by rfl⟩ : syracuseStep 1106963 = 1660445) B1660445
theorem B1106993 : Blo 734326 1106993 := bstep (se 2 (by rfl) ⟨415122, by rfl⟩ : syracuseStep 1106993 = 830245) B830245
theorem B1107011 : Blo 734326 1107011 := bstep (se 1 (by rfl) ⟨830258, by rfl⟩ : syracuseStep 1107011 = 1660517) B1660517
theorem B1107041 : Blo 734326 1107041 := bstep (se 2 (by rfl) ⟨415140, by rfl⟩ : syracuseStep 1107041 = 830281) B830281
theorem B7169123 : Blo 734326 7169123 := bstep (se 1 (by rfl) ⟨5376842, by rfl⟩ : syracuseStep 7169123 = 10753685) B10753685
theorem B1107059 : Blo 734326 1107059 := bstep (se 1 (by rfl) ⟨830294, by rfl⟩ : syracuseStep 1107059 = 1660589) B1660589
theorem B1107089 : Blo 734326 1107089 := bstep (se 2 (by rfl) ⟨415158, by rfl⟩ : syracuseStep 1107089 = 830317) B830317
theorem B1107107 : Blo 734326 1107107 := bstep (se 1 (by rfl) ⟨830330, by rfl⟩ : syracuseStep 1107107 = 1660661) B1660661
theorem B1107137 : Blo 734326 1107137 := bstep (se 2 (by rfl) ⟨415176, by rfl⟩ : syracuseStep 1107137 = 830353) B830353
theorem B1860803 : Blo 734326 1860803 := bstep (se 1 (by rfl) ⟨1395602, by rfl⟩ : syracuseStep 1860803 = 2791205) B2791205
theorem B10085573 : Blo 734326 10085573 := bstep (se 4 (by rfl) ⟨945522, by rfl⟩ : syracuseStep 10085573 = 1891045) B1891045
theorem B2483405 : Blo 734326 2483405 := bstep (se 3 (by rfl) ⟨465638, by rfl⟩ : syracuseStep 2483405 = 931277) B931277
theorem B1107155 : Blo 734326 1107155 := bstep (se 1 (by rfl) ⟨830366, by rfl⟩ : syracuseStep 1107155 = 1660733) B1660733
theorem B1008865 : Blo 734326 1008865 := bstep (se 2 (by rfl) ⟨378324, by rfl⟩ : syracuseStep 1008865 = 756649) B756649
theorem B746723 : Blo 734326 746723 := bstep (se 1 (by rfl) ⟨560042, by rfl⟩ : syracuseStep 746723 = 1120085) B1120085
theorem B1107185 : Blo 734326 1107185 := bstep (se 2 (by rfl) ⟨415194, by rfl⟩ : syracuseStep 1107185 = 830389) B830389
theorem B2483459 : Blo 734326 2483459 := bstep (se 1 (by rfl) ⟨1862594, by rfl⟩ : syracuseStep 2483459 = 3725189) B3725189
theorem B1107203 : Blo 734326 1107203 := bstep (se 1 (by rfl) ⟨830402, by rfl⟩ : syracuseStep 1107203 = 1660805) B1660805
theorem B1991953 : Blo 734326 1991953 := bstep (se 2 (by rfl) ⟨746982, by rfl⟩ : syracuseStep 1991953 = 1493965) B1493965
theorem B1107233 : Blo 734326 1107233 := bstep (se 2 (by rfl) ⟨415212, by rfl⟩ : syracuseStep 1107233 = 830425) B830425
theorem B1107251 : Blo 734326 1107251 := bstep (se 1 (by rfl) ⟨830438, by rfl⟩ : syracuseStep 1107251 = 1660877) B1660877
theorem B1107281 : Blo 734326 1107281 := bstep (se 2 (by rfl) ⟨415230, by rfl⟩ : syracuseStep 1107281 = 830461) B830461
theorem B1107299 : Blo 734326 1107299 := bstep (se 1 (by rfl) ⟨830474, by rfl⟩ : syracuseStep 1107299 = 1660949) B1660949
theorem B3728753 : Blo 734326 3728753 := bstep (se 2 (by rfl) ⟨1398282, by rfl⟩ : syracuseStep 3728753 = 2796565) B2796565
theorem B1107329 : Blo 734326 1107329 := bstep (se 2 (by rfl) ⟨415248, by rfl⟩ : syracuseStep 1107329 = 830497) B830497
theorem B1860995 : Blo 734326 1860995 := bstep (se 1 (by rfl) ⟨1395746, by rfl⟩ : syracuseStep 1860995 = 2791493) B2791493
theorem B1107347 : Blo 734326 1107347 := bstep (se 1 (by rfl) ⟨830510, by rfl⟩ : syracuseStep 1107347 = 1661021) B1661021
theorem B1107377 : Blo 734326 1107377 := bstep (se 2 (by rfl) ⟨415266, by rfl⟩ : syracuseStep 1107377 = 830533) B830533
theorem B1107395 : Blo 734326 1107395 := bstep (se 1 (by rfl) ⟨830546, by rfl⟩ : syracuseStep 1107395 = 1661093) B1661093
theorem B4711877 : Blo 734326 4711877 := bstep (se 4 (by rfl) ⟨441738, by rfl⟩ : syracuseStep 4711877 = 883477) B883477
theorem B1107425 : Blo 734326 1107425 := bstep (se 2 (by rfl) ⟨415284, by rfl⟩ : syracuseStep 1107425 = 830569) B830569
theorem B1107443 : Blo 734326 1107443 := bstep (se 1 (by rfl) ⟨830582, by rfl⟩ : syracuseStep 1107443 = 1661165) B1661165
theorem B2483729 : Blo 734326 2483729 := bstep (se 2 (by rfl) ⟨931398, by rfl⟩ : syracuseStep 2483729 = 1862797) B1862797
theorem B1107473 : Blo 734326 1107473 := bstep (se 2 (by rfl) ⟨415302, by rfl⟩ : syracuseStep 1107473 = 830605) B830605
theorem B2418275 : Blo 734326 2418275 := bstep (se 1 (by rfl) ⟨1813706, by rfl⟩ : syracuseStep 2418275 = 3627413) B3627413
theorem B3139235 : Blo 734326 3139235 := bstep (se 1 (by rfl) ⟨2354426, by rfl⟩ : syracuseStep 3139235 = 4708853) B4708853
theorem B2484269 : Blo 734326 2484269 := bstep (se 3 (by rfl) ⟨465800, by rfl⟩ : syracuseStep 2484269 = 931601) B931601
theorem B2484323 : Blo 734326 2484323 := bstep (se 1 (by rfl) ⟨1863242, by rfl⟩ : syracuseStep 2484323 = 3726485) B3726485
theorem B1239185 : Blo 734326 1239185 := bstep (se 2 (by rfl) ⟨464694, by rfl⟩ : syracuseStep 1239185 = 929389) B929389
theorem B2091217 : Blo 734326 2091217 := bstep (se 2 (by rfl) ⟨784206, by rfl⟩ : syracuseStep 2091217 = 1568413) B1568413
theorem B1009873 : Blo 734326 1009873 := bstep (se 2 (by rfl) ⟨378702, by rfl⟩ : syracuseStep 1009873 = 757405) B757405
theorem B1239313 : Blo 734326 1239313 := bstep (se 2 (by rfl) ⟨464742, by rfl⟩ : syracuseStep 1239313 = 929485) B929485
theorem B1861937 : Blo 734326 1861937 := bstep (se 2 (by rfl) ⟨698226, by rfl⟩ : syracuseStep 1861937 = 1396453) B1396453
theorem B1239347 : Blo 734326 1239347 := bstep (se 1 (by rfl) ⟨929510, by rfl⟩ : syracuseStep 1239347 = 1859021) B1859021
theorem B1861987 : Blo 734326 1861987 := bstep (se 1 (by rfl) ⟨1396490, by rfl⟩ : syracuseStep 1861987 = 2792981) B2792981
theorem B2484593 : Blo 734326 2484593 := bstep (se 2 (by rfl) ⟨931722, by rfl⟩ : syracuseStep 2484593 = 1863445) B1863445
theorem B9431437 : Blo 734326 9431437 := bstep (se 3 (by rfl) ⟨1768394, by rfl⟩ : syracuseStep 9431437 = 3536789) B3536789
theorem B1239475 : Blo 734326 1239475 := bstep (se 1 (by rfl) ⟨929606, by rfl⟩ : syracuseStep 1239475 = 1859213) B1859213
theorem B2091491 : Blo 734326 2091491 := bstep (se 1 (by rfl) ⟨1568618, by rfl⟩ : syracuseStep 2091491 = 3137237) B3137237
theorem B1993187 : Blo 734326 1993187 := bstep (se 1 (by rfl) ⟨1494890, by rfl⟩ : syracuseStep 1993187 = 2989781) B2989781
theorem B1862129 : Blo 734326 1862129 := bstep (se 2 (by rfl) ⟨698298, by rfl⟩ : syracuseStep 1862129 = 1396597) B1396597
theorem B1239617 : Blo 734326 1239617 := bstep (se 2 (by rfl) ⟨464856, by rfl⟩ : syracuseStep 1239617 = 929713) B929713
theorem B2091683 : Blo 734326 2091683 := bstep (se 1 (by rfl) ⟨1568762, by rfl⟩ : syracuseStep 2091683 = 3137525) B3137525
theorem B1239745 : Blo 734326 1239745 := bstep (se 2 (by rfl) ⟨464904, by rfl⟩ : syracuseStep 1239745 = 929809) B929809
theorem B1239779 : Blo 734326 1239779 := bstep (se 1 (by rfl) ⟨929834, by rfl⟩ : syracuseStep 1239779 = 1859669) B1859669
theorem B3730211 : Blo 734326 3730211 := bstep (se 1 (by rfl) ⟨2797658, by rfl⟩ : syracuseStep 3730211 = 5595317) B5595317
theorem B1239907 : Blo 734326 1239907 := bstep (se 1 (by rfl) ⟨929930, by rfl⟩ : syracuseStep 1239907 = 1859861) B1859861
theorem B2485133 : Blo 734326 2485133 := bstep (se 3 (by rfl) ⟨465962, by rfl⟩ : syracuseStep 2485133 = 931925) B931925
theorem B2354093 : Blo 734326 2354093 := bstep (se 3 (by rfl) ⟨441392, by rfl⟩ : syracuseStep 2354093 = 882785) B882785
theorem B2485187 : Blo 734326 2485187 := bstep (se 1 (by rfl) ⟨1863890, by rfl⟩ : syracuseStep 2485187 = 3727781) B3727781
theorem B1240049 : Blo 734326 1240049 := bstep (se 2 (by rfl) ⟨465018, by rfl⟩ : syracuseStep 1240049 = 930037) B930037
theorem B1240177 : Blo 734326 1240177 := bstep (se 2 (by rfl) ⟨465066, by rfl⟩ : syracuseStep 1240177 = 930133) B930133
theorem B1240211 : Blo 734326 1240211 := bstep (se 1 (by rfl) ⟨930158, by rfl⟩ : syracuseStep 1240211 = 1860317) B1860317
theorem B2485457 : Blo 734326 2485457 := bstep (se 2 (by rfl) ⟨932046, by rfl⟩ : syracuseStep 2485457 = 1864093) B1864093
theorem B1240339 : Blo 734326 1240339 := bstep (se 1 (by rfl) ⟨930254, by rfl⟩ : syracuseStep 1240339 = 1860509) B1860509
theorem B4484429 : Blo 734326 4484429 := bstep (se 3 (by rfl) ⟨840830, by rfl⟩ : syracuseStep 4484429 = 1681661) B1681661
theorem B3140977 : Blo 734326 3140977 := bstep (se 2 (by rfl) ⟨1177866, by rfl⟩ : syracuseStep 3140977 = 2355733) B2355733
theorem B1240481 : Blo 734326 1240481 := bstep (se 2 (by rfl) ⟨465180, by rfl⟩ : syracuseStep 1240481 = 930361) B930361
theorem B2092493 : Blo 734326 2092493 := bstep (se 3 (by rfl) ⟨392342, by rfl⟩ : syracuseStep 2092493 = 784685) B784685
theorem B1863121 : Blo 734326 1863121 := bstep (se 2 (by rfl) ⟨698670, by rfl⟩ : syracuseStep 1863121 = 1397341) B1397341
theorem B1240609 : Blo 734326 1240609 := bstep (se 2 (by rfl) ⟨465228, by rfl⟩ : syracuseStep 1240609 = 930457) B930457
theorem B4189745 : Blo 734326 4189745 := bstep (se 2 (by rfl) ⟨1571154, by rfl⟩ : syracuseStep 4189745 = 3142309) B3142309
theorem B1240643 : Blo 734326 1240643 := bstep (se 1 (by rfl) ⟨930482, by rfl⟩ : syracuseStep 1240643 = 1860965) B1860965
theorem B3731021 : Blo 734326 3731021 := bstep (se 3 (by rfl) ⟨699566, by rfl⟩ : syracuseStep 3731021 = 1399133) B1399133
theorem B2092675 : Blo 734326 2092675 := bstep (se 1 (by rfl) ⟨1569506, by rfl⟩ : syracuseStep 2092675 = 3139013) B3139013
theorem B1240771 : Blo 734326 1240771 := bstep (se 1 (by rfl) ⟨930578, by rfl⟩ : syracuseStep 1240771 = 1861157) B1861157
theorem B9432773 : Blo 734326 9432773 := bstep (se 4 (by rfl) ⟨884322, by rfl⟩ : syracuseStep 9432773 = 1768645) B1768645
theorem B1863395 : Blo 734326 1863395 := bstep (se 1 (by rfl) ⟨1397546, by rfl⟩ : syracuseStep 1863395 = 2795093) B2795093
theorem B2485997 : Blo 734326 2485997 := bstep (se 3 (by rfl) ⟨466124, by rfl⟩ : syracuseStep 2485997 = 932249) B932249
theorem B2486051 : Blo 734326 2486051 := bstep (se 1 (by rfl) ⟨1864538, by rfl⟩ : syracuseStep 2486051 = 3729077) B3729077
theorem B2354989 : Blo 734326 2354989 := bstep (se 3 (by rfl) ⟨441560, by rfl⟩ : syracuseStep 2354989 = 883121) B883121
theorem B1240913 : Blo 734326 1240913 := bstep (se 2 (by rfl) ⟨465342, by rfl⟩ : syracuseStep 1240913 = 930685) B930685
theorem B1863587 : Blo 734326 1863587 := bstep (se 1 (by rfl) ⟨1397690, by rfl⟩ : syracuseStep 1863587 = 2795381) B2795381
theorem B1241041 : Blo 734326 1241041 := bstep (se 2 (by rfl) ⟨465390, by rfl⟩ : syracuseStep 1241041 = 930781) B930781
theorem B1241075 : Blo 734326 1241075 := bstep (se 1 (by rfl) ⟨930806, by rfl⟩ : syracuseStep 1241075 = 1861613) B1861613
theorem B2486321 : Blo 734326 2486321 := bstep (se 2 (by rfl) ⟨932370, by rfl⟩ : syracuseStep 2486321 = 1864741) B1864741
theorem B2093165 : Blo 734326 2093165 := bstep (se 3 (by rfl) ⟨392468, by rfl⟩ : syracuseStep 2093165 = 784937) B784937
theorem B1241203 : Blo 734326 1241203 := bstep (se 1 (by rfl) ⟨930902, by rfl⟩ : syracuseStep 1241203 = 1861805) B1861805
theorem B1568899 : Blo 734326 1568899 := bstep (se 1 (by rfl) ⟨1176674, by rfl⟩ : syracuseStep 1568899 = 2353349) B2353349
theorem B1241345 : Blo 734326 1241345 := bstep (se 2 (by rfl) ⟨465504, by rfl⟩ : syracuseStep 1241345 = 931009) B931009
theorem B1241473 : Blo 734326 1241473 := bstep (se 2 (by rfl) ⟨465552, by rfl⟩ : syracuseStep 1241473 = 931105) B931105
theorem B1241507 : Blo 734326 1241507 := bstep (se 1 (by rfl) ⟨931130, by rfl⟩ : syracuseStep 1241507 = 1862261) B1862261
theorem B1569233 : Blo 734326 1569233 := bstep (se 2 (by rfl) ⟨588462, by rfl⟩ : syracuseStep 1569233 = 1176925) B1176925
theorem B1241635 : Blo 734326 1241635 := bstep (se 1 (by rfl) ⟨931226, by rfl⟩ : syracuseStep 1241635 = 1862453) B1862453
theorem B2486861 : Blo 734326 2486861 := bstep (se 3 (by rfl) ⟨466286, by rfl⟩ : syracuseStep 2486861 = 932573) B932573
theorem B2486915 : Blo 734326 2486915 := bstep (se 1 (by rfl) ⟨1865186, by rfl⟩ : syracuseStep 2486915 = 3730373) B3730373
theorem B1241777 : Blo 734326 1241777 := bstep (se 2 (by rfl) ⟨465666, by rfl⟩ : syracuseStep 1241777 = 931333) B931333
theorem B1241905 : Blo 734326 1241905 := bstep (se 2 (by rfl) ⟨465714, by rfl⟩ : syracuseStep 1241905 = 931429) B931429
theorem B1995587 : Blo 734326 1995587 := bstep (se 1 (by rfl) ⟨1496690, by rfl⟩ : syracuseStep 1995587 = 2993381) B2993381
theorem B1864529 : Blo 734326 1864529 := bstep (se 2 (by rfl) ⟨699198, by rfl⟩ : syracuseStep 1864529 = 1398397) B1398397
theorem B1241939 : Blo 734326 1241939 := bstep (se 1 (by rfl) ⟨931454, by rfl⟩ : syracuseStep 1241939 = 1862909) B1862909
theorem B1176419 : Blo 734326 1176419 := bstep (se 1 (by rfl) ⟨882314, by rfl⟩ : syracuseStep 1176419 = 1764629) B1764629
theorem B2356067 : Blo 734326 2356067 := bstep (se 1 (by rfl) ⟨1767050, by rfl⟩ : syracuseStep 2356067 = 3534101) B3534101
theorem B1864579 : Blo 734326 1864579 := bstep (se 1 (by rfl) ⟨1398434, by rfl⟩ : syracuseStep 1864579 = 2796869) B2796869
theorem B2487185 : Blo 734326 2487185 := bstep (se 2 (by rfl) ⟨932694, by rfl⟩ : syracuseStep 2487185 = 1865389) B1865389
theorem B1242067 : Blo 734326 1242067 := bstep (se 1 (by rfl) ⟨931550, by rfl⟩ : syracuseStep 1242067 = 1863101) B1863101
theorem B1176547 : Blo 734326 1176547 := bstep (se 1 (by rfl) ⟨882410, by rfl⟩ : syracuseStep 1176547 = 1764821) B1764821
theorem B4191203 : Blo 734326 4191203 := bstep (se 1 (by rfl) ⟨3143402, by rfl⟩ : syracuseStep 4191203 = 6286805) B6286805
theorem B1864721 : Blo 734326 1864721 := bstep (se 2 (by rfl) ⟨699270, by rfl⟩ : syracuseStep 1864721 = 1398541) B1398541
theorem B1242209 : Blo 734326 1242209 := bstep (se 2 (by rfl) ⟨465828, by rfl⟩ : syracuseStep 1242209 = 931657) B931657
theorem B1242337 : Blo 734326 1242337 := bstep (se 2 (by rfl) ⟨465876, by rfl⟩ : syracuseStep 1242337 = 931753) B931753
theorem B1766627 : Blo 734326 1766627 := bstep (se 1 (by rfl) ⟨1324970, by rfl⟩ : syracuseStep 1766627 = 2649941) B2649941
theorem B3536099 : Blo 734326 3536099 := bstep (se 1 (by rfl) ⟨2652074, by rfl⟩ : syracuseStep 3536099 = 5304149) B5304149
theorem B1242371 : Blo 734326 1242371 := bstep (se 1 (by rfl) ⟨931778, by rfl⟩ : syracuseStep 1242371 = 1863557) B1863557
theorem B2094349 : Blo 734326 2094349 := bstep (se 3 (by rfl) ⟨392690, by rfl⟩ : syracuseStep 2094349 = 785381) B785381
theorem B3142925 : Blo 734326 3142925 := bstep (se 3 (by rfl) ⟨589298, by rfl⟩ : syracuseStep 3142925 = 1178597) B1178597
theorem B1176931 : Blo 734326 1176931 := bstep (se 1 (by rfl) ⟨882698, by rfl⟩ : syracuseStep 1176931 = 1765397) B1765397
theorem B1242499 : Blo 734326 1242499 := bstep (se 1 (by rfl) ⟨931874, by rfl⟩ : syracuseStep 1242499 = 1863749) B1863749
theorem B1766819 : Blo 734326 1766819 := bstep (se 1 (by rfl) ⟨1325114, by rfl⟩ : syracuseStep 1766819 = 2650229) B2650229
theorem B2651555 : Blo 734326 2651555 := bstep (se 1 (by rfl) ⟨1988666, by rfl⟩ : syracuseStep 2651555 = 3977333) B3977333
theorem B2487725 : Blo 734326 2487725 := bstep (se 3 (by rfl) ⟨466448, by rfl⟩ : syracuseStep 2487725 = 932897) B932897
theorem B2487779 : Blo 734326 2487779 := bstep (se 1 (by rfl) ⟨1865834, by rfl⟩ : syracuseStep 2487779 = 3731669) B3731669
theorem B2356721 : Blo 734326 2356721 := bstep (se 2 (by rfl) ⟨883770, by rfl⟩ : syracuseStep 2356721 = 1767541) B1767541
theorem B3536369 : Blo 734326 3536369 := bstep (se 2 (by rfl) ⟨1326138, by rfl⟩ : syracuseStep 3536369 = 2652277) B2652277
theorem B10057229 : Blo 734326 10057229 := bstep (se 3 (by rfl) ⟨1885730, by rfl⟩ : syracuseStep 10057229 = 3771461) B3771461
theorem B1242641 : Blo 734326 1242641 := bstep (se 2 (by rfl) ⟨465990, by rfl⟩ : syracuseStep 1242641 = 931981) B931981
theorem B1078849 : Blo 734326 1078849 := bstep (se 2 (by rfl) ⟨404568, by rfl⟩ : syracuseStep 1078849 = 809137) B809137
theorem B1046081 : Blo 734326 1046081 := bstep (se 2 (by rfl) ⟨392280, by rfl⟩ : syracuseStep 1046081 = 784561) B784561
theorem B1177187 : Blo 734326 1177187 := bstep (se 1 (by rfl) ⟨882890, by rfl⟩ : syracuseStep 1177187 = 1765781) B1765781
theorem B1570403 : Blo 734326 1570403 := bstep (se 1 (by rfl) ⟨1177802, by rfl⟩ : syracuseStep 1570403 = 2355605) B2355605
theorem B1242769 : Blo 734326 1242769 := bstep (se 2 (by rfl) ⟨466038, by rfl⟩ : syracuseStep 1242769 = 932077) B932077
theorem B1767089 : Blo 734326 1767089 := bstep (se 2 (by rfl) ⟨662658, by rfl⟩ : syracuseStep 1767089 = 1325317) B1325317
theorem B3536561 : Blo 734326 3536561 := bstep (se 2 (by rfl) ⟨1326210, by rfl⟩ : syracuseStep 3536561 = 2652421) B2652421
theorem B1242803 : Blo 734326 1242803 := bstep (se 1 (by rfl) ⟨932102, by rfl⟩ : syracuseStep 1242803 = 1864205) B1864205
theorem B2488049 : Blo 734326 2488049 := bstep (se 2 (by rfl) ⟨933018, by rfl⟩ : syracuseStep 2488049 = 1866037) B1866037
theorem B2520877 : Blo 734326 2520877 := bstep (se 3 (by rfl) ⟨472664, by rfl⟩ : syracuseStep 2520877 = 945329) B945329
theorem B1242931 : Blo 734326 1242931 := bstep (se 1 (by rfl) ⟨932198, by rfl⟩ : syracuseStep 1242931 = 1864397) B1864397
theorem B6289265 : Blo 734326 6289265 := bstep (se 2 (by rfl) ⟨2358474, by rfl⟩ : syracuseStep 6289265 = 4716949) B4716949
theorem B1243073 : Blo 734326 1243073 := bstep (se 2 (by rfl) ⟨466152, by rfl⟩ : syracuseStep 1243073 = 932305) B932305
theorem B2652131 : Blo 734326 2652131 := bstep (se 1 (by rfl) ⟨1989098, by rfl⟩ : syracuseStep 2652131 = 3978197) B3978197
theorem B1865713 : Blo 734326 1865713 := bstep (se 2 (by rfl) ⟨699642, by rfl⟩ : syracuseStep 1865713 = 1399285) B1399285
theorem B2488333 : Blo 734326 2488333 := bstep (se 3 (by rfl) ⟨466562, by rfl⟩ : syracuseStep 2488333 = 933125) B933125
theorem B1177649 : Blo 734326 1177649 := bstep (se 2 (by rfl) ⟨441618, by rfl⟩ : syracuseStep 1177649 = 883237) B883237
theorem B1767473 : Blo 734326 1767473 := bstep (se 2 (by rfl) ⟨662802, by rfl⟩ : syracuseStep 1767473 = 1325605) B1325605
theorem B3536945 : Blo 734326 3536945 := bstep (se 2 (by rfl) ⟨1326354, by rfl⟩ : syracuseStep 3536945 = 2652709) B2652709
theorem B1243201 : Blo 734326 1243201 := bstep (se 2 (by rfl) ⟨466200, by rfl⟩ : syracuseStep 1243201 = 932401) B932401
theorem B1046611 : Blo 734326 1046611 := bstep (se 1 (by rfl) ⟨784958, by rfl⟩ : syracuseStep 1046611 = 1569917) B1569917
theorem B1243235 : Blo 734326 1243235 := bstep (se 1 (by rfl) ⟨932426, by rfl⟩ : syracuseStep 1243235 = 1864853) B1864853
theorem B1177745 : Blo 734326 1177745 := bstep (se 2 (by rfl) ⟨441654, by rfl⟩ : syracuseStep 1177745 = 883309) B883309
theorem B1177777 : Blo 734326 1177777 := bstep (se 2 (by rfl) ⟨441666, by rfl⟩ : syracuseStep 1177777 = 883333) B883333
theorem B1243363 : Blo 734326 1243363 := bstep (se 1 (by rfl) ⟨932522, by rfl⟩ : syracuseStep 1243363 = 1865045) B1865045
theorem B1865987 : Blo 734326 1865987 := bstep (se 1 (by rfl) ⟨1399490, by rfl⟩ : syracuseStep 1865987 = 2798981) B2798981
theorem B2488589 : Blo 734326 2488589 := bstep (se 3 (by rfl) ⟨466610, by rfl⟩ : syracuseStep 2488589 = 933221) B933221
theorem B2095409 : Blo 734326 2095409 := bstep (se 2 (by rfl) ⟨785778, by rfl⟩ : syracuseStep 2095409 = 1571557) B1571557
theorem B2488643 : Blo 734326 2488643 := bstep (se 1 (by rfl) ⟨1866482, by rfl⟩ : syracuseStep 2488643 = 3732965) B3732965
theorem B5601635 : Blo 734326 5601635 := bstep (se 1 (by rfl) ⟨4201226, by rfl⟩ : syracuseStep 5601635 = 8402453) B8402453
theorem B1243505 : Blo 734326 1243505 := bstep (se 2 (by rfl) ⟨466314, by rfl⟩ : syracuseStep 1243505 = 932629) B932629
theorem B2128259 : Blo 734326 2128259 := bstep (se 1 (by rfl) ⟨1596194, by rfl⟩ : syracuseStep 2128259 = 3192389) B3192389
theorem B1046947 : Blo 734326 1046947 := bstep (se 1 (by rfl) ⟨785210, by rfl⟩ : syracuseStep 1046947 = 1570421) B1570421
theorem B3733937 : Blo 734326 3733937 := bstep (se 2 (by rfl) ⟨1400226, by rfl⟩ : syracuseStep 3733937 = 2800453) B2800453
theorem B1866179 : Blo 734326 1866179 := bstep (se 1 (by rfl) ⟨1399634, by rfl⟩ : syracuseStep 1866179 = 2799269) B2799269
theorem B1341937 : Blo 734326 1341937 := bstep (se 2 (by rfl) ⟨503226, by rfl⟩ : syracuseStep 1341937 = 1006453) B1006453
theorem B1243633 : Blo 734326 1243633 := bstep (se 2 (by rfl) ⟨466362, by rfl⟩ : syracuseStep 1243633 = 932725) B932725
theorem B1243667 : Blo 734326 1243667 := bstep (se 1 (by rfl) ⟨932750, by rfl⟩ : syracuseStep 1243667 = 1865501) B1865501
theorem B2488913 : Blo 734326 2488913 := bstep (se 2 (by rfl) ⟨933342, by rfl⟩ : syracuseStep 2488913 = 1866685) B1866685
theorem B1243795 : Blo 734326 1243795 := bstep (se 1 (by rfl) ⟨932846, by rfl⟩ : syracuseStep 1243795 = 1865693) B1865693
theorem B1243937 : Blo 734326 1243937 := bstep (se 2 (by rfl) ⟨466476, by rfl⟩ : syracuseStep 1243937 = 932953) B932953
theorem B1768241 : Blo 734326 1768241 := bstep (se 2 (by rfl) ⟨663090, by rfl⟩ : syracuseStep 1768241 = 1326181) B1326181
theorem B2358065 : Blo 734326 2358065 := bstep (se 2 (by rfl) ⟨884274, by rfl⟩ : syracuseStep 2358065 = 1768549) B1768549
theorem B12549005 : Blo 734326 12549005 := bstep (se 3 (by rfl) ⟨2352938, by rfl⟩ : syracuseStep 12549005 = 4705877) B4705877
theorem B1244065 : Blo 734326 1244065 := bstep (se 2 (by rfl) ⟨466524, by rfl⟩ : syracuseStep 1244065 = 933049) B933049
theorem B1768387 : Blo 734326 1768387 := bstep (se 1 (by rfl) ⟨1326290, by rfl⟩ : syracuseStep 1768387 = 2652581) B2652581
theorem B1244099 : Blo 734326 1244099 := bstep (se 1 (by rfl) ⟨933074, by rfl⟩ : syracuseStep 1244099 = 1866149) B1866149
theorem B1047505 : Blo 734326 1047505 := bstep (se 2 (by rfl) ⟨392814, by rfl⟩ : syracuseStep 1047505 = 785629) B785629
theorem B2096081 : Blo 734326 2096081 := bstep (se 2 (by rfl) ⟨786030, by rfl⟩ : syracuseStep 2096081 = 1572061) B1572061
theorem B1047539 : Blo 734326 1047539 := bstep (se 1 (by rfl) ⟨785654, by rfl⟩ : syracuseStep 1047539 = 1571309) B1571309
theorem B1244227 : Blo 734326 1244227 := bstep (se 1 (by rfl) ⟨933170, by rfl⟩ : syracuseStep 1244227 = 1866341) B1866341
theorem B2489453 : Blo 734326 2489453 := bstep (se 3 (by rfl) ⟨466772, by rfl⟩ : syracuseStep 2489453 = 933545) B933545
theorem B2489507 : Blo 734326 2489507 := bstep (se 1 (by rfl) ⟨1867130, by rfl⟩ : syracuseStep 2489507 = 3734261) B3734261
theorem B1244369 : Blo 734326 1244369 := bstep (se 2 (by rfl) ⟨466638, by rfl⟩ : syracuseStep 1244369 = 933277) B933277
theorem B1244497 : Blo 734326 1244497 := bstep (se 2 (by rfl) ⟨466686, by rfl⟩ : syracuseStep 1244497 = 933373) B933373
theorem B1867121 : Blo 734326 1867121 := bstep (se 2 (by rfl) ⟨700170, by rfl⟩ : syracuseStep 1867121 = 1400341) B1400341
theorem B1244531 : Blo 734326 1244531 := bstep (se 1 (by rfl) ⟨933398, by rfl⟩ : syracuseStep 1244531 = 1866797) B1866797
theorem B1867171 : Blo 734326 1867171 := bstep (se 1 (by rfl) ⟨1400378, by rfl⟩ : syracuseStep 1867171 = 2800757) B2800757
theorem B2489777 : Blo 734326 2489777 := bstep (se 2 (by rfl) ⟨933666, by rfl⟩ : syracuseStep 2489777 = 1867333) B1867333
theorem B1244659 : Blo 734326 1244659 := bstep (se 1 (by rfl) ⟨933494, by rfl⟩ : syracuseStep 1244659 = 1866989) B1866989
theorem B1048097 : Blo 734326 1048097 := bstep (se 2 (by rfl) ⟨393036, by rfl⟩ : syracuseStep 1048097 = 786073) B786073
theorem B1867313 : Blo 734326 1867313 := bstep (se 2 (by rfl) ⟨700242, by rfl⟩ : syracuseStep 1867313 = 1400485) B1400485
theorem B1572419 : Blo 734326 1572419 := bstep (se 1 (by rfl) ⟨1179314, by rfl⟩ : syracuseStep 1572419 = 2358629) B2358629
theorem B4718179 : Blo 734326 4718179 := bstep (se 1 (by rfl) ⟨3538634, by rfl⟩ : syracuseStep 4718179 = 7077269) B7077269
theorem B1048177 : Blo 734326 1048177 := bstep (se 2 (by rfl) ⟨393066, by rfl⟩ : syracuseStep 1048177 = 786133) B786133
theorem B1244801 : Blo 734326 1244801 := bstep (se 2 (by rfl) ⟨466800, by rfl⟩ : syracuseStep 1244801 = 933601) B933601
theorem B2522819 : Blo 734326 2522819 := bstep (se 1 (by rfl) ⟨1892114, by rfl⟩ : syracuseStep 2522819 = 3784229) B3784229
theorem B2096867 : Blo 734326 2096867 := bstep (se 1 (by rfl) ⟨1572650, by rfl⟩ : syracuseStep 2096867 = 3145301) B3145301
theorem B884467 : Blo 734326 884467 := bstep (se 1 (by rfl) ⟨663350, by rfl⟩ : syracuseStep 884467 = 1326701) B1326701
theorem B1244929 : Blo 734326 1244929 := bstep (se 2 (by rfl) ⟨466848, by rfl⟩ : syracuseStep 1244929 = 933697) B933697
theorem B1244963 : Blo 734326 1244963 := bstep (se 1 (by rfl) ⟨933722, by rfl⟩ : syracuseStep 1244963 = 1867445) B1867445
theorem B1343281 : Blo 734326 1343281 := bstep (se 2 (by rfl) ⟨503730, by rfl⟩ : syracuseStep 1343281 = 1007461) B1007461
theorem B1179443 : Blo 734326 1179443 := bstep (se 1 (by rfl) ⟨884582, by rfl⟩ : syracuseStep 1179443 = 1769165) B1769165
theorem B3735395 : Blo 734326 3735395 := bstep (se 1 (by rfl) ⟨2801546, by rfl⟩ : syracuseStep 3735395 = 5603093) B5603093
theorem B2359181 : Blo 734326 2359181 := bstep (se 3 (by rfl) ⟨442346, by rfl⟩ : syracuseStep 2359181 = 884693) B884693
theorem B3538829 : Blo 734326 3538829 := bstep (se 3 (by rfl) ⟨663530, by rfl⟩ : syracuseStep 3538829 = 1327061) B1327061
theorem B1245091 : Blo 734326 1245091 := bstep (se 1 (by rfl) ⟨933818, by rfl⟩ : syracuseStep 1245091 = 1867637) B1867637
theorem B2490317 : Blo 734326 2490317 := bstep (se 3 (by rfl) ⟨466934, by rfl⟩ : syracuseStep 2490317 = 933869) B933869
theorem B1867799 : Blo 734326 1867799 := bstep (se 1 (by rfl) ⟨1400849, by rfl⟩ : syracuseStep 1867799 = 2801699) B2801699
theorem B2359489 : Blo 734326 2359489 := bstep (se 2 (by rfl) ⟨884808, by rfl⟩ : syracuseStep 2359489 = 1769617) B1769617
theorem B2982091 : Blo 734326 2982091 := bstep (se 1 (by rfl) ⟨2236568, by rfl⟩ : syracuseStep 2982091 = 4473137) B4473137
theorem B786667 : Blo 734326 786667 := bstep (se 1 (by rfl) ⟨590000, by rfl⟩ : syracuseStep 786667 = 1180001) B1180001
theorem B1769779 : Blo 734326 1769779 := bstep (se 1 (by rfl) ⟨1327334, by rfl⟩ : syracuseStep 1769779 = 2654669) B2654669
theorem B6291863 : Blo 734326 6291863 := bstep (se 1 (by rfl) ⟨4718897, by rfl⟩ : syracuseStep 6291863 = 9437795) B9437795
theorem B4718999 : Blo 734326 4718999 := bstep (se 1 (by rfl) ⟨3539249, by rfl⟩ : syracuseStep 4718999 = 7078499) B7078499
theorem B1573273 : Blo 734326 1573273 := bstep (se 2 (by rfl) ⟨589977, by rfl⟩ : syracuseStep 1573273 = 1179955) B1179955
theorem B2490803 : Blo 734326 2490803 := bstep (se 1 (by rfl) ⟨1868102, by rfl⟩ : syracuseStep 2490803 = 3736205) B3736205
theorem B1245719 : Blo 734326 1245719 := bstep (se 1 (by rfl) ⟨934289, by rfl⟩ : syracuseStep 1245719 = 1868579) B1868579
theorem B2654813 : Blo 734326 2654813 := bstep (se 3 (by rfl) ⟨497777, by rfl⟩ : syracuseStep 2654813 = 995555) B995555
theorem B1245847 : Blo 734326 1245847 := bstep (se 1 (by rfl) ⟨934385, by rfl⟩ : syracuseStep 1245847 = 1868771) B1868771
theorem B787115 : Blo 734326 787115 := bstep (se 1 (by rfl) ⟨590336, by rfl⟩ : syracuseStep 787115 = 1180673) B1180673
theorem B1868467 : Blo 734326 1868467 := bstep (se 1 (by rfl) ⟨1401350, by rfl⟩ : syracuseStep 1868467 = 2802701) B2802701
theorem B2491073 : Blo 734326 2491073 := bstep (se 2 (by rfl) ⟨934152, by rfl⟩ : syracuseStep 2491073 = 1868305) B1868305
theorem B6292241 : Blo 734326 6292241 := bstep (se 2 (by rfl) ⟨2359590, by rfl⟩ : syracuseStep 6292241 = 4719181) B4719181
theorem B2097971 : Blo 734326 2097971 := bstep (se 1 (by rfl) ⟨1573478, by rfl⟩ : syracuseStep 2097971 = 3146957) B3146957
theorem B1868609 : Blo 734326 1868609 := bstep (se 2 (by rfl) ⟨700728, by rfl⟩ : syracuseStep 1868609 = 1401457) B1401457
theorem B2098199 : Blo 734326 2098199 := bstep (se 1 (by rfl) ⟨1573649, by rfl⟩ : syracuseStep 2098199 = 3147299) B3147299
theorem B2491613 : Blo 734326 2491613 := bstep (se 3 (by rfl) ⟨467177, by rfl⟩ : syracuseStep 2491613 = 934355) B934355
theorem B3147025 : Blo 734326 3147025 := bstep (se 2 (by rfl) ⟨1180134, by rfl⟩ : syracuseStep 3147025 = 2360269) B2360269
theorem B1770817 : Blo 734326 1770817 := bstep (se 2 (by rfl) ⟨664056, by rfl⟩ : syracuseStep 1770817 = 1328113) B1328113
theorem B2098507 : Blo 734326 2098507 := bstep (se 1 (by rfl) ⟨1573880, by rfl⟩ : syracuseStep 2098507 = 3147761) B3147761
theorem B55248277 : Blo 734326 55248277 := bstep (se 6 (by rfl) ⟨1294881, by rfl⟩ : syracuseStep 55248277 = 2589763) B2589763
theorem B886231 : Blo 734326 886231 := bstep (se 1 (by rfl) ⟨664673, by rfl⟩ : syracuseStep 886231 = 1329347) B1329347
theorem B2098781 : Blo 734326 2098781 := bstep (se 3 (by rfl) ⟨393521, by rfl⟩ : syracuseStep 2098781 = 787043) B787043
theorem B2655937 : Blo 734326 2655937 := bstep (se 2 (by rfl) ⟨995976, by rfl⟩ : syracuseStep 2655937 = 1991953) B1991953
theorem B1574743 : Blo 734326 1574743 := bstep (se 1 (by rfl) ⟨1181057, by rfl⟩ : syracuseStep 1574743 = 2362115) B2362115
theorem B1050455 : Blo 734326 1050455 := bstep (se 1 (by rfl) ⟨787841, by rfl⟩ : syracuseStep 1050455 = 1575683) B1575683
theorem B788311 : Blo 734326 788311 := bstep (se 1 (by rfl) ⟨591233, by rfl⟩ : syracuseStep 788311 = 1182467) B1182467
theorem B1574795 : Blo 734326 1574795 := bstep (se 1 (by rfl) ⟨1181096, by rfl⟩ : syracuseStep 1574795 = 2362193) B2362193
theorem B2361437 : Blo 734326 2361437 := bstep (se 3 (by rfl) ⟨442769, by rfl⟩ : syracuseStep 2361437 = 885539) B885539
theorem B1182359 : Blo 734326 1182359 := bstep (se 1 (by rfl) ⟨886769, by rfl⟩ : syracuseStep 1182359 = 1773539) B1773539
theorem B2788289 : Blo 734326 2788289 := bstep (se 2 (by rfl) ⟨1045608, by rfl⟩ : syracuseStep 2788289 = 2091217) B2091217
theorem B2657539 : Blo 734326 2657539 := bstep (se 1 (by rfl) ⟨1993154, by rfl⟩ : syracuseStep 2657539 = 3986309) B3986309
theorem B757207 : Blo 734326 757207 := bstep (se 1 (by rfl) ⟨567905, by rfl⟩ : syracuseStep 757207 = 1135811) B1135811
theorem B1576435 : Blo 734326 1576435 := bstep (se 1 (by rfl) ⟨1182326, by rfl⟩ : syracuseStep 1576435 = 2364653) B2364653
theorem B3149401 : Blo 734326 3149401 := bstep (se 2 (by rfl) ⟨1181025, by rfl⟩ : syracuseStep 3149401 = 2362051) B2362051
theorem B2100887 : Blo 734326 2100887 := bstep (se 1 (by rfl) ⟨1575665, by rfl⟩ : syracuseStep 2100887 = 3151331) B3151331
theorem B2559709 : Blo 734326 2559709 := bstep (se 3 (by rfl) ⟨479945, by rfl⟩ : syracuseStep 2559709 = 959891) B959891
theorem B2690833 : Blo 734326 2690833 := bstep (se 2 (by rfl) ⟨1009062, by rfl⟩ : syracuseStep 2690833 = 2018125) B2018125
theorem B2658071 : Blo 734326 2658071 := bstep (se 1 (by rfl) ⟨1993553, by rfl⟩ : syracuseStep 2658071 = 3987107) B3987107
theorem B5246795 : Blo 734326 5246795 := bstep (se 1 (by rfl) ⟨3935096, by rfl⟩ : syracuseStep 5246795 = 7870193) B7870193
theorem B1576793 : Blo 734326 1576793 := bstep (se 2 (by rfl) ⟨591297, by rfl⟩ : syracuseStep 1576793 = 1182595) B1182595
theorem B30642245 : Blo 734326 30642245 := bstep (se 4 (by rfl) ⟨2872710, by rfl⟩ : syracuseStep 30642245 = 5745421) B5745421
theorem B4198493 : Blo 734326 4198493 := bstep (se 3 (by rfl) ⟨787217, by rfl⟩ : syracuseStep 4198493 = 1574435) B1574435
theorem B2789549 : Blo 734326 2789549 := bstep (se 3 (by rfl) ⟨523040, by rfl⟩ : syracuseStep 2789549 = 1046081) B1046081
theorem B1675457 : Blo 734326 1675457 := bstep (se 2 (by rfl) ⟨628296, by rfl⟩ : syracuseStep 1675457 = 1256593) B1256593
theorem B2789579 : Blo 734326 2789579 := bstep (se 1 (by rfl) ⟨2092184, by rfl⟩ : syracuseStep 2789579 = 4184369) B4184369
theorem B2101697 : Blo 734326 2101697 := bstep (se 2 (by rfl) ⟨788136, by rfl⟩ : syracuseStep 2101697 = 1576273) B1576273
theorem B3150359 : Blo 734326 3150359 := bstep (se 1 (by rfl) ⟨2362769, by rfl⟩ : syracuseStep 3150359 = 4725539) B4725539
theorem B2233163 : Blo 734326 2233163 := bstep (se 1 (by rfl) ⟨1674872, by rfl⟩ : syracuseStep 2233163 = 3349745) B3349745
theorem B2790233 : Blo 734326 2790233 := bstep (se 2 (by rfl) ⟨1046337, by rfl⟩ : syracuseStep 2790233 = 2092675) B2092675
theorem B3969893 : Blo 734326 3969893 := bstep (se 4 (by rfl) ⟨372177, by rfl⟩ : syracuseStep 3969893 = 744355) B744355
theorem B2790551 : Blo 734326 2790551 := bstep (se 1 (by rfl) ⟨2092913, by rfl⟩ : syracuseStep 2790551 = 4185827) B4185827
theorem B2791219 : Blo 734326 2791219 := bstep (se 1 (by rfl) ⟨2093414, by rfl⟩ : syracuseStep 2791219 = 4186829) B4186829
theorem B2988433 : Blo 734326 2988433 := bstep (se 2 (by rfl) ⟨1120662, by rfl⟩ : syracuseStep 2988433 = 2241325) B2241325
theorem B5380613 : Blo 734326 5380613 := bstep (se 4 (by rfl) ⟨504432, by rfl⟩ : syracuseStep 5380613 = 1008865) B1008865
theorem B3152459 : Blo 734326 3152459 := bstep (se 1 (by rfl) ⟨2364344, by rfl⟩ : syracuseStep 3152459 = 4728689) B4728689
theorem B4201091 : Blo 734326 4201091 := bstep (se 1 (by rfl) ⟨3150818, by rfl⟩ : syracuseStep 4201091 = 6301637) B6301637
theorem B2235097 : Blo 734326 2235097 := bstep (se 2 (by rfl) ⟨838161, by rfl⟩ : syracuseStep 2235097 = 1676323) B1676323
theorem B826123 : Blo 734326 826123 := bstep (se 1 (by rfl) ⟨619592, by rfl⟩ : syracuseStep 826123 = 1239185) B1239185
theorem B826231 : Blo 734326 826231 := bstep (se 1 (by rfl) ⟨619673, by rfl⟩ : syracuseStep 826231 = 1239347) B1239347
theorem B2235329 : Blo 734326 2235329 := bstep (se 2 (by rfl) ⟨838248, by rfl⟩ : syracuseStep 2235329 = 1676497) B1676497
theorem B2792465 : Blo 734326 2792465 := bstep (se 2 (by rfl) ⟨1047174, by rfl⟩ : syracuseStep 2792465 = 2094349) B2094349
theorem B826411 : Blo 734326 826411 := bstep (se 1 (by rfl) ⟨619808, by rfl⟩ : syracuseStep 826411 = 1239617) B1239617
theorem B5577821 : Blo 734326 5577821 := bstep (se 3 (by rfl) ⟨1045841, by rfl⟩ : syracuseStep 5577821 = 2091683) B2091683
theorem B826519 : Blo 734326 826519 := bstep (se 1 (by rfl) ⟨619889, by rfl⟩ : syracuseStep 826519 = 1239779) B1239779
theorem B826699 : Blo 734326 826699 := bstep (se 1 (by rfl) ⟨620024, by rfl⟩ : syracuseStep 826699 = 1240049) B1240049
theorem B826807 : Blo 734326 826807 := bstep (se 1 (by rfl) ⟨620105, by rfl⟩ : syracuseStep 826807 = 1240211) B1240211
theorem B2989619 : Blo 734326 2989619 := bstep (se 1 (by rfl) ⟨2242214, by rfl⟩ : syracuseStep 2989619 = 4484429) B4484429
theorem B826987 : Blo 734326 826987 := bstep (se 1 (by rfl) ⟨620240, by rfl⟩ : syracuseStep 826987 = 1240481) B1240481
theorem B2793163 : Blo 734326 2793163 := bstep (se 1 (by rfl) ⟨2094872, by rfl⟩ : syracuseStep 2793163 = 4189745) B4189745
theorem B827095 : Blo 734326 827095 := bstep (se 1 (by rfl) ⟨620321, by rfl⟩ : syracuseStep 827095 = 1240643) B1240643
theorem B827275 : Blo 734326 827275 := bstep (se 1 (by rfl) ⟨620456, by rfl⟩ : syracuseStep 827275 = 1240913) B1240913
theorem B2793437 : Blo 734326 2793437 := bstep (se 3 (by rfl) ⟨523769, by rfl⟩ : syracuseStep 2793437 = 1047539) B1047539
theorem B827383 : Blo 734326 827383 := bstep (se 1 (by rfl) ⟨620537, by rfl⟩ : syracuseStep 827383 = 1241075) B1241075
theorem B6299653 : Blo 734326 6299653 := bstep (se 4 (by rfl) ⟨590592, by rfl⟩ : syracuseStep 6299653 = 1181185) B1181185
theorem B3317777 : Blo 734326 3317777 := bstep (se 2 (by rfl) ⟨1244166, by rfl⟩ : syracuseStep 3317777 = 2488333) B2488333
theorem B827563 : Blo 734326 827563 := bstep (se 1 (by rfl) ⟨620672, by rfl⟩ : syracuseStep 827563 = 1241345) B1241345
theorem B827671 : Blo 734326 827671 := bstep (se 1 (by rfl) ⟨620753, by rfl⟩ : syracuseStep 827671 = 1241507) B1241507
theorem B827851 : Blo 734326 827851 := bstep (se 1 (by rfl) ⟨620888, by rfl⟩ : syracuseStep 827851 = 1241777) B1241777
theorem B5677573 : Blo 734326 5677573 := bstep (se 4 (by rfl) ⟨532272, by rfl⟩ : syracuseStep 5677573 = 1064545) B1064545
theorem B827959 : Blo 734326 827959 := bstep (se 1 (by rfl) ⟨620969, by rfl⟩ : syracuseStep 827959 = 1241939) B1241939
theorem B2794135 : Blo 734326 2794135 := bstep (se 1 (by rfl) ⟨2095601, by rfl⟩ : syracuseStep 2794135 = 4191203) B4191203
theorem B828139 : Blo 734326 828139 := bstep (se 1 (by rfl) ⟨621104, by rfl⟩ : syracuseStep 828139 = 1242209) B1242209
theorem B828247 : Blo 734326 828247 := bstep (se 1 (by rfl) ⟨621185, by rfl⟩ : syracuseStep 828247 = 1242371) B1242371
theorem B828427 : Blo 734326 828427 := bstep (se 1 (by rfl) ⟨621320, by rfl⟩ : syracuseStep 828427 = 1242641) B1242641
theorem B828535 : Blo 734326 828535 := bstep (se 1 (by rfl) ⟨621401, by rfl⟩ : syracuseStep 828535 = 1242803) B1242803
theorem B828715 : Blo 734326 828715 := bstep (se 1 (by rfl) ⟨621536, by rfl⟩ : syracuseStep 828715 = 1243073) B1243073
theorem B11937125 : Blo 734326 11937125 := bstep (se 4 (by rfl) ⟨1119105, by rfl⟩ : syracuseStep 11937125 = 2238211) B2238211
theorem B828823 : Blo 734326 828823 := bstep (se 1 (by rfl) ⟨621617, by rfl⟩ : syracuseStep 828823 = 1243235) B1243235
theorem B2794925 : Blo 734326 2794925 := bstep (se 3 (by rfl) ⟨524048, by rfl⟩ : syracuseStep 2794925 = 1048097) B1048097
theorem B829003 : Blo 734326 829003 := bstep (se 1 (by rfl) ⟨621752, by rfl⟩ : syracuseStep 829003 = 1243505) B1243505
theorem B1418839 : Blo 734326 1418839 := bstep (se 1 (by rfl) ⟨1064129, by rfl⟩ : syracuseStep 1418839 = 2128259) B2128259
theorem B829111 : Blo 734326 829111 := bstep (se 1 (by rfl) ⟨621833, by rfl⟩ : syracuseStep 829111 = 1243667) B1243667
theorem B2991809 : Blo 734326 2991809 := bstep (se 2 (by rfl) ⟨1121928, by rfl⟩ : syracuseStep 2991809 = 2243857) B2243857
theorem B829291 : Blo 734326 829291 := bstep (se 1 (by rfl) ⟨621968, by rfl⟩ : syracuseStep 829291 = 1243937) B1243937
theorem B8366003 : Blo 734326 8366003 := bstep (se 1 (by rfl) ⟨6274502, by rfl⟩ : syracuseStep 8366003 = 12549005) B12549005
theorem B829399 : Blo 734326 829399 := bstep (se 1 (by rfl) ⟨622049, by rfl⟩ : syracuseStep 829399 = 1244099) B1244099
theorem B829579 : Blo 734326 829579 := bstep (se 1 (by rfl) ⟨622184, by rfl⟩ : syracuseStep 829579 = 1244369) B1244369
theorem B829687 : Blo 734326 829687 := bstep (se 1 (by rfl) ⟨622265, by rfl⟩ : syracuseStep 829687 = 1244531) B1244531
theorem B829867 : Blo 734326 829867 := bstep (se 1 (by rfl) ⟨622400, by rfl⟩ : syracuseStep 829867 = 1244801) B1244801
theorem B1681879 : Blo 734326 1681879 := bstep (se 1 (by rfl) ⟨1261409, by rfl⟩ : syracuseStep 1681879 = 2522819) B2522819
theorem B829975 : Blo 734326 829975 := bstep (se 1 (by rfl) ⟨622481, by rfl⟩ : syracuseStep 829975 = 1244963) B1244963
theorem B2992733 : Blo 734326 2992733 := bstep (se 3 (by rfl) ⟨561137, by rfl⟩ : syracuseStep 2992733 = 1122275) B1122275
theorem B6302387 : Blo 734326 6302387 := bstep (se 1 (by rfl) ⟨4726790, by rfl⟩ : syracuseStep 6302387 = 9453581) B9453581
theorem B830155 : Blo 734326 830155 := bstep (se 1 (by rfl) ⟨622616, by rfl⟩ : syracuseStep 830155 = 1245233) B1245233
theorem B830263 : Blo 734326 830263 := bstep (se 1 (by rfl) ⟨622697, by rfl⟩ : syracuseStep 830263 = 1245395) B1245395
theorem B2796353 : Blo 734326 2796353 := bstep (se 2 (by rfl) ⟨1048632, by rfl⟩ : syracuseStep 2796353 = 2097265) B2097265
theorem B1616843 : Blo 734326 1616843 := bstep (se 1 (by rfl) ⟨1212632, by rfl⟩ : syracuseStep 1616843 = 2425265) B2425265
theorem B830443 : Blo 734326 830443 := bstep (se 1 (by rfl) ⟨622832, by rfl⟩ : syracuseStep 830443 = 1245665) B1245665
theorem B830551 : Blo 734326 830551 := bstep (se 1 (by rfl) ⟨622913, by rfl⟩ : syracuseStep 830551 = 1245827) B1245827
theorem B11349233 : Blo 734326 11349233 := bstep (se 2 (by rfl) ⟨4255962, by rfl⟩ : syracuseStep 11349233 = 8511925) B8511925
theorem B8367461 : Blo 734326 8367461 := bstep (se 4 (by rfl) ⟨784449, by rfl⟩ : syracuseStep 8367461 = 1568899) B1568899
theorem B1420747 : Blo 734326 1420747 := bstep (se 1 (by rfl) ⟨1065560, by rfl⟩ : syracuseStep 1420747 = 2131121) B2131121
theorem B929495 : Blo 734326 929495 := bstep (se 1 (by rfl) ⟨697121, by rfl⟩ : syracuseStep 929495 = 1394243) B1394243
theorem B5385989 : Blo 734326 5385989 := bstep (se 4 (by rfl) ⟨504936, by rfl⟩ : syracuseStep 5385989 = 1009873) B1009873
theorem B1060619 : Blo 734326 1060619 := bstep (se 1 (by rfl) ⟨795464, by rfl⟩ : syracuseStep 1060619 = 1590929) B1590929
theorem B4534147 : Blo 734326 4534147 := bstep (se 1 (by rfl) ⟨3400610, by rfl⟩ : syracuseStep 4534147 = 6801221) B6801221
theorem B2797841 : Blo 734326 2797841 := bstep (se 2 (by rfl) ⟨1049190, by rfl⟩ : syracuseStep 2797841 = 2098381) B2098381
theorem B930199 : Blo 734326 930199 := bstep (se 1 (by rfl) ⟨697649, by rfl⟩ : syracuseStep 930199 = 1395299) B1395299
theorem B7090649 : Blo 734326 7090649 := bstep (se 2 (by rfl) ⟨2658993, by rfl⟩ : syracuseStep 7090649 = 5317987) B5317987
theorem B6304301 : Blo 734326 6304301 := bstep (se 3 (by rfl) ⟨1182056, by rfl⟩ : syracuseStep 6304301 = 2364113) B2364113
theorem B1323659 : Blo 734326 1323659 := bstep (se 1 (by rfl) ⟨992744, by rfl⟩ : syracuseStep 1323659 = 1985489) B1985489
theorem B2798297 : Blo 734326 2798297 := bstep (se 2 (by rfl) ⟨1049361, by rfl⟩ : syracuseStep 2798297 = 2098723) B2098723
theorem B2798509 : Blo 734326 2798509 := bstep (se 3 (by rfl) ⟨524720, by rfl⟩ : syracuseStep 2798509 = 1049441) B1049441
theorem B734327 : Blo 734326 734327 := bstep (se 1 (by rfl) ⟨550745, by rfl⟩ : syracuseStep 734327 = 1101491) B1101491
theorem B734347 : Blo 734326 734347 := bstep (se 1 (by rfl) ⟨550760, by rfl⟩ : syracuseStep 734347 = 1101521) B1101521
theorem B734359 : Blo 734326 734359 := bstep (se 1 (by rfl) ⟨550769, by rfl⟩ : syracuseStep 734359 = 1101539) B1101539
theorem B734379 : Blo 734326 734379 := bstep (se 1 (by rfl) ⟨550784, by rfl⟩ : syracuseStep 734379 = 1101569) B1101569
theorem B734391 : Blo 734326 734391 := bstep (se 1 (by rfl) ⟨550793, by rfl⟩ : syracuseStep 734391 = 1101587) B1101587
theorem B734411 : Blo 734326 734411 := bstep (se 1 (by rfl) ⟨550808, by rfl⟩ : syracuseStep 734411 = 1101617) B1101617
theorem B734423 : Blo 734326 734423 := bstep (se 1 (by rfl) ⟨550817, by rfl⟩ : syracuseStep 734423 = 1101635) B1101635
theorem B6304985 : Blo 734326 6304985 := bstep (se 2 (by rfl) ⟨2364369, by rfl⟩ : syracuseStep 6304985 = 4728739) B4728739
theorem B2798813 : Blo 734326 2798813 := bstep (se 3 (by rfl) ⟨524777, by rfl⟩ : syracuseStep 2798813 = 1049555) B1049555
theorem B734443 : Blo 734326 734443 := bstep (se 1 (by rfl) ⟨550832, by rfl⟩ : syracuseStep 734443 = 1101665) B1101665
theorem B734455 : Blo 734326 734455 := bstep (se 1 (by rfl) ⟨550841, by rfl⟩ : syracuseStep 734455 = 1101683) B1101683
theorem B7156997 : Blo 734326 7156997 := bstep (se 4 (by rfl) ⟨670968, by rfl⟩ : syracuseStep 7156997 = 1341937) B1341937
theorem B734475 : Blo 734326 734475 := bstep (se 1 (by rfl) ⟨550856, by rfl⟩ : syracuseStep 734475 = 1101713) B1101713
theorem B734487 : Blo 734326 734487 := bstep (se 1 (by rfl) ⟨550865, by rfl⟩ : syracuseStep 734487 = 1101731) B1101731
theorem B734507 : Blo 734326 734507 := bstep (se 1 (by rfl) ⟨550880, by rfl⟩ : syracuseStep 734507 = 1101761) B1101761
theorem B734519 : Blo 734326 734519 := bstep (se 1 (by rfl) ⟨550889, by rfl⟩ : syracuseStep 734519 = 1101779) B1101779
theorem B734539 : Blo 734326 734539 := bstep (se 1 (by rfl) ⟨550904, by rfl⟩ : syracuseStep 734539 = 1101809) B1101809
theorem B734551 : Blo 734326 734551 := bstep (se 1 (by rfl) ⟨550913, by rfl⟩ : syracuseStep 734551 = 1101827) B1101827
theorem B734571 : Blo 734326 734571 := bstep (se 1 (by rfl) ⟨550928, by rfl⟩ : syracuseStep 734571 = 1101857) B1101857
theorem B734583 : Blo 734326 734583 := bstep (se 1 (by rfl) ⟨550937, by rfl⟩ : syracuseStep 734583 = 1101875) B1101875
theorem B734603 : Blo 734326 734603 := bstep (se 1 (by rfl) ⟨550952, by rfl⟩ : syracuseStep 734603 = 1101905) B1101905
theorem B734615 : Blo 734326 734615 := bstep (se 1 (by rfl) ⟨550961, by rfl⟩ : syracuseStep 734615 = 1101923) B1101923
theorem B734635 : Blo 734326 734635 := bstep (se 1 (by rfl) ⟨550976, by rfl⟩ : syracuseStep 734635 = 1101953) B1101953
theorem B734647 : Blo 734326 734647 := bstep (se 1 (by rfl) ⟨550985, by rfl⟩ : syracuseStep 734647 = 1101971) B1101971
theorem B734667 : Blo 734326 734667 := bstep (se 1 (by rfl) ⟨551000, by rfl⟩ : syracuseStep 734667 = 1102001) B1102001
theorem B734679 : Blo 734326 734679 := bstep (se 1 (by rfl) ⟨551009, by rfl⟩ : syracuseStep 734679 = 1102019) B1102019
theorem B2242009 : Blo 734326 2242009 := bstep (se 2 (by rfl) ⟨840753, by rfl⟩ : syracuseStep 2242009 = 1681507) B1681507
theorem B734699 : Blo 734326 734699 := bstep (se 1 (by rfl) ⟨551024, by rfl⟩ : syracuseStep 734699 = 1102049) B1102049
theorem B734711 : Blo 734326 734711 := bstep (se 1 (by rfl) ⟨551033, by rfl⟩ : syracuseStep 734711 = 1102067) B1102067
theorem B734731 : Blo 734326 734731 := bstep (se 1 (by rfl) ⟨551048, by rfl⟩ : syracuseStep 734731 = 1102097) B1102097
theorem B734743 : Blo 734326 734743 := bstep (se 1 (by rfl) ⟨551057, by rfl⟩ : syracuseStep 734743 = 1102115) B1102115
theorem B734763 : Blo 734326 734763 := bstep (se 1 (by rfl) ⟨551072, by rfl⟩ : syracuseStep 734763 = 1102145) B1102145
theorem B734775 : Blo 734326 734775 := bstep (se 1 (by rfl) ⟨551081, by rfl⟩ : syracuseStep 734775 = 1102163) B1102163
theorem B734795 : Blo 734326 734795 := bstep (se 1 (by rfl) ⟨551096, by rfl⟩ : syracuseStep 734795 = 1102193) B1102193
theorem B9418315 : Blo 734326 9418315 := bstep (se 1 (by rfl) ⟨7063736, by rfl⟩ : syracuseStep 9418315 = 14127473) B14127473
theorem B734807 : Blo 734326 734807 := bstep (se 1 (by rfl) ⟨551105, by rfl⟩ : syracuseStep 734807 = 1102211) B1102211
theorem B734827 : Blo 734326 734827 := bstep (se 1 (by rfl) ⟨551120, by rfl⟩ : syracuseStep 734827 = 1102241) B1102241
theorem B734839 : Blo 734326 734839 := bstep (se 1 (by rfl) ⟨551129, by rfl⟩ : syracuseStep 734839 = 1102259) B1102259
theorem B1652363 : Blo 734326 1652363 := bstep (se 1 (by rfl) ⟨1239272, by rfl⟩ : syracuseStep 1652363 = 2478545) B2478545
theorem B734859 : Blo 734326 734859 := bstep (se 1 (by rfl) ⟨551144, by rfl⟩ : syracuseStep 734859 = 1102289) B1102289
theorem B734871 : Blo 734326 734871 := bstep (se 1 (by rfl) ⟨551153, by rfl⟩ : syracuseStep 734871 = 1102307) B1102307
theorem B997015 : Blo 734326 997015 := bstep (se 1 (by rfl) ⟨747761, by rfl⟩ : syracuseStep 997015 = 1495523) B1495523
theorem B734891 : Blo 734326 734891 := bstep (se 1 (by rfl) ⟨551168, by rfl⟩ : syracuseStep 734891 = 1102337) B1102337
theorem B734903 : Blo 734326 734903 := bstep (se 1 (by rfl) ⟨551177, by rfl⟩ : syracuseStep 734903 = 1102355) B1102355
theorem B1652417 : Blo 734326 1652417 := bstep (se 2 (by rfl) ⟨619656, by rfl⟩ : syracuseStep 1652417 = 1239313) B1239313
theorem B734923 : Blo 734326 734923 := bstep (se 1 (by rfl) ⟨551192, by rfl⟩ : syracuseStep 734923 = 1102385) B1102385
theorem B734935 : Blo 734326 734935 := bstep (se 1 (by rfl) ⟨551201, by rfl⟩ : syracuseStep 734935 = 1102403) B1102403
theorem B734955 : Blo 734326 734955 := bstep (se 1 (by rfl) ⟨551216, by rfl⟩ : syracuseStep 734955 = 1102433) B1102433
theorem B734967 : Blo 734326 734967 := bstep (se 1 (by rfl) ⟨551225, by rfl⟩ : syracuseStep 734967 = 1102451) B1102451
theorem B734987 : Blo 734326 734987 := bstep (se 1 (by rfl) ⟨551240, by rfl⟩ : syracuseStep 734987 = 1102481) B1102481
theorem B734999 : Blo 734326 734999 := bstep (se 1 (by rfl) ⟨551249, by rfl⟩ : syracuseStep 734999 = 1102499) B1102499
theorem B735019 : Blo 734326 735019 := bstep (se 1 (by rfl) ⟨551264, by rfl⟩ : syracuseStep 735019 = 1102529) B1102529
theorem B735031 : Blo 734326 735031 := bstep (se 1 (by rfl) ⟨551273, by rfl⟩ : syracuseStep 735031 = 1102547) B1102547
theorem B735051 : Blo 734326 735051 := bstep (se 1 (by rfl) ⟨551288, by rfl⟩ : syracuseStep 735051 = 1102577) B1102577
theorem B735063 : Blo 734326 735063 := bstep (se 1 (by rfl) ⟨551297, by rfl⟩ : syracuseStep 735063 = 1102595) B1102595
theorem B735083 : Blo 734326 735083 := bstep (se 1 (by rfl) ⟨551312, by rfl⟩ : syracuseStep 735083 = 1102625) B1102625
theorem B735095 : Blo 734326 735095 := bstep (se 1 (by rfl) ⟨551321, by rfl⟩ : syracuseStep 735095 = 1102643) B1102643
theorem B735115 : Blo 734326 735115 := bstep (se 1 (by rfl) ⟨551336, by rfl⟩ : syracuseStep 735115 = 1102673) B1102673
theorem B735127 : Blo 734326 735127 := bstep (se 1 (by rfl) ⟨551345, by rfl⟩ : syracuseStep 735127 = 1102691) B1102691
theorem B1488793 : Blo 734326 1488793 := bstep (se 2 (by rfl) ⟨558297, by rfl⟩ : syracuseStep 1488793 = 1116595) B1116595
theorem B1652633 : Blo 734326 1652633 := bstep (se 2 (by rfl) ⟨619737, by rfl⟩ : syracuseStep 1652633 = 1239475) B1239475
theorem B735147 : Blo 734326 735147 := bstep (se 1 (by rfl) ⟨551360, by rfl⟩ : syracuseStep 735147 = 1102721) B1102721
theorem B4470707 : Blo 734326 4470707 := bstep (se 1 (by rfl) ⟨3353030, by rfl⟩ : syracuseStep 4470707 = 6706061) B6706061
theorem B735159 : Blo 734326 735159 := bstep (se 1 (by rfl) ⟨551369, by rfl⟩ : syracuseStep 735159 = 1102739) B1102739
theorem B735179 : Blo 734326 735179 := bstep (se 1 (by rfl) ⟨551384, by rfl⟩ : syracuseStep 735179 = 1102769) B1102769
theorem B735191 : Blo 734326 735191 := bstep (se 1 (by rfl) ⟨551393, by rfl⟩ : syracuseStep 735191 = 1102787) B1102787
theorem B735211 : Blo 734326 735211 := bstep (se 1 (by rfl) ⟨551408, by rfl⟩ : syracuseStep 735211 = 1102817) B1102817
theorem B1652723 : Blo 734326 1652723 := bstep (se 1 (by rfl) ⟨1239542, by rfl⟩ : syracuseStep 1652723 = 2479085) B2479085
theorem B735223 : Blo 734326 735223 := bstep (se 1 (by rfl) ⟨551417, by rfl⟩ : syracuseStep 735223 = 1102835) B1102835
theorem B735243 : Blo 734326 735243 := bstep (se 1 (by rfl) ⟨551432, by rfl⟩ : syracuseStep 735243 = 1102865) B1102865
theorem B1652759 : Blo 734326 1652759 := bstep (se 1 (by rfl) ⟨1239569, by rfl⟩ : syracuseStep 1652759 = 2479139) B2479139
theorem B735255 : Blo 734326 735255 := bstep (se 1 (by rfl) ⟨551441, by rfl⟩ : syracuseStep 735255 = 1102883) B1102883
theorem B735275 : Blo 734326 735275 := bstep (se 1 (by rfl) ⟨551456, by rfl⟩ : syracuseStep 735275 = 1102913) B1102913
theorem B735287 : Blo 734326 735287 := bstep (se 1 (by rfl) ⟨551465, by rfl⟩ : syracuseStep 735287 = 1102931) B1102931
theorem B735307 : Blo 734326 735307 := bstep (se 1 (by rfl) ⟨551480, by rfl⟩ : syracuseStep 735307 = 1102961) B1102961
theorem B4536395 : Blo 734326 4536395 := bstep (se 1 (by rfl) ⟨3402296, by rfl⟩ : syracuseStep 4536395 = 6804593) B6804593
theorem B931915 : Blo 734326 931915 := bstep (se 1 (by rfl) ⟨698936, by rfl⟩ : syracuseStep 931915 = 1397873) B1397873
theorem B735319 : Blo 734326 735319 := bstep (se 1 (by rfl) ⟨551489, by rfl⟩ : syracuseStep 735319 = 1102979) B1102979
theorem B1325143 : Blo 734326 1325143 := bstep (se 1 (by rfl) ⟨993857, by rfl⟩ : syracuseStep 1325143 = 1987715) B1987715
theorem B735339 : Blo 734326 735339 := bstep (se 1 (by rfl) ⟨551504, by rfl⟩ : syracuseStep 735339 = 1103009) B1103009
theorem B735351 : Blo 734326 735351 := bstep (se 1 (by rfl) ⟨551513, by rfl⟩ : syracuseStep 735351 = 1103027) B1103027
theorem B735371 : Blo 734326 735371 := bstep (se 1 (by rfl) ⟨551528, by rfl⟩ : syracuseStep 735371 = 1103057) B1103057
theorem B735383 : Blo 734326 735383 := bstep (se 1 (by rfl) ⟨551537, by rfl⟩ : syracuseStep 735383 = 1103075) B1103075
theorem B735403 : Blo 734326 735403 := bstep (se 1 (by rfl) ⟨551552, by rfl⟩ : syracuseStep 735403 = 1103105) B1103105
theorem B735415 : Blo 734326 735415 := bstep (se 1 (by rfl) ⟨551561, by rfl⟩ : syracuseStep 735415 = 1103123) B1103123
theorem B1652939 : Blo 734326 1652939 := bstep (se 1 (by rfl) ⟨1239704, by rfl⟩ : syracuseStep 1652939 = 2479409) B2479409
theorem B735435 : Blo 734326 735435 := bstep (se 1 (by rfl) ⟨551576, by rfl⟩ : syracuseStep 735435 = 1103153) B1103153
theorem B735447 : Blo 734326 735447 := bstep (se 1 (by rfl) ⟨551585, by rfl⟩ : syracuseStep 735447 = 1103171) B1103171
theorem B735467 : Blo 734326 735467 := bstep (se 1 (by rfl) ⟨551600, by rfl⟩ : syracuseStep 735467 = 1103201) B1103201
theorem B735479 : Blo 734326 735479 := bstep (se 1 (by rfl) ⟨551609, by rfl⟩ : syracuseStep 735479 = 1103219) B1103219
theorem B1652993 : Blo 734326 1652993 := bstep (se 2 (by rfl) ⟨619872, by rfl⟩ : syracuseStep 1652993 = 1239745) B1239745
theorem B735499 : Blo 734326 735499 := bstep (se 1 (by rfl) ⟨551624, by rfl⟩ : syracuseStep 735499 = 1103249) B1103249
theorem B735511 : Blo 734326 735511 := bstep (se 1 (by rfl) ⟨551633, by rfl⟩ : syracuseStep 735511 = 1103267) B1103267
theorem B735531 : Blo 734326 735531 := bstep (se 1 (by rfl) ⟨551648, by rfl⟩ : syracuseStep 735531 = 1103297) B1103297
theorem B735543 : Blo 734326 735543 := bstep (se 1 (by rfl) ⟨551657, by rfl⟩ : syracuseStep 735543 = 1103315) B1103315
theorem B735563 : Blo 734326 735563 := bstep (se 1 (by rfl) ⟨551672, by rfl⟩ : syracuseStep 735563 = 1103345) B1103345
theorem B735575 : Blo 734326 735575 := bstep (se 1 (by rfl) ⟨551681, by rfl⟩ : syracuseStep 735575 = 1103363) B1103363
theorem B735595 : Blo 734326 735595 := bstep (se 1 (by rfl) ⟨551696, by rfl⟩ : syracuseStep 735595 = 1103393) B1103393
theorem B735607 : Blo 734326 735607 := bstep (se 1 (by rfl) ⟨551705, by rfl⟩ : syracuseStep 735607 = 1103411) B1103411
theorem B735627 : Blo 734326 735627 := bstep (se 1 (by rfl) ⟨551720, by rfl⟩ : syracuseStep 735627 = 1103441) B1103441
theorem B735639 : Blo 734326 735639 := bstep (se 1 (by rfl) ⟨551729, by rfl⟩ : syracuseStep 735639 = 1103459) B1103459
theorem B735659 : Blo 734326 735659 := bstep (se 1 (by rfl) ⟨551744, by rfl⟩ : syracuseStep 735659 = 1103489) B1103489
theorem B735671 : Blo 734326 735671 := bstep (se 1 (by rfl) ⟨551753, by rfl⟩ : syracuseStep 735671 = 1103507) B1103507
theorem B735691 : Blo 734326 735691 := bstep (se 1 (by rfl) ⟨551768, by rfl⟩ : syracuseStep 735691 = 1103537) B1103537
theorem B735703 : Blo 734326 735703 := bstep (se 1 (by rfl) ⟨551777, by rfl⟩ : syracuseStep 735703 = 1103555) B1103555
theorem B1653209 : Blo 734326 1653209 := bstep (se 2 (by rfl) ⟨619953, by rfl⟩ : syracuseStep 1653209 = 1239907) B1239907
theorem B735723 : Blo 734326 735723 := bstep (se 1 (by rfl) ⟨551792, by rfl⟩ : syracuseStep 735723 = 1103585) B1103585
theorem B735735 : Blo 734326 735735 := bstep (se 1 (by rfl) ⟨551801, by rfl⟩ : syracuseStep 735735 = 1103603) B1103603
theorem B735755 : Blo 734326 735755 := bstep (se 1 (by rfl) ⟨551816, by rfl⟩ : syracuseStep 735755 = 1103633) B1103633
theorem B735767 : Blo 734326 735767 := bstep (se 1 (by rfl) ⟨551825, by rfl⟩ : syracuseStep 735767 = 1103651) B1103651
theorem B9812515 : Blo 734326 9812515 := bstep (se 1 (by rfl) ⟨7359386, by rfl⟩ : syracuseStep 9812515 = 14718773) B14718773
theorem B735787 : Blo 734326 735787 := bstep (se 1 (by rfl) ⟨551840, by rfl⟩ : syracuseStep 735787 = 1103681) B1103681
theorem B1653299 : Blo 734326 1653299 := bstep (se 1 (by rfl) ⟨1239974, by rfl⟩ : syracuseStep 1653299 = 2479949) B2479949
theorem B735799 : Blo 734326 735799 := bstep (se 1 (by rfl) ⟨551849, by rfl⟩ : syracuseStep 735799 = 1103699) B1103699
theorem B735819 : Blo 734326 735819 := bstep (se 1 (by rfl) ⟨551864, by rfl⟩ : syracuseStep 735819 = 1103729) B1103729
theorem B1653335 : Blo 734326 1653335 := bstep (se 1 (by rfl) ⟨1240001, by rfl⟩ : syracuseStep 1653335 = 2480003) B2480003
theorem B735831 : Blo 734326 735831 := bstep (se 1 (by rfl) ⟨551873, by rfl⟩ : syracuseStep 735831 = 1103747) B1103747
theorem B735851 : Blo 734326 735851 := bstep (se 1 (by rfl) ⟨551888, by rfl⟩ : syracuseStep 735851 = 1103777) B1103777
theorem B735863 : Blo 734326 735863 := bstep (se 1 (by rfl) ⟨551897, by rfl⟩ : syracuseStep 735863 = 1103795) B1103795
theorem B735883 : Blo 734326 735883 := bstep (se 1 (by rfl) ⟨551912, by rfl⟩ : syracuseStep 735883 = 1103825) B1103825
theorem B735895 : Blo 734326 735895 := bstep (se 1 (by rfl) ⟨551921, by rfl⟩ : syracuseStep 735895 = 1103843) B1103843
theorem B735915 : Blo 734326 735915 := bstep (se 1 (by rfl) ⟨551936, by rfl⟩ : syracuseStep 735915 = 1103873) B1103873
theorem B735927 : Blo 734326 735927 := bstep (se 1 (by rfl) ⟨551945, by rfl⟩ : syracuseStep 735927 = 1103891) B1103891
theorem B735947 : Blo 734326 735947 := bstep (se 1 (by rfl) ⟨551960, by rfl⟩ : syracuseStep 735947 = 1103921) B1103921
theorem B735959 : Blo 734326 735959 := bstep (se 1 (by rfl) ⟨551969, by rfl⟩ : syracuseStep 735959 = 1103939) B1103939
theorem B735979 : Blo 734326 735979 := bstep (se 1 (by rfl) ⟨551984, by rfl⟩ : syracuseStep 735979 = 1103969) B1103969
theorem B735991 : Blo 734326 735991 := bstep (se 1 (by rfl) ⟨551993, by rfl⟩ : syracuseStep 735991 = 1103987) B1103987
theorem B1653515 : Blo 734326 1653515 := bstep (se 1 (by rfl) ⟨1240136, by rfl⟩ : syracuseStep 1653515 = 2480273) B2480273
theorem B736011 : Blo 734326 736011 := bstep (se 1 (by rfl) ⟨552008, by rfl⟩ : syracuseStep 736011 = 1104017) B1104017
theorem B736023 : Blo 734326 736023 := bstep (se 1 (by rfl) ⟨552017, by rfl⟩ : syracuseStep 736023 = 1104035) B1104035
theorem B736043 : Blo 734326 736043 := bstep (se 1 (by rfl) ⟨552032, by rfl⟩ : syracuseStep 736043 = 1104065) B1104065
theorem B736055 : Blo 734326 736055 := bstep (se 1 (by rfl) ⟨552041, by rfl⟩ : syracuseStep 736055 = 1104083) B1104083
theorem B1653569 : Blo 734326 1653569 := bstep (se 2 (by rfl) ⟨620088, by rfl⟩ : syracuseStep 1653569 = 1240177) B1240177
theorem B736075 : Blo 734326 736075 := bstep (se 1 (by rfl) ⟨552056, by rfl⟩ : syracuseStep 736075 = 1104113) B1104113
theorem B736087 : Blo 734326 736087 := bstep (se 1 (by rfl) ⟨552065, by rfl⟩ : syracuseStep 736087 = 1104131) B1104131
theorem B736107 : Blo 734326 736107 := bstep (se 1 (by rfl) ⟨552080, by rfl⟩ : syracuseStep 736107 = 1104161) B1104161
theorem B736119 : Blo 734326 736119 := bstep (se 1 (by rfl) ⟨552089, by rfl⟩ : syracuseStep 736119 = 1104179) B1104179
theorem B736139 : Blo 734326 736139 := bstep (se 1 (by rfl) ⟨552104, by rfl⟩ : syracuseStep 736139 = 1104209) B1104209
theorem B736151 : Blo 734326 736151 := bstep (se 1 (by rfl) ⟨552113, by rfl⟩ : syracuseStep 736151 = 1104227) B1104227
theorem B736171 : Blo 734326 736171 := bstep (se 1 (by rfl) ⟨552128, by rfl⟩ : syracuseStep 736171 = 1104257) B1104257
theorem B736183 : Blo 734326 736183 := bstep (se 1 (by rfl) ⟨552137, by rfl⟩ : syracuseStep 736183 = 1104275) B1104275
theorem B736203 : Blo 734326 736203 := bstep (se 1 (by rfl) ⟨552152, by rfl⟩ : syracuseStep 736203 = 1104305) B1104305
theorem B736215 : Blo 734326 736215 := bstep (se 1 (by rfl) ⟨552161, by rfl⟩ : syracuseStep 736215 = 1104323) B1104323
theorem B736235 : Blo 734326 736235 := bstep (se 1 (by rfl) ⟨552176, by rfl⟩ : syracuseStep 736235 = 1104353) B1104353
theorem B736247 : Blo 734326 736247 := bstep (se 1 (by rfl) ⟨552185, by rfl⟩ : syracuseStep 736247 = 1104371) B1104371
theorem B736267 : Blo 734326 736267 := bstep (se 1 (by rfl) ⟨552200, by rfl⟩ : syracuseStep 736267 = 1104401) B1104401
theorem B736279 : Blo 734326 736279 := bstep (se 1 (by rfl) ⟨552209, by rfl⟩ : syracuseStep 736279 = 1104419) B1104419
theorem B932887 : Blo 734326 932887 := bstep (se 1 (by rfl) ⟨699665, by rfl⟩ : syracuseStep 932887 = 1399331) B1399331
theorem B1653785 : Blo 734326 1653785 := bstep (se 2 (by rfl) ⟨620169, by rfl⟩ : syracuseStep 1653785 = 1240339) B1240339
theorem B736299 : Blo 734326 736299 := bstep (se 1 (by rfl) ⟨552224, by rfl⟩ : syracuseStep 736299 = 1104449) B1104449
theorem B736311 : Blo 734326 736311 := bstep (se 1 (by rfl) ⟨552233, by rfl⟩ : syracuseStep 736311 = 1104467) B1104467
theorem B736331 : Blo 734326 736331 := bstep (se 1 (by rfl) ⟨552248, by rfl⟩ : syracuseStep 736331 = 1104497) B1104497
theorem B736343 : Blo 734326 736343 := bstep (se 1 (by rfl) ⟨552257, by rfl⟩ : syracuseStep 736343 = 1104515) B1104515
theorem B736363 : Blo 734326 736363 := bstep (se 1 (by rfl) ⟨552272, by rfl⟩ : syracuseStep 736363 = 1104545) B1104545
theorem B1653875 : Blo 734326 1653875 := bstep (se 1 (by rfl) ⟨1240406, by rfl⟩ : syracuseStep 1653875 = 2480813) B2480813
theorem B736375 : Blo 734326 736375 := bstep (se 1 (by rfl) ⟨552281, by rfl⟩ : syracuseStep 736375 = 1104563) B1104563
theorem B736395 : Blo 734326 736395 := bstep (se 1 (by rfl) ⟨552296, by rfl⟩ : syracuseStep 736395 = 1104593) B1104593
theorem B1653911 : Blo 734326 1653911 := bstep (se 1 (by rfl) ⟨1240433, by rfl⟩ : syracuseStep 1653911 = 2480867) B2480867
theorem B736407 : Blo 734326 736407 := bstep (se 1 (by rfl) ⟨552305, by rfl⟩ : syracuseStep 736407 = 1104611) B1104611
theorem B736427 : Blo 734326 736427 := bstep (se 1 (by rfl) ⟨552320, by rfl⟩ : syracuseStep 736427 = 1104641) B1104641
theorem B736439 : Blo 734326 736439 := bstep (se 1 (by rfl) ⟨552329, by rfl⟩ : syracuseStep 736439 = 1104659) B1104659
theorem B736459 : Blo 734326 736459 := bstep (se 1 (by rfl) ⟨552344, by rfl⟩ : syracuseStep 736459 = 1104689) B1104689
theorem B736471 : Blo 734326 736471 := bstep (se 1 (by rfl) ⟨552353, by rfl⟩ : syracuseStep 736471 = 1104707) B1104707
theorem B736491 : Blo 734326 736491 := bstep (se 1 (by rfl) ⟨552368, by rfl⟩ : syracuseStep 736491 = 1104737) B1104737
theorem B736503 : Blo 734326 736503 := bstep (se 1 (by rfl) ⟨552377, by rfl⟩ : syracuseStep 736503 = 1104755) B1104755
theorem B736523 : Blo 734326 736523 := bstep (se 1 (by rfl) ⟨552392, by rfl⟩ : syracuseStep 736523 = 1104785) B1104785
theorem B736535 : Blo 734326 736535 := bstep (se 1 (by rfl) ⟨552401, by rfl⟩ : syracuseStep 736535 = 1104803) B1104803
theorem B736555 : Blo 734326 736555 := bstep (se 1 (by rfl) ⟨552416, by rfl⟩ : syracuseStep 736555 = 1104833) B1104833
theorem B736567 : Blo 734326 736567 := bstep (se 1 (by rfl) ⟨552425, by rfl⟩ : syracuseStep 736567 = 1104851) B1104851
theorem B1654091 : Blo 734326 1654091 := bstep (se 1 (by rfl) ⟨1240568, by rfl⟩ : syracuseStep 1654091 = 2481137) B2481137
theorem B736587 : Blo 734326 736587 := bstep (se 1 (by rfl) ⟨552440, by rfl⟩ : syracuseStep 736587 = 1104881) B1104881
theorem B736599 : Blo 734326 736599 := bstep (se 1 (by rfl) ⟨552449, by rfl⟩ : syracuseStep 736599 = 1104899) B1104899
theorem B736619 : Blo 734326 736619 := bstep (se 1 (by rfl) ⟨552464, by rfl⟩ : syracuseStep 736619 = 1104929) B1104929
theorem B736631 : Blo 734326 736631 := bstep (se 1 (by rfl) ⟨552473, by rfl⟩ : syracuseStep 736631 = 1104947) B1104947
theorem B1654145 : Blo 734326 1654145 := bstep (se 2 (by rfl) ⟨620304, by rfl⟩ : syracuseStep 1654145 = 1240609) B1240609
theorem B736651 : Blo 734326 736651 := bstep (se 1 (by rfl) ⟨552488, by rfl⟩ : syracuseStep 736651 = 1104977) B1104977
theorem B736663 : Blo 734326 736663 := bstep (se 1 (by rfl) ⟨552497, by rfl⟩ : syracuseStep 736663 = 1104995) B1104995
theorem B736683 : Blo 734326 736683 := bstep (se 1 (by rfl) ⟨552512, by rfl⟩ : syracuseStep 736683 = 1105025) B1105025
theorem B736695 : Blo 734326 736695 := bstep (se 1 (by rfl) ⟨552521, by rfl⟩ : syracuseStep 736695 = 1105043) B1105043
theorem B736715 : Blo 734326 736715 := bstep (se 1 (by rfl) ⟨552536, by rfl⟩ : syracuseStep 736715 = 1105073) B1105073
theorem B736727 : Blo 734326 736727 := bstep (se 1 (by rfl) ⟨552545, by rfl⟩ : syracuseStep 736727 = 1105091) B1105091
theorem B736747 : Blo 734326 736747 := bstep (se 1 (by rfl) ⟨552560, by rfl⟩ : syracuseStep 736747 = 1105121) B1105121
theorem B736759 : Blo 734326 736759 := bstep (se 1 (by rfl) ⟨552569, by rfl⟩ : syracuseStep 736759 = 1105139) B1105139
theorem B736779 : Blo 734326 736779 := bstep (se 1 (by rfl) ⟨552584, by rfl⟩ : syracuseStep 736779 = 1105169) B1105169
theorem B736791 : Blo 734326 736791 := bstep (se 1 (by rfl) ⟨552593, by rfl⟩ : syracuseStep 736791 = 1105187) B1105187
theorem B736811 : Blo 734326 736811 := bstep (se 1 (by rfl) ⟨552608, by rfl⟩ : syracuseStep 736811 = 1105217) B1105217
theorem B736823 : Blo 734326 736823 := bstep (se 1 (by rfl) ⟨552617, by rfl⟩ : syracuseStep 736823 = 1105235) B1105235
theorem B736843 : Blo 734326 736843 := bstep (se 1 (by rfl) ⟨552632, by rfl⟩ : syracuseStep 736843 = 1105265) B1105265
theorem B736855 : Blo 734326 736855 := bstep (se 1 (by rfl) ⟨552641, by rfl⟩ : syracuseStep 736855 = 1105283) B1105283
theorem B1490521 : Blo 734326 1490521 := bstep (se 2 (by rfl) ⟨558945, by rfl⟩ : syracuseStep 1490521 = 1117891) B1117891
theorem B1654361 : Blo 734326 1654361 := bstep (se 2 (by rfl) ⟨620385, by rfl⟩ : syracuseStep 1654361 = 1240771) B1240771
theorem B736875 : Blo 734326 736875 := bstep (se 1 (by rfl) ⟨552656, by rfl⟩ : syracuseStep 736875 = 1105313) B1105313
theorem B736887 : Blo 734326 736887 := bstep (se 1 (by rfl) ⟨552665, by rfl⟩ : syracuseStep 736887 = 1105331) B1105331
theorem B736907 : Blo 734326 736907 := bstep (se 1 (by rfl) ⟨552680, by rfl⟩ : syracuseStep 736907 = 1105361) B1105361
theorem B736919 : Blo 734326 736919 := bstep (se 1 (by rfl) ⟨552689, by rfl⟩ : syracuseStep 736919 = 1105379) B1105379
theorem B736939 : Blo 734326 736939 := bstep (se 1 (by rfl) ⟨552704, by rfl⟩ : syracuseStep 736939 = 1105409) B1105409
theorem B1654451 : Blo 734326 1654451 := bstep (se 1 (by rfl) ⟨1240838, by rfl⟩ : syracuseStep 1654451 = 2481677) B2481677
theorem B736951 : Blo 734326 736951 := bstep (se 1 (by rfl) ⟨552713, by rfl⟩ : syracuseStep 736951 = 1105427) B1105427
theorem B736971 : Blo 734326 736971 := bstep (se 1 (by rfl) ⟨552728, by rfl⟩ : syracuseStep 736971 = 1105457) B1105457
theorem B1654487 : Blo 734326 1654487 := bstep (se 1 (by rfl) ⟨1240865, by rfl⟩ : syracuseStep 1654487 = 2481731) B2481731
theorem B1326809 : Blo 734326 1326809 := bstep (se 2 (by rfl) ⟨497553, by rfl⟩ : syracuseStep 1326809 = 995107) B995107
theorem B736983 : Blo 734326 736983 := bstep (se 1 (by rfl) ⟨552737, by rfl⟩ : syracuseStep 736983 = 1105475) B1105475
theorem B737003 : Blo 734326 737003 := bstep (se 1 (by rfl) ⟨552752, by rfl⟩ : syracuseStep 737003 = 1105505) B1105505
theorem B737015 : Blo 734326 737015 := bstep (se 1 (by rfl) ⟨552761, by rfl⟩ : syracuseStep 737015 = 1105523) B1105523
theorem B2801411 : Blo 734326 2801411 := bstep (se 1 (by rfl) ⟨2101058, by rfl⟩ : syracuseStep 2801411 = 4202117) B4202117
theorem B737035 : Blo 734326 737035 := bstep (se 1 (by rfl) ⟨552776, by rfl⟩ : syracuseStep 737035 = 1105553) B1105553
theorem B2801425 : Blo 734326 2801425 := bstep (se 2 (by rfl) ⟨1050534, by rfl⟩ : syracuseStep 2801425 = 2101069) B2101069
theorem B737047 : Blo 734326 737047 := bstep (se 1 (by rfl) ⟨552785, by rfl⟩ : syracuseStep 737047 = 1105571) B1105571
theorem B737067 : Blo 734326 737067 := bstep (se 1 (by rfl) ⟨552800, by rfl⟩ : syracuseStep 737067 = 1105601) B1105601
theorem B737079 : Blo 734326 737079 := bstep (se 1 (by rfl) ⟨552809, by rfl⟩ : syracuseStep 737079 = 1105619) B1105619
theorem B737099 : Blo 734326 737099 := bstep (se 1 (by rfl) ⟨552824, by rfl⟩ : syracuseStep 737099 = 1105649) B1105649
theorem B933707 : Blo 734326 933707 := bstep (se 1 (by rfl) ⟨700280, by rfl⟩ : syracuseStep 933707 = 1400561) B1400561
theorem B737111 : Blo 734326 737111 := bstep (se 1 (by rfl) ⟨552833, by rfl⟩ : syracuseStep 737111 = 1105667) B1105667
theorem B737131 : Blo 734326 737131 := bstep (se 1 (by rfl) ⟨552848, by rfl⟩ : syracuseStep 737131 = 1105697) B1105697
theorem B737143 : Blo 734326 737143 := bstep (se 1 (by rfl) ⟨552857, by rfl⟩ : syracuseStep 737143 = 1105715) B1105715
theorem B1654667 : Blo 734326 1654667 := bstep (se 1 (by rfl) ⟨1241000, by rfl⟩ : syracuseStep 1654667 = 2482001) B2482001
theorem B737163 : Blo 734326 737163 := bstep (se 1 (by rfl) ⟨552872, by rfl⟩ : syracuseStep 737163 = 1105745) B1105745
theorem B737175 : Blo 734326 737175 := bstep (se 1 (by rfl) ⟨552881, by rfl⟩ : syracuseStep 737175 = 1105763) B1105763
theorem B737195 : Blo 734326 737195 := bstep (se 1 (by rfl) ⟨552896, by rfl⟩ : syracuseStep 737195 = 1105793) B1105793
theorem B737207 : Blo 734326 737207 := bstep (se 1 (by rfl) ⟨552905, by rfl⟩ : syracuseStep 737207 = 1105811) B1105811
theorem B1654721 : Blo 734326 1654721 := bstep (se 2 (by rfl) ⟨620520, by rfl⟩ : syracuseStep 1654721 = 1241041) B1241041
theorem B737227 : Blo 734326 737227 := bstep (se 1 (by rfl) ⟨552920, by rfl⟩ : syracuseStep 737227 = 1105841) B1105841
theorem B737239 : Blo 734326 737239 := bstep (se 1 (by rfl) ⟨552929, by rfl⟩ : syracuseStep 737239 = 1105859) B1105859
theorem B737259 : Blo 734326 737259 := bstep (se 1 (by rfl) ⟨552944, by rfl⟩ : syracuseStep 737259 = 1105889) B1105889
theorem B737271 : Blo 734326 737271 := bstep (se 1 (by rfl) ⟨552953, by rfl⟩ : syracuseStep 737271 = 1105907) B1105907
theorem B737291 : Blo 734326 737291 := bstep (se 1 (by rfl) ⟨552968, by rfl⟩ : syracuseStep 737291 = 1105937) B1105937
theorem B737303 : Blo 734326 737303 := bstep (se 1 (by rfl) ⟨552977, by rfl⟩ : syracuseStep 737303 = 1105955) B1105955
theorem B737323 : Blo 734326 737323 := bstep (se 1 (by rfl) ⟨552992, by rfl⟩ : syracuseStep 737323 = 1105985) B1105985
theorem B737335 : Blo 734326 737335 := bstep (se 1 (by rfl) ⟨553001, by rfl⟩ : syracuseStep 737335 = 1106003) B1106003
theorem B2801729 : Blo 734326 2801729 := bstep (se 2 (by rfl) ⟨1050648, by rfl⟩ : syracuseStep 2801729 = 2101297) B2101297
theorem B737355 : Blo 734326 737355 := bstep (se 1 (by rfl) ⟨553016, by rfl⟩ : syracuseStep 737355 = 1106033) B1106033
theorem B737367 : Blo 734326 737367 := bstep (se 1 (by rfl) ⟨553025, by rfl⟩ : syracuseStep 737367 = 1106051) B1106051
theorem B737387 : Blo 734326 737387 := bstep (se 1 (by rfl) ⟨553040, by rfl⟩ : syracuseStep 737387 = 1106081) B1106081
theorem B737399 : Blo 734326 737399 := bstep (se 1 (by rfl) ⟨553049, by rfl⟩ : syracuseStep 737399 = 1106099) B1106099
theorem B737419 : Blo 734326 737419 := bstep (se 1 (by rfl) ⟨553064, by rfl⟩ : syracuseStep 737419 = 1106129) B1106129
theorem B737431 : Blo 734326 737431 := bstep (se 1 (by rfl) ⟨553073, by rfl⟩ : syracuseStep 737431 = 1106147) B1106147
theorem B1654937 : Blo 734326 1654937 := bstep (se 2 (by rfl) ⟨620601, by rfl⟩ : syracuseStep 1654937 = 1241203) B1241203
theorem B737451 : Blo 734326 737451 := bstep (se 1 (by rfl) ⟨553088, by rfl⟩ : syracuseStep 737451 = 1106177) B1106177
theorem B737463 : Blo 734326 737463 := bstep (se 1 (by rfl) ⟨553097, by rfl⟩ : syracuseStep 737463 = 1106195) B1106195
theorem B737483 : Blo 734326 737483 := bstep (se 1 (by rfl) ⟨553112, by rfl⟩ : syracuseStep 737483 = 1106225) B1106225
theorem B11911373 : Blo 734326 11911373 := bstep (se 3 (by rfl) ⟨2233382, by rfl⟩ : syracuseStep 11911373 = 4466765) B4466765
theorem B737495 : Blo 734326 737495 := bstep (se 1 (by rfl) ⟨553121, by rfl⟩ : syracuseStep 737495 = 1106243) B1106243
theorem B737515 : Blo 734326 737515 := bstep (se 1 (by rfl) ⟨553136, by rfl⟩ : syracuseStep 737515 = 1106273) B1106273
theorem B1655027 : Blo 734326 1655027 := bstep (se 1 (by rfl) ⟨1241270, by rfl⟩ : syracuseStep 1655027 = 2482541) B2482541
theorem B737527 : Blo 734326 737527 := bstep (se 1 (by rfl) ⟨553145, by rfl⟩ : syracuseStep 737527 = 1106291) B1106291
theorem B737547 : Blo 734326 737547 := bstep (se 1 (by rfl) ⟨553160, by rfl⟩ : syracuseStep 737547 = 1106321) B1106321
theorem B1655063 : Blo 734326 1655063 := bstep (se 1 (by rfl) ⟨1241297, by rfl⟩ : syracuseStep 1655063 = 2482595) B2482595
theorem B737559 : Blo 734326 737559 := bstep (se 1 (by rfl) ⟨553169, by rfl⟩ : syracuseStep 737559 = 1106339) B1106339
theorem B737579 : Blo 734326 737579 := bstep (se 1 (by rfl) ⟨553184, by rfl⟩ : syracuseStep 737579 = 1106369) B1106369
theorem B737591 : Blo 734326 737591 := bstep (se 1 (by rfl) ⟨553193, by rfl⟩ : syracuseStep 737591 = 1106387) B1106387
theorem B6275393 : Blo 734326 6275393 := bstep (se 2 (by rfl) ⟨2353272, by rfl⟩ : syracuseStep 6275393 = 4706545) B4706545
theorem B737611 : Blo 734326 737611 := bstep (se 1 (by rfl) ⟨553208, by rfl⟩ : syracuseStep 737611 = 1106417) B1106417
theorem B737623 : Blo 734326 737623 := bstep (se 1 (by rfl) ⟨553217, by rfl⟩ : syracuseStep 737623 = 1106435) B1106435
theorem B737643 : Blo 734326 737643 := bstep (se 1 (by rfl) ⟨553232, by rfl⟩ : syracuseStep 737643 = 1106465) B1106465
theorem B737655 : Blo 734326 737655 := bstep (se 1 (by rfl) ⟨553241, by rfl⟩ : syracuseStep 737655 = 1106483) B1106483
theorem B737675 : Blo 734326 737675 := bstep (se 1 (by rfl) ⟨553256, by rfl⟩ : syracuseStep 737675 = 1106513) B1106513
theorem B737687 : Blo 734326 737687 := bstep (se 1 (by rfl) ⟨553265, by rfl⟩ : syracuseStep 737687 = 1106531) B1106531
theorem B737707 : Blo 734326 737707 := bstep (se 1 (by rfl) ⟨553280, by rfl⟩ : syracuseStep 737707 = 1106561) B1106561
theorem B737719 : Blo 734326 737719 := bstep (se 1 (by rfl) ⟨553289, by rfl⟩ : syracuseStep 737719 = 1106579) B1106579
theorem B1655243 : Blo 734326 1655243 := bstep (se 1 (by rfl) ⟨1241432, by rfl⟩ : syracuseStep 1655243 = 2482865) B2482865
theorem B737739 : Blo 734326 737739 := bstep (se 1 (by rfl) ⟨553304, by rfl⟩ : syracuseStep 737739 = 1106609) B1106609
theorem B737751 : Blo 734326 737751 := bstep (se 1 (by rfl) ⟨553313, by rfl⟩ : syracuseStep 737751 = 1106627) B1106627
theorem B737771 : Blo 734326 737771 := bstep (se 1 (by rfl) ⟨553328, by rfl⟩ : syracuseStep 737771 = 1106657) B1106657
theorem B737783 : Blo 734326 737783 := bstep (se 1 (by rfl) ⟨553337, by rfl⟩ : syracuseStep 737783 = 1106675) B1106675
theorem B1655297 : Blo 734326 1655297 := bstep (se 2 (by rfl) ⟨620736, by rfl⟩ : syracuseStep 1655297 = 1241473) B1241473
theorem B737803 : Blo 734326 737803 := bstep (se 1 (by rfl) ⟨553352, by rfl⟩ : syracuseStep 737803 = 1106705) B1106705
theorem B934411 : Blo 734326 934411 := bstep (se 1 (by rfl) ⟨700808, by rfl⟩ : syracuseStep 934411 = 1401617) B1401617
theorem B737815 : Blo 734326 737815 := bstep (se 1 (by rfl) ⟨553361, by rfl⟩ : syracuseStep 737815 = 1106723) B1106723
theorem B737835 : Blo 734326 737835 := bstep (se 1 (by rfl) ⟨553376, by rfl⟩ : syracuseStep 737835 = 1106753) B1106753
theorem B737847 : Blo 734326 737847 := bstep (se 1 (by rfl) ⟨553385, by rfl⟩ : syracuseStep 737847 = 1106771) B1106771
theorem B737867 : Blo 734326 737867 := bstep (se 1 (by rfl) ⟨553400, by rfl⟩ : syracuseStep 737867 = 1106801) B1106801
theorem B737879 : Blo 734326 737879 := bstep (se 1 (by rfl) ⟨553409, by rfl⟩ : syracuseStep 737879 = 1106819) B1106819
theorem B57459293 : Blo 734326 57459293 := bstep (se 3 (by rfl) ⟨10773617, by rfl⟩ : syracuseStep 57459293 = 21547235) B21547235
theorem B737899 : Blo 734326 737899 := bstep (se 1 (by rfl) ⟨553424, by rfl⟩ : syracuseStep 737899 = 1106849) B1106849
theorem B737911 : Blo 734326 737911 := bstep (se 1 (by rfl) ⟨553433, by rfl⟩ : syracuseStep 737911 = 1106867) B1106867
theorem B737931 : Blo 734326 737931 := bstep (se 1 (by rfl) ⟨553448, by rfl⟩ : syracuseStep 737931 = 1106897) B1106897
theorem B737943 : Blo 734326 737943 := bstep (se 1 (by rfl) ⟨553457, by rfl⟩ : syracuseStep 737943 = 1106915) B1106915
theorem B737963 : Blo 734326 737963 := bstep (se 1 (by rfl) ⟨553472, by rfl⟩ : syracuseStep 737963 = 1106945) B1106945
theorem B737975 : Blo 734326 737975 := bstep (se 1 (by rfl) ⟨553481, by rfl⟩ : syracuseStep 737975 = 1106963) B1106963
theorem B737995 : Blo 734326 737995 := bstep (se 1 (by rfl) ⟨553496, by rfl⟩ : syracuseStep 737995 = 1106993) B1106993
theorem B738007 : Blo 734326 738007 := bstep (se 1 (by rfl) ⟨553505, by rfl⟩ : syracuseStep 738007 = 1107011) B1107011
theorem B1655513 : Blo 734326 1655513 := bstep (se 2 (by rfl) ⟨620817, by rfl⟩ : syracuseStep 1655513 = 1241635) B1241635
theorem B2802397 : Blo 734326 2802397 := bstep (se 3 (by rfl) ⟨525449, by rfl⟩ : syracuseStep 2802397 = 1050899) B1050899
theorem B738027 : Blo 734326 738027 := bstep (se 1 (by rfl) ⟨553520, by rfl⟩ : syracuseStep 738027 = 1107041) B1107041
theorem B738039 : Blo 734326 738039 := bstep (se 1 (by rfl) ⟨553529, by rfl⟩ : syracuseStep 738039 = 1107059) B1107059
theorem B738059 : Blo 734326 738059 := bstep (se 1 (by rfl) ⟨553544, by rfl⟩ : syracuseStep 738059 = 1107089) B1107089
theorem B738071 : Blo 734326 738071 := bstep (se 1 (by rfl) ⟨553553, by rfl⟩ : syracuseStep 738071 = 1107107) B1107107
theorem B738091 : Blo 734326 738091 := bstep (se 1 (by rfl) ⟨553568, by rfl⟩ : syracuseStep 738091 = 1107137) B1107137
theorem B1655603 : Blo 734326 1655603 := bstep (se 1 (by rfl) ⟨1241702, by rfl⟩ : syracuseStep 1655603 = 2483405) B2483405
theorem B738103 : Blo 734326 738103 := bstep (se 1 (by rfl) ⟨553577, by rfl⟩ : syracuseStep 738103 = 1107155) B1107155
theorem B7652161 : Blo 734326 7652161 := bstep (se 2 (by rfl) ⟨2869560, by rfl⟩ : syracuseStep 7652161 = 5739121) B5739121
theorem B738123 : Blo 734326 738123 := bstep (se 1 (by rfl) ⟨553592, by rfl⟩ : syracuseStep 738123 = 1107185) B1107185
theorem B1655639 : Blo 734326 1655639 := bstep (se 1 (by rfl) ⟨1241729, by rfl⟩ : syracuseStep 1655639 = 2483459) B2483459
theorem B738135 : Blo 734326 738135 := bstep (se 1 (by rfl) ⟨553601, by rfl⟩ : syracuseStep 738135 = 1107203) B1107203
theorem B738155 : Blo 734326 738155 := bstep (se 1 (by rfl) ⟨553616, by rfl⟩ : syracuseStep 738155 = 1107233) B1107233
theorem B738167 : Blo 734326 738167 := bstep (se 1 (by rfl) ⟨553625, by rfl⟩ : syracuseStep 738167 = 1107251) B1107251
theorem B738187 : Blo 734326 738187 := bstep (se 1 (by rfl) ⟨553640, by rfl⟩ : syracuseStep 738187 = 1107281) B1107281
theorem B738199 : Blo 734326 738199 := bstep (se 1 (by rfl) ⟨553649, by rfl⟩ : syracuseStep 738199 = 1107299) B1107299
theorem B738219 : Blo 734326 738219 := bstep (se 1 (by rfl) ⟨553664, by rfl⟩ : syracuseStep 738219 = 1107329) B1107329
theorem B738231 : Blo 734326 738231 := bstep (se 1 (by rfl) ⟨553673, by rfl⟩ : syracuseStep 738231 = 1107347) B1107347
theorem B738251 : Blo 734326 738251 := bstep (se 1 (by rfl) ⟨553688, by rfl⟩ : syracuseStep 738251 = 1107377) B1107377
theorem B738263 : Blo 734326 738263 := bstep (se 1 (by rfl) ⟨553697, by rfl⟩ : syracuseStep 738263 = 1107395) B1107395
theorem B738283 : Blo 734326 738283 := bstep (se 1 (by rfl) ⟨553712, by rfl⟩ : syracuseStep 738283 = 1107425) B1107425
theorem B738295 : Blo 734326 738295 := bstep (se 1 (by rfl) ⟨553721, by rfl⟩ : syracuseStep 738295 = 1107443) B1107443
theorem B1655819 : Blo 734326 1655819 := bstep (se 1 (by rfl) ⟨1241864, by rfl⟩ : syracuseStep 1655819 = 2483729) B2483729
theorem B738315 : Blo 734326 738315 := bstep (se 1 (by rfl) ⟨553736, by rfl⟩ : syracuseStep 738315 = 1107473) B1107473
theorem B1655873 : Blo 734326 1655873 := bstep (se 2 (by rfl) ⟨620952, by rfl⟩ : syracuseStep 1655873 = 1241905) B1241905
theorem B1656089 : Blo 734326 1656089 := bstep (se 2 (by rfl) ⟨621033, by rfl⟩ : syracuseStep 1656089 = 1242067) B1242067
theorem B1656179 : Blo 734326 1656179 := bstep (se 1 (by rfl) ⟨1242134, by rfl⟩ : syracuseStep 1656179 = 2484269) B2484269
theorem B1656215 : Blo 734326 1656215 := bstep (se 1 (by rfl) ⟨1242161, by rfl⟩ : syracuseStep 1656215 = 2484323) B2484323
theorem B1656395 : Blo 734326 1656395 := bstep (se 1 (by rfl) ⟨1242296, by rfl⟩ : syracuseStep 1656395 = 2484593) B2484593
theorem B1656449 : Blo 734326 1656449 := bstep (se 2 (by rfl) ⟨621168, by rfl⟩ : syracuseStep 1656449 = 1242337) B1242337
theorem B1394327 : Blo 734326 1394327 := bstep (se 1 (by rfl) ⟨1045745, by rfl⟩ : syracuseStep 1394327 = 2091491) B2091491
theorem B1328791 : Blo 734326 1328791 := bstep (se 1 (by rfl) ⟨996593, by rfl⟩ : syracuseStep 1328791 = 1993187) B1993187
theorem B3720977 : Blo 734326 3720977 := bstep (se 2 (by rfl) ⟨1395366, by rfl⟩ : syracuseStep 3720977 = 2790733) B2790733
theorem B1656665 : Blo 734326 1656665 := bstep (se 2 (by rfl) ⟨621249, by rfl⟩ : syracuseStep 1656665 = 1242499) B1242499
theorem B3721139 : Blo 734326 3721139 := bstep (se 1 (by rfl) ⟨2790854, by rfl⟩ : syracuseStep 3721139 = 5581709) B5581709
theorem B1656755 : Blo 734326 1656755 := bstep (se 1 (by rfl) ⟨1242566, by rfl⟩ : syracuseStep 1656755 = 2485133) B2485133
theorem B1656791 : Blo 734326 1656791 := bstep (se 1 (by rfl) ⟨1242593, by rfl⟩ : syracuseStep 1656791 = 2485187) B2485187
theorem B1656971 : Blo 734326 1656971 := bstep (se 1 (by rfl) ⟨1242728, by rfl⟩ : syracuseStep 1656971 = 2485457) B2485457
theorem B1657025 : Blo 734326 1657025 := bstep (se 2 (by rfl) ⟨621384, by rfl⟩ : syracuseStep 1657025 = 1242769) B1242769
theorem B1394995 : Blo 734326 1394995 := bstep (se 1 (by rfl) ⟨1046246, by rfl⟩ : syracuseStep 1394995 = 2092493) B2092493
theorem B3361169 : Blo 734326 3361169 := bstep (se 2 (by rfl) ⟨1260438, by rfl⟩ : syracuseStep 3361169 = 2520877) B2520877
theorem B1657241 : Blo 734326 1657241 := bstep (se 2 (by rfl) ⟨621465, by rfl⟩ : syracuseStep 1657241 = 1242931) B1242931
theorem B1657331 : Blo 734326 1657331 := bstep (se 1 (by rfl) ⟨1242998, by rfl⟩ : syracuseStep 1657331 = 2485997) B2485997
theorem B1657367 : Blo 734326 1657367 := bstep (se 1 (by rfl) ⟨1243025, by rfl⟩ : syracuseStep 1657367 = 2486051) B2486051
theorem B6277783 : Blo 734326 6277783 := bstep (se 1 (by rfl) ⟨4708337, by rfl⟩ : syracuseStep 6277783 = 9416675) B9416675
theorem B1657547 : Blo 734326 1657547 := bstep (se 1 (by rfl) ⟨1243160, by rfl⟩ : syracuseStep 1657547 = 2486321) B2486321
theorem B1395443 : Blo 734326 1395443 := bstep (se 1 (by rfl) ⟨1046582, by rfl⟩ : syracuseStep 1395443 = 2093165) B2093165
theorem B1657601 : Blo 734326 1657601 := bstep (se 2 (by rfl) ⟨621600, by rfl⟩ : syracuseStep 1657601 = 1243201) B1243201
theorem B1395481 : Blo 734326 1395481 := bstep (se 2 (by rfl) ⟨523305, by rfl⟩ : syracuseStep 1395481 = 1046611) B1046611
theorem B1985369 : Blo 734326 1985369 := bstep (se 2 (by rfl) ⟨744513, by rfl⟩ : syracuseStep 1985369 = 1489027) B1489027
theorem B1657817 : Blo 734326 1657817 := bstep (se 2 (by rfl) ⟨621681, by rfl⟩ : syracuseStep 1657817 = 1243363) B1243363
theorem B5753861 : Blo 734326 5753861 := bstep (se 4 (by rfl) ⟨539424, by rfl⟩ : syracuseStep 5753861 = 1078849) B1078849
theorem B1657907 : Blo 734326 1657907 := bstep (se 1 (by rfl) ⟨1243430, by rfl⟩ : syracuseStep 1657907 = 2486861) B2486861
theorem B1657943 : Blo 734326 1657943 := bstep (se 1 (by rfl) ⟨1243457, by rfl⟩ : syracuseStep 1657943 = 2486915) B2486915
theorem B1592473 : Blo 734326 1592473 := bstep (se 2 (by rfl) ⟨597177, by rfl⟩ : syracuseStep 1592473 = 1194355) B1194355
theorem B1330391 : Blo 734326 1330391 := bstep (se 1 (by rfl) ⟨997793, by rfl⟩ : syracuseStep 1330391 = 1995587) B1995587
theorem B1395929 : Blo 734326 1395929 := bstep (se 2 (by rfl) ⟨523473, by rfl⟩ : syracuseStep 1395929 = 1046947) B1046947
theorem B1658123 : Blo 734326 1658123 := bstep (se 1 (by rfl) ⟨1243592, by rfl⟩ : syracuseStep 1658123 = 2487185) B2487185
theorem B1658177 : Blo 734326 1658177 := bstep (se 2 (by rfl) ⟨621816, by rfl⟩ : syracuseStep 1658177 = 1243633) B1243633
theorem B838987 : Blo 734326 838987 := bstep (se 1 (by rfl) ⟨629240, by rfl⟩ : syracuseStep 838987 = 1258481) B1258481
theorem B1658393 : Blo 734326 1658393 := bstep (se 2 (by rfl) ⟨621897, by rfl⟩ : syracuseStep 1658393 = 1243795) B1243795
theorem B3788333 : Blo 734326 3788333 := bstep (se 3 (by rfl) ⟨710312, by rfl⟩ : syracuseStep 3788333 = 1420625) B1420625
theorem B1658483 : Blo 734326 1658483 := bstep (se 1 (by rfl) ⟨1243862, by rfl⟩ : syracuseStep 1658483 = 2487725) B2487725
theorem B1658519 : Blo 734326 1658519 := bstep (se 1 (by rfl) ⟨1243889, by rfl⟩ : syracuseStep 1658519 = 2487779) B2487779
theorem B6704819 : Blo 734326 6704819 := bstep (se 1 (by rfl) ⟨5028614, by rfl⟩ : syracuseStep 6704819 = 10057229) B10057229
theorem B1101515 : Blo 734326 1101515 := bstep (se 1 (by rfl) ⟨826136, by rfl⟩ : syracuseStep 1101515 = 1652273) B1652273
theorem B1101527 : Blo 734326 1101527 := bstep (se 1 (by rfl) ⟨826145, by rfl⟩ : syracuseStep 1101527 = 1652291) B1652291
theorem B1101593 : Blo 734326 1101593 := bstep (se 2 (by rfl) ⟨413097, by rfl⟩ : syracuseStep 1101593 = 826195) B826195
theorem B3723083 : Blo 734326 3723083 := bstep (se 1 (by rfl) ⟨2792312, by rfl⟩ : syracuseStep 3723083 = 5584625) B5584625
theorem B1658699 : Blo 734326 1658699 := bstep (se 1 (by rfl) ⟨1244024, by rfl⟩ : syracuseStep 1658699 = 2488049) B2488049
theorem B1658753 : Blo 734326 1658753 := bstep (se 2 (by rfl) ⟨622032, by rfl⟩ : syracuseStep 1658753 = 1244065) B1244065
theorem B1101707 : Blo 734326 1101707 := bstep (se 1 (by rfl) ⟨826280, by rfl⟩ : syracuseStep 1101707 = 1652561) B1652561
theorem B1101719 : Blo 734326 1101719 := bstep (se 1 (by rfl) ⟨826289, by rfl⟩ : syracuseStep 1101719 = 1652579) B1652579
theorem B1396673 : Blo 734326 1396673 := bstep (se 2 (by rfl) ⟨523752, by rfl⟩ : syracuseStep 1396673 = 1047505) B1047505
theorem B1101785 : Blo 734326 1101785 := bstep (se 2 (by rfl) ⟨413169, by rfl⟩ : syracuseStep 1101785 = 826339) B826339
theorem B9457681 : Blo 734326 9457681 := bstep (se 2 (by rfl) ⟨3546630, by rfl⟩ : syracuseStep 9457681 = 7093261) B7093261
theorem B1101899 : Blo 734326 1101899 := bstep (se 1 (by rfl) ⟨826424, by rfl⟩ : syracuseStep 1101899 = 1652849) B1652849
theorem B1101911 : Blo 734326 1101911 := bstep (se 1 (by rfl) ⟨826433, by rfl⟩ : syracuseStep 1101911 = 1652867) B1652867
theorem B1658969 : Blo 734326 1658969 := bstep (se 2 (by rfl) ⟨622113, by rfl⟩ : syracuseStep 1658969 = 1244227) B1244227
theorem B1101977 : Blo 734326 1101977 := bstep (se 2 (by rfl) ⟨413241, by rfl⟩ : syracuseStep 1101977 = 826483) B826483
theorem B1659059 : Blo 734326 1659059 := bstep (se 1 (by rfl) ⟨1244294, by rfl⟩ : syracuseStep 1659059 = 2488589) B2488589
theorem B1396939 : Blo 734326 1396939 := bstep (se 1 (by rfl) ⟨1047704, by rfl⟩ : syracuseStep 1396939 = 2095409) B2095409
theorem B1659095 : Blo 734326 1659095 := bstep (se 1 (by rfl) ⟨1244321, by rfl⟩ : syracuseStep 1659095 = 2488643) B2488643
theorem B1495255 : Blo 734326 1495255 := bstep (se 1 (by rfl) ⟨1121441, by rfl⟩ : syracuseStep 1495255 = 2242883) B2242883
theorem B1102091 : Blo 734326 1102091 := bstep (se 1 (by rfl) ⟨826568, by rfl⟩ : syracuseStep 1102091 = 1653137) B1653137
theorem B1102103 : Blo 734326 1102103 := bstep (se 1 (by rfl) ⟨826577, by rfl⟩ : syracuseStep 1102103 = 1653155) B1653155
theorem B1102169 : Blo 734326 1102169 := bstep (se 2 (by rfl) ⟨413313, by rfl⟩ : syracuseStep 1102169 = 826627) B826627
theorem B1659275 : Blo 734326 1659275 := bstep (se 1 (by rfl) ⟨1244456, by rfl⟩ : syracuseStep 1659275 = 2488913) B2488913
theorem B1659329 : Blo 734326 1659329 := bstep (se 2 (by rfl) ⟨622248, by rfl⟩ : syracuseStep 1659329 = 1244497) B1244497
theorem B1102283 : Blo 734326 1102283 := bstep (se 1 (by rfl) ⟨826712, by rfl⟩ : syracuseStep 1102283 = 1653425) B1653425
theorem B1102295 : Blo 734326 1102295 := bstep (se 1 (by rfl) ⟨826721, by rfl⟩ : syracuseStep 1102295 = 1653443) B1653443
theorem B1102361 : Blo 734326 1102361 := bstep (se 2 (by rfl) ⟨413385, by rfl⟩ : syracuseStep 1102361 = 826771) B826771
theorem B1102475 : Blo 734326 1102475 := bstep (se 1 (by rfl) ⟨826856, by rfl⟩ : syracuseStep 1102475 = 1653713) B1653713
theorem B1397387 : Blo 734326 1397387 := bstep (se 1 (by rfl) ⟨1048040, by rfl⟩ : syracuseStep 1397387 = 2096081) B2096081
theorem B1102487 : Blo 734326 1102487 := bstep (se 1 (by rfl) ⟨826865, by rfl⟩ : syracuseStep 1102487 = 1653731) B1653731
theorem B1659545 : Blo 734326 1659545 := bstep (se 2 (by rfl) ⟨622329, by rfl⟩ : syracuseStep 1659545 = 1244659) B1244659
theorem B1102553 : Blo 734326 1102553 := bstep (se 2 (by rfl) ⟨413457, by rfl⟩ : syracuseStep 1102553 = 826915) B826915
theorem B60576497 : Blo 734326 60576497 := bstep (se 2 (by rfl) ⟨22716186, by rfl⟩ : syracuseStep 60576497 = 45432373) B45432373
theorem B1659635 : Blo 734326 1659635 := bstep (se 1 (by rfl) ⟨1244726, by rfl⟩ : syracuseStep 1659635 = 2489453) B2489453
theorem B1659671 : Blo 734326 1659671 := bstep (se 1 (by rfl) ⟨1244753, by rfl⟩ : syracuseStep 1659671 = 2489507) B2489507
theorem B12112685 : Blo 734326 12112685 := bstep (se 3 (by rfl) ⟨2271128, by rfl⟩ : syracuseStep 12112685 = 4542257) B4542257
theorem B1397569 : Blo 734326 1397569 := bstep (se 2 (by rfl) ⟨524088, by rfl⟩ : syracuseStep 1397569 = 1048177) B1048177
theorem B2478923 : Blo 734326 2478923 := bstep (se 1 (by rfl) ⟨1859192, by rfl⟩ : syracuseStep 2478923 = 3718385) B3718385
theorem B1102667 : Blo 734326 1102667 := bstep (se 1 (by rfl) ⟨827000, by rfl⟩ : syracuseStep 1102667 = 1654001) B1654001
theorem B1102679 : Blo 734326 1102679 := bstep (se 1 (by rfl) ⟨827009, by rfl⟩ : syracuseStep 1102679 = 1654019) B1654019
theorem B1364825 : Blo 734326 1364825 := bstep (se 2 (by rfl) ⟨511809, by rfl⟩ : syracuseStep 1364825 = 1023619) B1023619
theorem B1102745 : Blo 734326 1102745 := bstep (se 2 (by rfl) ⟨413529, by rfl⟩ : syracuseStep 1102745 = 827059) B827059
theorem B1659851 : Blo 734326 1659851 := bstep (se 1 (by rfl) ⟨1244888, by rfl⟩ : syracuseStep 1659851 = 2489777) B2489777
theorem B1659905 : Blo 734326 1659905 := bstep (se 2 (by rfl) ⟨622464, by rfl⟩ : syracuseStep 1659905 = 1244929) B1244929
theorem B1102859 : Blo 734326 1102859 := bstep (se 1 (by rfl) ⟨827144, by rfl⟩ : syracuseStep 1102859 = 1654289) B1654289
theorem B1102871 : Blo 734326 1102871 := bstep (se 1 (by rfl) ⟨827153, by rfl⟩ : syracuseStep 1102871 = 1654307) B1654307
theorem B1791041 : Blo 734326 1791041 := bstep (se 2 (by rfl) ⟨671640, by rfl⟩ : syracuseStep 1791041 = 1343281) B1343281
theorem B1889345 : Blo 734326 1889345 := bstep (se 2 (by rfl) ⟨708504, by rfl⟩ : syracuseStep 1889345 = 1417009) B1417009
theorem B2479193 : Blo 734326 2479193 := bstep (se 2 (by rfl) ⟨929697, by rfl⟩ : syracuseStep 2479193 = 1859395) B1859395
theorem B1102937 : Blo 734326 1102937 := bstep (se 2 (by rfl) ⟨413601, by rfl⟩ : syracuseStep 1102937 = 827203) B827203
theorem B1397911 : Blo 734326 1397911 := bstep (se 1 (by rfl) ⟨1048433, by rfl⟩ : syracuseStep 1397911 = 2096867) B2096867
theorem B1103051 : Blo 734326 1103051 := bstep (se 1 (by rfl) ⟨827288, by rfl⟩ : syracuseStep 1103051 = 1654577) B1654577
theorem B1103063 : Blo 734326 1103063 := bstep (se 1 (by rfl) ⟨827297, by rfl⟩ : syracuseStep 1103063 = 1654595) B1654595
theorem B1660121 : Blo 734326 1660121 := bstep (se 2 (by rfl) ⟨622545, by rfl⟩ : syracuseStep 1660121 = 1245091) B1245091
theorem B1103129 : Blo 734326 1103129 := bstep (se 2 (by rfl) ⟨413673, by rfl⟩ : syracuseStep 1103129 = 827347) B827347
theorem B1660211 : Blo 734326 1660211 := bstep (se 1 (by rfl) ⟨1245158, by rfl⟩ : syracuseStep 1660211 = 2490317) B2490317
theorem B1725761 : Blo 734326 1725761 := bstep (se 2 (by rfl) ⟨647160, by rfl⟩ : syracuseStep 1725761 = 1294321) B1294321
theorem B1660247 : Blo 734326 1660247 := bstep (se 1 (by rfl) ⟨1245185, by rfl⟩ : syracuseStep 1660247 = 2490371) B2490371
theorem B1398131 : Blo 734326 1398131 := bstep (se 1 (by rfl) ⟨1048598, by rfl⟩ : syracuseStep 1398131 = 2097197) B2097197
theorem B7853429 : Blo 734326 7853429 := bstep (se 5 (by rfl) ⟨368129, by rfl⟩ : syracuseStep 7853429 = 736259) B736259
theorem B1103243 : Blo 734326 1103243 := bstep (se 1 (by rfl) ⟨827432, by rfl⟩ : syracuseStep 1103243 = 1654865) B1654865
theorem B1103255 : Blo 734326 1103255 := bstep (se 1 (by rfl) ⟨827441, by rfl⟩ : syracuseStep 1103255 = 1654883) B1654883
theorem B1103321 : Blo 734326 1103321 := bstep (se 2 (by rfl) ⟨413745, by rfl⟩ : syracuseStep 1103321 = 827491) B827491
theorem B1660427 : Blo 734326 1660427 := bstep (se 1 (by rfl) ⟨1245320, by rfl⟩ : syracuseStep 1660427 = 2490641) B2490641
theorem B3724865 : Blo 734326 3724865 := bstep (se 2 (by rfl) ⟨1396824, by rfl⟩ : syracuseStep 3724865 = 2793649) B2793649
theorem B2840129 : Blo 734326 2840129 := bstep (se 2 (by rfl) ⟨1065048, by rfl⟩ : syracuseStep 2840129 = 2130097) B2130097
theorem B1660481 : Blo 734326 1660481 := bstep (se 2 (by rfl) ⟨622680, by rfl⟩ : syracuseStep 1660481 = 1245361) B1245361
theorem B1103435 : Blo 734326 1103435 := bstep (se 1 (by rfl) ⟨827576, by rfl⟩ : syracuseStep 1103435 = 1655153) B1655153
theorem B1103447 : Blo 734326 1103447 := bstep (se 1 (by rfl) ⟨827585, by rfl⟩ : syracuseStep 1103447 = 1655171) B1655171
theorem B1398359 : Blo 734326 1398359 := bstep (se 1 (by rfl) ⟨1048769, by rfl⟩ : syracuseStep 1398359 = 2097539) B2097539
theorem B1103513 : Blo 734326 1103513 := bstep (se 2 (by rfl) ⟨413817, by rfl⟩ : syracuseStep 1103513 = 827635) B827635
theorem B3364525 : Blo 734326 3364525 := bstep (se 3 (by rfl) ⟨630848, by rfl⟩ : syracuseStep 3364525 = 1261697) B1261697
theorem B1103627 : Blo 734326 1103627 := bstep (se 1 (by rfl) ⟨827720, by rfl⟩ : syracuseStep 1103627 = 1655441) B1655441
theorem B2479895 : Blo 734326 2479895 := bstep (se 1 (by rfl) ⟨1859921, by rfl⟩ : syracuseStep 2479895 = 3719843) B3719843
theorem B1103639 : Blo 734326 1103639 := bstep (se 1 (by rfl) ⟨827729, by rfl⟩ : syracuseStep 1103639 = 1655459) B1655459
theorem B1660697 : Blo 734326 1660697 := bstep (se 2 (by rfl) ⟨622761, by rfl⟩ : syracuseStep 1660697 = 1245523) B1245523
theorem B1103705 : Blo 734326 1103705 := bstep (se 2 (by rfl) ⟨413889, by rfl⟩ : syracuseStep 1103705 = 827779) B827779
theorem B1398617 : Blo 734326 1398617 := bstep (se 2 (by rfl) ⟨524481, by rfl⟩ : syracuseStep 1398617 = 1048963) B1048963
theorem B1660787 : Blo 734326 1660787 := bstep (se 1 (by rfl) ⟨1245590, by rfl⟩ : syracuseStep 1660787 = 2491181) B2491181
theorem B1660823 : Blo 734326 1660823 := bstep (se 1 (by rfl) ⟨1245617, by rfl⟩ : syracuseStep 1660823 = 2491235) B2491235
theorem B35903411 : Blo 734326 35903411 := bstep (se 1 (by rfl) ⟨26927558, by rfl⟩ : syracuseStep 35903411 = 53855117) B53855117
theorem B1103819 : Blo 734326 1103819 := bstep (se 1 (by rfl) ⟨827864, by rfl⟩ : syracuseStep 1103819 = 1655729) B1655729
theorem B1103831 : Blo 734326 1103831 := bstep (se 1 (by rfl) ⟨827873, by rfl⟩ : syracuseStep 1103831 = 1655747) B1655747
theorem B808951 : Blo 734326 808951 := bstep (se 1 (by rfl) ⟨606713, by rfl⟩ : syracuseStep 808951 = 1213427) B1213427
theorem B1103897 : Blo 734326 1103897 := bstep (se 2 (by rfl) ⟨413961, by rfl⟩ : syracuseStep 1103897 = 827923) B827923
theorem B1595467 : Blo 734326 1595467 := bstep (se 1 (by rfl) ⟨1196600, by rfl⟩ : syracuseStep 1595467 = 2393201) B2393201
theorem B1661003 : Blo 734326 1661003 := bstep (se 1 (by rfl) ⟨1245752, by rfl⟩ : syracuseStep 1661003 = 2491505) B2491505
theorem B1661057 : Blo 734326 1661057 := bstep (se 2 (by rfl) ⟨622896, by rfl⟩ : syracuseStep 1661057 = 1245793) B1245793
theorem B1104011 : Blo 734326 1104011 := bstep (se 1 (by rfl) ⟨828008, by rfl⟩ : syracuseStep 1104011 = 1656017) B1656017
theorem B1104023 : Blo 734326 1104023 := bstep (se 1 (by rfl) ⟨828017, by rfl⟩ : syracuseStep 1104023 = 1656035) B1656035
theorem B1104089 : Blo 734326 1104089 := bstep (se 2 (by rfl) ⟨414033, by rfl⟩ : syracuseStep 1104089 = 828067) B828067
theorem B1399027 : Blo 734326 1399027 := bstep (se 1 (by rfl) ⟨1049270, by rfl⟩ : syracuseStep 1399027 = 2098541) B2098541
theorem B2480435 : Blo 734326 2480435 := bstep (se 1 (by rfl) ⟨1860326, by rfl⟩ : syracuseStep 2480435 = 3720653) B3720653
theorem B1104203 : Blo 734326 1104203 := bstep (se 1 (by rfl) ⟨828152, by rfl⟩ : syracuseStep 1104203 = 1656305) B1656305
theorem B1104215 : Blo 734326 1104215 := bstep (se 1 (by rfl) ⟨828161, by rfl⟩ : syracuseStep 1104215 = 1656323) B1656323
theorem B1104281 : Blo 734326 1104281 := bstep (se 2 (by rfl) ⟨414105, by rfl⟩ : syracuseStep 1104281 = 828211) B828211
theorem B1104395 : Blo 734326 1104395 := bstep (se 1 (by rfl) ⟨828296, by rfl⟩ : syracuseStep 1104395 = 1656593) B1656593
theorem B1104407 : Blo 734326 1104407 := bstep (se 1 (by rfl) ⟨828305, by rfl⟩ : syracuseStep 1104407 = 1656611) B1656611
theorem B4184621 : Blo 734326 4184621 := bstep (se 3 (by rfl) ⟨784616, by rfl⟩ : syracuseStep 4184621 = 1569233) B1569233
theorem B2480705 : Blo 734326 2480705 := bstep (se 2 (by rfl) ⟨930264, by rfl⟩ : syracuseStep 2480705 = 1860529) B1860529
theorem B1104473 : Blo 734326 1104473 := bstep (se 2 (by rfl) ⟨414177, by rfl⟩ : syracuseStep 1104473 = 828355) B828355
theorem B1104587 : Blo 734326 1104587 := bstep (se 1 (by rfl) ⟨828440, by rfl⟩ : syracuseStep 1104587 = 1656881) B1656881
theorem B1104599 : Blo 734326 1104599 := bstep (se 1 (by rfl) ⟨828449, by rfl⟩ : syracuseStep 1104599 = 1656899) B1656899
theorem B1399513 : Blo 734326 1399513 := bstep (se 2 (by rfl) ⟨524817, by rfl⟩ : syracuseStep 1399513 = 1049635) B1049635
theorem B1104665 : Blo 734326 1104665 := bstep (se 2 (by rfl) ⟨414249, by rfl⟩ : syracuseStep 1104665 = 828499) B828499
theorem B5299019 : Blo 734326 5299019 := bstep (se 1 (by rfl) ⟨3974264, by rfl⟩ : syracuseStep 5299019 = 7948529) B7948529
theorem B1104779 : Blo 734326 1104779 := bstep (se 1 (by rfl) ⟨828584, by rfl⟩ : syracuseStep 1104779 = 1657169) B1657169
theorem B1104791 : Blo 734326 1104791 := bstep (se 1 (by rfl) ⟨828593, by rfl⟩ : syracuseStep 1104791 = 1657187) B1657187
theorem B1104857 : Blo 734326 1104857 := bstep (se 2 (by rfl) ⟨414321, by rfl⟩ : syracuseStep 1104857 = 828643) B828643
theorem B1104971 : Blo 734326 1104971 := bstep (se 1 (by rfl) ⟨828728, by rfl⟩ : syracuseStep 1104971 = 1657457) B1657457
theorem B1104983 : Blo 734326 1104983 := bstep (se 1 (by rfl) ⟨828737, by rfl⟩ : syracuseStep 1104983 = 1657475) B1657475
theorem B2481245 : Blo 734326 2481245 := bstep (se 3 (by rfl) ⟨465233, by rfl⟩ : syracuseStep 2481245 = 930467) B930467
theorem B1105049 : Blo 734326 1105049 := bstep (se 2 (by rfl) ⟨414393, by rfl⟩ : syracuseStep 1105049 = 828787) B828787
theorem B1105163 : Blo 734326 1105163 := bstep (se 1 (by rfl) ⟨828872, by rfl⟩ : syracuseStep 1105163 = 1657745) B1657745
theorem B1400075 : Blo 734326 1400075 := bstep (se 1 (by rfl) ⟨1050056, by rfl⟩ : syracuseStep 1400075 = 2100113) B2100113
theorem B1105175 : Blo 734326 1105175 := bstep (se 1 (by rfl) ⟨828881, by rfl⟩ : syracuseStep 1105175 = 1657763) B1657763
theorem B1105241 : Blo 734326 1105241 := bstep (se 2 (by rfl) ⟨414465, by rfl⟩ : syracuseStep 1105241 = 828931) B828931
theorem B1400257 : Blo 734326 1400257 := bstep (se 2 (by rfl) ⟨525096, by rfl⟩ : syracuseStep 1400257 = 1050193) B1050193
theorem B1105355 : Blo 734326 1105355 := bstep (se 1 (by rfl) ⟨829016, by rfl⟩ : syracuseStep 1105355 = 1658033) B1658033
theorem B1105367 : Blo 734326 1105367 := bstep (se 1 (by rfl) ⟨829025, by rfl⟩ : syracuseStep 1105367 = 1658051) B1658051
theorem B3726809 : Blo 734326 3726809 := bstep (se 2 (by rfl) ⟨1397553, by rfl⟩ : syracuseStep 3726809 = 2795107) B2795107
theorem B1105433 : Blo 734326 1105433 := bstep (se 2 (by rfl) ⟨414537, by rfl⟩ : syracuseStep 1105433 = 829075) B829075
theorem B1105547 : Blo 734326 1105547 := bstep (se 1 (by rfl) ⟨829160, by rfl⟩ : syracuseStep 1105547 = 1658321) B1658321
theorem B1105559 : Blo 734326 1105559 := bstep (se 1 (by rfl) ⟨829169, by rfl⟩ : syracuseStep 1105559 = 1658339) B1658339
theorem B1105625 : Blo 734326 1105625 := bstep (se 2 (by rfl) ⟨414609, by rfl⟩ : syracuseStep 1105625 = 829219) B829219
theorem B3366659 : Blo 734326 3366659 := bstep (se 1 (by rfl) ⟨2524994, by rfl⟩ : syracuseStep 3366659 = 5049989) B5049989
theorem B1105739 : Blo 734326 1105739 := bstep (se 1 (by rfl) ⟨829304, by rfl⟩ : syracuseStep 1105739 = 1658609) B1658609
theorem B1105751 : Blo 734326 1105751 := bstep (se 1 (by rfl) ⟨829313, by rfl⟩ : syracuseStep 1105751 = 1658627) B1658627
theorem B1105817 : Blo 734326 1105817 := bstep (se 2 (by rfl) ⟨414681, by rfl⟩ : syracuseStep 1105817 = 829363) B829363
theorem B1859507 : Blo 734326 1859507 := bstep (se 1 (by rfl) ⟨1394630, by rfl⟩ : syracuseStep 1859507 = 2789261) B2789261
theorem B1105931 : Blo 734326 1105931 := bstep (se 1 (by rfl) ⟨829448, by rfl⟩ : syracuseStep 1105931 = 1658897) B1658897
theorem B1105943 : Blo 734326 1105943 := bstep (se 1 (by rfl) ⟨829457, by rfl⟩ : syracuseStep 1105943 = 1658915) B1658915
theorem B1106009 : Blo 734326 1106009 := bstep (se 2 (by rfl) ⟨414753, by rfl⟩ : syracuseStep 1106009 = 829507) B829507
theorem B1400971 : Blo 734326 1400971 := bstep (se 1 (by rfl) ⟨1050728, by rfl⟩ : syracuseStep 1400971 = 2101457) B2101457
theorem B2482379 : Blo 734326 2482379 := bstep (se 1 (by rfl) ⟨1861784, by rfl⟩ : syracuseStep 2482379 = 3723569) B3723569
theorem B1106123 : Blo 734326 1106123 := bstep (se 1 (by rfl) ⟨829592, by rfl⟩ : syracuseStep 1106123 = 1659185) B1659185
theorem B3367115 : Blo 734326 3367115 := bstep (se 1 (by rfl) ⟨2525336, by rfl⟩ : syracuseStep 3367115 = 5050673) B5050673
theorem B1106135 : Blo 734326 1106135 := bstep (se 1 (by rfl) ⟨829601, by rfl⟩ : syracuseStep 1106135 = 1659203) B1659203
theorem B1401047 : Blo 734326 1401047 := bstep (se 1 (by rfl) ⟨1050785, by rfl⟩ : syracuseStep 1401047 = 2101571) B2101571
theorem B1106201 : Blo 734326 1106201 := bstep (se 2 (by rfl) ⟨414825, by rfl⟩ : syracuseStep 1106201 = 829651) B829651
theorem B1106315 : Blo 734326 1106315 := bstep (se 1 (by rfl) ⟨829736, by rfl⟩ : syracuseStep 1106315 = 1659473) B1659473
theorem B1106327 : Blo 734326 1106327 := bstep (se 1 (by rfl) ⟨829745, by rfl⟩ : syracuseStep 1106327 = 1659491) B1659491
theorem B1860043 : Blo 734326 1860043 := bstep (se 1 (by rfl) ⟨1395032, by rfl⟩ : syracuseStep 1860043 = 2790065) B2790065
theorem B2482649 : Blo 734326 2482649 := bstep (se 2 (by rfl) ⟨930993, by rfl⟩ : syracuseStep 2482649 = 1861987) B1861987
theorem B1106393 : Blo 734326 1106393 := bstep (se 2 (by rfl) ⟨414897, by rfl⟩ : syracuseStep 1106393 = 829795) B829795
theorem B26894861 : Blo 734326 26894861 := bstep (se 3 (by rfl) ⟨5042786, by rfl⟩ : syracuseStep 26894861 = 10085573) B10085573
theorem B12575249 : Blo 734326 12575249 := bstep (se 2 (by rfl) ⟨4715718, by rfl⟩ : syracuseStep 12575249 = 9431437) B9431437
theorem B1106507 : Blo 734326 1106507 := bstep (se 1 (by rfl) ⟨829880, by rfl⟩ : syracuseStep 1106507 = 1659761) B1659761
theorem B1106519 : Blo 734326 1106519 := bstep (se 1 (by rfl) ⟨829889, by rfl⟩ : syracuseStep 1106519 = 1659779) B1659779
theorem B1860185 : Blo 734326 1860185 := bstep (se 2 (by rfl) ⟨697569, by rfl⟩ : syracuseStep 1860185 = 1395139) B1395139
theorem B1991261 : Blo 734326 1991261 := bstep (se 3 (by rfl) ⟨373361, by rfl⟩ : syracuseStep 1991261 = 746723) B746723
theorem B1106585 : Blo 734326 1106585 := bstep (se 2 (by rfl) ⟨414969, by rfl⟩ : syracuseStep 1106585 = 829939) B829939
theorem B1991347 : Blo 734326 1991347 := bstep (se 1 (by rfl) ⟨1493510, by rfl⟩ : syracuseStep 1991347 = 2987021) B2987021
theorem B1106699 : Blo 734326 1106699 := bstep (se 1 (by rfl) ⟨830024, by rfl⟩ : syracuseStep 1106699 = 1660049) B1660049
theorem B1106711 : Blo 734326 1106711 := bstep (se 1 (by rfl) ⟨830033, by rfl⟩ : syracuseStep 1106711 = 1660067) B1660067
theorem B1106777 : Blo 734326 1106777 := bstep (se 2 (by rfl) ⟨415041, by rfl⟩ : syracuseStep 1106777 = 830083) B830083
theorem B4187011 : Blo 734326 4187011 := bstep (se 1 (by rfl) ⟨3140258, by rfl⟩ : syracuseStep 4187011 = 6280517) B6280517
theorem B1106891 : Blo 734326 1106891 := bstep (se 1 (by rfl) ⟨830168, by rfl⟩ : syracuseStep 1106891 = 1660337) B1660337
theorem B1106903 : Blo 734326 1106903 := bstep (se 1 (by rfl) ⟨830177, by rfl⟩ : syracuseStep 1106903 = 1660355) B1660355
theorem B1106969 : Blo 734326 1106969 := bstep (se 2 (by rfl) ⟨415113, by rfl⟩ : syracuseStep 1106969 = 830227) B830227
theorem B3728429 : Blo 734326 3728429 := bstep (se 3 (by rfl) ⟨699080, by rfl⟩ : syracuseStep 3728429 = 1398161) B1398161
theorem B4711517 : Blo 734326 4711517 := bstep (se 3 (by rfl) ⟨883409, by rfl⟩ : syracuseStep 4711517 = 1766819) B1766819
theorem B7070813 : Blo 734326 7070813 := bstep (se 3 (by rfl) ⟨1325777, by rfl⟩ : syracuseStep 7070813 = 2651555) B2651555
theorem B5301379 : Blo 734326 5301379 := bstep (se 1 (by rfl) ⟨3976034, by rfl⟩ : syracuseStep 5301379 = 7952069) B7952069
theorem B1107083 : Blo 734326 1107083 := bstep (se 1 (by rfl) ⟨830312, by rfl⟩ : syracuseStep 1107083 = 1660625) B1660625
theorem B2483351 : Blo 734326 2483351 := bstep (se 1 (by rfl) ⟨1862513, by rfl⟩ : syracuseStep 2483351 = 3725027) B3725027
theorem B1107095 : Blo 734326 1107095 := bstep (se 1 (by rfl) ⟨830321, by rfl⟩ : syracuseStep 1107095 = 1660643) B1660643
theorem B1107161 : Blo 734326 1107161 := bstep (se 2 (by rfl) ⟨415185, by rfl⟩ : syracuseStep 1107161 = 830371) B830371
theorem B1107275 : Blo 734326 1107275 := bstep (se 1 (by rfl) ⟨830456, by rfl⟩ : syracuseStep 1107275 = 1660913) B1660913
theorem B1107287 : Blo 734326 1107287 := bstep (se 1 (by rfl) ⟨830465, by rfl⟩ : syracuseStep 1107287 = 1660931) B1660931
theorem B1861015 : Blo 734326 1861015 := bstep (se 1 (by rfl) ⟨1395761, by rfl⟩ : syracuseStep 1861015 = 2791523) B2791523
theorem B1107353 : Blo 734326 1107353 := bstep (se 2 (by rfl) ⟨415257, by rfl⟩ : syracuseStep 1107353 = 830515) B830515
theorem B1107467 : Blo 734326 1107467 := bstep (se 1 (by rfl) ⟨830600, by rfl⟩ : syracuseStep 1107467 = 1661201) B1661201
theorem B1107479 : Blo 734326 1107479 := bstep (se 1 (by rfl) ⟨830609, by rfl⟩ : syracuseStep 1107479 = 1661219) B1661219
theorem B6448733 : Blo 734326 6448733 := bstep (se 3 (by rfl) ⟨1209137, by rfl⟩ : syracuseStep 6448733 = 2418275) B2418275
theorem B3139165 : Blo 734326 3139165 := bstep (se 3 (by rfl) ⟨588593, by rfl⟩ : syracuseStep 3139165 = 1177187) B1177187
theorem B13428317 : Blo 734326 13428317 := bstep (se 3 (by rfl) ⟨2517809, by rfl⟩ : syracuseStep 13428317 = 5035619) B5035619
theorem B22668893 : Blo 734326 22668893 := bstep (se 3 (by rfl) ⟨4250417, by rfl⟩ : syracuseStep 22668893 = 8500835) B8500835
theorem B2483891 : Blo 734326 2483891 := bstep (se 1 (by rfl) ⟨1862918, by rfl⟩ : syracuseStep 2483891 = 3725837) B3725837
theorem B25192133 : Blo 734326 25192133 := bstep (se 4 (by rfl) ⟨2361762, by rfl⟩ : syracuseStep 25192133 = 4723525) B4723525
theorem B4187969 : Blo 734326 4187969 := bstep (se 2 (by rfl) ⟨1570488, by rfl⟩ : syracuseStep 4187969 = 3140977) B3140977
theorem B1861451 : Blo 734326 1861451 := bstep (se 1 (by rfl) ⟨1396088, by rfl⟩ : syracuseStep 1861451 = 2792177) B2792177
theorem B2484161 : Blo 734326 2484161 := bstep (se 2 (by rfl) ⟨931560, by rfl⟩ : syracuseStep 2484161 = 1863121) B1863121
theorem B2648153 : Blo 734326 2648153 := bstep (se 2 (by rfl) ⟨993057, by rfl⟩ : syracuseStep 2648153 = 1986115) B1986115
theorem B1861825 : Blo 734326 1861825 := bstep (se 2 (by rfl) ⟨698184, by rfl⟩ : syracuseStep 1861825 = 1396369) B1396369
theorem B3139985 : Blo 734326 3139985 := bstep (se 2 (by rfl) ⟨1177494, by rfl⟩ : syracuseStep 3139985 = 2354989) B2354989
theorem B2484701 : Blo 734326 2484701 := bstep (se 3 (by rfl) ⟨465881, by rfl⟩ : syracuseStep 2484701 = 931763) B931763
theorem B1239563 : Blo 734326 1239563 := bstep (se 1 (by rfl) ⟨929672, by rfl⟩ : syracuseStep 1239563 = 1859345) B1859345
theorem B1010263 : Blo 734326 1010263 := bstep (se 1 (by rfl) ⟨757697, by rfl⟩ : syracuseStep 1010263 = 1515395) B1515395
theorem B1239691 : Blo 734326 1239691 := bstep (se 1 (by rfl) ⟨929768, by rfl⟩ : syracuseStep 1239691 = 1859537) B1859537
theorem B1862423 : Blo 734326 1862423 := bstep (se 1 (by rfl) ⟨1396817, by rfl⟩ : syracuseStep 1862423 = 2793635) B2793635
theorem B1239833 : Blo 734326 1239833 := bstep (se 2 (by rfl) ⟨464937, by rfl⟩ : syracuseStep 1239833 = 929875) B929875
theorem B1239961 : Blo 734326 1239961 := bstep (se 2 (by rfl) ⟨464985, by rfl⟩ : syracuseStep 1239961 = 929971) B929971
theorem B3140653 : Blo 734326 3140653 := bstep (se 3 (by rfl) ⟨588872, by rfl⟩ : syracuseStep 3140653 = 1177745) B1177745
theorem B4779415 : Blo 734326 4779415 := bstep (se 1 (by rfl) ⟨3584561, by rfl⟩ : syracuseStep 4779415 = 7169123) B7169123
theorem B1240535 : Blo 734326 1240535 := bstep (se 1 (by rfl) ⟨930401, by rfl⟩ : syracuseStep 1240535 = 1860803) B1860803
theorem B1863233 : Blo 734326 1863233 := bstep (se 2 (by rfl) ⟨698712, by rfl⟩ : syracuseStep 1863233 = 1397425) B1397425
theorem B2485835 : Blo 734326 2485835 := bstep (se 1 (by rfl) ⟨1864376, by rfl⟩ : syracuseStep 2485835 = 3728753) B3728753
theorem B1240663 : Blo 734326 1240663 := bstep (se 1 (by rfl) ⟨930497, by rfl⟩ : syracuseStep 1240663 = 1860995) B1860995
theorem B3141251 : Blo 734326 3141251 := bstep (se 1 (by rfl) ⟨2355938, by rfl⟩ : syracuseStep 3141251 = 4711877) B4711877
theorem B1994419 : Blo 734326 1994419 := bstep (se 1 (by rfl) ⟨1495814, by rfl⟩ : syracuseStep 1994419 = 2991629) B2991629
theorem B2420417 : Blo 734326 2420417 := bstep (se 2 (by rfl) ⟨907656, by rfl⟩ : syracuseStep 2420417 = 1815313) B1815313
theorem B2092823 : Blo 734326 2092823 := bstep (se 1 (by rfl) ⟨1569617, by rfl⟩ : syracuseStep 2092823 = 3139235) B3139235
theorem B3534637 : Blo 734326 3534637 := bstep (se 3 (by rfl) ⟨662744, by rfl⟩ : syracuseStep 3534637 = 1325489) B1325489
theorem B945995 : Blo 734326 945995 := bstep (se 1 (by rfl) ⟨709496, by rfl⟩ : syracuseStep 945995 = 1418993) B1418993
theorem B2486105 : Blo 734326 2486105 := bstep (se 2 (by rfl) ⟨932289, by rfl⟩ : syracuseStep 2486105 = 1864579) B1864579
theorem B2977681 : Blo 734326 2977681 := bstep (se 2 (by rfl) ⟨1116630, by rfl⟩ : syracuseStep 2977681 = 2233261) B2233261
theorem B1863575 : Blo 734326 1863575 := bstep (se 1 (by rfl) ⟨1397681, by rfl⟩ : syracuseStep 1863575 = 2795363) B2795363
theorem B1568729 : Blo 734326 1568729 := bstep (se 2 (by rfl) ⟨588273, by rfl⟩ : syracuseStep 1568729 = 1176547) B1176547
theorem B1863769 : Blo 734326 1863769 := bstep (se 2 (by rfl) ⟨698913, by rfl⟩ : syracuseStep 1863769 = 1397827) B1397827
theorem B1241291 : Blo 734326 1241291 := bstep (se 1 (by rfl) ⟨930968, by rfl⟩ : syracuseStep 1241291 = 1861937) B1861937
theorem B1241419 : Blo 734326 1241419 := bstep (se 1 (by rfl) ⟨931064, by rfl⟩ : syracuseStep 1241419 = 1862129) B1862129
theorem B1569241 : Blo 734326 1569241 := bstep (se 2 (by rfl) ⟨588465, by rfl⟩ : syracuseStep 1569241 = 1176931) B1176931
theorem B1241561 : Blo 734326 1241561 := bstep (se 2 (by rfl) ⟨465585, by rfl⟩ : syracuseStep 1241561 = 931171) B931171
theorem B2486807 : Blo 734326 2486807 := bstep (se 1 (by rfl) ⟨1865105, by rfl⟩ : syracuseStep 2486807 = 3730211) B3730211
theorem B1241689 : Blo 734326 1241689 := bstep (se 2 (by rfl) ⟨465633, by rfl⟩ : syracuseStep 1241689 = 931267) B931267
theorem B1569395 : Blo 734326 1569395 := bstep (se 1 (by rfl) ⟨1177046, by rfl⟩ : syracuseStep 1569395 = 2354093) B2354093
theorem B1078039 : Blo 734326 1078039 := bstep (se 1 (by rfl) ⟨808529, by rfl⟩ : syracuseStep 1078039 = 1617059) B1617059
theorem B4715309 : Blo 734326 4715309 := bstep (se 3 (by rfl) ⟨884120, by rfl⟩ : syracuseStep 4715309 = 1768241) B1768241
theorem B3732317 : Blo 734326 3732317 := bstep (se 3 (by rfl) ⟨699809, by rfl⟩ : syracuseStep 3732317 = 1399619) B1399619
theorem B5600177 : Blo 734326 5600177 := bstep (se 2 (by rfl) ⟨2100066, by rfl⟩ : syracuseStep 5600177 = 4200133) B4200133
theorem B2487347 : Blo 734326 2487347 := bstep (se 1 (by rfl) ⟨1865510, by rfl⟩ : syracuseStep 2487347 = 3731021) B3731021
theorem B6288515 : Blo 734326 6288515 := bstep (se 1 (by rfl) ⟨4716386, by rfl⟩ : syracuseStep 6288515 = 9432773) B9432773
theorem B1242263 : Blo 734326 1242263 := bstep (se 1 (by rfl) ⟨931697, by rfl⟩ : syracuseStep 1242263 = 1863395) B1863395
theorem B1864883 : Blo 734326 1864883 := bstep (se 1 (by rfl) ⟨1398662, by rfl⟩ : syracuseStep 1864883 = 2797325) B2797325
theorem B51573941 : Blo 734326 51573941 := bstep (se 5 (by rfl) ⟨2417528, by rfl⟩ : syracuseStep 51573941 = 4835057) B4835057
theorem B1242391 : Blo 734326 1242391 := bstep (se 1 (by rfl) ⟨931793, by rfl⟩ : syracuseStep 1242391 = 1863587) B1863587
theorem B2487617 : Blo 734326 2487617 := bstep (se 2 (by rfl) ⟨932856, by rfl⟩ : syracuseStep 2487617 = 1865713) B1865713
theorem B13464949 : Blo 734326 13464949 := bstep (se 5 (by rfl) ⟨631169, by rfl⟩ : syracuseStep 13464949 = 1262339) B1262339
theorem B5600663 : Blo 734326 5600663 := bstep (se 1 (by rfl) ⟨4200497, by rfl⟩ : syracuseStep 5600663 = 8400995) B8400995
theorem B1865177 : Blo 734326 1865177 := bstep (se 2 (by rfl) ⟨699441, by rfl⟩ : syracuseStep 1865177 = 1398883) B1398883
theorem B1570369 : Blo 734326 1570369 := bstep (se 2 (by rfl) ⟨588888, by rfl⟩ : syracuseStep 1570369 = 1177777) B1177777
theorem B1767233 : Blo 734326 1767233 := bstep (se 2 (by rfl) ⟨662712, by rfl⟩ : syracuseStep 1767233 = 1325425) B1325425
theorem B2488157 : Blo 734326 2488157 := bstep (se 3 (by rfl) ⟨466529, by rfl⟩ : syracuseStep 2488157 = 933059) B933059
theorem B4257629 : Blo 734326 4257629 := bstep (se 3 (by rfl) ⟨798305, by rfl⟩ : syracuseStep 4257629 = 1596611) B1596611
theorem B1243019 : Blo 734326 1243019 := bstep (se 1 (by rfl) ⟨932264, by rfl⟩ : syracuseStep 1243019 = 1864529) B1864529
theorem B784279 : Blo 734326 784279 := bstep (se 1 (by rfl) ⟨588209, by rfl⟩ : syracuseStep 784279 = 1176419) B1176419
theorem B1570711 : Blo 734326 1570711 := bstep (se 1 (by rfl) ⟨1178033, by rfl⟩ : syracuseStep 1570711 = 2356067) B2356067
theorem B2389981 : Blo 734326 2389981 := bstep (se 3 (by rfl) ⟨448121, by rfl⟩ : syracuseStep 2389981 = 896243) B896243
theorem B1243147 : Blo 734326 1243147 := bstep (se 1 (by rfl) ⟨932360, by rfl⟩ : syracuseStep 1243147 = 1864721) B1864721
theorem B1177751 : Blo 734326 1177751 := bstep (se 1 (by rfl) ⟨883313, by rfl⟩ : syracuseStep 1177751 = 1766627) B1766627
theorem B2357399 : Blo 734326 2357399 := bstep (se 1 (by rfl) ⟨1768049, by rfl⟩ : syracuseStep 2357399 = 3536099) B3536099
theorem B6715543 : Blo 734326 6715543 := bstep (se 1 (by rfl) ⟨5036657, by rfl⟩ : syracuseStep 6715543 = 10073315) B10073315
theorem B1243289 : Blo 734326 1243289 := bstep (se 2 (by rfl) ⟨466233, by rfl⟩ : syracuseStep 1243289 = 932467) B932467
theorem B2095283 : Blo 734326 2095283 := bstep (se 1 (by rfl) ⟨1571462, by rfl⟩ : syracuseStep 2095283 = 3142925) B3142925
theorem B1243417 : Blo 734326 1243417 := bstep (se 2 (by rfl) ⟨466281, by rfl⟩ : syracuseStep 1243417 = 932563) B932563
theorem B1571147 : Blo 734326 1571147 := bstep (se 1 (by rfl) ⟨1178360, by rfl⟩ : syracuseStep 1571147 = 2356721) B2356721
theorem B2357579 : Blo 734326 2357579 := bstep (se 1 (by rfl) ⟨1768184, by rfl⟩ : syracuseStep 2357579 = 3536369) B3536369
theorem B1046935 : Blo 734326 1046935 := bstep (se 1 (by rfl) ⟨785201, by rfl⟩ : syracuseStep 1046935 = 1570403) B1570403
theorem B1178059 : Blo 734326 1178059 := bstep (se 1 (by rfl) ⟨883544, by rfl⟩ : syracuseStep 1178059 = 1767089) B1767089
theorem B2357707 : Blo 734326 2357707 := bstep (se 1 (by rfl) ⟨1768280, by rfl⟩ : syracuseStep 2357707 = 3536561) B3536561
theorem B4192843 : Blo 734326 4192843 := bstep (se 1 (by rfl) ⟨3144632, by rfl⟩ : syracuseStep 4192843 = 6289265) B6289265
theorem B2357849 : Blo 734326 2357849 := bstep (se 2 (by rfl) ⟨884193, by rfl⟩ : syracuseStep 2357849 = 1768387) B1768387
theorem B1768087 : Blo 734326 1768087 := bstep (se 1 (by rfl) ⟨1326065, by rfl⟩ : syracuseStep 1768087 = 2652131) B2652131
theorem B785099 : Blo 734326 785099 := bstep (se 1 (by rfl) ⟨588824, by rfl⟩ : syracuseStep 785099 = 1177649) B1177649
theorem B1178315 : Blo 734326 1178315 := bstep (se 1 (by rfl) ⟨883736, by rfl⟩ : syracuseStep 1178315 = 1767473) B1767473
theorem B2357963 : Blo 734326 2357963 := bstep (se 1 (by rfl) ⟨1768472, by rfl⟩ : syracuseStep 2357963 = 3536945) B3536945
theorem B1243991 : Blo 734326 1243991 := bstep (se 1 (by rfl) ⟨932993, by rfl⟩ : syracuseStep 1243991 = 1865987) B1865987
theorem B4193117 : Blo 734326 4193117 := bstep (se 3 (by rfl) ⟨786209, by rfl⟩ : syracuseStep 4193117 = 1572419) B1572419
theorem B3734423 : Blo 734326 3734423 := bstep (se 1 (by rfl) ⟨2800817, by rfl⟩ : syracuseStep 3734423 = 5601635) B5601635
theorem B2489291 : Blo 734326 2489291 := bstep (se 1 (by rfl) ⟨1866968, by rfl⟩ : syracuseStep 2489291 = 3733937) B3733937
theorem B1244119 : Blo 734326 1244119 := bstep (se 1 (by rfl) ⟨933089, by rfl⟩ : syracuseStep 1244119 = 1866179) B1866179
theorem B1866827 : Blo 734326 1866827 := bstep (se 1 (by rfl) ⟨1400120, by rfl⟩ : syracuseStep 1866827 = 2800241) B2800241
theorem B1572043 : Blo 734326 1572043 := bstep (se 1 (by rfl) ⟨1179032, by rfl⟩ : syracuseStep 1572043 = 2358065) B2358065
theorem B2489561 : Blo 734326 2489561 := bstep (se 2 (by rfl) ⟨933585, by rfl⟩ : syracuseStep 2489561 = 1867171) B1867171
theorem B2653505 : Blo 734326 2653505 := bstep (se 2 (by rfl) ⟨995064, by rfl⟩ : syracuseStep 2653505 = 1990129) B1990129
theorem B6290905 : Blo 734326 6290905 := bstep (se 2 (by rfl) ⟨2359089, by rfl⟩ : syracuseStep 6290905 = 4718179) B4718179
theorem B1244747 : Blo 734326 1244747 := bstep (se 1 (by rfl) ⟨933560, by rfl⟩ : syracuseStep 1244747 = 1867121) B1867121
theorem B1179289 : Blo 734326 1179289 := bstep (se 2 (by rfl) ⟨442233, by rfl⟩ : syracuseStep 1179289 = 884467) B884467
theorem B1244875 : Blo 734326 1244875 := bstep (se 1 (by rfl) ⟨933656, by rfl⟩ : syracuseStep 1244875 = 1867313) B1867313
theorem B1245017 : Blo 734326 1245017 := bstep (se 2 (by rfl) ⟨466881, by rfl⟩ : syracuseStep 1245017 = 933763) B933763
theorem B786295 : Blo 734326 786295 := bstep (se 1 (by rfl) ⟨589721, by rfl⟩ : syracuseStep 786295 = 1179443) B1179443
theorem B2490263 : Blo 734326 2490263 := bstep (se 1 (by rfl) ⟨1867697, by rfl⟩ : syracuseStep 2490263 = 3735395) B3735395
theorem B1572787 : Blo 734326 1572787 := bstep (se 1 (by rfl) ⟨1179590, by rfl⟩ : syracuseStep 1572787 = 2359181) B2359181
theorem B2359219 : Blo 734326 2359219 := bstep (se 1 (by rfl) ⟨1769414, by rfl⟩ : syracuseStep 2359219 = 3538829) B3538829
theorem B1245145 : Blo 734326 1245145 := bstep (se 2 (by rfl) ⟨466929, by rfl⟩ : syracuseStep 1245145 = 933859) B933859
theorem B1245199 : Blo 734326 1245199 := bstep (se 1 (by rfl) ⟨933899, by rfl⟩ : syracuseStep 1245199 = 1867799) B1867799
theorem B1867819 : Blo 734326 1867819 := bstep (se 1 (by rfl) ⟨1400864, by rfl⟩ : syracuseStep 1867819 = 2801729) B2801729
theorem B1867961 : Blo 734326 1867961 := bstep (se 2 (by rfl) ⟨700485, by rfl⟩ : syracuseStep 1867961 = 1400971) B1400971
theorem B3145985 : Blo 734326 3145985 := bstep (se 2 (by rfl) ⟨1179744, by rfl⟩ : syracuseStep 3145985 = 2359489) B2359489
theorem B4194575 : Blo 734326 4194575 := bstep (se 1 (by rfl) ⟨3145931, by rfl⟩ : syracuseStep 4194575 = 6291863) B6291863
theorem B1048889 : Blo 734326 1048889 := bstep (se 2 (by rfl) ⟨393333, by rfl⟩ : syracuseStep 1048889 = 786667) B786667
theorem B38306195 : Blo 734326 38306195 := bstep (se 1 (by rfl) ⟨28729646, by rfl⟩ : syracuseStep 38306195 = 57459293) B57459293
theorem B2359705 : Blo 734326 2359705 := bstep (se 2 (by rfl) ⟨884889, by rfl⟩ : syracuseStep 2359705 = 1769779) B1769779
theorem B4194827 : Blo 734326 4194827 := bstep (se 1 (by rfl) ⟨3146120, by rfl⟩ : syracuseStep 4194827 = 6292241) B6292241
theorem B1245739 : Blo 734326 1245739 := bstep (se 1 (by rfl) ⟨934304, by rfl⟩ : syracuseStep 1245739 = 1868609) B1868609
theorem B7570097 : Blo 734326 7570097 := bstep (se 2 (by rfl) ⟨2838786, by rfl⟩ : syracuseStep 7570097 = 5677573) B5677573
theorem B19104437 : Blo 734326 19104437 := bstep (se 5 (by rfl) ⟨895520, by rfl⟩ : syracuseStep 19104437 = 1791041) B1791041
theorem B1245881 : Blo 734326 1245881 := bstep (se 2 (by rfl) ⟨467205, by rfl⟩ : syracuseStep 1245881 = 934411) B934411
theorem B2491289 : Blo 734326 2491289 := bstep (se 2 (by rfl) ⟨934233, by rfl⟩ : syracuseStep 2491289 = 1868467) B1868467
theorem B3736529 : Blo 734326 3736529 := bstep (se 2 (by rfl) ⟨1401198, by rfl⟩ : syracuseStep 3736529 = 2802397) B2802397
theorem B12583997 : Blo 734326 12583997 := bstep (se 3 (by rfl) ⟨2359499, by rfl⟩ : syracuseStep 12583997 = 4718999) B4718999
theorem B1049863 : Blo 734326 1049863 := bstep (se 1 (by rfl) ⟨787397, by rfl⟩ : syracuseStep 1049863 = 1574795) B1574795
theorem B1574291 : Blo 734326 1574291 := bstep (se 1 (by rfl) ⟨1180718, by rfl⟩ : syracuseStep 1574291 = 2361437) B2361437
theorem B7079501 : Blo 734326 7079501 := bstep (se 3 (by rfl) ⟨1327406, by rfl⟩ : syracuseStep 7079501 = 2654813) B2654813
theorem B5310029 : Blo 734326 5310029 := bstep (se 3 (by rfl) ⟨995630, by rfl⟩ : syracuseStep 5310029 = 1991261) B1991261
theorem B4196033 : Blo 734326 4196033 := bstep (se 2 (by rfl) ⟨1573512, by rfl⟩ : syracuseStep 4196033 = 3147025) B3147025
theorem B2361089 : Blo 734326 2361089 := bstep (se 2 (by rfl) ⟨885408, by rfl⟩ : syracuseStep 2361089 = 1770817) B1770817
theorem B788239 : Blo 734326 788239 := bstep (se 1 (by rfl) ⟨591179, by rfl⟩ : syracuseStep 788239 = 1182359) B1182359
theorem B2098973 : Blo 734326 2098973 := bstep (se 3 (by rfl) ⟨393557, by rfl⟩ : syracuseStep 2098973 = 787115) B787115
theorem B73664369 : Blo 734326 73664369 := bstep (se 2 (by rfl) ⟨27624138, by rfl⟩ : syracuseStep 73664369 = 55248277) B55248277
theorem B1181641 : Blo 734326 1181641 := bstep (se 2 (by rfl) ⟨443115, by rfl⟩ : syracuseStep 1181641 = 886231) B886231
theorem B3835907 : Blo 734326 3835907 := bstep (se 1 (by rfl) ⟨2876930, by rfl⟩ : syracuseStep 3835907 = 5753861) B5753861
theorem B8390789 : Blo 734326 8390789 := bstep (se 4 (by rfl) ⟨786636, by rfl⟩ : syracuseStep 8390789 = 1573273) B1573273
theorem B1771721 : Blo 734326 1771721 := bstep (se 2 (by rfl) ⟨664395, by rfl⟩ : syracuseStep 1771721 = 1328791) B1328791
theorem B3541249 : Blo 734326 3541249 := bstep (se 2 (by rfl) ⟨1327968, by rfl⟩ : syracuseStep 3541249 = 2655937) B2655937
theorem B2525555 : Blo 734326 2525555 := bstep (se 1 (by rfl) ⟨1894166, by rfl⟩ : syracuseStep 2525555 = 3788333) B3788333
theorem B2099657 : Blo 734326 2099657 := bstep (se 2 (by rfl) ⟨787371, by rfl⟩ : syracuseStep 2099657 = 1574743) B1574743
theorem B1772047 : Blo 734326 1772047 := bstep (se 1 (by rfl) ⟨1329035, by rfl⟩ : syracuseStep 1772047 = 2658071) B2658071
theorem B1116971 : Blo 734326 1116971 := bstep (se 1 (by rfl) ⟨837728, by rfl⟩ : syracuseStep 1116971 = 1675457) B1675457
theorem B2100239 : Blo 734326 2100239 := bstep (se 1 (by rfl) ⟨1575179, by rfl⟩ : syracuseStep 2100239 = 3150359) B3150359
theorem B1347017 : Blo 734326 1347017 := bstep (se 2 (by rfl) ⟨505131, by rfl⟩ : syracuseStep 1347017 = 1010263) B1010263
theorem B1150507 : Blo 734326 1150507 := bstep (se 1 (by rfl) ⟨862880, by rfl⟩ : syracuseStep 1150507 = 1725761) B1725761
theorem B10620517 : Blo 734326 10620517 := bstep (se 4 (by rfl) ⟨995673, by rfl⟩ : syracuseStep 10620517 = 1991347) B1991347
theorem B3543385 : Blo 734326 3543385 := bstep (se 2 (by rfl) ⟨1328769, by rfl⟩ : syracuseStep 3543385 = 2657539) B2657539
theorem B2789747 : Blo 734326 2789747 := bstep (se 1 (by rfl) ⟨2092310, by rfl⟩ : syracuseStep 2789747 = 4184621) B4184621
theorem B2101639 : Blo 734326 2101639 := bstep (se 1 (by rfl) ⟨1576229, by rfl⟩ : syracuseStep 2101639 = 3152459) B3152459
theorem B2101913 : Blo 734326 2101913 := bstep (se 2 (by rfl) ⟨788217, by rfl⟩ : syracuseStep 2101913 = 1576435) B1576435
theorem B4199201 : Blo 734326 4199201 := bstep (se 2 (by rfl) ⟨1574700, by rfl⟩ : syracuseStep 4199201 = 3149401) B3149401
theorem B2659225 : Blo 734326 2659225 := bstep (se 2 (by rfl) ⟨997209, by rfl⟩ : syracuseStep 2659225 = 1994419) B1994419
theorem B3412945 : Blo 734326 3412945 := bstep (se 2 (by rfl) ⟨1279854, by rfl⟩ : syracuseStep 3412945 = 2559709) B2559709
theorem B3970241 : Blo 734326 3970241 := bstep (se 2 (by rfl) ⟨1488840, by rfl⟩ : syracuseStep 3970241 = 2977681) B2977681
theorem B17929907 : Blo 734326 17929907 := bstep (se 1 (by rfl) ⟨13447430, by rfl⟩ : syracuseStep 17929907 = 26894861) B26894861
theorem B15112595 : Blo 734326 15112595 := bstep (se 1 (by rfl) ⟨11334446, by rfl⟩ : syracuseStep 15112595 = 22668893) B22668893
theorem B4299155 : Blo 734326 4299155 := bstep (se 1 (by rfl) ⟨3224366, by rfl⟩ : syracuseStep 4299155 = 6448733) B6448733
theorem B8952211 : Blo 734326 8952211 := bstep (se 1 (by rfl) ⟨6714158, by rfl⟩ : syracuseStep 8952211 = 13428317) B13428317
theorem B2791979 : Blo 734326 2791979 := bstep (se 1 (by rfl) ⟨2093984, by rfl⟩ : syracuseStep 2791979 = 4187969) B4187969
theorem B5577335 : Blo 734326 5577335 := bstep (se 1 (by rfl) ⟨4183001, by rfl⟩ : syracuseStep 5577335 = 8366003) B8366003
theorem B826375 : Blo 734326 826375 := bstep (se 1 (by rfl) ⟨619781, by rfl⟩ : syracuseStep 826375 = 1239563) B1239563
theorem B4201591 : Blo 734326 4201591 := bstep (se 1 (by rfl) ⟨3151193, by rfl⟩ : syracuseStep 4201591 = 6302387) B6302387
theorem B826555 : Blo 734326 826555 := bstep (se 1 (by rfl) ⟨619916, by rfl⟩ : syracuseStep 826555 = 1239833) B1239833
theorem B2989345 : Blo 734326 2989345 := bstep (se 2 (by rfl) ⟨1121004, by rfl⟩ : syracuseStep 2989345 = 2242009) B2242009
theorem B12557753 : Blo 734326 12557753 := bstep (se 2 (by rfl) ⟨4709157, by rfl⟩ : syracuseStep 12557753 = 9418315) B9418315
theorem B5578307 : Blo 734326 5578307 := bstep (se 1 (by rfl) ⟨4183730, by rfl⟩ : syracuseStep 5578307 = 8367461) B8367461
theorem B827023 : Blo 734326 827023 := bstep (se 1 (by rfl) ⟨620267, by rfl⟩ : syracuseStep 827023 = 1240535) B1240535
theorem B7577317 : Blo 734326 7577317 := bstep (se 4 (by rfl) ⟨710373, by rfl⟩ : syracuseStep 7577317 = 1420747) B1420747
theorem B4038437 : Blo 734326 4038437 := bstep (se 4 (by rfl) ⟨378603, by rfl⟩ : syracuseStep 4038437 = 757207) B757207
theorem B1613611 : Blo 734326 1613611 := bstep (se 1 (by rfl) ⟨1210208, by rfl⟩ : syracuseStep 1613611 = 2420417) B2420417
theorem B3186641 : Blo 734326 3186641 := bstep (se 2 (by rfl) ⟨1194990, by rfl⟩ : syracuseStep 3186641 = 2389981) B2389981
theorem B827527 : Blo 734326 827527 := bstep (se 1 (by rfl) ⟨620645, by rfl⟩ : syracuseStep 827527 = 1241291) B1241291
theorem B8954057 : Blo 734326 8954057 := bstep (se 2 (by rfl) ⟨3357771, by rfl⟩ : syracuseStep 8954057 = 6715543) B6715543
theorem B827707 : Blo 734326 827707 := bstep (se 1 (by rfl) ⟨620780, by rfl⟩ : syracuseStep 827707 = 1241561) B1241561
theorem B4727099 : Blo 734326 4727099 := bstep (se 1 (by rfl) ⟨3545324, by rfl⟩ : syracuseStep 4727099 = 7090649) B7090649
theorem B4202867 : Blo 734326 4202867 := bstep (se 1 (by rfl) ⟨3152150, by rfl⟩ : syracuseStep 4202867 = 6304301) B6304301
theorem B3547709 : Blo 734326 3547709 := bstep (se 3 (by rfl) ⟨665195, by rfl⟩ : syracuseStep 3547709 = 1330391) B1330391
theorem B13083353 : Blo 734326 13083353 := bstep (se 2 (by rfl) ⟨4906257, by rfl⟩ : syracuseStep 13083353 = 9812515) B9812515
theorem B828175 : Blo 734326 828175 := bstep (se 1 (by rfl) ⟨621131, by rfl⟩ : syracuseStep 828175 = 1242263) B1242263
theorem B34382627 : Blo 734326 34382627 := bstep (se 1 (by rfl) ⟨25786970, by rfl⟩ : syracuseStep 34382627 = 51573941) B51573941
theorem B4203323 : Blo 734326 4203323 := bstep (se 1 (by rfl) ⟨3152492, by rfl⟩ : syracuseStep 4203323 = 6304985) B6304985
theorem B828679 : Blo 734326 828679 := bstep (se 1 (by rfl) ⟨621509, by rfl⟩ : syracuseStep 828679 = 1243019) B1243019
theorem B3024263 : Blo 734326 3024263 := bstep (se 1 (by rfl) ⟨2268197, by rfl⟩ : syracuseStep 3024263 = 4536395) B4536395
theorem B828859 : Blo 734326 828859 := bstep (se 1 (by rfl) ⟨621644, by rfl⟩ : syracuseStep 828859 = 1243289) B1243289
theorem B4204325 : Blo 734326 4204325 := bstep (se 4 (by rfl) ⟨394155, by rfl⟩ : syracuseStep 4204325 = 788311) B788311
theorem B829327 : Blo 734326 829327 := bstep (se 1 (by rfl) ⟨621995, by rfl⟩ : syracuseStep 829327 = 1243991) B1243991
theorem B2795411 : Blo 734326 2795411 := bstep (se 1 (by rfl) ⟨2096558, by rfl⟩ : syracuseStep 2795411 = 4193117) B4193117
theorem B2828317 : Blo 734326 2828317 := bstep (se 3 (by rfl) ⟨530309, by rfl⟩ : syracuseStep 2828317 = 1060619) B1060619
theorem B4204781 : Blo 734326 4204781 := bstep (se 3 (by rfl) ⟨788396, by rfl⟩ : syracuseStep 4204781 = 1576793) B1576793
theorem B829831 : Blo 734326 829831 := bstep (se 1 (by rfl) ⟨622373, by rfl⟩ : syracuseStep 829831 = 1244747) B1244747
theorem B830011 : Blo 734326 830011 := bstep (se 1 (by rfl) ⟨622508, by rfl⟩ : syracuseStep 830011 = 1245017) B1245017
theorem B8399537 : Blo 734326 8399537 := bstep (se 2 (by rfl) ⟨3149826, by rfl⟩ : syracuseStep 8399537 = 6299653) B6299653
theorem B7940915 : Blo 734326 7940915 := bstep (se 1 (by rfl) ⟨5955686, by rfl⟩ : syracuseStep 7940915 = 11911373) B11911373
theorem B3976121 : Blo 734326 3976121 := bstep (se 2 (by rfl) ⟨1491045, by rfl⟩ : syracuseStep 3976121 = 2982091) B2982091
theorem B830479 : Blo 734326 830479 := bstep (se 1 (by rfl) ⟨622859, by rfl⟩ : syracuseStep 830479 = 1245719) B1245719
theorem B929551 : Blo 734326 929551 := bstep (se 1 (by rfl) ⟨697163, by rfl⟩ : syracuseStep 929551 = 1394327) B1394327
theorem B5582681 : Blo 734326 5582681 := bstep (se 2 (by rfl) ⟨2093505, by rfl⟩ : syracuseStep 5582681 = 4187011) B4187011
theorem B2240779 : Blo 734326 2240779 := bstep (se 1 (by rfl) ⟨1680584, by rfl⟩ : syracuseStep 2240779 = 3361169) B3361169
theorem B2798009 : Blo 734326 2798009 := bstep (se 2 (by rfl) ⟨1049253, by rfl⟩ : syracuseStep 2798009 = 2098507) B2098507
theorem B930295 : Blo 734326 930295 := bstep (se 1 (by rfl) ⟨697721, by rfl⟩ : syracuseStep 930295 = 1395443) B1395443
theorem B15938309 : Blo 734326 15938309 := bstep (se 4 (by rfl) ⟨1494216, by rfl⟩ : syracuseStep 15938309 = 2988433) B2988433
theorem B5583653 : Blo 734326 5583653 := bstep (se 4 (by rfl) ⟨523467, by rfl⟩ : syracuseStep 5583653 = 1046935) B1046935
theorem B930619 : Blo 734326 930619 := bstep (se 1 (by rfl) ⟨697964, by rfl⟩ : syracuseStep 930619 = 1395929) B1395929
theorem B4469879 : Blo 734326 4469879 := bstep (se 1 (by rfl) ⟨3352409, by rfl⟩ : syracuseStep 4469879 = 6704819) B6704819
theorem B734343 : Blo 734326 734343 := bstep (se 1 (by rfl) ⟨550757, by rfl⟩ : syracuseStep 734343 = 1101515) B1101515
theorem B734351 : Blo 734326 734351 := bstep (se 1 (by rfl) ⟨550763, by rfl⟩ : syracuseStep 734351 = 1101527) B1101527
theorem B734395 : Blo 734326 734395 := bstep (se 1 (by rfl) ⟨550796, by rfl⟩ : syracuseStep 734395 = 1101593) B1101593
theorem B734471 : Blo 734326 734471 := bstep (se 1 (by rfl) ⟨550853, by rfl⟩ : syracuseStep 734471 = 1101707) B1101707
theorem B734479 : Blo 734326 734479 := bstep (se 1 (by rfl) ⟨550859, by rfl⟩ : syracuseStep 734479 = 1101719) B1101719
theorem B931115 : Blo 734326 931115 := bstep (se 1 (by rfl) ⟨698336, by rfl⟩ : syracuseStep 931115 = 1396673) B1396673
theorem B734523 : Blo 734326 734523 := bstep (se 1 (by rfl) ⟨550892, by rfl⟩ : syracuseStep 734523 = 1101785) B1101785
theorem B20428163 : Blo 734326 20428163 := bstep (se 1 (by rfl) ⟨15321122, by rfl⟩ : syracuseStep 20428163 = 30642245) B30642245
theorem B734599 : Blo 734326 734599 := bstep (se 1 (by rfl) ⟨550949, by rfl⟩ : syracuseStep 734599 = 1101899) B1101899
theorem B734607 : Blo 734326 734607 := bstep (se 1 (by rfl) ⟨550955, by rfl⟩ : syracuseStep 734607 = 1101911) B1101911
theorem B2798995 : Blo 734326 2798995 := bstep (se 1 (by rfl) ⟨2099246, by rfl⟩ : syracuseStep 2798995 = 4198493) B4198493
theorem B734651 : Blo 734326 734651 := bstep (se 1 (by rfl) ⟨550988, by rfl⟩ : syracuseStep 734651 = 1101977) B1101977
theorem B734727 : Blo 734326 734727 := bstep (se 1 (by rfl) ⟨551045, by rfl⟩ : syracuseStep 734727 = 1102091) B1102091
theorem B734735 : Blo 734326 734735 := bstep (se 1 (by rfl) ⟨551051, by rfl⟩ : syracuseStep 734735 = 1102103) B1102103
theorem B734779 : Blo 734326 734779 := bstep (se 1 (by rfl) ⟨551084, by rfl⟩ : syracuseStep 734779 = 1102169) B1102169
theorem B734855 : Blo 734326 734855 := bstep (se 1 (by rfl) ⟨551141, by rfl⟩ : syracuseStep 734855 = 1102283) B1102283
theorem B734863 : Blo 734326 734863 := bstep (se 1 (by rfl) ⟨551147, by rfl⟩ : syracuseStep 734863 = 1102295) B1102295
theorem B734907 : Blo 734326 734907 := bstep (se 1 (by rfl) ⟨551180, by rfl⟩ : syracuseStep 734907 = 1102361) B1102361
theorem B734983 : Blo 734326 734983 := bstep (se 1 (by rfl) ⟨551237, by rfl⟩ : syracuseStep 734983 = 1102475) B1102475
theorem B931591 : Blo 734326 931591 := bstep (se 1 (by rfl) ⟨698693, by rfl⟩ : syracuseStep 931591 = 1397387) B1397387
theorem B734991 : Blo 734326 734991 := bstep (se 1 (by rfl) ⟨551243, by rfl⟩ : syracuseStep 734991 = 1102487) B1102487
theorem B735035 : Blo 734326 735035 := bstep (se 1 (by rfl) ⟨551276, by rfl⟩ : syracuseStep 735035 = 1102553) B1102553
theorem B40384331 : Blo 734326 40384331 := bstep (se 1 (by rfl) ⟨30288248, by rfl⟩ : syracuseStep 40384331 = 60576497) B60576497
theorem B8075123 : Blo 734326 8075123 := bstep (se 1 (by rfl) ⟨6056342, by rfl⟩ : syracuseStep 8075123 = 12112685) B12112685
theorem B1488775 : Blo 734326 1488775 := bstep (se 1 (by rfl) ⟨1116581, by rfl⟩ : syracuseStep 1488775 = 2233163) B2233163
theorem B1652615 : Blo 734326 1652615 := bstep (se 1 (by rfl) ⟨1239461, by rfl⟩ : syracuseStep 1652615 = 2478923) B2478923
theorem B735111 : Blo 734326 735111 := bstep (se 1 (by rfl) ⟨551333, by rfl⟩ : syracuseStep 735111 = 1102667) B1102667
theorem B735119 : Blo 734326 735119 := bstep (se 1 (by rfl) ⟨551339, by rfl⟩ : syracuseStep 735119 = 1102679) B1102679
theorem B735163 : Blo 734326 735163 := bstep (se 1 (by rfl) ⟨551372, by rfl⟩ : syracuseStep 735163 = 1102745) B1102745
theorem B2242505 : Blo 734326 2242505 := bstep (se 2 (by rfl) ⟨840939, by rfl⟩ : syracuseStep 2242505 = 1681879) B1681879
theorem B735239 : Blo 734326 735239 := bstep (se 1 (by rfl) ⟨551429, by rfl⟩ : syracuseStep 735239 = 1102859) B1102859
theorem B735247 : Blo 734326 735247 := bstep (se 1 (by rfl) ⟨551435, by rfl⟩ : syracuseStep 735247 = 1102871) B1102871
theorem B1259563 : Blo 734326 1259563 := bstep (se 1 (by rfl) ⟨944672, by rfl⟩ : syracuseStep 1259563 = 1889345) B1889345
theorem B1652795 : Blo 734326 1652795 := bstep (se 1 (by rfl) ⟨1239596, by rfl⟩ : syracuseStep 1652795 = 2479193) B2479193
theorem B735291 : Blo 734326 735291 := bstep (se 1 (by rfl) ⟨551468, by rfl⟩ : syracuseStep 735291 = 1102937) B1102937
theorem B735367 : Blo 734326 735367 := bstep (se 1 (by rfl) ⟨551525, by rfl⟩ : syracuseStep 735367 = 1103051) B1103051
theorem B735375 : Blo 734326 735375 := bstep (se 1 (by rfl) ⟨551531, by rfl⟩ : syracuseStep 735375 = 1103063) B1103063
theorem B1652921 : Blo 734326 1652921 := bstep (se 2 (by rfl) ⟨619845, by rfl⟩ : syracuseStep 1652921 = 1239691) B1239691
theorem B735419 : Blo 734326 735419 := bstep (se 1 (by rfl) ⟨551564, by rfl⟩ : syracuseStep 735419 = 1103129) B1103129
theorem B8370377 : Blo 734326 8370377 := bstep (se 2 (by rfl) ⟨3138891, by rfl⟩ : syracuseStep 8370377 = 6277783) B6277783
theorem B932087 : Blo 734326 932087 := bstep (se 1 (by rfl) ⟨699065, by rfl⟩ : syracuseStep 932087 = 1398131) B1398131
theorem B735495 : Blo 734326 735495 := bstep (se 1 (by rfl) ⟨551621, by rfl⟩ : syracuseStep 735495 = 1103243) B1103243
theorem B735503 : Blo 734326 735503 := bstep (se 1 (by rfl) ⟨551627, by rfl⟩ : syracuseStep 735503 = 1103255) B1103255
theorem B735547 : Blo 734326 735547 := bstep (se 1 (by rfl) ⟨551660, by rfl⟩ : syracuseStep 735547 = 1103321) B1103321
theorem B735623 : Blo 734326 735623 := bstep (se 1 (by rfl) ⟨551717, by rfl⟩ : syracuseStep 735623 = 1103435) B1103435
theorem B735631 : Blo 734326 735631 := bstep (se 1 (by rfl) ⟨551723, by rfl⟩ : syracuseStep 735631 = 1103447) B1103447
theorem B932239 : Blo 734326 932239 := bstep (se 1 (by rfl) ⟨699179, by rfl⟩ : syracuseStep 932239 = 1398359) B1398359
theorem B735675 : Blo 734326 735675 := bstep (se 1 (by rfl) ⟨551756, by rfl⟩ : syracuseStep 735675 = 1103513) B1103513
theorem B735751 : Blo 734326 735751 := bstep (se 1 (by rfl) ⟨551813, by rfl⟩ : syracuseStep 735751 = 1103627) B1103627
theorem B1653263 : Blo 734326 1653263 := bstep (se 1 (by rfl) ⟨1239947, by rfl⟩ : syracuseStep 1653263 = 2479895) B2479895
theorem B735759 : Blo 734326 735759 := bstep (se 1 (by rfl) ⟨551819, by rfl⟩ : syracuseStep 735759 = 1103639) B1103639
theorem B1653281 : Blo 734326 1653281 := bstep (se 2 (by rfl) ⟨619980, by rfl⟩ : syracuseStep 1653281 = 1239961) B1239961
theorem B735803 : Blo 734326 735803 := bstep (se 1 (by rfl) ⟨551852, by rfl⟩ : syracuseStep 735803 = 1103705) B1103705
theorem B932411 : Blo 734326 932411 := bstep (se 1 (by rfl) ⟨699308, by rfl⟩ : syracuseStep 932411 = 1398617) B1398617
theorem B23935607 : Blo 734326 23935607 := bstep (se 1 (by rfl) ⟨17951705, by rfl⟩ : syracuseStep 23935607 = 35903411) B35903411
theorem B735879 : Blo 734326 735879 := bstep (se 1 (by rfl) ⟨551909, by rfl⟩ : syracuseStep 735879 = 1103819) B1103819
theorem B735887 : Blo 734326 735887 := bstep (se 1 (by rfl) ⟨551915, by rfl⟩ : syracuseStep 735887 = 1103831) B1103831
theorem B735931 : Blo 734326 735931 := bstep (se 1 (by rfl) ⟨551948, by rfl⟩ : syracuseStep 735931 = 1103897) B1103897
theorem B736007 : Blo 734326 736007 := bstep (se 1 (by rfl) ⟨552005, by rfl⟩ : syracuseStep 736007 = 1104011) B1104011
theorem B736015 : Blo 734326 736015 := bstep (se 1 (by rfl) ⟨552011, by rfl⟩ : syracuseStep 736015 = 1104023) B1104023
theorem B736059 : Blo 734326 736059 := bstep (se 1 (by rfl) ⟨552044, by rfl⟩ : syracuseStep 736059 = 1104089) B1104089
theorem B1653623 : Blo 734326 1653623 := bstep (se 1 (by rfl) ⟨1240217, by rfl⟩ : syracuseStep 1653623 = 2480435) B2480435
theorem B736135 : Blo 734326 736135 := bstep (se 1 (by rfl) ⟨552101, by rfl⟩ : syracuseStep 736135 = 1104203) B1104203
theorem B736143 : Blo 734326 736143 := bstep (se 1 (by rfl) ⟨552107, by rfl⟩ : syracuseStep 736143 = 1104215) B1104215
theorem B736187 : Blo 734326 736187 := bstep (se 1 (by rfl) ⟨552140, by rfl⟩ : syracuseStep 736187 = 1104281) B1104281
theorem B3587075 : Blo 734326 3587075 := bstep (se 1 (by rfl) ⟨2690306, by rfl⟩ : syracuseStep 3587075 = 5380613) B5380613
theorem B40811525 : Blo 734326 40811525 := bstep (se 4 (by rfl) ⟨3826080, by rfl⟩ : syracuseStep 40811525 = 7652161) B7652161
theorem B736263 : Blo 734326 736263 := bstep (se 1 (by rfl) ⟨552197, by rfl⟩ : syracuseStep 736263 = 1104395) B1104395
theorem B736271 : Blo 734326 736271 := bstep (se 1 (by rfl) ⟨552203, by rfl⟩ : syracuseStep 736271 = 1104407) B1104407
theorem B1653803 : Blo 734326 1653803 := bstep (se 1 (by rfl) ⟨1240352, by rfl⟩ : syracuseStep 1653803 = 2480705) B2480705
theorem B736315 : Blo 734326 736315 := bstep (se 1 (by rfl) ⟨552236, by rfl⟩ : syracuseStep 736315 = 1104473) B1104473
theorem B2800727 : Blo 734326 2800727 := bstep (se 1 (by rfl) ⟨2100545, by rfl⟩ : syracuseStep 2800727 = 4201091) B4201091
theorem B736391 : Blo 734326 736391 := bstep (se 1 (by rfl) ⟨552293, by rfl⟩ : syracuseStep 736391 = 1104587) B1104587
theorem B736399 : Blo 734326 736399 := bstep (se 1 (by rfl) ⟨552299, by rfl⟩ : syracuseStep 736399 = 1104599) B1104599
theorem B736443 : Blo 734326 736443 := bstep (se 1 (by rfl) ⟨552332, by rfl⟩ : syracuseStep 736443 = 1104665) B1104665
theorem B6372553 : Blo 734326 6372553 := bstep (se 2 (by rfl) ⟨2389707, by rfl⟩ : syracuseStep 6372553 = 4779415) B4779415
theorem B736519 : Blo 734326 736519 := bstep (se 1 (by rfl) ⟨552389, by rfl⟩ : syracuseStep 736519 = 1104779) B1104779
theorem B736527 : Blo 734326 736527 := bstep (se 1 (by rfl) ⟨552395, by rfl⟩ : syracuseStep 736527 = 1104791) B1104791
theorem B1490219 : Blo 734326 1490219 := bstep (se 1 (by rfl) ⟨1117664, by rfl⟩ : syracuseStep 1490219 = 2235329) B2235329
theorem B736571 : Blo 734326 736571 := bstep (se 1 (by rfl) ⟨552428, by rfl⟩ : syracuseStep 736571 = 1104857) B1104857
theorem B736647 : Blo 734326 736647 := bstep (se 1 (by rfl) ⟨552485, by rfl⟩ : syracuseStep 736647 = 1104971) B1104971
theorem B736655 : Blo 734326 736655 := bstep (se 1 (by rfl) ⟨552491, by rfl⟩ : syracuseStep 736655 = 1104983) B1104983
theorem B3718547 : Blo 734326 3718547 := bstep (se 1 (by rfl) ⟨2788910, by rfl⟩ : syracuseStep 3718547 = 5577821) B5577821
theorem B1654163 : Blo 734326 1654163 := bstep (se 1 (by rfl) ⟨1240622, by rfl⟩ : syracuseStep 1654163 = 2481245) B2481245
theorem B736699 : Blo 734326 736699 := bstep (se 1 (by rfl) ⟨552524, by rfl⟩ : syracuseStep 736699 = 1105049) B1105049
theorem B1654217 : Blo 734326 1654217 := bstep (se 2 (by rfl) ⟨620331, by rfl⟩ : syracuseStep 1654217 = 1240663) B1240663
theorem B736775 : Blo 734326 736775 := bstep (se 1 (by rfl) ⟨552581, by rfl⟩ : syracuseStep 736775 = 1105163) B1105163
theorem B933383 : Blo 734326 933383 := bstep (se 1 (by rfl) ⟨700037, by rfl⟩ : syracuseStep 933383 = 1400075) B1400075
theorem B736783 : Blo 734326 736783 := bstep (se 1 (by rfl) ⟨552587, by rfl⟩ : syracuseStep 736783 = 1105175) B1105175
theorem B736827 : Blo 734326 736827 := bstep (se 1 (by rfl) ⟨552620, by rfl⟩ : syracuseStep 736827 = 1105241) B1105241
theorem B2801213 : Blo 734326 2801213 := bstep (se 3 (by rfl) ⟨525227, by rfl⟩ : syracuseStep 2801213 = 1050455) B1050455
theorem B736903 : Blo 734326 736903 := bstep (se 1 (by rfl) ⟨552677, by rfl⟩ : syracuseStep 736903 = 1105355) B1105355
theorem B736911 : Blo 734326 736911 := bstep (se 1 (by rfl) ⟨552683, by rfl⟩ : syracuseStep 736911 = 1105367) B1105367
theorem B736955 : Blo 734326 736955 := bstep (se 1 (by rfl) ⟨552716, by rfl⟩ : syracuseStep 736955 = 1105433) B1105433
theorem B3587777 : Blo 734326 3587777 := bstep (se 2 (by rfl) ⟨1345416, by rfl⟩ : syracuseStep 3587777 = 2690833) B2690833
theorem B737031 : Blo 734326 737031 := bstep (se 1 (by rfl) ⟨552773, by rfl⟩ : syracuseStep 737031 = 1105547) B1105547
theorem B737039 : Blo 734326 737039 := bstep (se 1 (by rfl) ⟨552779, by rfl⟩ : syracuseStep 737039 = 1105559) B1105559
theorem B737083 : Blo 734326 737083 := bstep (se 1 (by rfl) ⟨552812, by rfl⟩ : syracuseStep 737083 = 1105625) B1105625
theorem B2244439 : Blo 734326 2244439 := bstep (se 1 (by rfl) ⟨1683329, by rfl⟩ : syracuseStep 2244439 = 3366659) B3366659
theorem B6045529 : Blo 734326 6045529 := bstep (se 2 (by rfl) ⟨2267073, by rfl⟩ : syracuseStep 6045529 = 4534147) B4534147
theorem B737159 : Blo 734326 737159 := bstep (se 1 (by rfl) ⟨552869, by rfl⟩ : syracuseStep 737159 = 1105739) B1105739
theorem B737167 : Blo 734326 737167 := bstep (se 1 (by rfl) ⟨552875, by rfl⟩ : syracuseStep 737167 = 1105751) B1105751
theorem B737211 : Blo 734326 737211 := bstep (se 1 (by rfl) ⟨552908, by rfl⟩ : syracuseStep 737211 = 1105817) B1105817
theorem B737287 : Blo 734326 737287 := bstep (se 1 (by rfl) ⟨552965, by rfl⟩ : syracuseStep 737287 = 1105931) B1105931
theorem B2211851 : Blo 734326 2211851 := bstep (se 1 (by rfl) ⟨1658888, by rfl⟩ : syracuseStep 2211851 = 3317777) B3317777
theorem B737295 : Blo 734326 737295 := bstep (se 1 (by rfl) ⟨552971, by rfl⟩ : syracuseStep 737295 = 1105943) B1105943
theorem B737339 : Blo 734326 737339 := bstep (se 1 (by rfl) ⟨553004, by rfl⟩ : syracuseStep 737339 = 1106009) B1106009
theorem B1654919 : Blo 734326 1654919 := bstep (se 1 (by rfl) ⟨1241189, by rfl⟩ : syracuseStep 1654919 = 2482379) B2482379
theorem B737415 : Blo 734326 737415 := bstep (se 1 (by rfl) ⟨553061, by rfl⟩ : syracuseStep 737415 = 1106123) B1106123
theorem B2244743 : Blo 734326 2244743 := bstep (se 1 (by rfl) ⟨1683557, by rfl⟩ : syracuseStep 2244743 = 3367115) B3367115
theorem B737423 : Blo 734326 737423 := bstep (se 1 (by rfl) ⟨553067, by rfl⟩ : syracuseStep 737423 = 1106135) B1106135
theorem B934031 : Blo 734326 934031 := bstep (se 1 (by rfl) ⟨700523, by rfl⟩ : syracuseStep 934031 = 1401047) B1401047
theorem B737467 : Blo 734326 737467 := bstep (se 1 (by rfl) ⟨553100, by rfl⟩ : syracuseStep 737467 = 1106201) B1106201
theorem B7061741 : Blo 734326 7061741 := bstep (se 3 (by rfl) ⟨1324076, by rfl⟩ : syracuseStep 7061741 = 2648153) B2648153
theorem B737543 : Blo 734326 737543 := bstep (se 1 (by rfl) ⟨553157, by rfl⟩ : syracuseStep 737543 = 1106315) B1106315
theorem B737551 : Blo 734326 737551 := bstep (se 1 (by rfl) ⟨553163, by rfl⟩ : syracuseStep 737551 = 1106327) B1106327
theorem B1655099 : Blo 734326 1655099 := bstep (se 1 (by rfl) ⟨1241324, by rfl⟩ : syracuseStep 1655099 = 2482649) B2482649
theorem B737595 : Blo 734326 737595 := bstep (se 1 (by rfl) ⟨553196, by rfl⟩ : syracuseStep 737595 = 1106393) B1106393
theorem B737671 : Blo 734326 737671 := bstep (se 1 (by rfl) ⟨553253, by rfl⟩ : syracuseStep 737671 = 1106507) B1106507
theorem B737679 : Blo 734326 737679 := bstep (se 1 (by rfl) ⟨553259, by rfl⟩ : syracuseStep 737679 = 1106519) B1106519
theorem B1655225 : Blo 734326 1655225 := bstep (se 2 (by rfl) ⟨620709, by rfl⟩ : syracuseStep 1655225 = 1241419) B1241419
theorem B737723 : Blo 734326 737723 := bstep (se 1 (by rfl) ⟨553292, by rfl⟩ : syracuseStep 737723 = 1106585) B1106585
theorem B737799 : Blo 734326 737799 := bstep (se 1 (by rfl) ⟨553349, by rfl⟩ : syracuseStep 737799 = 1106699) B1106699
theorem B737807 : Blo 734326 737807 := bstep (se 1 (by rfl) ⟨553355, by rfl⟩ : syracuseStep 737807 = 1106711) B1106711
theorem B737851 : Blo 734326 737851 := bstep (se 1 (by rfl) ⟨553388, by rfl⟩ : syracuseStep 737851 = 1106777) B1106777
theorem B737927 : Blo 734326 737927 := bstep (se 1 (by rfl) ⟨553445, by rfl⟩ : syracuseStep 737927 = 1106891) B1106891
theorem B737935 : Blo 734326 737935 := bstep (se 1 (by rfl) ⟨553451, by rfl⟩ : syracuseStep 737935 = 1106903) B1106903
theorem B737979 : Blo 734326 737979 := bstep (se 1 (by rfl) ⟨553484, by rfl⟩ : syracuseStep 737979 = 1106969) B1106969
theorem B738055 : Blo 734326 738055 := bstep (se 1 (by rfl) ⟨553541, by rfl⟩ : syracuseStep 738055 = 1107083) B1107083
theorem B1655567 : Blo 734326 1655567 := bstep (se 1 (by rfl) ⟨1241675, by rfl⟩ : syracuseStep 1655567 = 2483351) B2483351
theorem B738063 : Blo 734326 738063 := bstep (se 1 (by rfl) ⟨553547, by rfl⟩ : syracuseStep 738063 = 1107095) B1107095
theorem B1655585 : Blo 734326 1655585 := bstep (se 2 (by rfl) ⟨620844, by rfl⟩ : syracuseStep 1655585 = 1241689) B1241689
theorem B738107 : Blo 734326 738107 := bstep (se 1 (by rfl) ⟨553580, by rfl⟩ : syracuseStep 738107 = 1107161) B1107161
theorem B738183 : Blo 734326 738183 := bstep (se 1 (by rfl) ⟨553637, by rfl⟩ : syracuseStep 738183 = 1107275) B1107275
theorem B738191 : Blo 734326 738191 := bstep (se 1 (by rfl) ⟨553643, by rfl⟩ : syracuseStep 738191 = 1107287) B1107287
theorem B738235 : Blo 734326 738235 := bstep (se 1 (by rfl) ⟨553676, by rfl⟩ : syracuseStep 738235 = 1107353) B1107353
theorem B738311 : Blo 734326 738311 := bstep (se 1 (by rfl) ⟨553733, by rfl⟩ : syracuseStep 738311 = 1107467) B1107467
theorem B738319 : Blo 734326 738319 := bstep (se 1 (by rfl) ⟨553739, by rfl⟩ : syracuseStep 738319 = 1107479) B1107479
theorem B8373293 : Blo 734326 8373293 := bstep (se 3 (by rfl) ⟨1569992, by rfl⟩ : syracuseStep 8373293 = 3139985) B3139985
theorem B1655927 : Blo 734326 1655927 := bstep (se 1 (by rfl) ⟨1241945, by rfl⟩ : syracuseStep 1655927 = 2483891) B2483891
theorem B16794755 : Blo 734326 16794755 := bstep (se 1 (by rfl) ⟨12596066, by rfl⟩ : syracuseStep 16794755 = 25192133) B25192133
theorem B1656107 : Blo 734326 1656107 := bstep (se 1 (by rfl) ⟨1242080, by rfl⟩ : syracuseStep 1656107 = 2484161) B2484161
theorem B1656467 : Blo 734326 1656467 := bstep (se 1 (by rfl) ⟨1242350, by rfl⟩ : syracuseStep 1656467 = 2484701) B2484701
theorem B1656521 : Blo 734326 1656521 := bstep (se 2 (by rfl) ⟨621195, by rfl⟩ : syracuseStep 1656521 = 1242391) B1242391
theorem B4474597 : Blo 734326 4474597 := bstep (se 4 (by rfl) ⟨419493, by rfl⟩ : syracuseStep 4474597 = 838987) B838987
theorem B1329353 : Blo 734326 1329353 := bstep (se 2 (by rfl) ⟨498507, by rfl⟩ : syracuseStep 1329353 = 997015) B997015
theorem B5294317 : Blo 734326 5294317 := bstep (se 3 (by rfl) ⟨992684, by rfl⟩ : syracuseStep 5294317 = 1985369) B1985369
theorem B1657223 : Blo 734326 1657223 := bstep (se 1 (by rfl) ⟨1242917, by rfl⟩ : syracuseStep 1657223 = 2485835) B2485835
theorem B3721625 : Blo 734326 3721625 := bstep (se 2 (by rfl) ⟨1395609, by rfl⟩ : syracuseStep 3721625 = 2791219) B2791219
theorem B3590659 : Blo 734326 3590659 := bstep (se 1 (by rfl) ⟨2692994, by rfl⟩ : syracuseStep 3590659 = 5385989) B5385989
theorem B1395215 : Blo 734326 1395215 := bstep (se 1 (by rfl) ⟨1046411, by rfl⟩ : syracuseStep 1395215 = 2092823) B2092823
theorem B1985057 : Blo 734326 1985057 := bstep (se 2 (by rfl) ⟨744396, by rfl⟩ : syracuseStep 1985057 = 1488793) B1488793
theorem B1657403 : Blo 734326 1657403 := bstep (se 1 (by rfl) ⟨1243052, by rfl⟩ : syracuseStep 1657403 = 2486105) B2486105
theorem B1657529 : Blo 734326 1657529 := bstep (se 2 (by rfl) ⟨621573, by rfl⟩ : syracuseStep 1657529 = 1243147) B1243147
theorem B1657871 : Blo 734326 1657871 := bstep (se 1 (by rfl) ⟨1243403, by rfl⟩ : syracuseStep 1657871 = 2486807) B2486807
theorem B1657889 : Blo 734326 1657889 := bstep (se 2 (by rfl) ⟨621708, by rfl⟩ : syracuseStep 1657889 = 1243417) B1243417
theorem B1658231 : Blo 734326 1658231 := bstep (se 1 (by rfl) ⟨1243673, by rfl⟩ : syracuseStep 1658231 = 2487347) B2487347
theorem B5590457 : Blo 734326 5590457 := bstep (se 2 (by rfl) ⟨2096421, by rfl⟩ : syracuseStep 5590457 = 4192843) B4192843
theorem B4771331 : Blo 734326 4771331 := bstep (se 1 (by rfl) ⟨3578498, by rfl⟩ : syracuseStep 4771331 = 7156997) B7156997
theorem B1658411 : Blo 734326 1658411 := bstep (se 1 (by rfl) ⟨1243808, by rfl⟩ : syracuseStep 1658411 = 2487617) B2487617
theorem B1101497 : Blo 734326 1101497 := bstep (se 2 (by rfl) ⟨413061, by rfl⟩ : syracuseStep 1101497 = 826123) B826123
theorem B1101575 : Blo 734326 1101575 := bstep (se 1 (by rfl) ⟨826181, by rfl⟩ : syracuseStep 1101575 = 1652363) B1652363
theorem B1101611 : Blo 734326 1101611 := bstep (se 1 (by rfl) ⟨826208, by rfl⟩ : syracuseStep 1101611 = 1652417) B1652417
theorem B1101641 : Blo 734326 1101641 := bstep (se 2 (by rfl) ⟨413115, by rfl⟩ : syracuseStep 1101641 = 826231) B826231
theorem B1658771 : Blo 734326 1658771 := bstep (se 1 (by rfl) ⟨1244078, by rfl⟩ : syracuseStep 1658771 = 2488157) B2488157
theorem B2838419 : Blo 734326 2838419 := bstep (se 1 (by rfl) ⟨2128814, by rfl⟩ : syracuseStep 2838419 = 4257629) B4257629
theorem B1101755 : Blo 734326 1101755 := bstep (se 1 (by rfl) ⟨826316, by rfl⟩ : syracuseStep 1101755 = 1652633) B1652633
theorem B1658825 : Blo 734326 1658825 := bstep (se 2 (by rfl) ⟨622059, by rfl⟩ : syracuseStep 1658825 = 1244119) B1244119
theorem B1101815 : Blo 734326 1101815 := bstep (se 1 (by rfl) ⟨826361, by rfl⟩ : syracuseStep 1101815 = 1652723) B1652723
theorem B1101839 : Blo 734326 1101839 := bstep (se 1 (by rfl) ⟨826379, by rfl⟩ : syracuseStep 1101839 = 1652759) B1652759
theorem B1101881 : Blo 734326 1101881 := bstep (se 2 (by rfl) ⟨413205, by rfl⟩ : syracuseStep 1101881 = 826411) B826411
theorem B1396855 : Blo 734326 1396855 := bstep (se 1 (by rfl) ⟨1047641, by rfl⟩ : syracuseStep 1396855 = 2095283) B2095283
theorem B1101959 : Blo 734326 1101959 := bstep (se 1 (by rfl) ⟨826469, by rfl⟩ : syracuseStep 1101959 = 1652939) B1652939
theorem B1101995 : Blo 734326 1101995 := bstep (se 1 (by rfl) ⟨826496, by rfl⟩ : syracuseStep 1101995 = 1652993) B1652993
theorem B1102025 : Blo 734326 1102025 := bstep (se 2 (by rfl) ⟨413259, by rfl⟩ : syracuseStep 1102025 = 826519) B826519
theorem B1102139 : Blo 734326 1102139 := bstep (se 1 (by rfl) ⟨826604, by rfl⟩ : syracuseStep 1102139 = 1653209) B1653209
theorem B1102199 : Blo 734326 1102199 := bstep (se 1 (by rfl) ⟨826649, by rfl⟩ : syracuseStep 1102199 = 1653299) B1653299
theorem B1102223 : Blo 734326 1102223 := bstep (se 1 (by rfl) ⟨826667, by rfl⟩ : syracuseStep 1102223 = 1653335) B1653335
theorem B1102265 : Blo 734326 1102265 := bstep (se 2 (by rfl) ⟨413349, by rfl⟩ : syracuseStep 1102265 = 826699) B826699
theorem B1102343 : Blo 734326 1102343 := bstep (se 1 (by rfl) ⟨826757, by rfl⟩ : syracuseStep 1102343 = 1653515) B1653515
theorem B1102379 : Blo 734326 1102379 := bstep (se 1 (by rfl) ⟨826784, by rfl⟩ : syracuseStep 1102379 = 1653569) B1653569
theorem B2478653 : Blo 734326 2478653 := bstep (se 3 (by rfl) ⟨464747, by rfl⟩ : syracuseStep 2478653 = 929495) B929495
theorem B1102409 : Blo 734326 1102409 := bstep (se 2 (by rfl) ⟨413403, by rfl⟩ : syracuseStep 1102409 = 826807) B826807
theorem B1659527 : Blo 734326 1659527 := bstep (se 1 (by rfl) ⟨1244645, by rfl⟩ : syracuseStep 1659527 = 2489291) B2489291
theorem B1102523 : Blo 734326 1102523 := bstep (se 1 (by rfl) ⟨826892, by rfl⟩ : syracuseStep 1102523 = 1653785) B1653785
theorem B1102583 : Blo 734326 1102583 := bstep (se 1 (by rfl) ⟨826937, by rfl⟩ : syracuseStep 1102583 = 1653875) B1653875
theorem B1102607 : Blo 734326 1102607 := bstep (se 1 (by rfl) ⟨826955, by rfl⟩ : syracuseStep 1102607 = 1653911) B1653911
theorem B1987361 : Blo 734326 1987361 := bstep (se 2 (by rfl) ⟨745260, by rfl⟩ : syracuseStep 1987361 = 1490521) B1490521
theorem B1102649 : Blo 734326 1102649 := bstep (se 2 (by rfl) ⟨413493, by rfl⟩ : syracuseStep 1102649 = 826987) B826987
theorem B1659707 : Blo 734326 1659707 := bstep (se 1 (by rfl) ⟨1244780, by rfl⟩ : syracuseStep 1659707 = 2489561) B2489561
theorem B1102727 : Blo 734326 1102727 := bstep (se 1 (by rfl) ⟨827045, by rfl⟩ : syracuseStep 1102727 = 1654091) B1654091
theorem B1102763 : Blo 734326 1102763 := bstep (se 1 (by rfl) ⟨827072, by rfl⟩ : syracuseStep 1102763 = 1654145) B1654145
theorem B3724217 : Blo 734326 3724217 := bstep (se 2 (by rfl) ⟨1396581, by rfl⟩ : syracuseStep 3724217 = 2793163) B2793163
theorem B1659833 : Blo 734326 1659833 := bstep (se 2 (by rfl) ⟨622437, by rfl⟩ : syracuseStep 1659833 = 1244875) B1244875
theorem B1102793 : Blo 734326 1102793 := bstep (se 2 (by rfl) ⟨413547, by rfl⟩ : syracuseStep 1102793 = 827095) B827095
theorem B1102907 : Blo 734326 1102907 := bstep (se 1 (by rfl) ⟨827180, by rfl⟩ : syracuseStep 1102907 = 1654361) B1654361
theorem B1102967 : Blo 734326 1102967 := bstep (se 1 (by rfl) ⟨827225, by rfl⟩ : syracuseStep 1102967 = 1654451) B1654451
theorem B1102991 : Blo 734326 1102991 := bstep (se 1 (by rfl) ⟨827243, by rfl⟩ : syracuseStep 1102991 = 1654487) B1654487
theorem B1103033 : Blo 734326 1103033 := bstep (se 2 (by rfl) ⟨413637, by rfl⟩ : syracuseStep 1103033 = 827275) B827275
theorem B1103111 : Blo 734326 1103111 := bstep (se 1 (by rfl) ⟨827333, by rfl⟩ : syracuseStep 1103111 = 1654667) B1654667
theorem B1660175 : Blo 734326 1660175 := bstep (se 1 (by rfl) ⟨1245131, by rfl⟩ : syracuseStep 1660175 = 2490263) B2490263
theorem B1660193 : Blo 734326 1660193 := bstep (se 2 (by rfl) ⟨622572, by rfl⟩ : syracuseStep 1660193 = 1245145) B1245145
theorem B1103147 : Blo 734326 1103147 := bstep (se 1 (by rfl) ⟨827360, by rfl⟩ : syracuseStep 1103147 = 1654721) B1654721
theorem B1103177 : Blo 734326 1103177 := bstep (se 2 (by rfl) ⟨413691, by rfl⟩ : syracuseStep 1103177 = 827383) B827383
theorem B1103291 : Blo 734326 1103291 := bstep (se 1 (by rfl) ⟨827468, by rfl⟩ : syracuseStep 1103291 = 1654937) B1654937
theorem B1103351 : Blo 734326 1103351 := bstep (se 1 (by rfl) ⟨827513, by rfl⟩ : syracuseStep 1103351 = 1655027) B1655027
theorem B1103375 : Blo 734326 1103375 := bstep (se 1 (by rfl) ⟨827531, by rfl⟩ : syracuseStep 1103375 = 1655063) B1655063
theorem B4183595 : Blo 734326 4183595 := bstep (se 1 (by rfl) ⟨3137696, by rfl⟩ : syracuseStep 4183595 = 6275393) B6275393
theorem B1103417 : Blo 734326 1103417 := bstep (se 2 (by rfl) ⟨413781, by rfl⟩ : syracuseStep 1103417 = 827563) B827563
theorem B1660535 : Blo 734326 1660535 := bstep (se 1 (by rfl) ⟨1245401, by rfl⟩ : syracuseStep 1660535 = 2490803) B2490803
theorem B1103495 : Blo 734326 1103495 := bstep (se 1 (by rfl) ⟨827621, by rfl⟩ : syracuseStep 1103495 = 1655243) B1655243
theorem B1103531 : Blo 734326 1103531 := bstep (se 1 (by rfl) ⟨827648, by rfl⟩ : syracuseStep 1103531 = 1655297) B1655297
theorem B1103561 : Blo 734326 1103561 := bstep (se 2 (by rfl) ⟨413835, by rfl⟩ : syracuseStep 1103561 = 827671) B827671
theorem B8509157 : Blo 734326 8509157 := bstep (se 4 (by rfl) ⟨797733, by rfl⟩ : syracuseStep 8509157 = 1595467) B1595467
theorem B1660715 : Blo 734326 1660715 := bstep (se 1 (by rfl) ⟨1245536, by rfl⟩ : syracuseStep 1660715 = 2491073) B2491073
theorem B1103675 : Blo 734326 1103675 := bstep (se 1 (by rfl) ⟨827756, by rfl⟩ : syracuseStep 1103675 = 1655513) B1655513
theorem B1103735 : Blo 734326 1103735 := bstep (se 1 (by rfl) ⟨827801, by rfl⟩ : syracuseStep 1103735 = 1655603) B1655603
theorem B1398647 : Blo 734326 1398647 := bstep (se 1 (by rfl) ⟨1048985, by rfl⟩ : syracuseStep 1398647 = 2097971) B2097971
theorem B1103759 : Blo 734326 1103759 := bstep (se 1 (by rfl) ⟨827819, by rfl⟩ : syracuseStep 1103759 = 1655639) B1655639
theorem B2480057 : Blo 734326 2480057 := bstep (se 2 (by rfl) ⟨930021, by rfl⟩ : syracuseStep 2480057 = 1860043) B1860043
theorem B1103801 : Blo 734326 1103801 := bstep (se 2 (by rfl) ⟨413925, by rfl⟩ : syracuseStep 1103801 = 827851) B827851
theorem B1103879 : Blo 734326 1103879 := bstep (se 1 (by rfl) ⟨827909, by rfl⟩ : syracuseStep 1103879 = 1655819) B1655819
theorem B1398799 : Blo 734326 1398799 := bstep (se 1 (by rfl) ⟨1049099, by rfl⟩ : syracuseStep 1398799 = 2098199) B2098199
theorem B1103915 : Blo 734326 1103915 := bstep (se 1 (by rfl) ⟨827936, by rfl⟩ : syracuseStep 1103915 = 1655873) B1655873
theorem B1103945 : Blo 734326 1103945 := bstep (se 2 (by rfl) ⟨413979, by rfl⟩ : syracuseStep 1103945 = 827959) B827959
theorem B1661075 : Blo 734326 1661075 := bstep (se 1 (by rfl) ⟨1245806, by rfl⟩ : syracuseStep 1661075 = 2491613) B2491613
theorem B1104059 : Blo 734326 1104059 := bstep (se 1 (by rfl) ⟨828044, by rfl⟩ : syracuseStep 1104059 = 1656089) B1656089
theorem B3725513 : Blo 734326 3725513 := bstep (se 2 (by rfl) ⟨1397067, by rfl⟩ : syracuseStep 3725513 = 2794135) B2794135
theorem B1661129 : Blo 734326 1661129 := bstep (se 2 (by rfl) ⟨622923, by rfl⟩ : syracuseStep 1661129 = 1245847) B1245847
theorem B1104119 : Blo 734326 1104119 := bstep (se 1 (by rfl) ⟨828089, by rfl⟩ : syracuseStep 1104119 = 1656179) B1656179
theorem B1104143 : Blo 734326 1104143 := bstep (se 1 (by rfl) ⟨828107, by rfl⟩ : syracuseStep 1104143 = 1656215) B1656215
theorem B1104185 : Blo 734326 1104185 := bstep (se 2 (by rfl) ⟨414069, by rfl⟩ : syracuseStep 1104185 = 828139) B828139
theorem B1104263 : Blo 734326 1104263 := bstep (se 1 (by rfl) ⟨828197, by rfl⟩ : syracuseStep 1104263 = 1656395) B1656395
theorem B1399187 : Blo 734326 1399187 := bstep (se 1 (by rfl) ⟨1049390, by rfl⟩ : syracuseStep 1399187 = 2098781) B2098781
theorem B1104299 : Blo 734326 1104299 := bstep (se 1 (by rfl) ⟨828224, by rfl⟩ : syracuseStep 1104299 = 1656449) B1656449
theorem B1104329 : Blo 734326 1104329 := bstep (se 2 (by rfl) ⟨414123, by rfl⟩ : syracuseStep 1104329 = 828247) B828247
theorem B2480651 : Blo 734326 2480651 := bstep (se 1 (by rfl) ⟨1860488, by rfl⟩ : syracuseStep 2480651 = 3720977) B3720977
theorem B1104443 : Blo 734326 1104443 := bstep (se 1 (by rfl) ⟨828332, by rfl⟩ : syracuseStep 1104443 = 1656665) B1656665
theorem B1104503 : Blo 734326 1104503 := bstep (se 1 (by rfl) ⟨828377, by rfl⟩ : syracuseStep 1104503 = 1656755) B1656755
theorem B2480759 : Blo 734326 2480759 := bstep (se 1 (by rfl) ⟨1860569, by rfl⟩ : syracuseStep 2480759 = 3721139) B3721139
theorem B1104527 : Blo 734326 1104527 := bstep (se 1 (by rfl) ⟨828395, by rfl⟩ : syracuseStep 1104527 = 1656791) B1656791
theorem B1104569 : Blo 734326 1104569 := bstep (se 2 (by rfl) ⟨414213, by rfl⟩ : syracuseStep 1104569 = 828427) B828427
theorem B1104647 : Blo 734326 1104647 := bstep (se 1 (by rfl) ⟨828485, by rfl⟩ : syracuseStep 1104647 = 1656971) B1656971
theorem B1104683 : Blo 734326 1104683 := bstep (se 1 (by rfl) ⟨828512, by rfl⟩ : syracuseStep 1104683 = 1657025) B1657025
theorem B1104713 : Blo 734326 1104713 := bstep (se 2 (by rfl) ⟨414267, by rfl⟩ : syracuseStep 1104713 = 828535) B828535
theorem B7068505 : Blo 734326 7068505 := bstep (se 2 (by rfl) ⟨2650689, by rfl⟩ : syracuseStep 7068505 = 5301379) B5301379
theorem B1104827 : Blo 734326 1104827 := bstep (se 1 (by rfl) ⟨828620, by rfl⟩ : syracuseStep 1104827 = 1657241) B1657241
theorem B4185053 : Blo 734326 4185053 := bstep (se 3 (by rfl) ⟨784697, by rfl⟩ : syracuseStep 4185053 = 1569395) B1569395
theorem B1104887 : Blo 734326 1104887 := bstep (se 1 (by rfl) ⟨828665, by rfl⟩ : syracuseStep 1104887 = 1657331) B1657331
theorem B1104911 : Blo 734326 1104911 := bstep (se 1 (by rfl) ⟨828683, by rfl⟩ : syracuseStep 1104911 = 1657367) B1657367
theorem B3529757 : Blo 734326 3529757 := bstep (se 3 (by rfl) ⟨661829, by rfl⟩ : syracuseStep 3529757 = 1323659) B1323659
theorem B1104953 : Blo 734326 1104953 := bstep (se 2 (by rfl) ⟨414357, by rfl⟩ : syracuseStep 1104953 = 828715) B828715
theorem B1105031 : Blo 734326 1105031 := bstep (se 1 (by rfl) ⟨828773, by rfl⟩ : syracuseStep 1105031 = 1657547) B1657547
theorem B1105067 : Blo 734326 1105067 := bstep (se 1 (by rfl) ⟨828800, by rfl⟩ : syracuseStep 1105067 = 1657601) B1657601
theorem B2481353 : Blo 734326 2481353 := bstep (se 2 (by rfl) ⟨930507, by rfl⟩ : syracuseStep 2481353 = 1861015) B1861015
theorem B1105097 : Blo 734326 1105097 := bstep (se 2 (by rfl) ⟨414411, by rfl⟩ : syracuseStep 1105097 = 828823) B828823
theorem B1858859 : Blo 734326 1858859 := bstep (se 1 (by rfl) ⟨1394144, by rfl⟩ : syracuseStep 1858859 = 2788289) B2788289
theorem B1105211 : Blo 734326 1105211 := bstep (se 1 (by rfl) ⟨828908, by rfl⟩ : syracuseStep 1105211 = 1657817) B1657817
theorem B1105271 : Blo 734326 1105271 := bstep (se 1 (by rfl) ⟨828953, by rfl⟩ : syracuseStep 1105271 = 1657907) B1657907
theorem B1105295 : Blo 734326 1105295 := bstep (se 1 (by rfl) ⟨828971, by rfl⟩ : syracuseStep 1105295 = 1657943) B1657943
theorem B1105337 : Blo 734326 1105337 := bstep (se 2 (by rfl) ⟨414501, by rfl⟩ : syracuseStep 1105337 = 829003) B829003
theorem B4185553 : Blo 734326 4185553 := bstep (se 2 (by rfl) ⟨1569582, by rfl⟩ : syracuseStep 4185553 = 3139165) B3139165
theorem B1105415 : Blo 734326 1105415 := bstep (se 1 (by rfl) ⟨829061, by rfl⟩ : syracuseStep 1105415 = 1658123) B1658123
theorem B1105451 : Blo 734326 1105451 := bstep (se 1 (by rfl) ⟨829088, by rfl⟩ : syracuseStep 1105451 = 1658177) B1658177
theorem B1105481 : Blo 734326 1105481 := bstep (se 2 (by rfl) ⟨414555, by rfl⟩ : syracuseStep 1105481 = 829111) B829111
theorem B1105595 : Blo 734326 1105595 := bstep (se 1 (by rfl) ⟨829196, by rfl⟩ : syracuseStep 1105595 = 1658393) B1658393
theorem B1105655 : Blo 734326 1105655 := bstep (se 1 (by rfl) ⟨829241, by rfl⟩ : syracuseStep 1105655 = 1658483) B1658483
theorem B1105679 : Blo 734326 1105679 := bstep (se 1 (by rfl) ⟨829259, by rfl⟩ : syracuseStep 1105679 = 1658519) B1658519
theorem B1400591 : Blo 734326 1400591 := bstep (se 1 (by rfl) ⟨1050443, by rfl⟩ : syracuseStep 1400591 = 2100887) B2100887
theorem B1105721 : Blo 734326 1105721 := bstep (se 2 (by rfl) ⟨414645, by rfl⟩ : syracuseStep 1105721 = 829291) B829291
theorem B2482055 : Blo 734326 2482055 := bstep (se 1 (by rfl) ⟨1861541, by rfl⟩ : syracuseStep 2482055 = 3723083) B3723083
theorem B3497863 : Blo 734326 3497863 := bstep (se 1 (by rfl) ⟨2623397, by rfl⟩ : syracuseStep 3497863 = 5246795) B5246795
theorem B1105799 : Blo 734326 1105799 := bstep (se 1 (by rfl) ⟨829349, by rfl⟩ : syracuseStep 1105799 = 1658699) B1658699
theorem B1105835 : Blo 734326 1105835 := bstep (se 1 (by rfl) ⟨829376, by rfl⟩ : syracuseStep 1105835 = 1658753) B1658753
theorem B1105865 : Blo 734326 1105865 := bstep (se 2 (by rfl) ⟨414699, by rfl⟩ : syracuseStep 1105865 = 829399) B829399
theorem B1105979 : Blo 734326 1105979 := bstep (se 1 (by rfl) ⟨829484, by rfl⟩ : syracuseStep 1105979 = 1658969) B1658969
theorem B1859699 : Blo 734326 1859699 := bstep (se 1 (by rfl) ⟨1394774, by rfl⟩ : syracuseStep 1859699 = 2789549) B2789549
theorem B1106039 : Blo 734326 1106039 := bstep (se 1 (by rfl) ⟨829529, by rfl⟩ : syracuseStep 1106039 = 1659059) B1659059
theorem B1859719 : Blo 734326 1859719 := bstep (se 1 (by rfl) ⟨1394789, by rfl⟩ : syracuseStep 1859719 = 2789579) B2789579
theorem B1106063 : Blo 734326 1106063 := bstep (se 1 (by rfl) ⟨829547, by rfl⟩ : syracuseStep 1106063 = 1659095) B1659095
theorem B1106105 : Blo 734326 1106105 := bstep (se 2 (by rfl) ⟨414789, by rfl⟩ : syracuseStep 1106105 = 829579) B829579
theorem B2482433 : Blo 734326 2482433 := bstep (se 2 (by rfl) ⟨930912, by rfl⟩ : syracuseStep 2482433 = 1861825) B1861825
theorem B1106183 : Blo 734326 1106183 := bstep (se 1 (by rfl) ⟨829637, by rfl⟩ : syracuseStep 1106183 = 1659275) B1659275
theorem B1106219 : Blo 734326 1106219 := bstep (se 1 (by rfl) ⟨829664, by rfl⟩ : syracuseStep 1106219 = 1659329) B1659329
theorem B1401131 : Blo 734326 1401131 := bstep (se 1 (by rfl) ⟨1050848, by rfl⟩ : syracuseStep 1401131 = 2101697) B2101697
theorem B1106249 : Blo 734326 1106249 := bstep (se 2 (by rfl) ⟨414843, by rfl⟩ : syracuseStep 1106249 = 829687) B829687
theorem B1859993 : Blo 734326 1859993 := bstep (se 2 (by rfl) ⟨697497, by rfl⟩ : syracuseStep 1859993 = 1394995) B1394995
theorem B1106363 : Blo 734326 1106363 := bstep (se 1 (by rfl) ⟨829772, by rfl⟩ : syracuseStep 1106363 = 1659545) B1659545
theorem B1106423 : Blo 734326 1106423 := bstep (se 1 (by rfl) ⟨829817, by rfl⟩ : syracuseStep 1106423 = 1659635) B1659635
theorem B1106447 : Blo 734326 1106447 := bstep (se 1 (by rfl) ⟨829835, by rfl⟩ : syracuseStep 1106447 = 1659671) B1659671
theorem B1106489 : Blo 734326 1106489 := bstep (se 2 (by rfl) ⟨414933, by rfl⟩ : syracuseStep 1106489 = 829867) B829867
theorem B1860155 : Blo 734326 1860155 := bstep (se 1 (by rfl) ⟨1395116, by rfl⟩ : syracuseStep 1860155 = 2790233) B2790233
theorem B909883 : Blo 734326 909883 := bstep (se 1 (by rfl) ⟨682412, by rfl⟩ : syracuseStep 909883 = 1364825) B1364825
theorem B2646595 : Blo 734326 2646595 := bstep (se 1 (by rfl) ⟨1984946, by rfl⟩ : syracuseStep 2646595 = 3969893) B3969893
theorem B1106567 : Blo 734326 1106567 := bstep (se 1 (by rfl) ⟨829925, by rfl⟩ : syracuseStep 1106567 = 1659851) B1659851
theorem B1106603 : Blo 734326 1106603 := bstep (se 1 (by rfl) ⟨829952, by rfl⟩ : syracuseStep 1106603 = 1659905) B1659905
theorem B1106633 : Blo 734326 1106633 := bstep (se 2 (by rfl) ⟨414987, by rfl⟩ : syracuseStep 1106633 = 829975) B829975
theorem B1860367 : Blo 734326 1860367 := bstep (se 1 (by rfl) ⟨1395275, by rfl⟩ : syracuseStep 1860367 = 2790551) B2790551
theorem B9429797 : Blo 734326 9429797 := bstep (se 4 (by rfl) ⟨884043, by rfl⟩ : syracuseStep 9429797 = 1768087) B1768087
theorem B1106747 : Blo 734326 1106747 := bstep (se 1 (by rfl) ⟨830060, by rfl⟩ : syracuseStep 1106747 = 1660121) B1660121
theorem B1106807 : Blo 734326 1106807 := bstep (se 1 (by rfl) ⟨830105, by rfl⟩ : syracuseStep 1106807 = 1660211) B1660211
theorem B1106831 : Blo 734326 1106831 := bstep (se 1 (by rfl) ⟨830123, by rfl⟩ : syracuseStep 1106831 = 1660247) B1660247
theorem B5235619 : Blo 734326 5235619 := bstep (se 1 (by rfl) ⟨3926714, by rfl⟩ : syracuseStep 5235619 = 7853429) B7853429
theorem B1106873 : Blo 734326 1106873 := bstep (se 2 (by rfl) ⟨415077, by rfl⟩ : syracuseStep 1106873 = 830155) B830155
theorem B1106951 : Blo 734326 1106951 := bstep (se 1 (by rfl) ⟨830213, by rfl⟩ : syracuseStep 1106951 = 1660427) B1660427
theorem B1860641 : Blo 734326 1860641 := bstep (se 2 (by rfl) ⟨697740, by rfl⟩ : syracuseStep 1860641 = 1395481) B1395481
theorem B2483243 : Blo 734326 2483243 := bstep (se 1 (by rfl) ⟨1862432, by rfl⟩ : syracuseStep 2483243 = 3724865) B3724865
theorem B1893419 : Blo 734326 1893419 := bstep (se 1 (by rfl) ⟨1420064, by rfl⟩ : syracuseStep 1893419 = 2840129) B2840129
theorem B1106987 : Blo 734326 1106987 := bstep (se 1 (by rfl) ⟨830240, by rfl⟩ : syracuseStep 1106987 = 1660481) B1660481
theorem B1107017 : Blo 734326 1107017 := bstep (se 2 (by rfl) ⟨415131, by rfl⟩ : syracuseStep 1107017 = 830263) B830263
theorem B11920517 : Blo 734326 11920517 := bstep (se 4 (by rfl) ⟨1117548, by rfl⟩ : syracuseStep 11920517 = 2235097) B2235097
theorem B1107131 : Blo 734326 1107131 := bstep (se 1 (by rfl) ⟨830348, by rfl⟩ : syracuseStep 1107131 = 1660697) B1660697
theorem B1107191 : Blo 734326 1107191 := bstep (se 1 (by rfl) ⟨830393, by rfl⟩ : syracuseStep 1107191 = 1660787) B1660787
theorem B1107215 : Blo 734326 1107215 := bstep (se 1 (by rfl) ⟨830411, by rfl⟩ : syracuseStep 1107215 = 1660823) B1660823
theorem B1107257 : Blo 734326 1107257 := bstep (se 2 (by rfl) ⟨415221, by rfl⟩ : syracuseStep 1107257 = 830443) B830443
theorem B1107335 : Blo 734326 1107335 := bstep (se 1 (by rfl) ⟨830501, by rfl⟩ : syracuseStep 1107335 = 1661003) B1661003
theorem B4187537 : Blo 734326 4187537 := bstep (se 2 (by rfl) ⟨1570326, by rfl⟩ : syracuseStep 4187537 = 3140653) B3140653
theorem B1107371 : Blo 734326 1107371 := bstep (se 1 (by rfl) ⟨830528, by rfl⟩ : syracuseStep 1107371 = 1661057) B1661057
theorem B1107401 : Blo 734326 1107401 := bstep (se 2 (by rfl) ⟨415275, by rfl⟩ : syracuseStep 1107401 = 830551) B830551
theorem B2123297 : Blo 734326 2123297 := bstep (se 2 (by rfl) ⟨796236, by rfl⟩ : syracuseStep 2123297 = 1592473) B1592473
theorem B3532679 : Blo 734326 3532679 := bstep (se 1 (by rfl) ⟨2649509, by rfl⟩ : syracuseStep 3532679 = 5299019) B5299019
theorem B1861643 : Blo 734326 1861643 := bstep (se 1 (by rfl) ⟨1396232, by rfl⟩ : syracuseStep 1861643 = 2792465) B2792465
theorem B2484539 : Blo 734326 2484539 := bstep (se 1 (by rfl) ⟨1863404, by rfl⟩ : syracuseStep 2484539 = 3726809) B3726809
theorem B1993079 : Blo 734326 1993079 := bstep (se 1 (by rfl) ⟨1494809, by rfl⟩ : syracuseStep 1993079 = 2989619) B2989619
theorem B4712849 : Blo 734326 4712849 := bstep (se 2 (by rfl) ⟨1767318, by rfl⟩ : syracuseStep 4712849 = 3534637) B3534637
theorem B1239671 : Blo 734326 1239671 := bstep (se 1 (by rfl) ⟨929753, by rfl⟩ : syracuseStep 1239671 = 1859507) B1859507
theorem B1862291 : Blo 734326 1862291 := bstep (se 1 (by rfl) ⟨1396718, by rfl⟩ : syracuseStep 1862291 = 2793437) B2793437
theorem B12610241 : Blo 734326 12610241 := bstep (se 2 (by rfl) ⟨4728840, by rfl⟩ : syracuseStep 12610241 = 9457681) B9457681
theorem B2485025 : Blo 734326 2485025 := bstep (se 2 (by rfl) ⟨931884, by rfl⟩ : syracuseStep 2485025 = 1863769) B1863769
theorem B1862585 : Blo 734326 1862585 := bstep (se 2 (by rfl) ⟨698469, by rfl⟩ : syracuseStep 1862585 = 1396939) B1396939
theorem B1993673 : Blo 734326 1993673 := bstep (se 2 (by rfl) ⟨747627, by rfl⟩ : syracuseStep 1993673 = 1495255) B1495255
theorem B8383499 : Blo 734326 8383499 := bstep (se 1 (by rfl) ⟨6287624, by rfl⟩ : syracuseStep 8383499 = 12575249) B12575249
theorem B1240123 : Blo 734326 1240123 := bstep (se 1 (by rfl) ⟨930092, by rfl⟩ : syracuseStep 1240123 = 1860185) B1860185
theorem B3140669 : Blo 734326 3140669 := bstep (se 3 (by rfl) ⟨588875, by rfl⟩ : syracuseStep 3140669 = 1177751) B1177751
theorem B1240265 : Blo 734326 1240265 := bstep (se 2 (by rfl) ⟨465099, by rfl⟩ : syracuseStep 1240265 = 930199) B930199
theorem B2092321 : Blo 734326 2092321 := bstep (se 2 (by rfl) ⟨784620, by rfl⟩ : syracuseStep 2092321 = 1569241) B1569241
theorem B2485619 : Blo 734326 2485619 := bstep (se 1 (by rfl) ⟨1864214, by rfl⟩ : syracuseStep 2485619 = 3728429) B3728429
theorem B3141011 : Blo 734326 3141011 := bstep (se 1 (by rfl) ⟨2355758, by rfl⟩ : syracuseStep 3141011 = 4711517) B4711517
theorem B4713875 : Blo 734326 4713875 := bstep (se 1 (by rfl) ⟨3535406, by rfl⟩ : syracuseStep 4713875 = 7070813) B7070813
theorem B7958083 : Blo 734326 7958083 := bstep (se 1 (by rfl) ⟨5968562, by rfl⟩ : syracuseStep 7958083 = 11937125) B11937125
theorem B1863283 : Blo 734326 1863283 := bstep (se 1 (by rfl) ⟨1397462, by rfl⟩ : syracuseStep 1863283 = 2794925) B2794925
theorem B1437385 : Blo 734326 1437385 := bstep (se 2 (by rfl) ⟨539019, by rfl⟩ : syracuseStep 1437385 = 1078039) B1078039
theorem B1863425 : Blo 734326 1863425 := bstep (se 2 (by rfl) ⟨698784, by rfl⟩ : syracuseStep 1863425 = 1397569) B1397569
theorem B1994539 : Blo 734326 1994539 := bstep (se 1 (by rfl) ⟨1495904, by rfl⟩ : syracuseStep 1994539 = 2991809) B2991809
theorem B1240967 : Blo 734326 1240967 := bstep (se 1 (by rfl) ⟨930725, by rfl⟩ : syracuseStep 1240967 = 1861451) B1861451
theorem B3731345 : Blo 734326 3731345 := bstep (se 2 (by rfl) ⟨1399254, by rfl⟩ : syracuseStep 3731345 = 2798509) B2798509
theorem B1863881 : Blo 734326 1863881 := bstep (se 2 (by rfl) ⟨698955, by rfl⟩ : syracuseStep 1863881 = 1397911) B1397911
theorem B1995155 : Blo 734326 1995155 := bstep (se 1 (by rfl) ⟨1496366, by rfl⟩ : syracuseStep 1995155 = 2992733) B2992733
theorem B17953265 : Blo 734326 17953265 := bstep (se 2 (by rfl) ⟨6732474, by rfl⟩ : syracuseStep 17953265 = 13464949) B13464949
theorem B1241615 : Blo 734326 1241615 := bstep (se 1 (by rfl) ⟨931211, by rfl⟩ : syracuseStep 1241615 = 1862423) B1862423
theorem B2093597 : Blo 734326 2093597 := bstep (se 3 (by rfl) ⟨392549, by rfl⟩ : syracuseStep 2093597 = 785099) B785099
theorem B1864235 : Blo 734326 1864235 := bstep (se 1 (by rfl) ⟨1398176, by rfl⟩ : syracuseStep 1864235 = 2796353) B2796353
theorem B1077895 : Blo 734326 1077895 := bstep (se 1 (by rfl) ⟨808421, by rfl⟩ : syracuseStep 1077895 = 1616843) B1616843
theorem B2093825 : Blo 734326 2093825 := bstep (se 2 (by rfl) ⟨785184, by rfl⟩ : syracuseStep 2093825 = 1570369) B1570369
theorem B7566155 : Blo 734326 7566155 := bstep (se 1 (by rfl) ⟨5674616, by rfl⟩ : syracuseStep 7566155 = 11349233) B11349233
theorem B4486033 : Blo 734326 4486033 := bstep (se 2 (by rfl) ⟨1682262, by rfl⟩ : syracuseStep 4486033 = 3364525) B3364525
theorem B1242155 : Blo 734326 1242155 := bstep (se 1 (by rfl) ⟨931616, by rfl⟩ : syracuseStep 1242155 = 1863233) B1863233
theorem B2094167 : Blo 734326 2094167 := bstep (se 1 (by rfl) ⟨1570625, by rfl⟩ : syracuseStep 2094167 = 3141251) B3141251
theorem B1045705 : Blo 734326 1045705 := bstep (se 2 (by rfl) ⟨392139, by rfl⟩ : syracuseStep 1045705 = 784279) B784279
theorem B2094281 : Blo 734326 2094281 := bstep (se 2 (by rfl) ⟨785355, by rfl⟩ : syracuseStep 2094281 = 1570711) B1570711
theorem B1242383 : Blo 734326 1242383 := bstep (se 1 (by rfl) ⟨931787, by rfl⟩ : syracuseStep 1242383 = 1863575) B1863575
theorem B1045819 : Blo 734326 1045819 := bstep (se 1 (by rfl) ⟨784364, by rfl⟩ : syracuseStep 1045819 = 1568729) B1568729
theorem B1078601 : Blo 734326 1078601 := bstep (se 2 (by rfl) ⟨404475, by rfl⟩ : syracuseStep 1078601 = 808951) B808951
theorem B1242553 : Blo 734326 1242553 := bstep (se 2 (by rfl) ⟨465957, by rfl⟩ : syracuseStep 1242553 = 931915) B931915
theorem B1766857 : Blo 734326 1766857 := bstep (se 2 (by rfl) ⟨662571, by rfl⟩ : syracuseStep 1766857 = 1325143) B1325143
theorem B1865227 : Blo 734326 1865227 := bstep (se 1 (by rfl) ⟨1398920, by rfl⟩ : syracuseStep 1865227 = 2797841) B2797841
theorem B1865369 : Blo 734326 1865369 := bstep (se 2 (by rfl) ⟨699513, by rfl⟩ : syracuseStep 1865369 = 1399027) B1399027
theorem B7567141 : Blo 734326 7567141 := bstep (se 4 (by rfl) ⟨709419, by rfl⟩ : syracuseStep 7567141 = 1418839) B1418839
theorem B1865531 : Blo 734326 1865531 := bstep (se 1 (by rfl) ⟨1399148, by rfl⟩ : syracuseStep 1865531 = 2798297) B2798297
theorem B3143539 : Blo 734326 3143539 := bstep (se 1 (by rfl) ⟨2357654, by rfl⟩ : syracuseStep 3143539 = 4715309) B4715309
theorem B2488211 : Blo 734326 2488211 := bstep (se 1 (by rfl) ⟨1866158, by rfl⟩ : syracuseStep 2488211 = 3732317) B3732317
theorem B1570745 : Blo 734326 1570745 := bstep (se 2 (by rfl) ⟨589029, by rfl⟩ : syracuseStep 1570745 = 1178059) B1178059
theorem B3143609 : Blo 734326 3143609 := bstep (se 2 (by rfl) ⟨1178853, by rfl⟩ : syracuseStep 3143609 = 2357707) B2357707
theorem B3733451 : Blo 734326 3733451 := bstep (se 1 (by rfl) ⟨2800088, by rfl⟩ : syracuseStep 3733451 = 5600177) B5600177
theorem B4192343 : Blo 734326 4192343 := bstep (se 1 (by rfl) ⟨3144257, by rfl⟩ : syracuseStep 4192343 = 6288515) B6288515
theorem B1243255 : Blo 734326 1243255 := bstep (se 1 (by rfl) ⟨932441, by rfl⟩ : syracuseStep 1243255 = 1864883) B1864883
theorem B10090613 : Blo 734326 10090613 := bstep (se 5 (by rfl) ⟨472997, by rfl⟩ : syracuseStep 10090613 = 945995) B945995
theorem B1865875 : Blo 734326 1865875 := bstep (se 1 (by rfl) ⟨1399406, by rfl⟩ : syracuseStep 1865875 = 2798813) B2798813
theorem B3733775 : Blo 734326 3733775 := bstep (se 1 (by rfl) ⟨2800331, by rfl⟩ : syracuseStep 3733775 = 5600663) B5600663
theorem B1866017 : Blo 734326 1866017 := bstep (se 2 (by rfl) ⟨699756, by rfl⟩ : syracuseStep 1866017 = 1399513) B1399513
theorem B1243451 : Blo 734326 1243451 := bstep (se 1 (by rfl) ⟨932588, by rfl⟩ : syracuseStep 1243451 = 1865177) B1865177
theorem B1178155 : Blo 734326 1178155 := bstep (se 1 (by rfl) ⟨883616, by rfl⟩ : syracuseStep 1178155 = 1767233) B1767233
theorem B2980471 : Blo 734326 2980471 := bstep (se 1 (by rfl) ⟨2235353, by rfl⟩ : syracuseStep 2980471 = 4470707) B4470707
theorem B1243849 : Blo 734326 1243849 := bstep (se 2 (by rfl) ⟨466443, by rfl⟩ : syracuseStep 1243849 = 932887) B932887
theorem B1571599 : Blo 734326 1571599 := bstep (se 1 (by rfl) ⟨1178699, by rfl⟩ : syracuseStep 1571599 = 2357399) B2357399
theorem B1047431 : Blo 734326 1047431 := bstep (se 1 (by rfl) ⟨785573, by rfl⟩ : syracuseStep 1047431 = 1571147) B1571147
theorem B1571719 : Blo 734326 1571719 := bstep (se 1 (by rfl) ⟨1178789, by rfl⟩ : syracuseStep 1571719 = 2357579) B2357579
theorem B2096057 : Blo 734326 2096057 := bstep (se 2 (by rfl) ⟨786021, by rfl⟩ : syracuseStep 2096057 = 1572043) B1572043
theorem B1571899 : Blo 734326 1571899 := bstep (se 1 (by rfl) ⟨1178924, by rfl⟩ : syracuseStep 1571899 = 2357849) B2357849
theorem B785543 : Blo 734326 785543 := bstep (se 1 (by rfl) ⟨589157, by rfl⟩ : syracuseStep 785543 = 1178315) B1178315
theorem B1571975 : Blo 734326 1571975 := bstep (se 1 (by rfl) ⟨1178981, by rfl⟩ : syracuseStep 1571975 = 2357963) B2357963
theorem B1867009 : Blo 734326 1867009 := bstep (se 2 (by rfl) ⟨700128, by rfl⟩ : syracuseStep 1867009 = 1400257) B1400257
theorem B2489615 : Blo 734326 2489615 := bstep (se 1 (by rfl) ⟨1867211, by rfl⟩ : syracuseStep 2489615 = 3734423) B3734423
theorem B8387873 : Blo 734326 8387873 := bstep (se 2 (by rfl) ⟨3145452, by rfl⟩ : syracuseStep 8387873 = 6290905) B6290905
theorem B1244551 : Blo 734326 1244551 := bstep (se 1 (by rfl) ⟨933413, by rfl⟩ : syracuseStep 1244551 = 1866827) B1866827
theorem B2489885 : Blo 734326 2489885 := bstep (se 3 (by rfl) ⟨466853, by rfl⟩ : syracuseStep 2489885 = 933707) B933707
theorem B1572385 : Blo 734326 1572385 := bstep (se 2 (by rfl) ⟨589644, by rfl⟩ : syracuseStep 1572385 = 1179289) B1179289
theorem B1769003 : Blo 734326 1769003 := bstep (se 1 (by rfl) ⟨1326752, by rfl⟩ : syracuseStep 1769003 = 2653505) B2653505
theorem B3735233 : Blo 734326 3735233 := bstep (se 2 (by rfl) ⟨1400712, by rfl⟩ : syracuseStep 3735233 = 2801425) B2801425
theorem B884539 : Blo 734326 884539 := bstep (se 1 (by rfl) ⟨663404, by rfl⟩ : syracuseStep 884539 = 1326809) B1326809
theorem B1048393 : Blo 734326 1048393 := bstep (se 2 (by rfl) ⟨393147, by rfl⟩ : syracuseStep 1048393 = 786295) B786295
theorem B1867607 : Blo 734326 1867607 := bstep (se 1 (by rfl) ⟨1400705, by rfl⟩ : syracuseStep 1867607 = 2801411) B2801411
theorem B2097049 : Blo 734326 2097049 := bstep (se 2 (by rfl) ⟨786393, by rfl⟩ : syracuseStep 2097049 = 1572787) B1572787
theorem B3145625 : Blo 734326 3145625 := bstep (se 2 (by rfl) ⟨1179609, by rfl⟩ : syracuseStep 3145625 = 2359219) B2359219
theorem B5898269 : Blo 734326 5898269 := bstep (se 3 (by rfl) ⟨1105925, by rfl⟩ : syracuseStep 5898269 = 2211851) B2211851
theorem B2490425 : Blo 734326 2490425 := bstep (se 2 (by rfl) ⟨933909, by rfl⟩ : syracuseStep 2490425 = 1867819) B1867819
theorem B1245307 : Blo 734326 1245307 := bstep (se 1 (by rfl) ⟨933980, by rfl⟩ : syracuseStep 1245307 = 1867961) B1867961
theorem B2097323 : Blo 734326 2097323 := bstep (se 1 (by rfl) ⟨1572992, by rfl⟩ : syracuseStep 2097323 = 3145985) B3145985
theorem B2490749 : Blo 734326 2490749 := bstep (se 3 (by rfl) ⟨467015, by rfl⟩ : syracuseStep 2490749 = 934031) B934031
theorem B5046731 : Blo 734326 5046731 := bstep (se 1 (by rfl) ⟨3785048, by rfl⟩ : syracuseStep 5046731 = 7570097) B7570097
theorem B3146273 : Blo 734326 3146273 := bstep (se 2 (by rfl) ⟨1179852, by rfl⟩ : syracuseStep 3146273 = 2359705) B2359705
theorem B2491019 : Blo 734326 2491019 := bstep (se 1 (by rfl) ⟨1868264, by rfl⟩ : syracuseStep 2491019 = 3736529) B3736529
theorem B8389331 : Blo 734326 8389331 := bstep (se 1 (by rfl) ⟨6291998, by rfl⟩ : syracuseStep 8389331 = 12583997) B12583997
theorem B1049527 : Blo 734326 1049527 := bstep (se 1 (by rfl) ⟨787145, by rfl⟩ : syracuseStep 1049527 = 1574291) B1574291
theorem B4719667 : Blo 734326 4719667 := bstep (se 1 (by rfl) ⟨3539750, by rfl⟩ : syracuseStep 4719667 = 7079501) B7079501
theorem B3540019 : Blo 734326 3540019 := bstep (se 1 (by rfl) ⟨2655014, by rfl⟩ : syracuseStep 3540019 = 5310029) B5310029
theorem B6980825 : Blo 734326 6980825 := bstep (se 2 (by rfl) ⟨2617809, by rfl⟩ : syracuseStep 6980825 = 5235619) B5235619
theorem B2557271 : Blo 734326 2557271 := bstep (se 1 (by rfl) ⟨1917953, by rfl⟩ : syracuseStep 2557271 = 3835907) B3835907
theorem B1181147 : Blo 734326 1181147 := bstep (se 1 (by rfl) ⟨885860, by rfl⟩ : syracuseStep 1181147 = 1771721) B1771721
theorem B886235 : Blo 734326 886235 := bstep (se 1 (by rfl) ⟨664676, by rfl⟩ : syracuseStep 886235 = 1329353) B1329353
theorem B5966129 : Blo 734326 5966129 := bstep (se 2 (by rfl) ⟨2237298, by rfl⟩ : syracuseStep 5966129 = 4474597) B4474597
theorem B3180887 : Blo 734326 3180887 := bstep (se 1 (by rfl) ⟨2385665, by rfl⟩ : syracuseStep 3180887 = 4771331) B4771331
theorem B1050985 : Blo 734326 1050985 := bstep (se 2 (by rfl) ⟨394119, by rfl⟩ : syracuseStep 1050985 = 788239) B788239
theorem B1575521 : Blo 734326 1575521 := bstep (se 2 (by rfl) ⟨590820, by rfl⟩ : syracuseStep 1575521 = 1181641) B1181641
theorem B3771089 : Blo 734326 3771089 := bstep (se 2 (by rfl) ⟨1414158, by rfl⟩ : syracuseStep 3771089 = 2828317) B2828317
theorem B4852709 : Blo 734326 4852709 := bstep (se 4 (by rfl) ⟨454941, by rfl⟩ : syracuseStep 4852709 = 909883) B909883
theorem B4721665 : Blo 734326 4721665 := bstep (se 2 (by rfl) ⟨1770624, by rfl⟩ : syracuseStep 4721665 = 3541249) B3541249
theorem B4787545 : Blo 734326 4787545 := bstep (se 2 (by rfl) ⟨1795329, by rfl⟩ : syracuseStep 4787545 = 3590659) B3590659
theorem B3313021 : Blo 734326 3313021 := bstep (se 3 (by rfl) ⟨621191, by rfl⟩ : syracuseStep 3313021 = 1242383) B1242383
theorem B11505077 : Blo 734326 11505077 := bstep (se 5 (by rfl) ⟨539300, by rfl⟩ : syracuseStep 11505077 = 1078601) B1078601
theorem B2789063 : Blo 734326 2789063 := bstep (se 1 (by rfl) ⟨2091797, by rfl⟩ : syracuseStep 2789063 = 4183595) B4183595
theorem B5672771 : Blo 734326 5672771 := bstep (se 1 (by rfl) ⟨4254578, by rfl⟩ : syracuseStep 5672771 = 8509157) B8509157
theorem B2789761 : Blo 734326 2789761 := bstep (se 2 (by rfl) ⟨1046160, by rfl⟩ : syracuseStep 2789761 = 2092321) B2092321
theorem B2790035 : Blo 734326 2790035 := bstep (se 1 (by rfl) ⟨2092526, by rfl⟩ : syracuseStep 2790035 = 4185053) B4185053
theorem B6296237 : Blo 734326 6296237 := bstep (se 3 (by rfl) ⟨1180544, by rfl⟩ : syracuseStep 6296237 = 2361089) B2361089
theorem B14160689 : Blo 734326 14160689 := bstep (se 2 (by rfl) ⟨5310258, by rfl⟩ : syracuseStep 14160689 = 10620517) B10620517
theorem B2659385 : Blo 734326 2659385 := bstep (se 2 (by rfl) ⟨997269, by rfl⟩ : syracuseStep 2659385 = 1994539) B1994539
theorem B5969371 : Blo 734326 5969371 := bstep (se 1 (by rfl) ⟨4477028, by rfl⟩ : syracuseStep 5969371 = 8954057) B8954057
theorem B3151399 : Blo 734326 3151399 := bstep (se 1 (by rfl) ⟨2363549, by rfl⟩ : syracuseStep 3151399 = 4727099) B4727099
theorem B26908301 : Blo 734326 26908301 := bstep (se 3 (by rfl) ⟨5045306, by rfl⟩ : syracuseStep 26908301 = 10090613) B10090613
theorem B2987705 : Blo 734326 2987705 := bstep (se 2 (by rfl) ⟨1120389, by rfl⟩ : syracuseStep 2987705 = 2240779) B2240779
theorem B2365139 : Blo 734326 2365139 := bstep (se 1 (by rfl) ⟨1773854, by rfl⟩ : syracuseStep 2365139 = 3547709) B3547709
theorem B4724513 : Blo 734326 4724513 := bstep (se 2 (by rfl) ⟨1771692, by rfl⟩ : syracuseStep 4724513 = 3543385) B3543385
theorem B8722235 : Blo 734326 8722235 := bstep (se 1 (by rfl) ⟨6541676, by rfl⟩ : syracuseStep 8722235 = 13083353) B13083353
theorem B2791691 : Blo 734326 2791691 := bstep (se 1 (by rfl) ⟨2093768, by rfl⟩ : syracuseStep 2791691 = 4187537) B4187537
theorem B1415531 : Blo 734326 1415531 := bstep (se 1 (by rfl) ⟨1061648, by rfl⟩ : syracuseStep 1415531 = 2123297) B2123297
theorem B3545633 : Blo 734326 3545633 := bstep (se 2 (by rfl) ⟨1329612, by rfl⟩ : syracuseStep 3545633 = 2659225) B2659225
theorem B826447 : Blo 734326 826447 := bstep (se 1 (by rfl) ⟨619835, by rfl⟩ : syracuseStep 826447 = 1239671) B1239671
theorem B826843 : Blo 734326 826843 := bstep (se 1 (by rfl) ⟨620132, by rfl⟩ : syracuseStep 826843 = 1240265) B1240265
theorem B2793149 : Blo 734326 2793149 := bstep (se 3 (by rfl) ⟨523715, by rfl⟩ : syracuseStep 2793149 = 1047431) B1047431
theorem B5316461 : Blo 734326 5316461 := bstep (se 3 (by rfl) ⟨996836, by rfl⟩ : syracuseStep 5316461 = 1993673) B1993673
theorem B827311 : Blo 734326 827311 := bstep (se 1 (by rfl) ⟨620483, by rfl⟩ : syracuseStep 827311 = 1240967) B1240967
theorem B1679417 : Blo 734326 1679417 := bstep (se 2 (by rfl) ⟨629781, by rfl⟩ : syracuseStep 1679417 = 1259563) B1259563
theorem B11968843 : Blo 734326 11968843 := bstep (se 1 (by rfl) ⟨8976632, by rfl⟩ : syracuseStep 11968843 = 17953265) B17953265
theorem B827743 : Blo 734326 827743 := bstep (se 1 (by rfl) ⟨620807, by rfl⟩ : syracuseStep 827743 = 1241615) B1241615
theorem B10625539 : Blo 734326 10625539 := bstep (se 1 (by rfl) ⟨7969154, by rfl⟩ : syracuseStep 10625539 = 15938309) B15938309
theorem B11936281 : Blo 734326 11936281 := bstep (se 2 (by rfl) ⟨4476105, by rfl⟩ : syracuseStep 11936281 = 8952211) B8952211
theorem B828103 : Blo 734326 828103 := bstep (se 1 (by rfl) ⟨621077, by rfl⟩ : syracuseStep 828103 = 1242155) B1242155
theorem B3973961 : Blo 734326 3973961 := bstep (se 2 (by rfl) ⟨1490235, by rfl⟩ : syracuseStep 3973961 = 2980471) B2980471
theorem B40412357 : Blo 734326 40412357 := bstep (se 4 (by rfl) ⟨3788658, by rfl⟩ : syracuseStep 40412357 = 7577317) B7577317
theorem B5383415 : Blo 734326 5383415 := bstep (se 1 (by rfl) ⟨4037561, by rfl⟩ : syracuseStep 5383415 = 8075123) B8075123
theorem B2794895 : Blo 734326 2794895 := bstep (se 1 (by rfl) ⟨2096171, by rfl⟩ : syracuseStep 2794895 = 4192343) B4192343
theorem B5580251 : Blo 734326 5580251 := bstep (se 1 (by rfl) ⟨4185188, by rfl⟩ : syracuseStep 5580251 = 8370377) B8370377
theorem B828967 : Blo 734326 828967 := bstep (se 1 (by rfl) ⟨621725, by rfl⟩ : syracuseStep 828967 = 1243451) B1243451
theorem B8496737 : Blo 734326 8496737 := bstep (se 2 (by rfl) ⟨3186276, by rfl⟩ : syracuseStep 8496737 = 6372553) B6372553
theorem B11970341 : Blo 734326 11970341 := bstep (se 4 (by rfl) ⟨1122219, by rfl⟩ : syracuseStep 11970341 = 2244439) B2244439
theorem B5580737 : Blo 734326 5580737 := bstep (se 2 (by rfl) ⟨2092776, by rfl⟩ : syracuseStep 5580737 = 4185553) B4185553
theorem B27207683 : Blo 734326 27207683 := bstep (se 1 (by rfl) ⟨20405762, by rfl⟩ : syracuseStep 27207683 = 40811525) B40811525
theorem B993479 : Blo 734326 993479 := bstep (se 1 (by rfl) ⟨745109, by rfl⟩ : syracuseStep 993479 = 1490219) B1490219
theorem B4663817 : Blo 734326 4663817 := bstep (se 2 (by rfl) ⟨1748931, by rfl⟩ : syracuseStep 4663817 = 3497863) B3497863
theorem B2796065 : Blo 734326 2796065 := bstep (se 2 (by rfl) ⟨1048524, by rfl⟩ : syracuseStep 2796065 = 2097049) B2097049
theorem B2796383 : Blo 734326 2796383 := bstep (se 1 (by rfl) ⟨2097287, by rfl⟩ : syracuseStep 2796383 = 4194575) B4194575
theorem B25537463 : Blo 734326 25537463 := bstep (se 1 (by rfl) ⟨19153097, by rfl⟩ : syracuseStep 25537463 = 38306195) B38306195
theorem B2796551 : Blo 734326 2796551 := bstep (se 1 (by rfl) ⟨2097413, by rfl⟩ : syracuseStep 2796551 = 4194827) B4194827
theorem B830587 : Blo 734326 830587 := bstep (se 1 (by rfl) ⟨622940, by rfl⟩ : syracuseStep 830587 = 1245881) B1245881
theorem B5582195 : Blo 734326 5582195 := bstep (se 1 (by rfl) ⟨4186646, by rfl⟩ : syracuseStep 5582195 = 8373293) B8373293
theorem B2797037 : Blo 734326 2797037 := bstep (se 3 (by rfl) ⟨524444, by rfl⟩ : syracuseStep 2797037 = 1048889) B1048889
theorem B2797355 : Blo 734326 2797355 := bstep (se 1 (by rfl) ⟨2098016, by rfl⟩ : syracuseStep 2797355 = 4196033) B4196033
theorem B1683703 : Blo 734326 1683703 := bstep (se 1 (by rfl) ⟨1262777, by rfl⟩ : syracuseStep 1683703 = 2525555) B2525555
theorem B930143 : Blo 734326 930143 := bstep (se 1 (by rfl) ⟨697607, by rfl⟩ : syracuseStep 930143 = 1395215) B1395215
theorem B1323371 : Blo 734326 1323371 := bstep (se 1 (by rfl) ⟨992528, by rfl⟩ : syracuseStep 1323371 = 1985057) B1985057
theorem B734331 : Blo 734326 734331 := bstep (se 1 (by rfl) ⟨550748, by rfl⟩ : syracuseStep 734331 = 1101497) B1101497
theorem B734383 : Blo 734326 734383 := bstep (se 1 (by rfl) ⟨550787, by rfl⟩ : syracuseStep 734383 = 1101575) B1101575
theorem B734407 : Blo 734326 734407 := bstep (se 1 (by rfl) ⟨550805, by rfl⟩ : syracuseStep 734407 = 1101611) B1101611
theorem B734427 : Blo 734326 734427 := bstep (se 1 (by rfl) ⟨550820, by rfl⟩ : syracuseStep 734427 = 1101641) B1101641
theorem B734503 : Blo 734326 734503 := bstep (se 1 (by rfl) ⟨550877, by rfl⟩ : syracuseStep 734503 = 1101755) B1101755
theorem B734543 : Blo 734326 734543 := bstep (se 1 (by rfl) ⟨550907, by rfl⟩ : syracuseStep 734543 = 1101815) B1101815
theorem B734559 : Blo 734326 734559 := bstep (se 1 (by rfl) ⟨550919, by rfl⟩ : syracuseStep 734559 = 1101839) B1101839
theorem B734587 : Blo 734326 734587 := bstep (se 1 (by rfl) ⟨550940, by rfl⟩ : syracuseStep 734587 = 1101881) B1101881
theorem B9450917 : Blo 734326 9450917 := bstep (se 4 (by rfl) ⟨886023, by rfl⟩ : syracuseStep 9450917 = 1772047) B1772047
theorem B734639 : Blo 734326 734639 := bstep (se 1 (by rfl) ⟨550979, by rfl⟩ : syracuseStep 734639 = 1101959) B1101959
theorem B734663 : Blo 734326 734663 := bstep (se 1 (by rfl) ⟨550997, by rfl⟩ : syracuseStep 734663 = 1101995) B1101995
theorem B734683 : Blo 734326 734683 := bstep (se 1 (by rfl) ⟨551012, by rfl⟩ : syracuseStep 734683 = 1102025) B1102025
theorem B734759 : Blo 734326 734759 := bstep (se 1 (by rfl) ⟨551069, by rfl⟩ : syracuseStep 734759 = 1102139) B1102139
theorem B734799 : Blo 734326 734799 := bstep (se 1 (by rfl) ⟨551099, by rfl⟩ : syracuseStep 734799 = 1102199) B1102199
theorem B734815 : Blo 734326 734815 := bstep (se 1 (by rfl) ⟨551111, by rfl⟩ : syracuseStep 734815 = 1102223) B1102223
theorem B734843 : Blo 734326 734843 := bstep (se 1 (by rfl) ⟨551132, by rfl⟩ : syracuseStep 734843 = 1102265) B1102265
theorem B7059089 : Blo 734326 7059089 := bstep (se 2 (by rfl) ⟨2647158, by rfl⟩ : syracuseStep 7059089 = 5294317) B5294317
theorem B734895 : Blo 734326 734895 := bstep (se 1 (by rfl) ⟨551171, by rfl⟩ : syracuseStep 734895 = 1102343) B1102343
theorem B734919 : Blo 734326 734919 := bstep (se 1 (by rfl) ⟨551189, by rfl⟩ : syracuseStep 734919 = 1102379) B1102379
theorem B1652435 : Blo 734326 1652435 := bstep (se 1 (by rfl) ⟨1239326, by rfl⟩ : syracuseStep 1652435 = 2478653) B2478653
theorem B734939 : Blo 734326 734939 := bstep (se 1 (by rfl) ⟨551204, by rfl⟩ : syracuseStep 734939 = 1102409) B1102409
theorem B735015 : Blo 734326 735015 := bstep (se 1 (by rfl) ⟨551261, by rfl⟩ : syracuseStep 735015 = 1102523) B1102523
theorem B735055 : Blo 734326 735055 := bstep (se 1 (by rfl) ⟨551291, by rfl⟩ : syracuseStep 735055 = 1102583) B1102583
theorem B735071 : Blo 734326 735071 := bstep (se 1 (by rfl) ⟨551303, by rfl⟩ : syracuseStep 735071 = 1102607) B1102607
theorem B2799467 : Blo 734326 2799467 := bstep (se 1 (by rfl) ⟨2099600, by rfl⟩ : syracuseStep 2799467 = 4199201) B4199201
theorem B1324907 : Blo 734326 1324907 := bstep (se 1 (by rfl) ⟨993680, by rfl⟩ : syracuseStep 1324907 = 1987361) B1987361
theorem B735099 : Blo 734326 735099 := bstep (se 1 (by rfl) ⟨551324, by rfl⟩ : syracuseStep 735099 = 1102649) B1102649
theorem B735151 : Blo 734326 735151 := bstep (se 1 (by rfl) ⟨551363, by rfl⟩ : syracuseStep 735151 = 1102727) B1102727
theorem B735175 : Blo 734326 735175 := bstep (se 1 (by rfl) ⟨551381, by rfl⟩ : syracuseStep 735175 = 1102763) B1102763
theorem B735195 : Blo 734326 735195 := bstep (se 1 (by rfl) ⟨551396, by rfl⟩ : syracuseStep 735195 = 1102793) B1102793
theorem B735271 : Blo 734326 735271 := bstep (se 1 (by rfl) ⟨551453, by rfl⟩ : syracuseStep 735271 = 1102907) B1102907
theorem B735311 : Blo 734326 735311 := bstep (se 1 (by rfl) ⟨551483, by rfl⟩ : syracuseStep 735311 = 1102967) B1102967
theorem B735327 : Blo 734326 735327 := bstep (se 1 (by rfl) ⟨551495, by rfl⟩ : syracuseStep 735327 = 1102991) B1102991
theorem B735355 : Blo 734326 735355 := bstep (se 1 (by rfl) ⟨551516, by rfl⟩ : syracuseStep 735355 = 1103033) B1103033
theorem B735407 : Blo 734326 735407 := bstep (se 1 (by rfl) ⟨551555, by rfl⟩ : syracuseStep 735407 = 1103111) B1103111
theorem B735431 : Blo 734326 735431 := bstep (se 1 (by rfl) ⟨551573, by rfl⟩ : syracuseStep 735431 = 1103147) B1103147
theorem B735451 : Blo 734326 735451 := bstep (se 1 (by rfl) ⟨551588, by rfl⟩ : syracuseStep 735451 = 1103177) B1103177
theorem B735527 : Blo 734326 735527 := bstep (se 1 (by rfl) ⟨551645, by rfl⟩ : syracuseStep 735527 = 1103291) B1103291
theorem B735567 : Blo 734326 735567 := bstep (se 1 (by rfl) ⟨551675, by rfl⟩ : syracuseStep 735567 = 1103351) B1103351
theorem B735583 : Blo 734326 735583 := bstep (se 1 (by rfl) ⟨551687, by rfl⟩ : syracuseStep 735583 = 1103375) B1103375
theorem B735611 : Blo 734326 735611 := bstep (se 1 (by rfl) ⟨551708, by rfl⟩ : syracuseStep 735611 = 1103417) B1103417
theorem B735663 : Blo 734326 735663 := bstep (se 1 (by rfl) ⟨551747, by rfl⟩ : syracuseStep 735663 = 1103495) B1103495
theorem B735687 : Blo 734326 735687 := bstep (se 1 (by rfl) ⟨551765, by rfl⟩ : syracuseStep 735687 = 1103531) B1103531
theorem B735707 : Blo 734326 735707 := bstep (se 1 (by rfl) ⟨551780, by rfl⟩ : syracuseStep 735707 = 1103561) B1103561
theorem B735783 : Blo 734326 735783 := bstep (se 1 (by rfl) ⟨551837, by rfl⟩ : syracuseStep 735783 = 1103675) B1103675
theorem B735823 : Blo 734326 735823 := bstep (se 1 (by rfl) ⟨551867, by rfl⟩ : syracuseStep 735823 = 1103735) B1103735
theorem B735839 : Blo 734326 735839 := bstep (se 1 (by rfl) ⟨551879, by rfl⟩ : syracuseStep 735839 = 1103759) B1103759
theorem B1653371 : Blo 734326 1653371 := bstep (se 1 (by rfl) ⟨1240028, by rfl⟩ : syracuseStep 1653371 = 2480057) B2480057
theorem B735867 : Blo 734326 735867 := bstep (se 1 (by rfl) ⟨551900, by rfl⟩ : syracuseStep 735867 = 1103801) B1103801
theorem B735919 : Blo 734326 735919 := bstep (se 1 (by rfl) ⟨551939, by rfl⟩ : syracuseStep 735919 = 1103879) B1103879
theorem B735943 : Blo 734326 735943 := bstep (se 1 (by rfl) ⟨551957, by rfl⟩ : syracuseStep 735943 = 1103915) B1103915
theorem B735963 : Blo 734326 735963 := bstep (se 1 (by rfl) ⟨551972, by rfl⟩ : syracuseStep 735963 = 1103945) B1103945
theorem B1653497 : Blo 734326 1653497 := bstep (se 2 (by rfl) ⟨620061, by rfl⟩ : syracuseStep 1653497 = 1240123) B1240123
theorem B736039 : Blo 734326 736039 := bstep (se 1 (by rfl) ⟨552029, by rfl⟩ : syracuseStep 736039 = 1104059) B1104059
theorem B736079 : Blo 734326 736079 := bstep (se 1 (by rfl) ⟨552059, by rfl⟩ : syracuseStep 736079 = 1104119) B1104119
theorem B736095 : Blo 734326 736095 := bstep (se 1 (by rfl) ⟨552071, by rfl⟩ : syracuseStep 736095 = 1104143) B1104143
theorem B736123 : Blo 734326 736123 := bstep (se 1 (by rfl) ⟨552092, by rfl⟩ : syracuseStep 736123 = 1104185) B1104185
theorem B736175 : Blo 734326 736175 := bstep (se 1 (by rfl) ⟨552131, by rfl⟩ : syracuseStep 736175 = 1104263) B1104263
theorem B2866103 : Blo 734326 2866103 := bstep (se 1 (by rfl) ⟨2149577, by rfl⟩ : syracuseStep 2866103 = 4299155) B4299155
theorem B932791 : Blo 734326 932791 := bstep (se 1 (by rfl) ⟨699593, by rfl⟩ : syracuseStep 932791 = 1399187) B1399187
theorem B736199 : Blo 734326 736199 := bstep (se 1 (by rfl) ⟨552149, by rfl⟩ : syracuseStep 736199 = 1104299) B1104299
theorem B736219 : Blo 734326 736219 := bstep (se 1 (by rfl) ⟨552164, by rfl⟩ : syracuseStep 736219 = 1104329) B1104329
theorem B1653767 : Blo 734326 1653767 := bstep (se 1 (by rfl) ⟨1240325, by rfl⟩ : syracuseStep 1653767 = 2480651) B2480651
theorem B736295 : Blo 734326 736295 := bstep (se 1 (by rfl) ⟨552221, by rfl⟩ : syracuseStep 736295 = 1104443) B1104443
theorem B3718223 : Blo 734326 3718223 := bstep (se 1 (by rfl) ⟨2788667, by rfl⟩ : syracuseStep 3718223 = 5577335) B5577335
theorem B1653839 : Blo 734326 1653839 := bstep (se 1 (by rfl) ⟨1240379, by rfl⟩ : syracuseStep 1653839 = 2480759) B2480759
theorem B736335 : Blo 734326 736335 := bstep (se 1 (by rfl) ⟨552251, by rfl⟩ : syracuseStep 736335 = 1104503) B1104503
theorem B736351 : Blo 734326 736351 := bstep (se 1 (by rfl) ⟨552263, by rfl⟩ : syracuseStep 736351 = 1104527) B1104527
theorem B736379 : Blo 734326 736379 := bstep (se 1 (by rfl) ⟨552284, by rfl⟩ : syracuseStep 736379 = 1104569) B1104569
theorem B736431 : Blo 734326 736431 := bstep (se 1 (by rfl) ⟨552323, by rfl⟩ : syracuseStep 736431 = 1104647) B1104647
theorem B736455 : Blo 734326 736455 := bstep (se 1 (by rfl) ⟨552341, by rfl⟩ : syracuseStep 736455 = 1104683) B1104683
theorem B736475 : Blo 734326 736475 := bstep (se 1 (by rfl) ⟨552356, by rfl⟩ : syracuseStep 736475 = 1104713) B1104713
theorem B736551 : Blo 734326 736551 := bstep (se 1 (by rfl) ⟨552413, by rfl⟩ : syracuseStep 736551 = 1104827) B1104827
theorem B736591 : Blo 734326 736591 := bstep (se 1 (by rfl) ⟨552443, by rfl⟩ : syracuseStep 736591 = 1104887) B1104887
theorem B736607 : Blo 734326 736607 := bstep (se 1 (by rfl) ⟨552455, by rfl⟩ : syracuseStep 736607 = 1104911) B1104911
theorem B736635 : Blo 734326 736635 := bstep (se 1 (by rfl) ⟨552476, by rfl⟩ : syracuseStep 736635 = 1104953) B1104953
theorem B736687 : Blo 734326 736687 := bstep (se 1 (by rfl) ⟨552515, by rfl⟩ : syracuseStep 736687 = 1105031) B1105031
theorem B736711 : Blo 734326 736711 := bstep (se 1 (by rfl) ⟨552533, by rfl⟩ : syracuseStep 736711 = 1105067) B1105067
theorem B1654235 : Blo 734326 1654235 := bstep (se 1 (by rfl) ⟨1240676, by rfl⟩ : syracuseStep 1654235 = 2481353) B2481353
theorem B736731 : Blo 734326 736731 := bstep (se 1 (by rfl) ⟨552548, by rfl⟩ : syracuseStep 736731 = 1105097) B1105097
theorem B736807 : Blo 734326 736807 := bstep (se 1 (by rfl) ⟨552605, by rfl⟩ : syracuseStep 736807 = 1105211) B1105211
theorem B736847 : Blo 734326 736847 := bstep (se 1 (by rfl) ⟨552635, by rfl⟩ : syracuseStep 736847 = 1105271) B1105271
theorem B736863 : Blo 734326 736863 := bstep (se 1 (by rfl) ⟨552647, by rfl⟩ : syracuseStep 736863 = 1105295) B1105295
theorem B1916513 : Blo 734326 1916513 := bstep (se 2 (by rfl) ⟨718692, by rfl⟩ : syracuseStep 1916513 = 1437385) B1437385
theorem B8371835 : Blo 734326 8371835 := bstep (se 1 (by rfl) ⟨6278876, by rfl⟩ : syracuseStep 8371835 = 12557753) B12557753
theorem B736891 : Blo 734326 736891 := bstep (se 1 (by rfl) ⟨552668, by rfl⟩ : syracuseStep 736891 = 1105337) B1105337
theorem B736943 : Blo 734326 736943 := bstep (se 1 (by rfl) ⟨552707, by rfl⟩ : syracuseStep 736943 = 1105415) B1105415
theorem B736967 : Blo 734326 736967 := bstep (se 1 (by rfl) ⟨552725, by rfl⟩ : syracuseStep 736967 = 1105451) B1105451
theorem B3718871 : Blo 734326 3718871 := bstep (se 1 (by rfl) ⟨2789153, by rfl⟩ : syracuseStep 3718871 = 5578307) B5578307
theorem B736987 : Blo 734326 736987 := bstep (se 1 (by rfl) ⟨552740, by rfl⟩ : syracuseStep 736987 = 1105481) B1105481
theorem B737063 : Blo 734326 737063 := bstep (se 1 (by rfl) ⟨552797, by rfl⟩ : syracuseStep 737063 = 1105595) B1105595
theorem B737103 : Blo 734326 737103 := bstep (se 1 (by rfl) ⟨552827, by rfl⟩ : syracuseStep 737103 = 1105655) B1105655
theorem B737119 : Blo 734326 737119 := bstep (se 1 (by rfl) ⟨552839, by rfl⟩ : syracuseStep 737119 = 1105679) B1105679
theorem B737147 : Blo 734326 737147 := bstep (se 1 (by rfl) ⟨552860, by rfl⟩ : syracuseStep 737147 = 1105721) B1105721
theorem B1654703 : Blo 734326 1654703 := bstep (se 1 (by rfl) ⟨1241027, by rfl⟩ : syracuseStep 1654703 = 2482055) B2482055
theorem B737199 : Blo 734326 737199 := bstep (se 1 (by rfl) ⟨552899, by rfl⟩ : syracuseStep 737199 = 1105799) B1105799
theorem B737223 : Blo 734326 737223 := bstep (se 1 (by rfl) ⟨552917, by rfl⟩ : syracuseStep 737223 = 1105835) B1105835
theorem B737243 : Blo 734326 737243 := bstep (se 1 (by rfl) ⟨552932, by rfl⟩ : syracuseStep 737243 = 1105865) B1105865
theorem B737319 : Blo 734326 737319 := bstep (se 1 (by rfl) ⟨552989, by rfl⟩ : syracuseStep 737319 = 1105979) B1105979
theorem B737359 : Blo 734326 737359 := bstep (se 1 (by rfl) ⟨553019, by rfl⟩ : syracuseStep 737359 = 1106039) B1106039
theorem B737375 : Blo 734326 737375 := bstep (se 1 (by rfl) ⟨553031, by rfl⟩ : syracuseStep 737375 = 1106063) B1106063
theorem B737403 : Blo 734326 737403 := bstep (se 1 (by rfl) ⟨553052, by rfl⟩ : syracuseStep 737403 = 1106105) B1106105
theorem B1654955 : Blo 734326 1654955 := bstep (se 1 (by rfl) ⟨1241216, by rfl⟩ : syracuseStep 1654955 = 2482433) B2482433
theorem B737455 : Blo 734326 737455 := bstep (se 1 (by rfl) ⟨553091, by rfl⟩ : syracuseStep 737455 = 1106183) B1106183
theorem B737479 : Blo 734326 737479 := bstep (se 1 (by rfl) ⟨553109, by rfl⟩ : syracuseStep 737479 = 1106219) B1106219
theorem B934087 : Blo 734326 934087 := bstep (se 1 (by rfl) ⟨700565, by rfl⟩ : syracuseStep 934087 = 1401131) B1401131
theorem B737499 : Blo 734326 737499 := bstep (se 1 (by rfl) ⟨553124, by rfl⟩ : syracuseStep 737499 = 1106249) B1106249
theorem B2801911 : Blo 734326 2801911 := bstep (se 1 (by rfl) ⟨2101433, by rfl⟩ : syracuseStep 2801911 = 4202867) B4202867
theorem B737575 : Blo 734326 737575 := bstep (se 1 (by rfl) ⟨553181, by rfl⟩ : syracuseStep 737575 = 1106363) B1106363
theorem B737615 : Blo 734326 737615 := bstep (se 1 (by rfl) ⟨553211, by rfl⟩ : syracuseStep 737615 = 1106423) B1106423
theorem B737631 : Blo 734326 737631 := bstep (se 1 (by rfl) ⟨553223, by rfl⟩ : syracuseStep 737631 = 1106447) B1106447
theorem B737659 : Blo 734326 737659 := bstep (se 1 (by rfl) ⟨553244, by rfl⟩ : syracuseStep 737659 = 1106489) B1106489
theorem B737711 : Blo 734326 737711 := bstep (se 1 (by rfl) ⟨553283, by rfl⟩ : syracuseStep 737711 = 1106567) B1106567
theorem B737735 : Blo 734326 737735 := bstep (se 1 (by rfl) ⟨553301, by rfl⟩ : syracuseStep 737735 = 1106603) B1106603
theorem B737755 : Blo 734326 737755 := bstep (se 1 (by rfl) ⟨553316, by rfl⟩ : syracuseStep 737755 = 1106633) B1106633
theorem B2802185 : Blo 734326 2802185 := bstep (se 2 (by rfl) ⟨1050819, by rfl⟩ : syracuseStep 2802185 = 2101639) B2101639
theorem B22921751 : Blo 734326 22921751 := bstep (se 1 (by rfl) ⟨17191313, by rfl⟩ : syracuseStep 22921751 = 34382627) B34382627
theorem B737831 : Blo 734326 737831 := bstep (se 1 (by rfl) ⟨553373, by rfl⟩ : syracuseStep 737831 = 1106747) B1106747
theorem B2802215 : Blo 734326 2802215 := bstep (se 1 (by rfl) ⟨2101661, by rfl⟩ : syracuseStep 2802215 = 4203323) B4203323
theorem B737871 : Blo 734326 737871 := bstep (se 1 (by rfl) ⟨553403, by rfl⟩ : syracuseStep 737871 = 1106807) B1106807
theorem B737887 : Blo 734326 737887 := bstep (se 1 (by rfl) ⟨553415, by rfl⟩ : syracuseStep 737887 = 1106831) B1106831
theorem B737915 : Blo 734326 737915 := bstep (se 1 (by rfl) ⟨553436, by rfl⟩ : syracuseStep 737915 = 1106873) B1106873
theorem B737967 : Blo 734326 737967 := bstep (se 1 (by rfl) ⟨553475, by rfl⟩ : syracuseStep 737967 = 1106951) B1106951
theorem B1655495 : Blo 734326 1655495 := bstep (se 1 (by rfl) ⟨1241621, by rfl⟩ : syracuseStep 1655495 = 2483243) B2483243
theorem B1262279 : Blo 734326 1262279 := bstep (se 1 (by rfl) ⟨946709, by rfl⟩ : syracuseStep 1262279 = 1893419) B1893419
theorem B737991 : Blo 734326 737991 := bstep (se 1 (by rfl) ⟨553493, by rfl⟩ : syracuseStep 737991 = 1106987) B1106987
theorem B738011 : Blo 734326 738011 := bstep (se 1 (by rfl) ⟨553508, by rfl⟩ : syracuseStep 738011 = 1107017) B1107017
theorem B7947011 : Blo 734326 7947011 := bstep (se 1 (by rfl) ⟨5960258, by rfl⟩ : syracuseStep 7947011 = 11920517) B11920517
theorem B738087 : Blo 734326 738087 := bstep (se 1 (by rfl) ⟨553565, by rfl⟩ : syracuseStep 738087 = 1107131) B1107131
theorem B738127 : Blo 734326 738127 := bstep (se 1 (by rfl) ⟨553595, by rfl⟩ : syracuseStep 738127 = 1107191) B1107191
theorem B738143 : Blo 734326 738143 := bstep (se 1 (by rfl) ⟨553607, by rfl⟩ : syracuseStep 738143 = 1107215) B1107215
theorem B738171 : Blo 734326 738171 := bstep (se 1 (by rfl) ⟨553628, by rfl⟩ : syracuseStep 738171 = 1107257) B1107257
theorem B2016175 : Blo 734326 2016175 := bstep (se 1 (by rfl) ⟨1512131, by rfl⟩ : syracuseStep 2016175 = 3024263) B3024263
theorem B738223 : Blo 734326 738223 := bstep (se 1 (by rfl) ⟨553667, by rfl⟩ : syracuseStep 738223 = 1107335) B1107335
theorem B738247 : Blo 734326 738247 := bstep (se 1 (by rfl) ⟨553685, by rfl⟩ : syracuseStep 738247 = 1107371) B1107371
theorem B738267 : Blo 734326 738267 := bstep (se 1 (by rfl) ⟨553700, by rfl⟩ : syracuseStep 738267 = 1107401) B1107401
theorem B5981377 : Blo 734326 5981377 := bstep (se 2 (by rfl) ⟨2243016, by rfl⟩ : syracuseStep 5981377 = 4486033) B4486033
theorem B2802883 : Blo 734326 2802883 := bstep (se 1 (by rfl) ⟨2102162, by rfl⟩ : syracuseStep 2802883 = 4204325) B4204325
theorem B2803187 : Blo 734326 2803187 := bstep (se 1 (by rfl) ⟨2102390, by rfl⟩ : syracuseStep 2803187 = 4204781) B4204781
theorem B1656359 : Blo 734326 1656359 := bstep (se 1 (by rfl) ⟨1242269, by rfl⟩ : syracuseStep 1656359 = 2484539) B2484539
theorem B1328719 : Blo 734326 1328719 := bstep (se 1 (by rfl) ⟨996539, by rfl⟩ : syracuseStep 1328719 = 1993079) B1993079
theorem B1394273 : Blo 734326 1394273 := bstep (se 2 (by rfl) ⟨522852, by rfl⟩ : syracuseStep 1394273 = 1045705) B1045705
theorem B1394425 : Blo 734326 1394425 := bstep (se 2 (by rfl) ⟨522909, by rfl⟩ : syracuseStep 1394425 = 1045819) B1045819
theorem B8406827 : Blo 734326 8406827 := bstep (se 1 (by rfl) ⟨6305120, by rfl⟩ : syracuseStep 8406827 = 12610241) B12610241
theorem B1656683 : Blo 734326 1656683 := bstep (se 1 (by rfl) ⟨1242512, by rfl⟩ : syracuseStep 1656683 = 2485025) B2485025
theorem B5293943 : Blo 734326 5293943 := bstep (se 1 (by rfl) ⟨3970457, by rfl⟩ : syracuseStep 5293943 = 7940915) B7940915
theorem B1656737 : Blo 734326 1656737 := bstep (se 2 (by rfl) ⟨621276, by rfl⟩ : syracuseStep 1656737 = 1242553) B1242553
theorem B5588999 : Blo 734326 5588999 := bstep (se 1 (by rfl) ⟨4191749, by rfl⟩ : syracuseStep 5588999 = 8383499) B8383499
theorem B1657079 : Blo 734326 1657079 := bstep (se 1 (by rfl) ⟨1242809, by rfl⟩ : syracuseStep 1657079 = 2485619) B2485619
theorem B5589485 : Blo 734326 5589485 := bstep (se 3 (by rfl) ⟨1048028, by rfl⟩ : syracuseStep 5589485 = 2096057) B2096057
theorem B1985033 : Blo 734326 1985033 := bstep (se 2 (by rfl) ⟨744387, by rfl⟩ : syracuseStep 1985033 = 1488775) B1488775
theorem B3721787 : Blo 734326 3721787 := bstep (se 1 (by rfl) ⟨2791340, by rfl⟩ : syracuseStep 3721787 = 5582681) B5582681
theorem B1657673 : Blo 734326 1657673 := bstep (se 2 (by rfl) ⟨621627, by rfl⟩ : syracuseStep 1657673 = 1243255) B1243255
theorem B1330103 : Blo 734326 1330103 := bstep (se 1 (by rfl) ⟨997577, by rfl⟩ : syracuseStep 1330103 = 1995155) B1995155
theorem B1395731 : Blo 734326 1395731 := bstep (se 1 (by rfl) ⟨1046798, by rfl⟩ : syracuseStep 1395731 = 2093597) B2093597
theorem B1395883 : Blo 734326 1395883 := bstep (se 1 (by rfl) ⟨1046912, by rfl⟩ : syracuseStep 1395883 = 2093825) B2093825
theorem B3722435 : Blo 734326 3722435 := bstep (se 1 (by rfl) ⟨2791826, by rfl⟩ : syracuseStep 3722435 = 5583653) B5583653
theorem B1396111 : Blo 734326 1396111 := bstep (se 1 (by rfl) ⟨1047083, by rfl⟩ : syracuseStep 1396111 = 2094167) B2094167
theorem B1396187 : Blo 734326 1396187 := bstep (se 1 (by rfl) ⟨1047140, by rfl⟩ : syracuseStep 1396187 = 2094281) B2094281
theorem B13618775 : Blo 734326 13618775 := bstep (se 1 (by rfl) ⟨10214081, by rfl⟩ : syracuseStep 13618775 = 20428163) B20428163
theorem B1658465 : Blo 734326 1658465 := bstep (se 2 (by rfl) ⟨621924, by rfl⟩ : syracuseStep 1658465 = 1243849) B1243849
theorem B9424673 : Blo 734326 9424673 := bstep (se 2 (by rfl) ⟨3534252, by rfl⟩ : syracuseStep 9424673 = 7068505) B7068505
theorem B3592045 : Blo 734326 3592045 := bstep (se 3 (by rfl) ⟨673508, by rfl⟩ : syracuseStep 3592045 = 1347017) B1347017
theorem B26922887 : Blo 734326 26922887 := bstep (se 1 (by rfl) ⟨20192165, by rfl⟩ : syracuseStep 26922887 = 40384331) B40384331
theorem B1101743 : Blo 734326 1101743 := bstep (se 1 (by rfl) ⟨826307, by rfl⟩ : syracuseStep 1101743 = 1652615) B1652615
theorem B1658807 : Blo 734326 1658807 := bstep (se 1 (by rfl) ⟨1244105, by rfl⟩ : syracuseStep 1658807 = 2488211) B2488211
theorem B1495003 : Blo 734326 1495003 := bstep (se 1 (by rfl) ⟨1121252, by rfl⟩ : syracuseStep 1495003 = 2242505) B2242505
theorem B1101833 : Blo 734326 1101833 := bstep (se 2 (by rfl) ⟨413187, by rfl⟩ : syracuseStep 1101833 = 826375) B826375
theorem B1101863 : Blo 734326 1101863 := bstep (se 1 (by rfl) ⟨826397, by rfl⟩ : syracuseStep 1101863 = 1652795) B1652795
theorem B1101947 : Blo 734326 1101947 := bstep (se 1 (by rfl) ⟨826460, by rfl⟩ : syracuseStep 1101947 = 1652921) B1652921
theorem B1102073 : Blo 734326 1102073 := bstep (se 2 (by rfl) ⟨413277, by rfl⟩ : syracuseStep 1102073 = 826555) B826555
theorem B1102175 : Blo 734326 1102175 := bstep (se 1 (by rfl) ⟨826631, by rfl⟩ : syracuseStep 1102175 = 1653263) B1653263
theorem B1102187 : Blo 734326 1102187 := bstep (se 1 (by rfl) ⟨826640, by rfl⟩ : syracuseStep 1102187 = 1653281) B1653281
theorem B3985793 : Blo 734326 3985793 := bstep (se 2 (by rfl) ⟨1494672, by rfl⟩ : syracuseStep 3985793 = 2989345) B2989345
theorem B5591429 : Blo 734326 5591429 := bstep (se 4 (by rfl) ⟨524196, by rfl⟩ : syracuseStep 5591429 = 1048393) B1048393
theorem B1659401 : Blo 734326 1659401 := bstep (se 2 (by rfl) ⟨622275, by rfl⟩ : syracuseStep 1659401 = 1244551) B1244551
theorem B1102415 : Blo 734326 1102415 := bstep (se 1 (by rfl) ⟨826811, by rfl⟩ : syracuseStep 1102415 = 1653623) B1653623
theorem B1102535 : Blo 734326 1102535 := bstep (se 1 (by rfl) ⟨826901, by rfl⟩ : syracuseStep 1102535 = 1653803) B1653803
theorem B10769165 : Blo 734326 10769165 := bstep (se 3 (by rfl) ⟨2019218, by rfl⟩ : syracuseStep 10769165 = 4038437) B4038437
theorem B1659743 : Blo 734326 1659743 := bstep (se 1 (by rfl) ⟨1244807, by rfl⟩ : syracuseStep 1659743 = 2489615) B2489615
theorem B1102697 : Blo 734326 1102697 := bstep (se 2 (by rfl) ⟨413511, by rfl⟩ : syracuseStep 1102697 = 827023) B827023
theorem B5591915 : Blo 734326 5591915 := bstep (se 1 (by rfl) ⟨4193936, by rfl⟩ : syracuseStep 5591915 = 8387873) B8387873
theorem B2479031 : Blo 734326 2479031 := bstep (se 1 (by rfl) ⟨1859273, by rfl⟩ : syracuseStep 2479031 = 3718547) B3718547
theorem B1102775 : Blo 734326 1102775 := bstep (se 1 (by rfl) ⟨827081, by rfl⟩ : syracuseStep 1102775 = 1654163) B1654163
theorem B1102811 : Blo 734326 1102811 := bstep (se 1 (by rfl) ⟨827108, by rfl⟩ : syracuseStep 1102811 = 1654217) B1654217
theorem B1659923 : Blo 734326 1659923 := bstep (se 1 (by rfl) ⟨1244942, by rfl⟩ : syracuseStep 1659923 = 2489885) B2489885
theorem B2151481 : Blo 734326 2151481 := bstep (se 2 (by rfl) ⟨806805, by rfl⟩ : syracuseStep 2151481 = 1613611) B1613611
theorem B1660265 : Blo 734326 1660265 := bstep (se 2 (by rfl) ⟨622599, by rfl⟩ : syracuseStep 1660265 = 1245199) B1245199
theorem B1103279 : Blo 734326 1103279 := bstep (se 1 (by rfl) ⟨827459, by rfl⟩ : syracuseStep 1103279 = 1654919) B1654919
theorem B1496495 : Blo 734326 1496495 := bstep (se 1 (by rfl) ⟨1122371, by rfl⟩ : syracuseStep 1496495 = 2244743) B2244743
theorem B4707827 : Blo 734326 4707827 := bstep (se 1 (by rfl) ⟨3530870, by rfl⟩ : syracuseStep 4707827 = 7061741) B7061741
theorem B2479625 : Blo 734326 2479625 := bstep (se 2 (by rfl) ⟨929859, by rfl⟩ : syracuseStep 2479625 = 1859719) B1859719
theorem B1103369 : Blo 734326 1103369 := bstep (se 2 (by rfl) ⟨413763, by rfl⟩ : syracuseStep 1103369 = 827527) B827527
theorem B1103399 : Blo 734326 1103399 := bstep (se 1 (by rfl) ⟨827549, by rfl⟩ : syracuseStep 1103399 = 1655099) B1655099
theorem B1103483 : Blo 734326 1103483 := bstep (se 1 (by rfl) ⟨827612, by rfl⟩ : syracuseStep 1103483 = 1655225) B1655225
theorem B1103609 : Blo 734326 1103609 := bstep (se 2 (by rfl) ⟨413853, by rfl⟩ : syracuseStep 1103609 = 827707) B827707
theorem B12736291 : Blo 734326 12736291 := bstep (se 1 (by rfl) ⟨9552218, by rfl⟩ : syracuseStep 12736291 = 19104437) B19104437
theorem B1103711 : Blo 734326 1103711 := bstep (se 1 (by rfl) ⟨827783, by rfl⟩ : syracuseStep 1103711 = 1655567) B1655567
theorem B1103723 : Blo 734326 1103723 := bstep (se 1 (by rfl) ⟨827792, by rfl⟩ : syracuseStep 1103723 = 1655585) B1655585
theorem B1660859 : Blo 734326 1660859 := bstep (se 1 (by rfl) ⟨1245644, by rfl⟩ : syracuseStep 1660859 = 2491289) B2491289
theorem B1660985 : Blo 734326 1660985 := bstep (se 2 (by rfl) ⟨622869, by rfl⟩ : syracuseStep 1660985 = 1245739) B1245739
theorem B1103951 : Blo 734326 1103951 := bstep (se 1 (by rfl) ⟨827963, by rfl⟩ : syracuseStep 1103951 = 1655927) B1655927
theorem B11196503 : Blo 734326 11196503 := bstep (se 1 (by rfl) ⟨8397377, by rfl⟩ : syracuseStep 11196503 = 16794755) B16794755
theorem B3528793 : Blo 734326 3528793 := bstep (se 2 (by rfl) ⟨1323297, by rfl⟩ : syracuseStep 3528793 = 2646595) B2646595
theorem B1104071 : Blo 734326 1104071 := bstep (se 1 (by rfl) ⟨828053, by rfl⟩ : syracuseStep 1104071 = 1656107) B1656107
theorem B2480489 : Blo 734326 2480489 := bstep (se 2 (by rfl) ⟨930183, by rfl⟩ : syracuseStep 2480489 = 1860367) B1860367
theorem B1104233 : Blo 734326 1104233 := bstep (se 2 (by rfl) ⟨414087, by rfl⟩ : syracuseStep 1104233 = 828175) B828175
theorem B1104311 : Blo 734326 1104311 := bstep (se 1 (by rfl) ⟨828233, by rfl⟩ : syracuseStep 1104311 = 1656467) B1656467
theorem B1104347 : Blo 734326 1104347 := bstep (se 1 (by rfl) ⟨828260, by rfl⟩ : syracuseStep 1104347 = 1656521) B1656521
theorem B49109579 : Blo 734326 49109579 := bstep (se 1 (by rfl) ⟨36832184, by rfl⟩ : syracuseStep 49109579 = 73664369) B73664369
theorem B8379125 : Blo 734326 8379125 := bstep (se 5 (by rfl) ⟨392771, by rfl⟩ : syracuseStep 8379125 = 785543) B785543
theorem B5593859 : Blo 734326 5593859 := bstep (se 1 (by rfl) ⟨4195394, by rfl⟩ : syracuseStep 5593859 = 8390789) B8390789
theorem B1104815 : Blo 734326 1104815 := bstep (se 1 (by rfl) ⟨828611, by rfl⟩ : syracuseStep 1104815 = 1657223) B1657223
theorem B2481083 : Blo 734326 2481083 := bstep (se 1 (by rfl) ⟨1860812, by rfl⟩ : syracuseStep 2481083 = 3721625) B3721625
theorem B1399771 : Blo 734326 1399771 := bstep (se 1 (by rfl) ⟨1049828, by rfl⟩ : syracuseStep 1399771 = 2099657) B2099657
theorem B1104905 : Blo 734326 1104905 := bstep (se 2 (by rfl) ⟨414339, by rfl⟩ : syracuseStep 1104905 = 828679) B828679
theorem B1399817 : Blo 734326 1399817 := bstep (se 2 (by rfl) ⟨524931, by rfl⟩ : syracuseStep 1399817 = 1049863) B1049863
theorem B1104935 : Blo 734326 1104935 := bstep (se 1 (by rfl) ⟨828701, by rfl⟩ : syracuseStep 1104935 = 1657403) B1657403
theorem B1105019 : Blo 734326 1105019 := bstep (se 1 (by rfl) ⟨828764, by rfl⟩ : syracuseStep 1105019 = 1657529) B1657529
theorem B744647 : Blo 734326 744647 := bstep (se 1 (by rfl) ⟨558485, by rfl⟩ : syracuseStep 744647 = 1116971) B1116971
theorem B1105145 : Blo 734326 1105145 := bstep (se 2 (by rfl) ⟨414429, by rfl⟩ : syracuseStep 1105145 = 828859) B828859
theorem B1105247 : Blo 734326 1105247 := bstep (se 1 (by rfl) ⟨828935, by rfl⟩ : syracuseStep 1105247 = 1657871) B1657871
theorem B1400159 : Blo 734326 1400159 := bstep (se 1 (by rfl) ⟨1050119, by rfl⟩ : syracuseStep 1400159 = 2100239) B2100239
theorem B1105259 : Blo 734326 1105259 := bstep (se 1 (by rfl) ⟨828944, by rfl⟩ : syracuseStep 1105259 = 1657889) B1657889
theorem B1105487 : Blo 734326 1105487 := bstep (se 1 (by rfl) ⟨829115, by rfl⟩ : syracuseStep 1105487 = 1658231) B1658231
theorem B3726971 : Blo 734326 3726971 := bstep (se 1 (by rfl) ⟨2795228, by rfl⟩ : syracuseStep 3726971 = 5590457) B5590457
theorem B1105607 : Blo 734326 1105607 := bstep (se 1 (by rfl) ⟨829205, by rfl⟩ : syracuseStep 1105607 = 1658411) B1658411
theorem B1105769 : Blo 734326 1105769 := bstep (se 2 (by rfl) ⟨414663, by rfl⟩ : syracuseStep 1105769 = 829327) B829327
theorem B1105847 : Blo 734326 1105847 := bstep (se 1 (by rfl) ⟨829385, by rfl⟩ : syracuseStep 1105847 = 1658771) B1658771
theorem B1892279 : Blo 734326 1892279 := bstep (se 1 (by rfl) ⟨1419209, by rfl⟩ : syracuseStep 1892279 = 2838419) B2838419
theorem B1105883 : Blo 734326 1105883 := bstep (se 1 (by rfl) ⟨829412, by rfl⟩ : syracuseStep 1105883 = 1658825) B1658825
theorem B6283493 : Blo 734326 6283493 := bstep (se 4 (by rfl) ⟨589077, by rfl⟩ : syracuseStep 6283493 = 1178155) B1178155
theorem B1859831 : Blo 734326 1859831 := bstep (se 1 (by rfl) ⟨1394873, by rfl⟩ : syracuseStep 1859831 = 2789747) B2789747
theorem B1106351 : Blo 734326 1106351 := bstep (se 1 (by rfl) ⟨829763, by rfl⟩ : syracuseStep 1106351 = 1659527) B1659527
theorem B1401275 : Blo 734326 1401275 := bstep (se 1 (by rfl) ⟨1050956, by rfl⟩ : syracuseStep 1401275 = 2101913) B2101913
theorem B1106441 : Blo 734326 1106441 := bstep (se 2 (by rfl) ⟨414915, by rfl⟩ : syracuseStep 1106441 = 829831) B829831
theorem B1106471 : Blo 734326 1106471 := bstep (se 1 (by rfl) ⟨829853, by rfl⟩ : syracuseStep 1106471 = 1659707) B1659707
theorem B2482811 : Blo 734326 2482811 := bstep (se 1 (by rfl) ⟨1862108, by rfl⟩ : syracuseStep 2482811 = 3724217) B3724217
theorem B1106555 : Blo 734326 1106555 := bstep (se 1 (by rfl) ⟨829916, by rfl⟩ : syracuseStep 1106555 = 1659833) B1659833
theorem B1106681 : Blo 734326 1106681 := bstep (se 2 (by rfl) ⟨415005, by rfl⟩ : syracuseStep 1106681 = 830011) B830011
theorem B2482973 : Blo 734326 2482973 := bstep (se 3 (by rfl) ⟨465557, by rfl⟩ : syracuseStep 2482973 = 931115) B931115
theorem B2646827 : Blo 734326 2646827 := bstep (se 1 (by rfl) ⟨1985120, by rfl⟩ : syracuseStep 2646827 = 3970241) B3970241
theorem B1106783 : Blo 734326 1106783 := bstep (se 1 (by rfl) ⟨830087, by rfl⟩ : syracuseStep 1106783 = 1660175) B1660175
theorem B1106795 : Blo 734326 1106795 := bstep (se 1 (by rfl) ⟨830096, by rfl⟩ : syracuseStep 1106795 = 1660193) B1660193
theorem B1107023 : Blo 734326 1107023 := bstep (se 1 (by rfl) ⟨830267, by rfl⟩ : syracuseStep 1107023 = 1660535) B1660535
theorem B11953271 : Blo 734326 11953271 := bstep (se 1 (by rfl) ⟨8964953, by rfl⟩ : syracuseStep 11953271 = 17929907) B17929907
theorem B1107143 : Blo 734326 1107143 := bstep (se 1 (by rfl) ⟨830357, by rfl⟩ : syracuseStep 1107143 = 1660715) B1660715
theorem B1107305 : Blo 734326 1107305 := bstep (se 2 (by rfl) ⟨415239, by rfl⟩ : syracuseStep 1107305 = 830479) B830479
theorem B1107383 : Blo 734326 1107383 := bstep (se 1 (by rfl) ⟨830537, by rfl⟩ : syracuseStep 1107383 = 1661075) B1661075
theorem B2483675 : Blo 734326 2483675 := bstep (se 1 (by rfl) ⟨1862756, by rfl⟩ : syracuseStep 2483675 = 3725513) B3725513
theorem B1107419 : Blo 734326 1107419 := bstep (se 1 (by rfl) ⟨830564, by rfl⟩ : syracuseStep 1107419 = 1661129) B1661129
theorem B1861319 : Blo 734326 1861319 := bstep (se 1 (by rfl) ⟨1395989, by rfl⟩ : syracuseStep 1861319 = 2791979) B2791979
theorem B2353171 : Blo 734326 2353171 := bstep (se 1 (by rfl) ⟨1764878, by rfl⟩ : syracuseStep 2353171 = 3529757) B3529757
theorem B1534009 : Blo 734326 1534009 := bstep (se 2 (by rfl) ⟨575253, by rfl⟩ : syracuseStep 1534009 = 1150507) B1150507
theorem B5597261 : Blo 734326 5597261 := bstep (se 3 (by rfl) ⟨1049486, by rfl⟩ : syracuseStep 5597261 = 2098973) B2098973
theorem B10610777 : Blo 734326 10610777 := bstep (se 2 (by rfl) ⟨3979041, by rfl⟩ : syracuseStep 10610777 = 7958083) B7958083
theorem B2484377 : Blo 734326 2484377 := bstep (se 2 (by rfl) ⟨931641, by rfl⟩ : syracuseStep 2484377 = 1863283) B1863283
theorem B1239239 : Blo 734326 1239239 := bstep (se 1 (by rfl) ⟨929429, by rfl⟩ : syracuseStep 1239239 = 1858859) B1858859
theorem B3729725 : Blo 734326 3729725 := bstep (se 3 (by rfl) ⟨699323, by rfl⟩ : syracuseStep 3729725 = 1398647) B1398647
theorem B1239401 : Blo 734326 1239401 := bstep (se 2 (by rfl) ⟨464775, by rfl⟩ : syracuseStep 1239401 = 929551) B929551
theorem B2124427 : Blo 734326 2124427 := bstep (se 1 (by rfl) ⟨1593320, by rfl⟩ : syracuseStep 2124427 = 3186641) B3186641
theorem B1239799 : Blo 734326 1239799 := bstep (se 1 (by rfl) ⟨929849, by rfl⟩ : syracuseStep 1239799 = 1859699) B1859699
theorem B1862473 : Blo 734326 1862473 := bstep (se 2 (by rfl) ⟨698427, by rfl⟩ : syracuseStep 1862473 = 1396855) B1396855
theorem B1239995 : Blo 734326 1239995 := bstep (se 1 (by rfl) ⟨929996, by rfl⟩ : syracuseStep 1239995 = 1859993) B1859993
theorem B1240103 : Blo 734326 1240103 := bstep (se 1 (by rfl) ⟨930077, by rfl⟩ : syracuseStep 1240103 = 1860155) B1860155
theorem B6286531 : Blo 734326 6286531 := bstep (se 1 (by rfl) ⟨4714898, by rfl⟩ : syracuseStep 6286531 = 9429797) B9429797
theorem B2485565 : Blo 734326 2485565 := bstep (se 3 (by rfl) ⟨466043, by rfl⟩ : syracuseStep 2485565 = 932087) B932087
theorem B1240393 : Blo 734326 1240393 := bstep (se 2 (by rfl) ⟨465147, by rfl⟩ : syracuseStep 1240393 = 930295) B930295
theorem B1240427 : Blo 734326 1240427 := bstep (se 1 (by rfl) ⟨930320, by rfl⟩ : syracuseStep 1240427 = 1860641) B1860641
theorem B1437193 : Blo 734326 1437193 := bstep (se 2 (by rfl) ⟨538947, by rfl⟩ : syracuseStep 1437193 = 1077895) B1077895
theorem B40300253 : Blo 734326 40300253 := bstep (se 3 (by rfl) ⟨7556297, by rfl⟩ : syracuseStep 40300253 = 15112595) B15112595
theorem B1240825 : Blo 734326 1240825 := bstep (se 2 (by rfl) ⟨465309, by rfl⟩ : syracuseStep 1240825 = 930619) B930619
theorem B2355119 : Blo 734326 2355119 := bstep (se 1 (by rfl) ⟨1766339, by rfl⟩ : syracuseStep 2355119 = 3532679) B3532679
theorem B1863607 : Blo 734326 1863607 := bstep (se 1 (by rfl) ⟨1397705, by rfl⟩ : syracuseStep 1863607 = 2795411) B2795411
theorem B4550593 : Blo 734326 4550593 := bstep (se 2 (by rfl) ⟨1706472, by rfl⟩ : syracuseStep 4550593 = 3412945) B3412945
theorem B1241095 : Blo 734326 1241095 := bstep (se 1 (by rfl) ⟨930821, by rfl⟩ : syracuseStep 1241095 = 1861643) B1861643
theorem B2486429 : Blo 734326 2486429 := bstep (se 3 (by rfl) ⟨466205, by rfl⟩ : syracuseStep 2486429 = 932411) B932411
theorem B3141899 : Blo 734326 3141899 := bstep (se 1 (by rfl) ⟨2356424, by rfl⟩ : syracuseStep 3141899 = 4712849) B4712849
theorem B1241527 : Blo 734326 1241527 := bstep (se 1 (by rfl) ⟨931145, by rfl⟩ : syracuseStep 1241527 = 1862291) B1862291
theorem B5599691 : Blo 734326 5599691 := bstep (se 1 (by rfl) ⟨4199768, by rfl⟩ : syracuseStep 5599691 = 8399537) B8399537
theorem B3731993 : Blo 734326 3731993 := bstep (se 2 (by rfl) ⟨1399497, by rfl⟩ : syracuseStep 3731993 = 2798995) B2798995
theorem B2355809 : Blo 734326 2355809 := bstep (se 2 (by rfl) ⟨883428, by rfl⟩ : syracuseStep 2355809 = 1766857) B1766857
theorem B2650747 : Blo 734326 2650747 := bstep (se 1 (by rfl) ⟨1988060, by rfl⟩ : syracuseStep 2650747 = 3976121) B3976121
theorem B1241723 : Blo 734326 1241723 := bstep (se 1 (by rfl) ⟨931292, by rfl⟩ : syracuseStep 1241723 = 1862585) B1862585
theorem B2486969 : Blo 734326 2486969 := bstep (se 2 (by rfl) ⟨932613, by rfl⟩ : syracuseStep 2486969 = 1865227) B1865227
theorem B2093779 : Blo 734326 2093779 := bstep (se 1 (by rfl) ⟨1570334, by rfl⟩ : syracuseStep 2093779 = 3140669) B3140669
theorem B2094007 : Blo 734326 2094007 := bstep (se 1 (by rfl) ⟨1570505, by rfl⟩ : syracuseStep 2094007 = 3141011) B3141011
theorem B3142583 : Blo 734326 3142583 := bstep (se 1 (by rfl) ⟨2356937, by rfl⟩ : syracuseStep 3142583 = 4713875) B4713875
theorem B1242121 : Blo 734326 1242121 := bstep (se 2 (by rfl) ⟨465795, by rfl⟩ : syracuseStep 1242121 = 931591) B931591
theorem B10089521 : Blo 734326 10089521 := bstep (se 2 (by rfl) ⟨3783570, by rfl⟩ : syracuseStep 10089521 = 7567141) B7567141
theorem B4191385 : Blo 734326 4191385 := bstep (se 2 (by rfl) ⟨1571769, by rfl⟩ : syracuseStep 4191385 = 3143539) B3143539
theorem B1242283 : Blo 734326 1242283 := bstep (se 1 (by rfl) ⟨931712, by rfl⟩ : syracuseStep 1242283 = 1863425) B1863425
theorem B2487563 : Blo 734326 2487563 := bstep (se 1 (by rfl) ⟨1865672, by rfl⟩ : syracuseStep 2487563 = 3731345) B3731345
theorem B1865065 : Blo 734326 1865065 := bstep (se 2 (by rfl) ⟨699399, by rfl⟩ : syracuseStep 1865065 = 1398799) B1398799
theorem B1242587 : Blo 734326 1242587 := bstep (se 1 (by rfl) ⟨931940, by rfl⟩ : syracuseStep 1242587 = 1863881) B1863881
theorem B2487833 : Blo 734326 2487833 := bstep (se 2 (by rfl) ⟨932937, by rfl⟩ : syracuseStep 2487833 = 1865875) B1865875
theorem B1865339 : Blo 734326 1865339 := bstep (se 1 (by rfl) ⟨1399004, by rfl⟩ : syracuseStep 1865339 = 2798009) B2798009
theorem B1242823 : Blo 734326 1242823 := bstep (se 1 (by rfl) ⟨932117, by rfl⟩ : syracuseStep 1242823 = 1864235) B1864235
theorem B1242985 : Blo 734326 1242985 := bstep (se 2 (by rfl) ⟨466119, by rfl⟩ : syracuseStep 1242985 = 932239) B932239
theorem B5044103 : Blo 734326 5044103 := bstep (se 1 (by rfl) ⟨3783077, by rfl⟩ : syracuseStep 5044103 = 7566155) B7566155
theorem B2979919 : Blo 734326 2979919 := bstep (se 1 (by rfl) ⟨2234939, by rfl⟩ : syracuseStep 2979919 = 4469879) B4469879
theorem B2095465 : Blo 734326 2095465 := bstep (se 2 (by rfl) ⟨785799, by rfl⟩ : syracuseStep 2095465 = 1571599) B1571599
theorem B1243579 : Blo 734326 1243579 := bstep (se 1 (by rfl) ⟨932684, by rfl⟩ : syracuseStep 1243579 = 1865369) B1865369
theorem B2095625 : Blo 734326 2095625 := bstep (se 2 (by rfl) ⟨785859, by rfl⟩ : syracuseStep 2095625 = 1571719) B1571719
theorem B1243687 : Blo 734326 1243687 := bstep (se 1 (by rfl) ⟨932765, by rfl⟩ : syracuseStep 1243687 = 1865531) B1865531
theorem B1047163 : Blo 734326 1047163 := bstep (se 1 (by rfl) ⟨785372, by rfl⟩ : syracuseStep 1047163 = 1570745) B1570745
theorem B2095739 : Blo 734326 2095739 := bstep (se 1 (by rfl) ⟨1571804, by rfl⟩ : syracuseStep 2095739 = 3143609) B3143609
theorem B2488967 : Blo 734326 2488967 := bstep (se 1 (by rfl) ⟨1866725, by rfl⟩ : syracuseStep 2488967 = 3733451) B3733451
theorem B2489021 : Blo 734326 2489021 := bstep (se 3 (by rfl) ⟨466691, by rfl⟩ : syracuseStep 2489021 = 933383) B933383
theorem B2095865 : Blo 734326 2095865 := bstep (se 2 (by rfl) ⟨785949, by rfl⟩ : syracuseStep 2095865 = 1571899) B1571899
theorem B5602121 : Blo 734326 5602121 := bstep (se 2 (by rfl) ⟨2100795, by rfl⟩ : syracuseStep 5602121 = 4201591) B4201591
theorem B2489183 : Blo 734326 2489183 := bstep (se 1 (by rfl) ⟨1866887, by rfl⟩ : syracuseStep 2489183 = 3733775) B3733775
theorem B1244011 : Blo 734326 1244011 := bstep (se 1 (by rfl) ⟨933008, by rfl⟩ : syracuseStep 1244011 = 1866017) B1866017
theorem B4717541 : Blo 734326 4717541 := bstep (se 4 (by rfl) ⟨442269, by rfl⟩ : syracuseStep 4717541 = 884539) B884539
theorem B2489345 : Blo 734326 2489345 := bstep (se 2 (by rfl) ⟨933504, by rfl⟩ : syracuseStep 2489345 = 1867009) B1867009
theorem B15957071 : Blo 734326 15957071 := bstep (se 1 (by rfl) ⟨11967803, by rfl⟩ : syracuseStep 15957071 = 23935607) B23935607
theorem B2391383 : Blo 734326 2391383 := bstep (se 1 (by rfl) ⟨1793537, by rfl⟩ : syracuseStep 2391383 = 3587075) B3587075
theorem B3734909 : Blo 734326 3734909 := bstep (se 3 (by rfl) ⟨700295, by rfl⟩ : syracuseStep 3734909 = 1400591) B1400591
theorem B2096513 : Blo 734326 2096513 := bstep (se 2 (by rfl) ⟨786192, by rfl⟩ : syracuseStep 2096513 = 1572385) B1572385
theorem B1867151 : Blo 734326 1867151 := bstep (se 1 (by rfl) ⟨1400363, by rfl⟩ : syracuseStep 1867151 = 2800727) B2800727
theorem B1047983 : Blo 734326 1047983 := bstep (se 1 (by rfl) ⟨785987, by rfl⟩ : syracuseStep 1047983 = 1571975) B1571975
theorem B1179335 : Blo 734326 1179335 := bstep (se 1 (by rfl) ⟨884501, by rfl⟩ : syracuseStep 1179335 = 1769003) B1769003
theorem B1867475 : Blo 734326 1867475 := bstep (se 1 (by rfl) ⟨1400606, by rfl⟩ : syracuseStep 1867475 = 2801213) B2801213
theorem B8060705 : Blo 734326 8060705 := bstep (se 2 (by rfl) ⟨3022764, by rfl⟩ : syracuseStep 8060705 = 6045529) B6045529
theorem B2391851 : Blo 734326 2391851 := bstep (se 1 (by rfl) ⟨1793888, by rfl⟩ : syracuseStep 2391851 = 3587777) B3587777
theorem B2490155 : Blo 734326 2490155 := bstep (se 1 (by rfl) ⟨1867616, by rfl⟩ : syracuseStep 2490155 = 3735233) B3735233
theorem B1245071 : Blo 734326 1245071 := bstep (se 1 (by rfl) ⟨933803, by rfl⟩ : syracuseStep 1245071 = 1867607) B1867607
theorem B2097083 : Blo 734326 2097083 := bstep (se 1 (by rfl) ⟨1572812, by rfl⟩ : syracuseStep 2097083 = 3145625) B3145625
theorem B15728717 : Blo 734326 15728717 := bstep (se 3 (by rfl) ⟨2949134, by rfl⟩ : syracuseStep 15728717 = 5898269) B5898269
theorem B1245449 : Blo 734326 1245449 := bstep (se 2 (by rfl) ⟨467043, by rfl⟩ : syracuseStep 1245449 = 934087) B934087
theorem B3735881 : Blo 734326 3735881 := bstep (se 2 (by rfl) ⟨1400955, by rfl⟩ : syracuseStep 3735881 = 2801911) B2801911
theorem B1868123 : Blo 734326 1868123 := bstep (se 1 (by rfl) ⟨1401092, by rfl⟩ : syracuseStep 1868123 = 2802185) B2802185
theorem B2097515 : Blo 734326 2097515 := bstep (se 1 (by rfl) ⟨1573136, by rfl⟩ : syracuseStep 2097515 = 3146273) B3146273
theorem B1868143 : Blo 734326 1868143 := bstep (se 1 (by rfl) ⟨1401107, by rfl⟩ : syracuseStep 1868143 = 2802215) B2802215
theorem B15958457 : Blo 734326 15958457 := bstep (se 2 (by rfl) ⟨5984421, by rfl⟩ : syracuseStep 15958457 = 11968843) B11968843
theorem B4653883 : Blo 734326 4653883 := bstep (se 1 (by rfl) ⟨3490412, by rfl⟩ : syracuseStep 4653883 = 6980825) B6980825
theorem B1704847 : Blo 734326 1704847 := bstep (se 1 (by rfl) ⟨1278635, by rfl⟩ : syracuseStep 1704847 = 2557271) B2557271
theorem B1868791 : Blo 734326 1868791 := bstep (se 1 (by rfl) ⟨1401593, by rfl⟩ : syracuseStep 1868791 = 2803187) B2803187
theorem B5604551 : Blo 734326 5604551 := bstep (se 1 (by rfl) ⟨4203413, by rfl⟩ : syracuseStep 5604551 = 8406827) B8406827
theorem B2688233 : Blo 734326 2688233 := bstep (se 2 (by rfl) ⟨1008087, by rfl⟩ : syracuseStep 2688233 = 2016175) B2016175
theorem B6292889 : Blo 734326 6292889 := bstep (se 2 (by rfl) ⟨2359833, by rfl⟩ : syracuseStep 6292889 = 4719667) B4719667
theorem B4720025 : Blo 734326 4720025 := bstep (se 2 (by rfl) ⟨1770009, by rfl⟩ : syracuseStep 4720025 = 3540019) B3540019
theorem B3737177 : Blo 734326 3737177 := bstep (se 2 (by rfl) ⟨1401441, by rfl⟩ : syracuseStep 3737177 = 2802883) B2802883
theorem B1050347 : Blo 734326 1050347 := bstep (se 1 (by rfl) ⟨787760, by rfl⟩ : syracuseStep 1050347 = 1575521) B1575521
theorem B886735 : Blo 734326 886735 := bstep (se 1 (by rfl) ⟨665051, by rfl⟩ : syracuseStep 886735 = 1330103) B1330103
theorem B1771625 : Blo 734326 1771625 := bstep (se 2 (by rfl) ⟨664359, by rfl⟩ : syracuseStep 1771625 = 1328719) B1328719
theorem B7670051 : Blo 734326 7670051 := bstep (se 1 (by rfl) ⟨5752538, by rfl⟩ : syracuseStep 7670051 = 11505077) B11505077
theorem B9079183 : Blo 734326 9079183 := bstep (se 1 (by rfl) ⟨6809387, by rfl⟩ : syracuseStep 9079183 = 13618775) B13618775
theorem B2657195 : Blo 734326 2657195 := bstep (se 1 (by rfl) ⟨1992896, by rfl⟩ : syracuseStep 2657195 = 3985793) B3985793
theorem B4197491 : Blo 734326 4197491 := bstep (se 1 (by rfl) ⟨3148118, by rfl⟩ : syracuseStep 4197491 = 6296237) B6296237
theorem B7179443 : Blo 734326 7179443 := bstep (se 1 (by rfl) ⟨5384582, by rfl⟩ : syracuseStep 7179443 = 10769165) B10769165
theorem B9440459 : Blo 734326 9440459 := bstep (se 1 (by rfl) ⟨7080344, by rfl⟩ : syracuseStep 9440459 = 14160689) B14160689
theorem B1772923 : Blo 734326 1772923 := bstep (se 1 (by rfl) ⟨1329692, by rfl⟩ : syracuseStep 1772923 = 2659385) B2659385
theorem B1576759 : Blo 734326 1576759 := bstep (se 1 (by rfl) ⟨1182569, by rfl⟩ : syracuseStep 1576759 = 2365139) B2365139
theorem B3149675 : Blo 734326 3149675 := bstep (se 1 (by rfl) ⟨2362256, by rfl⟩ : syracuseStep 3149675 = 4724513) B4724513
theorem B3149725 : Blo 734326 3149725 := bstep (se 3 (by rfl) ⟨590573, by rfl⟩ : syracuseStep 3149725 = 1181147) B1181147
theorem B2363293 : Blo 734326 2363293 := bstep (se 3 (by rfl) ⟨443117, by rfl⟩ : syracuseStep 2363293 = 886235) B886235
theorem B6295553 : Blo 734326 6295553 := bstep (se 2 (by rfl) ⟨2360832, by rfl⟩ : syracuseStep 6295553 = 4721665) B4721665
theorem B2363755 : Blo 734326 2363755 := bstep (se 1 (by rfl) ⟨1772816, by rfl⟩ : syracuseStep 2363755 = 3545633) B3545633
theorem B32739719 : Blo 734326 32739719 := bstep (se 1 (by rfl) ⟨24554789, by rfl⟩ : syracuseStep 32739719 = 49109579) B49109579
theorem B3544307 : Blo 734326 3544307 := bstep (se 1 (by rfl) ⟨2658230, by rfl⟩ : syracuseStep 3544307 = 5316461) B5316461
theorem B6067457 : Blo 734326 6067457 := bstep (se 2 (by rfl) ⟨2275296, by rfl⟩ : syracuseStep 6067457 = 4550593) B4550593
theorem B1119611 : Blo 734326 1119611 := bstep (se 1 (by rfl) ⟨839708, by rfl⟩ : syracuseStep 1119611 = 1679417) B1679417
theorem B26941571 : Blo 734326 26941571 := bstep (se 1 (by rfl) ⟨20206178, by rfl⟩ : syracuseStep 26941571 = 40412357) B40412357
theorem B2791705 : Blo 734326 2791705 := bstep (se 2 (by rfl) ⟨1046889, by rfl⟩ : syracuseStep 2791705 = 2093779) B2093779
theorem B2792009 : Blo 734326 2792009 := bstep (se 2 (by rfl) ⟨1047003, by rfl⟩ : syracuseStep 2792009 = 2094007) B2094007
theorem B826159 : Blo 734326 826159 := bstep (se 1 (by rfl) ⟨619619, by rfl⟩ : syracuseStep 826159 = 1239239) B1239239
theorem B826267 : Blo 734326 826267 := bstep (se 1 (by rfl) ⟨619700, by rfl⟩ : syracuseStep 826267 = 1239401) B1239401
theorem B826663 : Blo 734326 826663 := bstep (se 1 (by rfl) ⟨619997, by rfl⟩ : syracuseStep 826663 = 1239995) B1239995
theorem B826735 : Blo 734326 826735 := bstep (se 1 (by rfl) ⟨620051, by rfl⟩ : syracuseStep 826735 = 1240103) B1240103
theorem B4201865 : Blo 734326 4201865 := bstep (se 2 (by rfl) ⟨1575699, by rfl⟩ : syracuseStep 4201865 = 3151399) B3151399
theorem B826951 : Blo 734326 826951 := bstep (se 1 (by rfl) ⟨620213, by rfl⟩ : syracuseStep 826951 = 1240427) B1240427
theorem B16981721 : Blo 734326 16981721 := bstep (se 2 (by rfl) ⟨6368145, by rfl⟩ : syracuseStep 16981721 = 12736291) B12736291
theorem B3973225 : Blo 734326 3973225 := bstep (se 2 (by rfl) ⟨1489959, by rfl⟩ : syracuseStep 3973225 = 2979919) B2979919
theorem B827815 : Blo 734326 827815 := bstep (se 1 (by rfl) ⟨620861, by rfl⟩ : syracuseStep 827815 = 1241723) B1241723
theorem B2793953 : Blo 734326 2793953 := bstep (se 2 (by rfl) ⟨1047732, by rfl⟩ : syracuseStep 2793953 = 2095465) B2095465
theorem B6726347 : Blo 734326 6726347 := bstep (se 1 (by rfl) ⟨5044760, by rfl⟩ : syracuseStep 6726347 = 10089521) B10089521
theorem B6300611 : Blo 734326 6300611 := bstep (se 1 (by rfl) ⟨4725458, by rfl⟩ : syracuseStep 6300611 = 9450917) B9450917
theorem B828391 : Blo 734326 828391 := bstep (se 1 (by rfl) ⟨621293, by rfl⟩ : syracuseStep 828391 = 1242587) B1242587
theorem B2794621 : Blo 734326 2794621 := bstep (se 3 (by rfl) ⟨523991, by rfl⟩ : syracuseStep 2794621 = 1047983) B1047983
theorem B1910735 : Blo 734326 1910735 := bstep (se 1 (by rfl) ⟨1433051, by rfl⟩ : syracuseStep 1910735 = 2866103) B2866103
theorem B5581223 : Blo 734326 5581223 := bstep (se 1 (by rfl) ⟨4185917, by rfl⟩ : syracuseStep 5581223 = 8371835) B8371835
theorem B830047 : Blo 734326 830047 := bstep (se 1 (by rfl) ⟨622535, by rfl⟩ : syracuseStep 830047 = 1245071) B1245071
theorem B15281167 : Blo 734326 15281167 := bstep (se 1 (by rfl) ⟨11460875, by rfl⟩ : syracuseStep 15281167 = 22921751) B22921751
theorem B14167385 : Blo 734326 14167385 := bstep (se 2 (by rfl) ⟨5312769, by rfl⟩ : syracuseStep 14167385 = 10625539) B10625539
theorem B3977419 : Blo 734326 3977419 := bstep (se 1 (by rfl) ⟨2983064, by rfl⟩ : syracuseStep 3977419 = 5966129) B5966129
theorem B7975169 : Blo 734326 7975169 := bstep (se 2 (by rfl) ⟨2990688, by rfl⟩ : syracuseStep 7975169 = 5981377) B5981377
theorem B930791 : Blo 734326 930791 := bstep (se 1 (by rfl) ⟨698093, by rfl⟩ : syracuseStep 930791 = 1396187) B1396187
theorem B3781847 : Blo 734326 3781847 := bstep (se 1 (by rfl) ⟨2836385, by rfl⟩ : syracuseStep 3781847 = 5672771) B5672771
theorem B734495 : Blo 734326 734495 := bstep (se 1 (by rfl) ⟨550871, by rfl⟩ : syracuseStep 734495 = 1101743) B1101743
theorem B734555 : Blo 734326 734555 := bstep (se 1 (by rfl) ⟨550916, by rfl⟩ : syracuseStep 734555 = 1101833) B1101833
theorem B734575 : Blo 734326 734575 := bstep (se 1 (by rfl) ⟨550931, by rfl⟩ : syracuseStep 734575 = 1101863) B1101863
theorem B2045345 : Blo 734326 2045345 := bstep (se 2 (by rfl) ⟨767004, by rfl⟩ : syracuseStep 2045345 = 1534009) B1534009
theorem B734631 : Blo 734326 734631 := bstep (se 1 (by rfl) ⟨550973, by rfl⟩ : syracuseStep 734631 = 1101947) B1101947
theorem B734715 : Blo 734326 734715 := bstep (se 1 (by rfl) ⟨551036, by rfl⟩ : syracuseStep 734715 = 1102073) B1102073
theorem B734783 : Blo 734326 734783 := bstep (se 1 (by rfl) ⟨551087, by rfl⟩ : syracuseStep 734783 = 1102175) B1102175
theorem B734791 : Blo 734326 734791 := bstep (se 1 (by rfl) ⟨551093, by rfl⟩ : syracuseStep 734791 = 1102187) B1102187
theorem B734943 : Blo 734326 734943 := bstep (se 1 (by rfl) ⟨551207, by rfl⟩ : syracuseStep 734943 = 1102415) B1102415
theorem B735023 : Blo 734326 735023 := bstep (se 1 (by rfl) ⟨551267, by rfl⟩ : syracuseStep 735023 = 1102535) B1102535
theorem B735131 : Blo 734326 735131 := bstep (se 1 (by rfl) ⟨551348, by rfl⟩ : syracuseStep 735131 = 1102697) B1102697
theorem B1652687 : Blo 734326 1652687 := bstep (se 1 (by rfl) ⟨1239515, by rfl⟩ : syracuseStep 1652687 = 2479031) B2479031
theorem B735183 : Blo 734326 735183 := bstep (se 1 (by rfl) ⟨551387, by rfl⟩ : syracuseStep 735183 = 1102775) B1102775
theorem B735207 : Blo 734326 735207 := bstep (se 1 (by rfl) ⟨551405, by rfl⟩ : syracuseStep 735207 = 1102811) B1102811
theorem B2832569 : Blo 734326 2832569 := bstep (se 2 (by rfl) ⟨1062213, by rfl⟩ : syracuseStep 2832569 = 2124427) B2124427
theorem B735519 : Blo 734326 735519 := bstep (se 1 (by rfl) ⟨551639, by rfl⟩ : syracuseStep 735519 = 1103279) B1103279
theorem B1653065 : Blo 734326 1653065 := bstep (se 2 (by rfl) ⟨619899, by rfl⟩ : syracuseStep 1653065 = 1239799) B1239799
theorem B1653083 : Blo 734326 1653083 := bstep (se 1 (by rfl) ⟨1239812, by rfl⟩ : syracuseStep 1653083 = 2479625) B2479625
theorem B735579 : Blo 734326 735579 := bstep (se 1 (by rfl) ⟨551684, by rfl⟩ : syracuseStep 735579 = 1103369) B1103369
theorem B735599 : Blo 734326 735599 := bstep (se 1 (by rfl) ⟨551699, by rfl⟩ : syracuseStep 735599 = 1103399) B1103399
theorem B735655 : Blo 734326 735655 := bstep (se 1 (by rfl) ⟨551741, by rfl⟩ : syracuseStep 735655 = 1103483) B1103483
theorem B17938867 : Blo 734326 17938867 := bstep (se 1 (by rfl) ⟨13454150, by rfl⟩ : syracuseStep 17938867 = 26908301) B26908301
theorem B735739 : Blo 734326 735739 := bstep (se 1 (by rfl) ⟨551804, by rfl⟩ : syracuseStep 735739 = 1103609) B1103609
theorem B5814823 : Blo 734326 5814823 := bstep (se 1 (by rfl) ⟨4361117, by rfl⟩ : syracuseStep 5814823 = 8722235) B8722235
theorem B735807 : Blo 734326 735807 := bstep (se 1 (by rfl) ⟨551855, by rfl⟩ : syracuseStep 735807 = 1103711) B1103711
theorem B735815 : Blo 734326 735815 := bstep (se 1 (by rfl) ⟨551861, by rfl⟩ : syracuseStep 735815 = 1103723) B1103723
theorem B735967 : Blo 734326 735967 := bstep (se 1 (by rfl) ⟨551975, by rfl⟩ : syracuseStep 735967 = 1103951) B1103951
theorem B736047 : Blo 734326 736047 := bstep (se 1 (by rfl) ⟨552035, by rfl⟩ : syracuseStep 736047 = 1104071) B1104071
theorem B1653659 : Blo 734326 1653659 := bstep (se 1 (by rfl) ⟨1240244, by rfl⟩ : syracuseStep 1653659 = 2480489) B2480489
theorem B736155 : Blo 734326 736155 := bstep (se 1 (by rfl) ⟨552116, by rfl⟩ : syracuseStep 736155 = 1104233) B1104233
theorem B3718061 : Blo 734326 3718061 := bstep (se 3 (by rfl) ⟨697136, by rfl⟩ : syracuseStep 3718061 = 1394273) B1394273
theorem B736207 : Blo 734326 736207 := bstep (se 1 (by rfl) ⟨552155, by rfl⟩ : syracuseStep 736207 = 1104311) B1104311
theorem B736231 : Blo 734326 736231 := bstep (se 1 (by rfl) ⟨552173, by rfl⟩ : syracuseStep 736231 = 1104347) B1104347
theorem B1653857 : Blo 734326 1653857 := bstep (se 2 (by rfl) ⟨620196, by rfl⟩ : syracuseStep 1653857 = 1240393) B1240393
theorem B5586083 : Blo 734326 5586083 := bstep (se 1 (by rfl) ⟨4189562, by rfl⟩ : syracuseStep 5586083 = 8379125) B8379125
theorem B736543 : Blo 734326 736543 := bstep (se 1 (by rfl) ⟨552407, by rfl⟩ : syracuseStep 736543 = 1104815) B1104815
theorem B1654055 : Blo 734326 1654055 := bstep (se 1 (by rfl) ⟨1240541, by rfl⟩ : syracuseStep 1654055 = 2481083) B2481083
theorem B736603 : Blo 734326 736603 := bstep (se 1 (by rfl) ⟨552452, by rfl⟩ : syracuseStep 736603 = 1104905) B1104905
theorem B933211 : Blo 734326 933211 := bstep (se 1 (by rfl) ⟨699908, by rfl⟩ : syracuseStep 933211 = 1399817) B1399817
theorem B1916257 : Blo 734326 1916257 := bstep (se 2 (by rfl) ⟨718596, by rfl⟩ : syracuseStep 1916257 = 1437193) B1437193
theorem B736623 : Blo 734326 736623 := bstep (se 1 (by rfl) ⟨552467, by rfl⟩ : syracuseStep 736623 = 1104935) B1104935
theorem B736679 : Blo 734326 736679 := bstep (se 1 (by rfl) ⟨552509, by rfl⟩ : syracuseStep 736679 = 1105019) B1105019
theorem B736763 : Blo 734326 736763 := bstep (se 1 (by rfl) ⟨552572, by rfl⟩ : syracuseStep 736763 = 1105145) B1105145
theorem B933439 : Blo 734326 933439 := bstep (se 1 (by rfl) ⟨700079, by rfl⟩ : syracuseStep 933439 = 1400159) B1400159
theorem B736831 : Blo 734326 736831 := bstep (se 1 (by rfl) ⟨552623, by rfl⟩ : syracuseStep 736831 = 1105247) B1105247
theorem B736839 : Blo 734326 736839 := bstep (se 1 (by rfl) ⟨552629, by rfl⟩ : syracuseStep 736839 = 1105259) B1105259
theorem B1654433 : Blo 734326 1654433 := bstep (se 2 (by rfl) ⟨620412, by rfl⟩ : syracuseStep 1654433 = 1240825) B1240825
theorem B736991 : Blo 734326 736991 := bstep (se 1 (by rfl) ⟨552743, by rfl⟩ : syracuseStep 736991 = 1105487) B1105487
theorem B737071 : Blo 734326 737071 := bstep (se 1 (by rfl) ⟨552803, by rfl⟩ : syracuseStep 737071 = 1105607) B1105607
theorem B737179 : Blo 734326 737179 := bstep (se 1 (by rfl) ⟨552884, by rfl⟩ : syracuseStep 737179 = 1105769) B1105769
theorem B737231 : Blo 734326 737231 := bstep (se 1 (by rfl) ⟨552923, by rfl⟩ : syracuseStep 737231 = 1105847) B1105847
theorem B737255 : Blo 734326 737255 := bstep (se 1 (by rfl) ⟨552941, by rfl⟩ : syracuseStep 737255 = 1105883) B1105883
theorem B1654793 : Blo 734326 1654793 := bstep (se 2 (by rfl) ⟨620547, by rfl⟩ : syracuseStep 1654793 = 1241095) B1241095
theorem B737567 : Blo 734326 737567 := bstep (se 1 (by rfl) ⟨553175, by rfl⟩ : syracuseStep 737567 = 1106351) B1106351
theorem B934183 : Blo 734326 934183 := bstep (se 1 (by rfl) ⟨700637, by rfl⟩ : syracuseStep 934183 = 1401275) B1401275
theorem B2244937 : Blo 734326 2244937 := bstep (se 2 (by rfl) ⟨841851, by rfl⟩ : syracuseStep 2244937 = 1683703) B1683703
theorem B737627 : Blo 734326 737627 := bstep (se 1 (by rfl) ⟨553220, by rfl⟩ : syracuseStep 737627 = 1106441) B1106441
theorem B737647 : Blo 734326 737647 := bstep (se 1 (by rfl) ⟨553235, by rfl⟩ : syracuseStep 737647 = 1106471) B1106471
theorem B1655207 : Blo 734326 1655207 := bstep (se 1 (by rfl) ⟨1241405, by rfl⟩ : syracuseStep 1655207 = 2482811) B2482811
theorem B737703 : Blo 734326 737703 := bstep (se 1 (by rfl) ⟨553277, by rfl⟩ : syracuseStep 737703 = 1106555) B1106555
theorem B737787 : Blo 734326 737787 := bstep (se 1 (by rfl) ⟨553340, by rfl⟩ : syracuseStep 737787 = 1106681) B1106681
theorem B3719681 : Blo 734326 3719681 := bstep (se 2 (by rfl) ⟨1394880, by rfl⟩ : syracuseStep 3719681 = 2789761) B2789761
theorem B1655315 : Blo 734326 1655315 := bstep (se 1 (by rfl) ⟨1241486, by rfl⟩ : syracuseStep 1655315 = 2482973) B2482973
theorem B737855 : Blo 734326 737855 := bstep (se 1 (by rfl) ⟨553391, by rfl⟩ : syracuseStep 737855 = 1106783) B1106783
theorem B737863 : Blo 734326 737863 := bstep (se 1 (by rfl) ⟨553397, by rfl⟩ : syracuseStep 737863 = 1106795) B1106795
theorem B1655369 : Blo 734326 1655369 := bstep (se 2 (by rfl) ⟨620763, by rfl⟩ : syracuseStep 1655369 = 1241527) B1241527
theorem B738015 : Blo 734326 738015 := bstep (se 1 (by rfl) ⟨553511, by rfl⟩ : syracuseStep 738015 = 1107023) B1107023
theorem B738095 : Blo 734326 738095 := bstep (se 1 (by rfl) ⟨553571, by rfl⟩ : syracuseStep 738095 = 1107143) B1107143
theorem B3588943 : Blo 734326 3588943 := bstep (se 1 (by rfl) ⟨2691707, by rfl⟩ : syracuseStep 3588943 = 5383415) B5383415
theorem B738203 : Blo 734326 738203 := bstep (se 1 (by rfl) ⟨553652, by rfl⟩ : syracuseStep 738203 = 1107305) B1107305
theorem B738255 : Blo 734326 738255 := bstep (se 1 (by rfl) ⟨553691, by rfl⟩ : syracuseStep 738255 = 1107383) B1107383
theorem B3720167 : Blo 734326 3720167 := bstep (se 1 (by rfl) ⟨2790125, by rfl⟩ : syracuseStep 3720167 = 5580251) B5580251
theorem B1655783 : Blo 734326 1655783 := bstep (se 1 (by rfl) ⟨1241837, by rfl⟩ : syracuseStep 1655783 = 2483675) B2483675
theorem B738279 : Blo 734326 738279 := bstep (se 1 (by rfl) ⟨553709, by rfl⟩ : syracuseStep 738279 = 1107419) B1107419
theorem B7980227 : Blo 734326 7980227 := bstep (se 1 (by rfl) ⟨5985170, by rfl⟩ : syracuseStep 7980227 = 11970341) B11970341
theorem B3720491 : Blo 734326 3720491 := bstep (se 1 (by rfl) ⟨2790368, by rfl⟩ : syracuseStep 3720491 = 5580737) B5580737
theorem B18138455 : Blo 734326 18138455 := bstep (se 1 (by rfl) ⟨13603841, by rfl⟩ : syracuseStep 18138455 = 27207683) B27207683
theorem B1656161 : Blo 734326 1656161 := bstep (se 2 (by rfl) ⟨621060, by rfl⟩ : syracuseStep 1656161 = 1242121) B1242121
theorem B5293421 : Blo 734326 5293421 := bstep (se 3 (by rfl) ⟨992516, by rfl⟩ : syracuseStep 5293421 = 1985033) B1985033
theorem B2868641 : Blo 734326 2868641 := bstep (se 2 (by rfl) ⟨1075740, by rfl⟩ : syracuseStep 2868641 = 2151481) B2151481
theorem B1656251 : Blo 734326 1656251 := bstep (se 1 (by rfl) ⟨1242188, by rfl⟩ : syracuseStep 1656251 = 2484377) B2484377
theorem B5588513 : Blo 734326 5588513 := bstep (se 2 (by rfl) ⟨2095692, by rfl⟩ : syracuseStep 5588513 = 4191385) B4191385
theorem B1656377 : Blo 734326 1656377 := bstep (se 2 (by rfl) ⟨621141, by rfl⟩ : syracuseStep 1656377 = 1242283) B1242283
theorem B17024975 : Blo 734326 17024975 := bstep (se 1 (by rfl) ⟨12768731, by rfl⟩ : syracuseStep 17024975 = 25537463) B25537463
theorem B1657043 : Blo 734326 1657043 := bstep (se 1 (by rfl) ⟨1242782, by rfl⟩ : syracuseStep 1657043 = 2485565) B2485565
theorem B3721463 : Blo 734326 3721463 := bstep (se 1 (by rfl) ⟨2791097, by rfl⟩ : syracuseStep 3721463 = 5582195) B5582195
theorem B1657097 : Blo 734326 1657097 := bstep (se 2 (by rfl) ⟨621411, by rfl⟩ : syracuseStep 1657097 = 1242823) B1242823
theorem B1657313 : Blo 734326 1657313 := bstep (se 2 (by rfl) ⟨621492, by rfl⟩ : syracuseStep 1657313 = 1242985) B1242985
theorem B3721949 : Blo 734326 3721949 := bstep (se 3 (by rfl) ⟨697865, by rfl⟩ : syracuseStep 3721949 = 1395731) B1395731
theorem B1657619 : Blo 734326 1657619 := bstep (se 1 (by rfl) ⟨1243214, by rfl⟩ : syracuseStep 1657619 = 2486429) B2486429
theorem B4705057 : Blo 734326 4705057 := bstep (se 2 (by rfl) ⟨1764396, by rfl⟩ : syracuseStep 4705057 = 3528793) B3528793
theorem B1657979 : Blo 734326 1657979 := bstep (se 1 (by rfl) ⟨1243484, by rfl⟩ : syracuseStep 1657979 = 2486969) B2486969
theorem B1985725 : Blo 734326 1985725 := bstep (se 3 (by rfl) ⟨372323, by rfl⟩ : syracuseStep 1985725 = 744647) B744647
theorem B1658105 : Blo 734326 1658105 := bstep (se 2 (by rfl) ⟨621789, by rfl⟩ : syracuseStep 1658105 = 1243579) B1243579
theorem B1658249 : Blo 734326 1658249 := bstep (se 2 (by rfl) ⟨621843, by rfl⟩ : syracuseStep 1658249 = 1243687) B1243687
theorem B1396217 : Blo 734326 1396217 := bstep (se 2 (by rfl) ⟨523581, by rfl⟩ : syracuseStep 1396217 = 1047163) B1047163
theorem B1658375 : Blo 734326 1658375 := bstep (se 1 (by rfl) ⟨1243781, by rfl⟩ : syracuseStep 1658375 = 2487563) B2487563
theorem B1658555 : Blo 734326 1658555 := bstep (se 1 (by rfl) ⟨1243916, by rfl⟩ : syracuseStep 1658555 = 2487833) B2487833
theorem B4706059 : Blo 734326 4706059 := bstep (se 1 (by rfl) ⟨3529544, by rfl⟩ : syracuseStep 4706059 = 7059089) B7059089
theorem B1101623 : Blo 734326 1101623 := bstep (se 1 (by rfl) ⟨826217, by rfl⟩ : syracuseStep 1101623 = 1652435) B1652435
theorem B1658681 : Blo 734326 1658681 := bstep (se 2 (by rfl) ⟨622005, by rfl⟩ : syracuseStep 1658681 = 1244011) B1244011
theorem B3362735 : Blo 734326 3362735 := bstep (se 1 (by rfl) ⟨2522051, by rfl⟩ : syracuseStep 3362735 = 5044103) B5044103
theorem B1101929 : Blo 734326 1101929 := bstep (se 2 (by rfl) ⟨413223, by rfl⟩ : syracuseStep 1101929 = 826447) B826447
theorem B1397083 : Blo 734326 1397083 := bstep (se 1 (by rfl) ⟨1047812, by rfl⟩ : syracuseStep 1397083 = 2095625) B2095625
theorem B1102247 : Blo 734326 1102247 := bstep (se 1 (by rfl) ⟨826685, by rfl⟩ : syracuseStep 1102247 = 1653371) B1653371
theorem B1397159 : Blo 734326 1397159 := bstep (se 1 (by rfl) ⟨1047869, by rfl⟩ : syracuseStep 1397159 = 2095739) B2095739
theorem B1659311 : Blo 734326 1659311 := bstep (se 1 (by rfl) ⟨1244483, by rfl⟩ : syracuseStep 1659311 = 2488967) B2488967
theorem B1659347 : Blo 734326 1659347 := bstep (se 1 (by rfl) ⟨1244510, by rfl⟩ : syracuseStep 1659347 = 2489021) B2489021
theorem B1102331 : Blo 734326 1102331 := bstep (se 1 (by rfl) ⟨826748, by rfl⟩ : syracuseStep 1102331 = 1653497) B1653497
theorem B1397243 : Blo 734326 1397243 := bstep (se 1 (by rfl) ⟨1047932, by rfl⟩ : syracuseStep 1397243 = 2095865) B2095865
theorem B1659455 : Blo 734326 1659455 := bstep (se 1 (by rfl) ⟨1244591, by rfl⟩ : syracuseStep 1659455 = 2489183) B2489183
theorem B19157573 : Blo 734326 19157573 := bstep (se 4 (by rfl) ⟨1796022, by rfl⟩ : syracuseStep 19157573 = 3592045) B3592045
theorem B1102457 : Blo 734326 1102457 := bstep (se 2 (by rfl) ⟨413421, by rfl⟩ : syracuseStep 1102457 = 826843) B826843
theorem B1659563 : Blo 734326 1659563 := bstep (se 1 (by rfl) ⟨1244672, by rfl⟩ : syracuseStep 1659563 = 2489345) B2489345
theorem B1102511 : Blo 734326 1102511 := bstep (se 1 (by rfl) ⟨826883, by rfl⟩ : syracuseStep 1102511 = 1653767) B1653767
theorem B2478815 : Blo 734326 2478815 := bstep (se 1 (by rfl) ⟨1859111, by rfl⟩ : syracuseStep 2478815 = 3718223) B3718223
theorem B1102559 : Blo 734326 1102559 := bstep (se 1 (by rfl) ⟨826919, by rfl⟩ : syracuseStep 1102559 = 1653839) B1653839
theorem B10638047 : Blo 734326 10638047 := bstep (se 1 (by rfl) ⟨7978535, by rfl⟩ : syracuseStep 10638047 = 15957071) B15957071
theorem B1594255 : Blo 734326 1594255 := bstep (se 1 (by rfl) ⟨1195691, by rfl⟩ : syracuseStep 1594255 = 2391383) B2391383
theorem B1397675 : Blo 734326 1397675 := bstep (se 1 (by rfl) ⟨1048256, by rfl⟩ : syracuseStep 1397675 = 2096513) B2096513
theorem B1102823 : Blo 734326 1102823 := bstep (se 1 (by rfl) ⟨827117, by rfl⟩ : syracuseStep 1102823 = 1654235) B1654235
theorem B2479247 : Blo 734326 2479247 := bstep (se 1 (by rfl) ⟨1859435, by rfl⟩ : syracuseStep 2479247 = 3718871) B3718871
theorem B1594567 : Blo 734326 1594567 := bstep (se 1 (by rfl) ⟨1195925, by rfl⟩ : syracuseStep 1594567 = 2391851) B2391851
theorem B1660103 : Blo 734326 1660103 := bstep (se 1 (by rfl) ⟨1245077, by rfl⟩ : syracuseStep 1660103 = 2490155) B2490155
theorem B1103081 : Blo 734326 1103081 := bstep (se 2 (by rfl) ⟨413655, by rfl⟩ : syracuseStep 1103081 = 827311) B827311
theorem B1103135 : Blo 734326 1103135 := bstep (se 1 (by rfl) ⟨827351, by rfl⟩ : syracuseStep 1103135 = 1654703) B1654703
theorem B1398055 : Blo 734326 1398055 := bstep (se 1 (by rfl) ⟨1048541, by rfl⟩ : syracuseStep 1398055 = 2097083) B2097083
theorem B1660283 : Blo 734326 1660283 := bstep (se 1 (by rfl) ⟨1245212, by rfl⟩ : syracuseStep 1660283 = 2490425) B2490425
theorem B1103303 : Blo 734326 1103303 := bstep (se 1 (by rfl) ⟨827477, by rfl⟩ : syracuseStep 1103303 = 1654955) B1654955
theorem B1398215 : Blo 734326 1398215 := bstep (se 1 (by rfl) ⟨1048661, by rfl⟩ : syracuseStep 1398215 = 2097323) B2097323
theorem B1660409 : Blo 734326 1660409 := bstep (se 2 (by rfl) ⟨622653, by rfl⟩ : syracuseStep 1660409 = 1245307) B1245307
theorem B1660499 : Blo 734326 1660499 := bstep (se 1 (by rfl) ⟨1245374, by rfl⟩ : syracuseStep 1660499 = 2490749) B2490749
theorem B3364487 : Blo 734326 3364487 := bstep (se 1 (by rfl) ⟨2523365, by rfl⟩ : syracuseStep 3364487 = 5046731) B5046731
theorem B1660679 : Blo 734326 1660679 := bstep (se 1 (by rfl) ⟨1245509, by rfl⟩ : syracuseStep 1660679 = 2491019) B2491019
theorem B1103657 : Blo 734326 1103657 := bstep (se 2 (by rfl) ⟨413871, by rfl⟩ : syracuseStep 1103657 = 827743) B827743
theorem B1103663 : Blo 734326 1103663 := bstep (se 1 (by rfl) ⟨827747, by rfl⟩ : syracuseStep 1103663 = 1655495) B1655495
theorem B841519 : Blo 734326 841519 := bstep (se 1 (by rfl) ⟨631139, by rfl⟩ : syracuseStep 841519 = 1262279) B1262279
theorem B5592887 : Blo 734326 5592887 := bstep (se 1 (by rfl) ⟨4194665, by rfl⟩ : syracuseStep 5592887 = 8389331) B8389331
theorem B15915041 : Blo 734326 15915041 := bstep (se 2 (by rfl) ⟨5968140, by rfl⟩ : syracuseStep 15915041 = 11936281) B11936281
theorem B2480381 : Blo 734326 2480381 := bstep (se 3 (by rfl) ⟨465071, by rfl⟩ : syracuseStep 2480381 = 930143) B930143
theorem B1104137 : Blo 734326 1104137 := bstep (se 2 (by rfl) ⟨414051, by rfl⟩ : syracuseStep 1104137 = 828103) B828103
theorem B1104239 : Blo 734326 1104239 := bstep (se 1 (by rfl) ⟨828179, by rfl⟩ : syracuseStep 1104239 = 1656359) B1656359
theorem B1104455 : Blo 734326 1104455 := bstep (se 1 (by rfl) ⟨828341, by rfl⟩ : syracuseStep 1104455 = 1656683) B1656683
theorem B1399369 : Blo 734326 1399369 := bstep (se 2 (by rfl) ⟨524763, by rfl⟩ : syracuseStep 1399369 = 1049527) B1049527
theorem B3529295 : Blo 734326 3529295 := bstep (se 1 (by rfl) ⟨2646971, by rfl⟩ : syracuseStep 3529295 = 5293943) B5293943
theorem B1104491 : Blo 734326 1104491 := bstep (se 1 (by rfl) ⟨828368, by rfl⟩ : syracuseStep 1104491 = 1656737) B1656737
theorem B3725999 : Blo 734326 3725999 := bstep (se 1 (by rfl) ⟨2794499, by rfl⟩ : syracuseStep 3725999 = 5588999) B5588999
theorem B1104719 : Blo 734326 1104719 := bstep (se 1 (by rfl) ⟨828539, by rfl⟩ : syracuseStep 1104719 = 1657079) B1657079
theorem B2120591 : Blo 734326 2120591 := bstep (se 1 (by rfl) ⟨1590443, by rfl⟩ : syracuseStep 2120591 = 3180887) B3180887
theorem B6282157 : Blo 734326 6282157 := bstep (se 3 (by rfl) ⟨1177904, by rfl⟩ : syracuseStep 6282157 = 2355809) B2355809
theorem B3726323 : Blo 734326 3726323 := bstep (se 1 (by rfl) ⟨2794742, by rfl⟩ : syracuseStep 3726323 = 5589485) B5589485
theorem B2481191 : Blo 734326 2481191 := bstep (se 1 (by rfl) ⟨1860893, by rfl⟩ : syracuseStep 2481191 = 3721787) B3721787
theorem B2514059 : Blo 734326 2514059 := bstep (se 1 (by rfl) ⟨1885544, by rfl⟩ : syracuseStep 2514059 = 3771089) B3771089
theorem B1105115 : Blo 734326 1105115 := bstep (se 1 (by rfl) ⟨828836, by rfl⟩ : syracuseStep 1105115 = 1657673) B1657673
theorem B3235139 : Blo 734326 3235139 := bstep (se 1 (by rfl) ⟨2426354, by rfl⟩ : syracuseStep 3235139 = 4852709) B4852709
theorem B21192029 : Blo 734326 21192029 := bstep (se 3 (by rfl) ⟨3973505, by rfl⟩ : syracuseStep 21192029 = 7947011) B7947011
theorem B1105289 : Blo 734326 1105289 := bstep (se 2 (by rfl) ⟨414483, by rfl⟩ : syracuseStep 1105289 = 828967) B828967
theorem B2481623 : Blo 734326 2481623 := bstep (se 1 (by rfl) ⟨1861217, by rfl⟩ : syracuseStep 2481623 = 3722435) B3722435
theorem B1859233 : Blo 734326 1859233 := bstep (se 2 (by rfl) ⟨697212, by rfl⟩ : syracuseStep 1859233 = 1394425) B1394425
theorem B1105643 : Blo 734326 1105643 := bstep (se 1 (by rfl) ⟨829232, by rfl⟩ : syracuseStep 1105643 = 1658465) B1658465
theorem B1859375 : Blo 734326 1859375 := bstep (se 1 (by rfl) ⟨1394531, by rfl⟩ : syracuseStep 1859375 = 2789063) B2789063
theorem B6283115 : Blo 734326 6283115 := bstep (se 1 (by rfl) ⟨4712336, by rfl⟩ : syracuseStep 6283115 = 9424673) B9424673
theorem B17948591 : Blo 734326 17948591 := bstep (se 1 (by rfl) ⟨13461443, by rfl⟩ : syracuseStep 17948591 = 26922887) B26922887
theorem B1105871 : Blo 734326 1105871 := bstep (se 1 (by rfl) ⟨829403, by rfl⟩ : syracuseStep 1105871 = 1658807) B1658807
theorem B3137561 : Blo 734326 3137561 := bstep (se 2 (by rfl) ⟨1176585, by rfl⟩ : syracuseStep 3137561 = 2353171) B2353171
theorem B3727619 : Blo 734326 3727619 := bstep (se 1 (by rfl) ⟨2795714, by rfl⟩ : syracuseStep 3727619 = 5591429) B5591429
theorem B31875389 : Blo 734326 31875389 := bstep (se 3 (by rfl) ⟨5976635, by rfl⟩ : syracuseStep 31875389 = 11953271) B11953271
theorem B1106267 : Blo 734326 1106267 := bstep (se 1 (by rfl) ⟨829700, by rfl⟩ : syracuseStep 1106267 = 1659401) B1659401
theorem B1860023 : Blo 734326 1860023 := bstep (se 1 (by rfl) ⟨1395017, by rfl⟩ : syracuseStep 1860023 = 2790035) B2790035
theorem B1401313 : Blo 734326 1401313 := bstep (se 2 (by rfl) ⟨525492, by rfl⟩ : syracuseStep 1401313 = 1050985) B1050985
theorem B1106495 : Blo 734326 1106495 := bstep (se 1 (by rfl) ⟨829871, by rfl⟩ : syracuseStep 1106495 = 1659743) B1659743
theorem B3727943 : Blo 734326 3727943 := bstep (se 1 (by rfl) ⟨2795957, by rfl⟩ : syracuseStep 3727943 = 5591915) B5591915
theorem B1106615 : Blo 734326 1106615 := bstep (se 1 (by rfl) ⟨829961, by rfl⟩ : syracuseStep 1106615 = 1659923) B1659923
theorem B1106843 : Blo 734326 1106843 := bstep (se 1 (by rfl) ⟨830132, by rfl⟩ : syracuseStep 1106843 = 1660265) B1660265
theorem B3138551 : Blo 734326 3138551 := bstep (se 1 (by rfl) ⟨2353913, by rfl⟩ : syracuseStep 3138551 = 4707827) B4707827
theorem B2483297 : Blo 734326 2483297 := bstep (se 2 (by rfl) ⟨931236, by rfl⟩ : syracuseStep 2483297 = 1862473) B1862473
theorem B1991803 : Blo 734326 1991803 := bstep (se 1 (by rfl) ⟨1493852, by rfl⟩ : syracuseStep 1991803 = 2987705) B2987705
theorem B3990653 : Blo 734326 3990653 := bstep (se 3 (by rfl) ⟨748247, by rfl⟩ : syracuseStep 3990653 = 1496495) B1496495
theorem B1107239 : Blo 734326 1107239 := bstep (se 1 (by rfl) ⟨830429, by rfl⟩ : syracuseStep 1107239 = 1660859) B1660859
theorem B1107323 : Blo 734326 1107323 := bstep (se 1 (by rfl) ⟨830492, by rfl⟩ : syracuseStep 1107323 = 1660985) B1660985
theorem B7464335 : Blo 734326 7464335 := bstep (se 1 (by rfl) ⟨5598251, by rfl⟩ : syracuseStep 7464335 = 11196503) B11196503
theorem B1107449 : Blo 734326 1107449 := bstep (se 2 (by rfl) ⟨415293, by rfl⟩ : syracuseStep 1107449 = 830587) B830587
theorem B1861127 : Blo 734326 1861127 := bstep (se 1 (by rfl) ⟨1395845, by rfl⟩ : syracuseStep 1861127 = 2791691) B2791691
theorem B1861177 : Blo 734326 1861177 := bstep (se 2 (by rfl) ⟨697941, by rfl⟩ : syracuseStep 1861177 = 1395883) B1395883
theorem B943687 : Blo 734326 943687 := bstep (se 1 (by rfl) ⟨707765, by rfl⟩ : syracuseStep 943687 = 1415531) B1415531
theorem B8382041 : Blo 734326 8382041 := bstep (se 2 (by rfl) ⟨3143265, by rfl⟩ : syracuseStep 8382041 = 6286531) B6286531
theorem B6383393 : Blo 734326 6383393 := bstep (se 2 (by rfl) ⟨2393772, by rfl⟩ : syracuseStep 6383393 = 4787545) B4787545
theorem B4417361 : Blo 734326 4417361 := bstep (se 2 (by rfl) ⟨1656510, by rfl⟩ : syracuseStep 4417361 = 3313021) B3313021
theorem B3729239 : Blo 734326 3729239 := bstep (se 1 (by rfl) ⟨2796929, by rfl⟩ : syracuseStep 3729239 = 5593859) B5593859
theorem B1861481 : Blo 734326 1861481 := bstep (se 2 (by rfl) ⟨698055, by rfl⟩ : syracuseStep 1861481 = 1396111) B1396111
theorem B2484647 : Blo 734326 2484647 := bstep (se 1 (by rfl) ⟨1863485, by rfl⟩ : syracuseStep 2484647 = 3726971) B3726971
theorem B1862099 : Blo 734326 1862099 := bstep (se 1 (by rfl) ⟨1396574, by rfl⟩ : syracuseStep 1862099 = 2793149) B2793149
theorem B2484809 : Blo 734326 2484809 := bstep (se 2 (by rfl) ⟨931803, by rfl⟩ : syracuseStep 2484809 = 1863607) B1863607
theorem B1993337 : Blo 734326 1993337 := bstep (se 2 (by rfl) ⟨747501, by rfl⟩ : syracuseStep 1993337 = 1495003) B1495003
theorem B4188995 : Blo 734326 4188995 := bstep (se 1 (by rfl) ⟨3141746, by rfl⟩ : syracuseStep 4188995 = 6283493) B6283493
theorem B1239887 : Blo 734326 1239887 := bstep (se 1 (by rfl) ⟨929915, by rfl⟩ : syracuseStep 1239887 = 1859831) B1859831
theorem B2649277 : Blo 734326 2649277 := bstep (se 3 (by rfl) ⟨496739, by rfl⟩ : syracuseStep 2649277 = 993479) B993479
theorem B1764551 : Blo 734326 1764551 := bstep (se 1 (by rfl) ⟨1323413, by rfl⟩ : syracuseStep 1764551 = 2646827) B2646827
theorem B2649307 : Blo 734326 2649307 := bstep (se 1 (by rfl) ⟨1986980, by rfl⟩ : syracuseStep 2649307 = 3973961) B3973961
theorem B3534329 : Blo 734326 3534329 := bstep (se 2 (by rfl) ⟨1325373, by rfl⟩ : syracuseStep 3534329 = 2650747) B2650747
theorem B1863263 : Blo 734326 1863263 := bstep (se 1 (by rfl) ⟨1397447, by rfl⟩ : syracuseStep 1863263 = 2794895) B2794895
theorem B5664491 : Blo 734326 5664491 := bstep (se 1 (by rfl) ⟨4248368, by rfl⟩ : syracuseStep 5664491 = 8496737) B8496737
theorem B1240879 : Blo 734326 1240879 := bstep (se 1 (by rfl) ⟨930659, by rfl⟩ : syracuseStep 1240879 = 1861319) B1861319
theorem B3731507 : Blo 734326 3731507 := bstep (se 1 (by rfl) ⟨2798630, by rfl⟩ : syracuseStep 3731507 = 5597261) B5597261
theorem B7073851 : Blo 734326 7073851 := bstep (se 1 (by rfl) ⟨5305388, by rfl⟩ : syracuseStep 7073851 = 10610777) B10610777
theorem B2486483 : Blo 734326 2486483 := bstep (se 1 (by rfl) ⟨1864862, by rfl⟩ : syracuseStep 2486483 = 3729725) B3729725
theorem B3109211 : Blo 734326 3109211 := bstep (se 1 (by rfl) ⟨2331908, by rfl⟩ : syracuseStep 3109211 = 4663817) B4663817
theorem B1864043 : Blo 734326 1864043 := bstep (se 1 (by rfl) ⟨1398032, by rfl⟩ : syracuseStep 1864043 = 2796065) B2796065
theorem B2486753 : Blo 734326 2486753 := bstep (se 2 (by rfl) ⟨932532, by rfl⟩ : syracuseStep 2486753 = 1865065) B1865065
theorem B1864255 : Blo 734326 1864255 := bstep (se 1 (by rfl) ⟨1398191, by rfl⟩ : syracuseStep 1864255 = 2796383) B2796383
theorem B7959161 : Blo 734326 7959161 := bstep (se 2 (by rfl) ⟨2984685, by rfl⟩ : syracuseStep 7959161 = 5969371) B5969371
theorem B1864367 : Blo 734326 1864367 := bstep (se 1 (by rfl) ⟨1398275, by rfl⟩ : syracuseStep 1864367 = 2796551) B2796551
theorem B1864691 : Blo 734326 1864691 := bstep (se 1 (by rfl) ⟨1398518, by rfl⟩ : syracuseStep 1864691 = 2797037) B2797037
theorem B26866835 : Blo 734326 26866835 := bstep (se 1 (by rfl) ⟨20150126, by rfl⟩ : syracuseStep 26866835 = 40300253) B40300253
theorem B1864903 : Blo 734326 1864903 := bstep (se 1 (by rfl) ⟨1398677, by rfl⟩ : syracuseStep 1864903 = 2797355) B2797355
theorem B1570079 : Blo 734326 1570079 := bstep (se 1 (by rfl) ⟨1177559, by rfl⟩ : syracuseStep 1570079 = 2355119) B2355119
theorem B2094599 : Blo 734326 2094599 := bstep (se 1 (by rfl) ⟨1570949, by rfl⟩ : syracuseStep 2094599 = 3141899) B3141899
theorem B882247 : Blo 734326 882247 := bstep (se 1 (by rfl) ⟨661685, by rfl⟩ : syracuseStep 882247 = 1323371) B1323371
theorem B3733127 : Blo 734326 3733127 := bstep (se 1 (by rfl) ⟨2799845, by rfl⟩ : syracuseStep 3733127 = 5599691) B5599691
theorem B2487995 : Blo 734326 2487995 := bstep (se 1 (by rfl) ⟨1865996, by rfl⟩ : syracuseStep 2487995 = 3731993) B3731993
theorem B2095055 : Blo 734326 2095055 := bstep (se 1 (by rfl) ⟨1571291, by rfl⟩ : syracuseStep 2095055 = 3142583) B3142583
theorem B1243559 : Blo 734326 1243559 := bstep (se 1 (by rfl) ⟨932669, by rfl⟩ : syracuseStep 1243559 = 1865339) B1865339
theorem B1866311 : Blo 734326 1866311 := bstep (se 1 (by rfl) ⟨1399733, by rfl⟩ : syracuseStep 1866311 = 2799467) B2799467
theorem B883271 : Blo 734326 883271 := bstep (se 1 (by rfl) ⟨662453, by rfl⟩ : syracuseStep 883271 = 1324907) B1324907
theorem B1243721 : Blo 734326 1243721 := bstep (se 2 (by rfl) ⟨466395, by rfl⟩ : syracuseStep 1243721 = 932791) B932791
theorem B1866361 : Blo 734326 1866361 := bstep (se 2 (by rfl) ⟨699885, by rfl⟩ : syracuseStep 1866361 = 1399771) B1399771
theorem B3734747 : Blo 734326 3734747 := bstep (se 1 (by rfl) ⟨2801060, by rfl⟩ : syracuseStep 3734747 = 5602121) B5602121
theorem B3145027 : Blo 734326 3145027 := bstep (se 1 (by rfl) ⟨2358770, by rfl⟩ : syracuseStep 3145027 = 4717541) B4717541
theorem B2489939 : Blo 734326 2489939 := bstep (se 1 (by rfl) ⟨1867454, by rfl⟩ : syracuseStep 2489939 = 3734909) B3734909
theorem B1244767 : Blo 734326 1244767 := bstep (se 1 (by rfl) ⟨933575, by rfl⟩ : syracuseStep 1244767 = 1867151) B1867151
theorem B1277675 : Blo 734326 1277675 := bstep (se 1 (by rfl) ⟨958256, by rfl⟩ : syracuseStep 1277675 = 1916513) B1916513
theorem B786223 : Blo 734326 786223 := bstep (se 1 (by rfl) ⟨589667, by rfl⟩ : syracuseStep 786223 = 1179335) B1179335
theorem B1244983 : Blo 734326 1244983 := bstep (se 1 (by rfl) ⟨933737, by rfl⟩ : syracuseStep 1244983 = 1867475) B1867475
theorem B5046077 : Blo 734326 5046077 := bstep (se 3 (by rfl) ⟨946139, by rfl⟩ : syracuseStep 5046077 = 1892279) B1892279
theorem B5373803 : Blo 734326 5373803 := bstep (se 1 (by rfl) ⟨4030352, by rfl⟩ : syracuseStep 5373803 = 8060705) B8060705
theorem B10485811 : Blo 734326 10485811 := bstep (se 1 (by rfl) ⟨7864358, by rfl⟩ : syracuseStep 10485811 = 15728717) B15728717
theorem B2490587 : Blo 734326 2490587 := bstep (se 1 (by rfl) ⟨1867940, by rfl⟩ : syracuseStep 2490587 = 3735881) B3735881
theorem B1245415 : Blo 734326 1245415 := bstep (se 1 (by rfl) ⟨934061, by rfl⟩ : syracuseStep 1245415 = 1868123) B1868123
theorem B1245577 : Blo 734326 1245577 := bstep (se 2 (by rfl) ⟨467091, by rfl⟩ : syracuseStep 1245577 = 934183) B934183
theorem B2490857 : Blo 734326 2490857 := bstep (se 2 (by rfl) ⟨934071, by rfl⟩ : syracuseStep 2490857 = 1868143) B1868143
theorem B1868417 : Blo 734326 1868417 := bstep (se 2 (by rfl) ⟨700656, by rfl⟩ : syracuseStep 1868417 = 1401313) B1401313
theorem B3736367 : Blo 734326 3736367 := bstep (se 1 (by rfl) ⟨2802275, by rfl⟩ : syracuseStep 3736367 = 5604551) B5604551
theorem B12092303 : Blo 734326 12092303 := bstep (se 1 (by rfl) ⟨9069227, by rfl⟩ : syracuseStep 12092303 = 18138455) B18138455
theorem B4195259 : Blo 734326 4195259 := bstep (se 1 (by rfl) ⟨3146444, by rfl⟩ : syracuseStep 4195259 = 6292889) B6292889
theorem B3146683 : Blo 734326 3146683 := bstep (se 1 (by rfl) ⟨2360012, by rfl⟩ : syracuseStep 3146683 = 4720025) B4720025
theorem B2491451 : Blo 734326 2491451 := bstep (se 1 (by rfl) ⟨1868588, by rfl⟩ : syracuseStep 2491451 = 3737177) B3737177
theorem B4785257 : Blo 734326 4785257 := bstep (se 2 (by rfl) ⟨1794471, by rfl⟩ : syracuseStep 4785257 = 3588943) B3588943
theorem B2491721 : Blo 734326 2491721 := bstep (se 2 (by rfl) ⟨934395, by rfl⟩ : syracuseStep 2491721 = 1868791) B1868791
theorem B1181083 : Blo 734326 1181083 := bstep (se 1 (by rfl) ⟨885812, by rfl⟩ : syracuseStep 1181083 = 1771625) B1771625
theorem B2655737 : Blo 734326 2655737 := bstep (se 2 (by rfl) ⟨995901, by rfl⟩ : syracuseStep 2655737 = 1991803) B1991803
theorem B5113367 : Blo 734326 5113367 := bstep (se 1 (by rfl) ⟨3835025, by rfl⟩ : syracuseStep 5113367 = 7670051) B7670051
theorem B1771463 : Blo 734326 1771463 := bstep (se 1 (by rfl) ⟨1328597, by rfl⟩ : syracuseStep 1771463 = 2657195) B2657195
theorem B4786295 : Blo 734326 4786295 := bstep (se 1 (by rfl) ⟨3589721, by rfl⟩ : syracuseStep 4786295 = 7179443) B7179443
theorem B6293639 : Blo 734326 6293639 := bstep (se 1 (by rfl) ⟨4720229, by rfl⟩ : syracuseStep 6293639 = 9440459) B9440459
theorem B2099783 : Blo 734326 2099783 := bstep (se 1 (by rfl) ⟨1574837, by rfl⟩ : syracuseStep 2099783 = 3149675) B3149675
theorem B1182313 : Blo 734326 1182313 := bstep (se 2 (by rfl) ⟨443367, by rfl⟩ : syracuseStep 1182313 = 886735) B886735
theorem B4197035 : Blo 734326 4197035 := bstep (se 1 (by rfl) ⟨3147776, by rfl⟩ : syracuseStep 4197035 = 6295553) B6295553
theorem B2362871 : Blo 734326 2362871 := bstep (se 1 (by rfl) ⟨1772153, by rfl⟩ : syracuseStep 2362871 = 3544307) B3544307
theorem B17961047 : Blo 734326 17961047 := bstep (se 1 (by rfl) ⟨13470785, by rfl⟩ : syracuseStep 17961047 = 26941571) B26941571
theorem B2363897 : Blo 734326 2363897 := bstep (se 2 (by rfl) ⟨886461, by rfl⟩ : syracuseStep 2363897 = 1772923) B1772923
theorem B14128019 : Blo 734326 14128019 := bstep (se 1 (by rfl) ⟨10596014, by rfl⟩ : syracuseStep 14128019 = 21192029) B21192029
theorem B2102345 : Blo 734326 2102345 := bstep (se 2 (by rfl) ⟨788379, by rfl⟩ : syracuseStep 2102345 = 1576759) B1576759
theorem B4199633 : Blo 734326 4199633 := bstep (se 2 (by rfl) ⟨1574862, by rfl⟩ : syracuseStep 4199633 = 3149725) B3149725
theorem B3151057 : Blo 734326 3151057 := bstep (se 2 (by rfl) ⟨1181646, by rfl⟩ : syracuseStep 3151057 = 2363293) B2363293
theorem B11965727 : Blo 734326 11965727 := bstep (se 1 (by rfl) ⟨8974295, by rfl⟩ : syracuseStep 11965727 = 17948591) B17948591
theorem B3151673 : Blo 734326 3151673 := bstep (se 2 (by rfl) ⟨1181877, by rfl⟩ : syracuseStep 3151673 = 2363755) B2363755
theorem B4200407 : Blo 734326 4200407 := bstep (se 1 (by rfl) ⟨3150305, by rfl⟩ : syracuseStep 4200407 = 6300611) B6300611
theorem B2660435 : Blo 734326 2660435 := bstep (se 1 (by rfl) ⟨1995326, by rfl⟩ : syracuseStep 2660435 = 3990653) B3990653
theorem B10590533 : Blo 734326 10590533 := bstep (se 4 (by rfl) ⟨992862, by rfl⟩ : syracuseStep 10590533 = 1985725) B1985725
theorem B14129477 : Blo 734326 14129477 := bstep (se 4 (by rfl) ⟨1324638, by rfl⟩ : syracuseStep 14129477 = 2649277) B2649277
theorem B2792663 : Blo 734326 2792663 := bstep (se 1 (by rfl) ⟨2094497, by rfl⟩ : syracuseStep 2792663 = 4188995) B4188995
theorem B826591 : Blo 734326 826591 := bstep (se 1 (by rfl) ⟨619943, by rfl⟩ : syracuseStep 826591 = 1239887) B1239887
theorem B9444923 : Blo 734326 9444923 := bstep (se 1 (by rfl) ⟨7083692, by rfl⟩ : syracuseStep 9444923 = 14167385) B14167385
theorem B3776327 : Blo 734326 3776327 := bstep (se 1 (by rfl) ⟨2832245, by rfl⟩ : syracuseStep 3776327 = 5664491) B5664491
theorem B5316779 : Blo 734326 5316779 := bstep (se 1 (by rfl) ⟨3987584, by rfl⟩ : syracuseStep 5316779 = 7975169) B7975169
theorem B2072807 : Blo 734326 2072807 := bstep (se 1 (by rfl) ⟨1554605, by rfl⟩ : syracuseStep 2072807 = 3109211) B3109211
theorem B829039 : Blo 734326 829039 := bstep (se 1 (by rfl) ⟨621779, by rfl⟩ : syracuseStep 829039 = 1243559) B1243559
theorem B829147 : Blo 734326 829147 := bstep (se 1 (by rfl) ⟨621860, by rfl⟩ : syracuseStep 829147 = 1243721) B1243721
theorem B14330141 : Blo 734326 14330141 := bstep (se 3 (by rfl) ⟨2686901, by rfl⟩ : syracuseStep 14330141 = 5373803) B5373803
theorem B830299 : Blo 734326 830299 := bstep (se 1 (by rfl) ⟨622724, by rfl⟩ : syracuseStep 830299 = 1245449) B1245449
theorem B2993249 : Blo 734326 2993249 := bstep (se 2 (by rfl) ⟨1122468, by rfl⟩ : syracuseStep 2993249 = 2244937) B2244937
theorem B5320151 : Blo 734326 5320151 := bstep (se 1 (by rfl) ⟨3990113, by rfl⟩ : syracuseStep 5320151 = 7980227) B7980227
theorem B1912427 : Blo 734326 1912427 := bstep (se 1 (by rfl) ⟨1434320, by rfl⟩ : syracuseStep 1912427 = 2868641) B2868641
theorem B6205177 : Blo 734326 6205177 := bstep (se 2 (by rfl) ⟨2326941, by rfl⟩ : syracuseStep 6205177 = 4653883) B4653883
theorem B2273129 : Blo 734326 2273129 := bstep (se 2 (by rfl) ⟨852423, by rfl⟩ : syracuseStep 2273129 = 1704847) B1704847
theorem B11349983 : Blo 734326 11349983 := bstep (se 1 (by rfl) ⟨8512487, by rfl⟩ : syracuseStep 11349983 = 17024975) B17024975
theorem B26816629 : Blo 734326 26816629 := bstep (se 5 (by rfl) ⟨1257029, by rfl⟩ : syracuseStep 26816629 = 2514059) B2514059
theorem B2798327 : Blo 734326 2798327 := bstep (se 1 (by rfl) ⟨2098745, by rfl⟩ : syracuseStep 2798327 = 4197491) B4197491
theorem B1258249 : Blo 734326 1258249 := bstep (se 2 (by rfl) ⟨471843, by rfl⟩ : syracuseStep 1258249 = 943687) B943687
theorem B734415 : Blo 734326 734415 := bstep (se 1 (by rfl) ⟨550811, by rfl⟩ : syracuseStep 734415 = 1101623) B1101623
theorem B734619 : Blo 734326 734619 := bstep (se 1 (by rfl) ⟨550964, by rfl⟩ : syracuseStep 734619 = 1101929) B1101929
theorem B734831 : Blo 734326 734831 := bstep (se 1 (by rfl) ⟨551123, by rfl⟩ : syracuseStep 734831 = 1102247) B1102247
theorem B931439 : Blo 734326 931439 := bstep (se 1 (by rfl) ⟨698579, by rfl⟩ : syracuseStep 931439 = 1397159) B1397159
theorem B734887 : Blo 734326 734887 := bstep (se 1 (by rfl) ⟨551165, by rfl⟩ : syracuseStep 734887 = 1102331) B1102331
theorem B931495 : Blo 734326 931495 := bstep (se 1 (by rfl) ⟨698621, by rfl⟩ : syracuseStep 931495 = 1397243) B1397243
theorem B734971 : Blo 734326 734971 := bstep (se 1 (by rfl) ⟨551228, by rfl⟩ : syracuseStep 734971 = 1102457) B1102457
theorem B735007 : Blo 734326 735007 := bstep (se 1 (by rfl) ⟨551255, by rfl⟩ : syracuseStep 735007 = 1102511) B1102511
theorem B1652543 : Blo 734326 1652543 := bstep (se 1 (by rfl) ⟨1239407, by rfl⟩ : syracuseStep 1652543 = 2478815) B2478815
theorem B735039 : Blo 734326 735039 := bstep (se 1 (by rfl) ⟨551279, by rfl⟩ : syracuseStep 735039 = 1102559) B1102559
theorem B7092031 : Blo 734326 7092031 := bstep (se 1 (by rfl) ⟨5319023, by rfl⟩ : syracuseStep 7092031 = 10638047) B10638047
theorem B12105577 : Blo 734326 12105577 := bstep (se 2 (by rfl) ⟨4539591, by rfl⟩ : syracuseStep 12105577 = 9079183) B9079183
theorem B735215 : Blo 734326 735215 := bstep (se 1 (by rfl) ⟨551411, by rfl⟩ : syracuseStep 735215 = 1102823) B1102823
theorem B1652831 : Blo 734326 1652831 := bstep (se 1 (by rfl) ⟨1239623, by rfl⟩ : syracuseStep 1652831 = 2479247) B2479247
theorem B735387 : Blo 734326 735387 := bstep (se 1 (by rfl) ⟨551540, by rfl⟩ : syracuseStep 735387 = 1103081) B1103081
theorem B4044971 : Blo 734326 4044971 := bstep (se 1 (by rfl) ⟨3033728, by rfl⟩ : syracuseStep 4044971 = 6067457) B6067457
theorem B735423 : Blo 734326 735423 := bstep (se 1 (by rfl) ⟨551567, by rfl⟩ : syracuseStep 735423 = 1103135) B1103135
theorem B735535 : Blo 734326 735535 := bstep (se 1 (by rfl) ⟨551651, by rfl⟩ : syracuseStep 735535 = 1103303) B1103303
theorem B932143 : Blo 734326 932143 := bstep (se 1 (by rfl) ⟨699107, by rfl⟩ : syracuseStep 932143 = 1398215) B1398215
theorem B6273409 : Blo 734326 6273409 := bstep (se 2 (by rfl) ⟨2352528, by rfl⟩ : syracuseStep 6273409 = 4705057) B4705057
theorem B5454253 : Blo 734326 5454253 := bstep (se 3 (by rfl) ⟨1022672, by rfl⟩ : syracuseStep 5454253 = 2045345) B2045345
theorem B2242991 : Blo 734326 2242991 := bstep (se 1 (by rfl) ⟨1682243, by rfl⟩ : syracuseStep 2242991 = 3364487) B3364487
theorem B735771 : Blo 734326 735771 := bstep (se 1 (by rfl) ⟨551828, by rfl⟩ : syracuseStep 735771 = 1103657) B1103657
theorem B735775 : Blo 734326 735775 := bstep (se 1 (by rfl) ⟨551831, by rfl⟩ : syracuseStep 735775 = 1103663) B1103663
theorem B5585597 : Blo 734326 5585597 := bstep (se 3 (by rfl) ⟨1047299, by rfl⟩ : syracuseStep 5585597 = 2094599) B2094599
theorem B349223669 : Blo 734326 349223669 := bstep (se 5 (by rfl) ⟨16369859, by rfl⟩ : syracuseStep 349223669 = 32739719) B32739719
theorem B1653587 : Blo 734326 1653587 := bstep (se 1 (by rfl) ⟨1240190, by rfl⟩ : syracuseStep 1653587 = 2480381) B2480381
theorem B736091 : Blo 734326 736091 := bstep (se 1 (by rfl) ⟨552068, by rfl⟩ : syracuseStep 736091 = 1104137) B1104137
theorem B736159 : Blo 734326 736159 := bstep (se 1 (by rfl) ⟨552119, by rfl⟩ : syracuseStep 736159 = 1104239) B1104239
theorem B736303 : Blo 734326 736303 := bstep (se 1 (by rfl) ⟨552227, by rfl⟩ : syracuseStep 736303 = 1104455) B1104455
theorem B736327 : Blo 734326 736327 := bstep (se 1 (by rfl) ⟨552245, by rfl⟩ : syracuseStep 736327 = 1104491) B1104491
theorem B736479 : Blo 734326 736479 := bstep (se 1 (by rfl) ⟨552359, by rfl⟩ : syracuseStep 736479 = 1104719) B1104719
theorem B2800925 : Blo 734326 2800925 := bstep (se 3 (by rfl) ⟨525173, by rfl⟩ : syracuseStep 2800925 = 1050347) B1050347
theorem B1654127 : Blo 734326 1654127 := bstep (se 1 (by rfl) ⟨1240595, by rfl⟩ : syracuseStep 1654127 = 2481191) B2481191
theorem B736743 : Blo 734326 736743 := bstep (se 1 (by rfl) ⟨552557, by rfl⟩ : syracuseStep 736743 = 1105115) B1105115
theorem B736859 : Blo 734326 736859 := bstep (se 1 (by rfl) ⟨552644, by rfl⟩ : syracuseStep 736859 = 1105289) B1105289
theorem B2801243 : Blo 734326 2801243 := bstep (se 1 (by rfl) ⟨2100932, by rfl⟩ : syracuseStep 2801243 = 4201865) B4201865
theorem B1654415 : Blo 734326 1654415 := bstep (se 1 (by rfl) ⟨1240811, by rfl⟩ : syracuseStep 1654415 = 2481623) B2481623
theorem B6274745 : Blo 734326 6274745 := bstep (se 2 (by rfl) ⟨2353029, by rfl⟩ : syracuseStep 6274745 = 4706059) B4706059
theorem B1654505 : Blo 734326 1654505 := bstep (se 2 (by rfl) ⟨620439, by rfl⟩ : syracuseStep 1654505 = 1240879) B1240879
theorem B11321147 : Blo 734326 11321147 := bstep (se 1 (by rfl) ⟨8490860, by rfl⟩ : syracuseStep 11321147 = 16981721) B16981721
theorem B737095 : Blo 734326 737095 := bstep (se 1 (by rfl) ⟨552821, by rfl⟩ : syracuseStep 737095 = 1105643) B1105643
theorem B737247 : Blo 734326 737247 := bstep (se 1 (by rfl) ⟨552935, by rfl⟩ : syracuseStep 737247 = 1105871) B1105871
theorem B21250259 : Blo 734326 21250259 := bstep (se 1 (by rfl) ⟨15937694, by rfl⟩ : syracuseStep 21250259 = 31875389) B31875389
theorem B737511 : Blo 734326 737511 := bstep (se 1 (by rfl) ⟨553133, by rfl⟩ : syracuseStep 737511 = 1106267) B1106267
theorem B737663 : Blo 734326 737663 := bstep (se 1 (by rfl) ⟨553247, by rfl⟩ : syracuseStep 737663 = 1106495) B1106495
theorem B737743 : Blo 734326 737743 := bstep (se 1 (by rfl) ⟨553307, by rfl⟩ : syracuseStep 737743 = 1106615) B1106615
theorem B737895 : Blo 734326 737895 := bstep (se 1 (by rfl) ⟨553421, by rfl⟩ : syracuseStep 737895 = 1106843) B1106843
theorem B1655531 : Blo 734326 1655531 := bstep (se 1 (by rfl) ⟨1241648, by rfl⟩ : syracuseStep 1655531 = 2483297) B2483297
theorem B738159 : Blo 734326 738159 := bstep (se 1 (by rfl) ⟨553619, by rfl⟩ : syracuseStep 738159 = 1107239) B1107239
theorem B738215 : Blo 734326 738215 := bstep (se 1 (by rfl) ⟨553661, by rfl⟩ : syracuseStep 738215 = 1107323) B1107323
theorem B738299 : Blo 734326 738299 := bstep (se 1 (by rfl) ⟨553724, by rfl⟩ : syracuseStep 738299 = 1107449) B1107449
theorem B5588027 : Blo 734326 5588027 := bstep (se 1 (by rfl) ⟨4191020, by rfl⟩ : syracuseStep 5588027 = 8382041) B8382041
theorem B3720815 : Blo 734326 3720815 := bstep (se 1 (by rfl) ⟨2790611, by rfl⟩ : syracuseStep 3720815 = 5581223) B5581223
theorem B1656431 : Blo 734326 1656431 := bstep (se 1 (by rfl) ⟨1242323, by rfl⟩ : syracuseStep 1656431 = 2484647) B2484647
theorem B1656539 : Blo 734326 1656539 := bstep (se 1 (by rfl) ⟨1242404, by rfl⟩ : syracuseStep 1656539 = 2484809) B2484809
theorem B1328891 : Blo 734326 1328891 := bstep (se 1 (by rfl) ⟨996668, by rfl⟩ : syracuseStep 1328891 = 1993337) B1993337
theorem B5654909 : Blo 734326 5654909 := bstep (se 3 (by rfl) ⟨1060295, by rfl⟩ : syracuseStep 5654909 = 2120591) B2120591
theorem B1657655 : Blo 734326 1657655 := bstep (se 1 (by rfl) ⟨1243241, by rfl⟩ : syracuseStep 1657655 = 2486483) B2486483
theorem B1657835 : Blo 734326 1657835 := bstep (se 1 (by rfl) ⟨1243376, by rfl⟩ : syracuseStep 1657835 = 2486753) B2486753
theorem B3722273 : Blo 734326 3722273 := bstep (se 2 (by rfl) ⟨1395852, by rfl⟩ : syracuseStep 3722273 = 2791705) B2791705
theorem B7753097 : Blo 734326 7753097 := bstep (se 2 (by rfl) ⟨2907411, by rfl⟩ : syracuseStep 7753097 = 5814823) B5814823
theorem B17911223 : Blo 734326 17911223 := bstep (se 1 (by rfl) ⟨13433417, by rfl⟩ : syracuseStep 17911223 = 26866835) B26866835
theorem B1101545 : Blo 734326 1101545 := bstep (se 2 (by rfl) ⟨413079, by rfl⟩ : syracuseStep 1101545 = 826159) B826159
theorem B1658663 : Blo 734326 1658663 := bstep (se 1 (by rfl) ⟨1243997, by rfl⟩ : syracuseStep 1658663 = 2487995) B2487995
theorem B1101689 : Blo 734326 1101689 := bstep (se 2 (by rfl) ⟨413133, by rfl⟩ : syracuseStep 1101689 = 826267) B826267
theorem B8376209 : Blo 734326 8376209 := bstep (se 2 (by rfl) ⟨3141078, by rfl⟩ : syracuseStep 8376209 = 6282157) B6282157
theorem B1101791 : Blo 734326 1101791 := bstep (se 1 (by rfl) ⟨826343, by rfl⟩ : syracuseStep 1101791 = 1652687) B1652687
theorem B1396703 : Blo 734326 1396703 := bstep (se 1 (by rfl) ⟨1047527, by rfl⟩ : syracuseStep 1396703 = 2095055) B2095055
theorem B3723245 : Blo 734326 3723245 := bstep (se 3 (by rfl) ⟨698108, by rfl⟩ : syracuseStep 3723245 = 1396217) B1396217
theorem B1888379 : Blo 734326 1888379 := bstep (se 1 (by rfl) ⟨1416284, by rfl⟩ : syracuseStep 1888379 = 2832569) B2832569
theorem B1102043 : Blo 734326 1102043 := bstep (se 1 (by rfl) ⟨826532, by rfl⟩ : syracuseStep 1102043 = 1653065) B1653065
theorem B1102055 : Blo 734326 1102055 := bstep (se 1 (by rfl) ⟨826541, by rfl⟩ : syracuseStep 1102055 = 1653083) B1653083
theorem B1102217 : Blo 734326 1102217 := bstep (se 2 (by rfl) ⟨413331, by rfl⟩ : syracuseStep 1102217 = 826663) B826663
theorem B54514133 : Blo 734326 54514133 := bstep (se 7 (by rfl) ⟨638837, by rfl⟩ : syracuseStep 54514133 = 1277675) B1277675
theorem B1102313 : Blo 734326 1102313 := bstep (se 2 (by rfl) ⟨413367, by rfl⟩ : syracuseStep 1102313 = 826735) B826735
theorem B1102439 : Blo 734326 1102439 := bstep (se 1 (by rfl) ⟨826829, by rfl⟩ : syracuseStep 1102439 = 1653659) B1653659
theorem B2478707 : Blo 734326 2478707 := bstep (se 1 (by rfl) ⟨1859030, by rfl⟩ : syracuseStep 2478707 = 3718061) B3718061
theorem B1102571 : Blo 734326 1102571 := bstep (se 1 (by rfl) ⟨826928, by rfl⟩ : syracuseStep 1102571 = 1653857) B1653857
theorem B1102601 : Blo 734326 1102601 := bstep (se 2 (by rfl) ⟨413475, by rfl⟩ : syracuseStep 1102601 = 826951) B826951
theorem B3724055 : Blo 734326 3724055 := bstep (se 1 (by rfl) ⟨2793041, by rfl⟩ : syracuseStep 3724055 = 5586083) B5586083
theorem B1659689 : Blo 734326 1659689 := bstep (se 2 (by rfl) ⟨622383, by rfl⟩ : syracuseStep 1659689 = 1244767) B1244767
theorem B1102703 : Blo 734326 1102703 := bstep (se 1 (by rfl) ⟨827027, by rfl⟩ : syracuseStep 1102703 = 1654055) B1654055
theorem B2478977 : Blo 734326 2478977 := bstep (se 2 (by rfl) ⟨929616, by rfl⟩ : syracuseStep 2478977 = 1859233) B1859233
theorem B1659959 : Blo 734326 1659959 := bstep (se 1 (by rfl) ⟨1244969, by rfl⟩ : syracuseStep 1659959 = 2489939) B2489939
theorem B1659977 : Blo 734326 1659977 := bstep (se 2 (by rfl) ⟨622491, by rfl⟩ : syracuseStep 1659977 = 1244983) B1244983
theorem B1102955 : Blo 734326 1102955 := bstep (se 1 (by rfl) ⟨827216, by rfl⟩ : syracuseStep 1102955 = 1654433) B1654433
theorem B8967293 : Blo 734326 8967293 := bstep (se 3 (by rfl) ⟨1681367, by rfl⟩ : syracuseStep 8967293 = 3362735) B3362735
theorem B3364051 : Blo 734326 3364051 := bstep (se 1 (by rfl) ⟨2523038, by rfl⟩ : syracuseStep 3364051 = 5046077) B5046077
theorem B1103195 : Blo 734326 1103195 := bstep (se 1 (by rfl) ⟨827396, by rfl⟩ : syracuseStep 1103195 = 1654793) B1654793
theorem B5297633 : Blo 734326 5297633 := bstep (se 2 (by rfl) ⟨1986612, by rfl⟩ : syracuseStep 5297633 = 3973225) B3973225
theorem B1103471 : Blo 734326 1103471 := bstep (se 1 (by rfl) ⟨827603, by rfl⟩ : syracuseStep 1103471 = 1655207) B1655207
theorem B10638971 : Blo 734326 10638971 := bstep (se 1 (by rfl) ⟨7979228, by rfl⟩ : syracuseStep 10638971 = 15958457) B15958457
theorem B325998229 : Blo 734326 325998229 := bstep (se 6 (by rfl) ⟨7640583, by rfl⟩ : syracuseStep 325998229 = 15281167) B15281167
theorem B2479787 : Blo 734326 2479787 := bstep (se 1 (by rfl) ⟨1859840, by rfl⟩ : syracuseStep 2479787 = 3719681) B3719681
theorem B1103543 : Blo 734326 1103543 := bstep (se 1 (by rfl) ⟨827657, by rfl⟩ : syracuseStep 1103543 = 1655315) B1655315
theorem B1103579 : Blo 734326 1103579 := bstep (se 1 (by rfl) ⟨827684, by rfl⟩ : syracuseStep 1103579 = 1655369) B1655369
theorem B1103753 : Blo 734326 1103753 := bstep (se 2 (by rfl) ⟨413907, by rfl⟩ : syracuseStep 1103753 = 827815) B827815
theorem B2480111 : Blo 734326 2480111 := bstep (se 1 (by rfl) ⟨1860083, by rfl⟩ : syracuseStep 2480111 = 3720167) B3720167
theorem B1103855 : Blo 734326 1103855 := bstep (se 1 (by rfl) ⟨827891, by rfl⟩ : syracuseStep 1103855 = 1655783) B1655783
theorem B2480327 : Blo 734326 2480327 := bstep (se 1 (by rfl) ⟨1860245, by rfl⟩ : syracuseStep 2480327 = 3720491) B3720491
theorem B1104107 : Blo 734326 1104107 := bstep (se 1 (by rfl) ⟨828080, by rfl⟩ : syracuseStep 1104107 = 1656161) B1656161
theorem B3528947 : Blo 734326 3528947 := bstep (se 1 (by rfl) ⟨2646710, by rfl⟩ : syracuseStep 3528947 = 5293421) B5293421
theorem B5593373 : Blo 734326 5593373 := bstep (se 3 (by rfl) ⟨1048757, by rfl⟩ : syracuseStep 5593373 = 2097515) B2097515
theorem B1104167 : Blo 734326 1104167 := bstep (se 1 (by rfl) ⟨828125, by rfl⟩ : syracuseStep 1104167 = 1656251) B1656251
theorem B3725675 : Blo 734326 3725675 := bstep (se 1 (by rfl) ⟨2794256, by rfl⟩ : syracuseStep 3725675 = 5588513) B5588513
theorem B1104251 : Blo 734326 1104251 := bstep (se 1 (by rfl) ⟨828188, by rfl⟩ : syracuseStep 1104251 = 1656377) B1656377
theorem B1104521 : Blo 734326 1104521 := bstep (se 2 (by rfl) ⟨414195, by rfl⟩ : syracuseStep 1104521 = 828391) B828391
theorem B1104695 : Blo 734326 1104695 := bstep (se 1 (by rfl) ⟨828521, by rfl⟩ : syracuseStep 1104695 = 1657043) B1657043
theorem B2480975 : Blo 734326 2480975 := bstep (se 1 (by rfl) ⟨1860731, by rfl⟩ : syracuseStep 2480975 = 3721463) B3721463
theorem B3726161 : Blo 734326 3726161 := bstep (se 2 (by rfl) ⟨1397310, by rfl⟩ : syracuseStep 3726161 = 2794621) B2794621
theorem B1104731 : Blo 734326 1104731 := bstep (se 1 (by rfl) ⟨828548, by rfl⟩ : syracuseStep 1104731 = 1657097) B1657097
theorem B1104875 : Blo 734326 1104875 := bstep (se 1 (by rfl) ⟨828656, by rfl⟩ : syracuseStep 1104875 = 1657313) B1657313
theorem B2481299 : Blo 734326 2481299 := bstep (se 1 (by rfl) ⟨1860974, by rfl⟩ : syracuseStep 2481299 = 3721949) B3721949
theorem B1105079 : Blo 734326 1105079 := bstep (se 1 (by rfl) ⟨828809, by rfl⟩ : syracuseStep 1105079 = 1657619) B1657619
theorem B2481569 : Blo 734326 2481569 := bstep (se 2 (by rfl) ⟨930588, by rfl⟩ : syracuseStep 2481569 = 1861177) B1861177
theorem B1105319 : Blo 734326 1105319 := bstep (se 1 (by rfl) ⟨828989, by rfl⟩ : syracuseStep 1105319 = 1657979) B1657979
theorem B1105403 : Blo 734326 1105403 := bstep (se 1 (by rfl) ⟨829052, by rfl⟩ : syracuseStep 1105403 = 1658105) B1658105
theorem B1105499 : Blo 734326 1105499 := bstep (se 1 (by rfl) ⟨829124, by rfl⟩ : syracuseStep 1105499 = 1658249) B1658249
theorem B1105583 : Blo 734326 1105583 := bstep (se 1 (by rfl) ⟨829187, by rfl⟩ : syracuseStep 1105583 = 1658375) B1658375
theorem B3727133 : Blo 734326 3727133 := bstep (se 3 (by rfl) ⟨698837, by rfl⟩ : syracuseStep 3727133 = 1397675) B1397675
theorem B1105703 : Blo 734326 1105703 := bstep (se 1 (by rfl) ⟨829277, by rfl⟩ : syracuseStep 1105703 = 1658555) B1658555
theorem B1105787 : Blo 734326 1105787 := bstep (se 1 (by rfl) ⟨829340, by rfl⟩ : syracuseStep 1105787 = 1658681) B1658681
theorem B2482109 : Blo 734326 2482109 := bstep (se 3 (by rfl) ⟨465395, by rfl⟩ : syracuseStep 2482109 = 930791) B930791
theorem B1106207 : Blo 734326 1106207 := bstep (se 1 (by rfl) ⟨829655, by rfl⟩ : syracuseStep 1106207 = 1659311) B1659311
theorem B1106231 : Blo 734326 1106231 := bstep (se 1 (by rfl) ⟨829673, by rfl⟩ : syracuseStep 1106231 = 1659347) B1659347
theorem B1106303 : Blo 734326 1106303 := bstep (se 1 (by rfl) ⟨829727, by rfl⟩ : syracuseStep 1106303 = 1659455) B1659455
theorem B12771715 : Blo 734326 12771715 := bstep (se 1 (by rfl) ⟨9578786, by rfl⟩ : syracuseStep 12771715 = 19157573) B19157573
theorem B1106375 : Blo 734326 1106375 := bstep (se 1 (by rfl) ⟨829781, by rfl⟩ : syracuseStep 1106375 = 1659563) B1659563
theorem B10084925 : Blo 734326 10084925 := bstep (se 3 (by rfl) ⟨1890923, by rfl⟩ : syracuseStep 10084925 = 3781847) B3781847
theorem B7168621 : Blo 734326 7168621 := bstep (se 3 (by rfl) ⟨1344116, by rfl⟩ : syracuseStep 7168621 = 2688233) B2688233
theorem B1106729 : Blo 734326 1106729 := bstep (se 2 (by rfl) ⟨415023, by rfl⟩ : syracuseStep 1106729 = 830047) B830047
theorem B1106735 : Blo 734326 1106735 := bstep (se 1 (by rfl) ⟨830051, by rfl⟩ : syracuseStep 1106735 = 1660103) B1660103
theorem B746407 : Blo 734326 746407 := bstep (se 1 (by rfl) ⟨559805, by rfl⟩ : syracuseStep 746407 = 1119611) B1119611
theorem B1106855 : Blo 734326 1106855 := bstep (se 1 (by rfl) ⟨830141, by rfl⟩ : syracuseStep 1106855 = 1660283) B1660283
theorem B1106939 : Blo 734326 1106939 := bstep (se 1 (by rfl) ⟨830204, by rfl⟩ : syracuseStep 1106939 = 1660409) B1660409
theorem B1106999 : Blo 734326 1106999 := bstep (se 1 (by rfl) ⟨830249, by rfl⟩ : syracuseStep 1106999 = 1660499) B1660499
theorem B1107119 : Blo 734326 1107119 := bstep (se 1 (by rfl) ⟨830339, by rfl⟩ : syracuseStep 1107119 = 1660679) B1660679
theorem B3728591 : Blo 734326 3728591 := bstep (se 1 (by rfl) ⟨2796443, by rfl⟩ : syracuseStep 3728591 = 5592887) B5592887
theorem B10610027 : Blo 734326 10610027 := bstep (se 1 (by rfl) ⟨7957520, by rfl⟩ : syracuseStep 10610027 = 15915041) B15915041
theorem B79619573 : Blo 734326 79619573 := bstep (se 5 (by rfl) ⟨3732167, by rfl⟩ : syracuseStep 79619573 = 7464335) B7464335
theorem B3532409 : Blo 734326 3532409 := bstep (se 2 (by rfl) ⟨1324653, by rfl⟩ : syracuseStep 3532409 = 2649307) B2649307
theorem B1861339 : Blo 734326 1861339 := bstep (se 1 (by rfl) ⟨1396004, by rfl⟩ : syracuseStep 1861339 = 2792009) B2792009
theorem B2352863 : Blo 734326 2352863 := bstep (se 1 (by rfl) ⟨1764647, by rfl⟩ : syracuseStep 2352863 = 3529295) B3529295
theorem B2483999 : Blo 734326 2483999 := bstep (se 1 (by rfl) ⟨1862999, by rfl⟩ : syracuseStep 2483999 = 3725999) B3725999
theorem B2484215 : Blo 734326 2484215 := bstep (se 1 (by rfl) ⟨1863161, by rfl⟩ : syracuseStep 2484215 = 3726323) B3726323
theorem B2156759 : Blo 734326 2156759 := bstep (se 1 (by rfl) ⟨1617569, by rfl⟩ : syracuseStep 2156759 = 3235139) B3235139
theorem B1239583 : Blo 734326 1239583 := bstep (se 1 (by rfl) ⟨929687, by rfl⟩ : syracuseStep 1239583 = 1859375) B1859375
theorem B4188743 : Blo 734326 4188743 := bstep (se 1 (by rfl) ⟨3141557, by rfl⟩ : syracuseStep 4188743 = 6283115) B6283115
theorem B2091707 : Blo 734326 2091707 := bstep (se 1 (by rfl) ⟨1568780, by rfl⟩ : syracuseStep 2091707 = 3137561) B3137561
theorem B9431801 : Blo 734326 9431801 := bstep (se 2 (by rfl) ⟨3536925, by rfl⟩ : syracuseStep 9431801 = 7073851) B7073851
theorem B2485079 : Blo 734326 2485079 := bstep (se 1 (by rfl) ⟨1863809, by rfl⟩ : syracuseStep 2485079 = 3727619) B3727619
theorem B5303225 : Blo 734326 5303225 := bstep (se 2 (by rfl) ⟨1988709, by rfl⟩ : syracuseStep 5303225 = 3977419) B3977419
theorem B1240015 : Blo 734326 1240015 := bstep (se 1 (by rfl) ⟨930011, by rfl⟩ : syracuseStep 1240015 = 1860023) B1860023
theorem B1862635 : Blo 734326 1862635 := bstep (se 1 (by rfl) ⟨1396976, by rfl⟩ : syracuseStep 1862635 = 2793953) B2793953
theorem B2485295 : Blo 734326 2485295 := bstep (se 1 (by rfl) ⟨1863971, by rfl⟩ : syracuseStep 2485295 = 3727943) B3727943
theorem B1862777 : Blo 734326 1862777 := bstep (se 2 (by rfl) ⟨698541, by rfl⟩ : syracuseStep 1862777 = 1397083) B1397083
theorem B4484231 : Blo 734326 4484231 := bstep (se 1 (by rfl) ⟨3363173, by rfl⟩ : syracuseStep 4484231 = 6726347) B6726347
theorem B2092367 : Blo 734326 2092367 := bstep (se 1 (by rfl) ⟨1569275, by rfl⟩ : syracuseStep 2092367 = 3138551) B3138551
theorem B2485673 : Blo 734326 2485673 := bstep (se 2 (by rfl) ⟨932127, by rfl⟩ : syracuseStep 2485673 = 1864255) B1864255
theorem B1240751 : Blo 734326 1240751 := bstep (se 1 (by rfl) ⟨930563, by rfl⟩ : syracuseStep 1240751 = 1861127) B1861127
theorem B2125673 : Blo 734326 2125673 := bstep (se 2 (by rfl) ⟨797127, by rfl⟩ : syracuseStep 2125673 = 1594255) B1594255
theorem B4255595 : Blo 734326 4255595 := bstep (se 1 (by rfl) ⟨3191696, by rfl⟩ : syracuseStep 4255595 = 6383393) B6383393
theorem B2944907 : Blo 734326 2944907 := bstep (se 1 (by rfl) ⟨2208680, by rfl⟩ : syracuseStep 2944907 = 4417361) B4417361
theorem B2486159 : Blo 734326 2486159 := bstep (se 1 (by rfl) ⟨1864619, by rfl⟩ : syracuseStep 2486159 = 3729239) B3729239
theorem B1240987 : Blo 734326 1240987 := bstep (se 1 (by rfl) ⟨930740, by rfl⟩ : syracuseStep 1240987 = 1861481) B1861481
theorem B1273823 : Blo 734326 1273823 := bstep (se 1 (by rfl) ⟨955367, by rfl⟩ : syracuseStep 1273823 = 1910735) B1910735
theorem B2355389 : Blo 734326 2355389 := bstep (se 3 (by rfl) ⟨441635, by rfl⟩ : syracuseStep 2355389 = 883271) B883271
theorem B2126089 : Blo 734326 2126089 := bstep (se 2 (by rfl) ⟨797283, by rfl⟩ : syracuseStep 2126089 = 1594567) B1594567
theorem B2486537 : Blo 734326 2486537 := bstep (se 2 (by rfl) ⟨932451, by rfl⟩ : syracuseStep 2486537 = 1864903) B1864903
theorem B1241399 : Blo 734326 1241399 := bstep (se 1 (by rfl) ⟨931049, by rfl⟩ : syracuseStep 1241399 = 1862099) B1862099
theorem B1864073 : Blo 734326 1864073 := bstep (se 2 (by rfl) ⟨699027, by rfl⟩ : syracuseStep 1864073 = 1398055) B1398055
theorem B1176329 : Blo 734326 1176329 := bstep (se 2 (by rfl) ⟨441123, by rfl⟩ : syracuseStep 1176329 = 882247) B882247
theorem B1176367 : Blo 734326 1176367 := bstep (se 1 (by rfl) ⟨882275, by rfl⟩ : syracuseStep 1176367 = 1764551) B1764551
theorem B2356219 : Blo 734326 2356219 := bstep (se 1 (by rfl) ⟨1767164, by rfl⟩ : syracuseStep 2356219 = 3534329) B3534329
theorem B1242175 : Blo 734326 1242175 := bstep (se 1 (by rfl) ⟨931631, by rfl⟩ : syracuseStep 1242175 = 1863263) B1863263
theorem B2487671 : Blo 734326 2487671 := bstep (se 1 (by rfl) ⟨1865753, by rfl⟩ : syracuseStep 2487671 = 3731507) B3731507
theorem B1242695 : Blo 734326 1242695 := bstep (se 1 (by rfl) ⟨932021, by rfl⟩ : syracuseStep 1242695 = 1864043) B1864043
theorem B5306107 : Blo 734326 5306107 := bstep (se 1 (by rfl) ⟨3979580, by rfl⟩ : syracuseStep 5306107 = 7959161) B7959161
theorem B1242911 : Blo 734326 1242911 := bstep (se 1 (by rfl) ⟨932183, by rfl⟩ : syracuseStep 1242911 = 1864367) B1864367
theorem B23918489 : Blo 734326 23918489 := bstep (se 2 (by rfl) ⟨8969433, by rfl⟩ : syracuseStep 23918489 = 17938867) B17938867
theorem B1243127 : Blo 734326 1243127 := bstep (se 1 (by rfl) ⟨932345, by rfl⟩ : syracuseStep 1243127 = 1864691) B1864691
theorem B1865825 : Blo 734326 1865825 := bstep (se 2 (by rfl) ⟨699684, by rfl⟩ : syracuseStep 1865825 = 1399369) B1399369
theorem B2488481 : Blo 734326 2488481 := bstep (se 2 (by rfl) ⟨933180, by rfl⟩ : syracuseStep 2488481 = 1866361) B1866361
theorem B1046719 : Blo 734326 1046719 := bstep (se 1 (by rfl) ⟨785039, by rfl⟩ : syracuseStep 1046719 = 1570079) B1570079
theorem B2488751 : Blo 734326 2488751 := bstep (se 1 (by rfl) ⟨1866563, by rfl⟩ : syracuseStep 2488751 = 3733127) B3733127
theorem B4488101 : Blo 734326 4488101 := bstep (se 4 (by rfl) ⟨420759, by rfl⟩ : syracuseStep 4488101 = 841519) B841519
theorem B1244207 : Blo 734326 1244207 := bstep (se 1 (by rfl) ⟨933155, by rfl⟩ : syracuseStep 1244207 = 1866311) B1866311
theorem B4193369 : Blo 734326 4193369 := bstep (se 2 (by rfl) ⟨1572513, by rfl⟩ : syracuseStep 4193369 = 3145027) B3145027
theorem B1244281 : Blo 734326 1244281 := bstep (se 2 (by rfl) ⟨466605, by rfl⟩ : syracuseStep 1244281 = 933211) B933211
theorem B2555009 : Blo 734326 2555009 := bstep (se 2 (by rfl) ⟨958128, by rfl⟩ : syracuseStep 2555009 = 1916257) B1916257
theorem B1244585 : Blo 734326 1244585 := bstep (se 2 (by rfl) ⟨466719, by rfl⟩ : syracuseStep 1244585 = 933439) B933439
theorem B2489831 : Blo 734326 2489831 := bstep (se 1 (by rfl) ⟨1867373, by rfl⟩ : syracuseStep 2489831 = 3734747) B3734747
theorem B1048297 : Blo 734326 1048297 := bstep (se 2 (by rfl) ⟨393111, by rfl⟩ : syracuseStep 1048297 = 786223) B786223
theorem B1245611 : Blo 734326 1245611 := bstep (se 1 (by rfl) ⟨934208, by rfl⟩ : syracuseStep 1245611 = 1868417) B1868417
theorem B2490911 : Blo 734326 2490911 := bstep (se 1 (by rfl) ⟨1868183, by rfl⟩ : syracuseStep 2490911 = 3736367) B3736367
theorem B8061535 : Blo 734326 8061535 := bstep (se 1 (by rfl) ⟨6046151, by rfl⟩ : syracuseStep 8061535 = 12092303) B12092303
theorem B1770491 : Blo 734326 1770491 := bstep (se 1 (by rfl) ⟨1327868, by rfl⟩ : syracuseStep 1770491 = 2655737) B2655737
theorem B3408911 : Blo 734326 3408911 := bstep (se 1 (by rfl) ⟨2556683, by rfl⟩ : syracuseStep 3408911 = 5113367) B5113367
theorem B4195577 : Blo 734326 4195577 := bstep (se 2 (by rfl) ⟨1573341, by rfl⟩ : syracuseStep 4195577 = 3146683) B3146683
theorem B1180975 : Blo 734326 1180975 := bstep (se 1 (by rfl) ⟨885731, by rfl⟩ : syracuseStep 1180975 = 1771463) B1771463
theorem B4195759 : Blo 734326 4195759 := bstep (se 1 (by rfl) ⟨3146819, by rfl⟩ : syracuseStep 4195759 = 6293639) B6293639
theorem B3769939 : Blo 734326 3769939 := bstep (se 1 (by rfl) ⟨2827454, by rfl⟩ : syracuseStep 3769939 = 5654909) B5654909
theorem B1574777 : Blo 734326 1574777 := bstep (se 2 (by rfl) ⟨590541, by rfl⟩ : syracuseStep 1574777 = 1181083) B1181083
theorem B36342755 : Blo 734326 36342755 := bstep (se 1 (by rfl) ⟨27257066, by rfl⟩ : syracuseStep 36342755 = 54514133) B54514133
theorem B1575931 : Blo 734326 1575931 := bstep (se 1 (by rfl) ⟨1181948, by rfl⟩ : syracuseStep 1575931 = 2363897) B2363897
theorem B1576417 : Blo 734326 1576417 := bstep (se 2 (by rfl) ⟨591156, by rfl⟩ : syracuseStep 1576417 = 1182313) B1182313
theorem B2101115 : Blo 734326 2101115 := bstep (se 1 (by rfl) ⟨1575836, by rfl⟩ : syracuseStep 2101115 = 3151673) B3151673
theorem B1773623 : Blo 734326 1773623 := bstep (se 1 (by rfl) ⟨1330217, by rfl⟩ : syracuseStep 1773623 = 2660435) B2660435
theorem B6296615 : Blo 734326 6296615 := bstep (se 1 (by rfl) ⟨4722461, by rfl⟩ : syracuseStep 6296615 = 9444923) B9444923
theorem B3544519 : Blo 734326 3544519 := bstep (se 1 (by rfl) ⟨2658389, by rfl⟩ : syracuseStep 3544519 = 5316779) B5316779
theorem B1381871 : Blo 734326 1381871 := bstep (se 1 (by rfl) ⟨1036403, by rfl⟩ : syracuseStep 1381871 = 2072807) B2072807
theorem B35755505 : Blo 734326 35755505 := bstep (se 2 (by rfl) ⟨13408314, by rfl⟩ : syracuseStep 35755505 = 26816629) B26816629
theorem B6723283 : Blo 734326 6723283 := bstep (se 1 (by rfl) ⟨5042462, by rfl⟩ : syracuseStep 6723283 = 10084925) B10084925
theorem B9410525 : Blo 734326 9410525 := bstep (se 3 (by rfl) ⟨1764473, by rfl⟩ : syracuseStep 9410525 = 3528947) B3528947
theorem B1677665 : Blo 734326 1677665 := bstep (se 2 (by rfl) ⟨629124, by rfl⟩ : syracuseStep 1677665 = 1258249) B1258249
theorem B4201409 : Blo 734326 4201409 := bstep (se 2 (by rfl) ⟨1575528, by rfl⟩ : syracuseStep 4201409 = 3151057) B3151057
theorem B2792495 : Blo 734326 2792495 := bstep (se 1 (by rfl) ⟨2094371, by rfl⟩ : syracuseStep 2792495 = 4188743) B4188743
theorem B2989487 : Blo 734326 2989487 := bstep (se 1 (by rfl) ⟨2242115, by rfl⟩ : syracuseStep 2989487 = 4484231) B4484231
theorem B3546767 : Blo 734326 3546767 := bstep (se 1 (by rfl) ⟨2660075, by rfl⟩ : syracuseStep 3546767 = 5320151) B5320151
theorem B827167 : Blo 734326 827167 := bstep (se 1 (by rfl) ⟨620375, by rfl⟩ : syracuseStep 827167 = 1240751) B1240751
theorem B1515419 : Blo 734326 1515419 := bstep (se 1 (by rfl) ⟨1136564, by rfl⟩ : syracuseStep 1515419 = 2273129) B2273129
theorem B1417115 : Blo 734326 1417115 := bstep (se 1 (by rfl) ⟨1062836, by rfl⟩ : syracuseStep 1417115 = 2125673) B2125673
theorem B827599 : Blo 734326 827599 := bstep (se 1 (by rfl) ⟨620699, by rfl⟩ : syracuseStep 827599 = 1241399) B1241399
theorem B8364545 : Blo 734326 8364545 := bstep (se 2 (by rfl) ⟨3136704, by rfl⟩ : syracuseStep 8364545 = 6273409) B6273409
theorem B828463 : Blo 734326 828463 := bstep (se 1 (by rfl) ⟨621347, by rfl⟩ : syracuseStep 828463 = 1242695) B1242695
theorem B828607 : Blo 734326 828607 := bstep (se 1 (by rfl) ⟨621455, by rfl⟩ : syracuseStep 828607 = 1242911) B1242911
theorem B6300989 : Blo 734326 6300989 := bstep (se 3 (by rfl) ⟨1181435, by rfl⟩ : syracuseStep 6300989 = 2362871) B2362871
theorem B828751 : Blo 734326 828751 := bstep (se 1 (by rfl) ⟨621563, by rfl⟩ : syracuseStep 828751 = 1243127) B1243127
theorem B2696647 : Blo 734326 2696647 := bstep (se 1 (by rfl) ⟨2022485, by rfl⟩ : syracuseStep 2696647 = 4044971) B4044971
theorem B64563077 : Blo 734326 64563077 := bstep (se 4 (by rfl) ⟨6052788, by rfl⟩ : syracuseStep 64563077 = 12105577) B12105577
theorem B2992067 : Blo 734326 2992067 := bstep (se 1 (by rfl) ⟨2244050, by rfl⟩ : syracuseStep 2992067 = 4488101) B4488101
theorem B829471 : Blo 734326 829471 := bstep (se 1 (by rfl) ⟨622103, by rfl⟩ : syracuseStep 829471 = 1244207) B1244207
theorem B2795579 : Blo 734326 2795579 := bstep (se 1 (by rfl) ⟨2096684, by rfl⟩ : syracuseStep 2795579 = 4193369) B4193369
theorem B30189725 : Blo 734326 30189725 := bstep (se 3 (by rfl) ⟨5660573, by rfl⟩ : syracuseStep 30189725 = 11321147) B11321147
theorem B829723 : Blo 734326 829723 := bstep (se 1 (by rfl) ⟨622292, by rfl⟩ : syracuseStep 829723 = 1244585) B1244585
theorem B14166839 : Blo 734326 14166839 := bstep (se 1 (by rfl) ⟨10625129, by rfl⟩ : syracuseStep 14166839 = 21250259) B21250259
theorem B2796839 : Blo 734326 2796839 := bstep (se 1 (by rfl) ⟨2097629, by rfl⟩ : syracuseStep 2796839 = 4195259) B4195259
theorem B995209 : Blo 734326 995209 := bstep (se 2 (by rfl) ⟨373203, by rfl⟩ : syracuseStep 995209 = 746407) B746407
theorem B2798023 : Blo 734326 2798023 := bstep (se 1 (by rfl) ⟨2098517, by rfl⟩ : syracuseStep 2798023 = 4197035) B4197035
theorem B11940815 : Blo 734326 11940815 := bstep (se 1 (by rfl) ⟨8955611, by rfl⟩ : syracuseStep 11940815 = 17911223) B17911223
theorem B734363 : Blo 734326 734363 := bstep (se 1 (by rfl) ⟨550772, by rfl⟩ : syracuseStep 734363 = 1101545) B1101545
theorem B734459 : Blo 734326 734459 := bstep (se 1 (by rfl) ⟨550844, by rfl⟩ : syracuseStep 734459 = 1101689) B1101689
theorem B5584139 : Blo 734326 5584139 := bstep (se 1 (by rfl) ⟨4188104, by rfl⟩ : syracuseStep 5584139 = 8376209) B8376209
theorem B734527 : Blo 734326 734527 := bstep (se 1 (by rfl) ⟨550895, by rfl⟩ : syracuseStep 734527 = 1101791) B1101791
theorem B11974031 : Blo 734326 11974031 := bstep (se 1 (by rfl) ⟨8980523, by rfl⟩ : syracuseStep 11974031 = 17961047) B17961047
theorem B1258919 : Blo 734326 1258919 := bstep (se 1 (by rfl) ⟨944189, by rfl⟩ : syracuseStep 1258919 = 1888379) B1888379
theorem B734695 : Blo 734326 734695 := bstep (se 1 (by rfl) ⟨551021, by rfl⟩ : syracuseStep 734695 = 1102043) B1102043
theorem B734703 : Blo 734326 734703 := bstep (se 1 (by rfl) ⟨551027, by rfl⟩ : syracuseStep 734703 = 1102055) B1102055
theorem B734811 : Blo 734326 734811 := bstep (se 1 (by rfl) ⟨551108, by rfl⟩ : syracuseStep 734811 = 1102217) B1102217
theorem B12760685 : Blo 734326 12760685 := bstep (se 3 (by rfl) ⟨2392628, by rfl⟩ : syracuseStep 12760685 = 4785257) B4785257
theorem B734875 : Blo 734326 734875 := bstep (se 1 (by rfl) ⟨551156, by rfl⟩ : syracuseStep 734875 = 1102313) B1102313
theorem B734959 : Blo 734326 734959 := bstep (se 1 (by rfl) ⟨551219, by rfl⟩ : syracuseStep 734959 = 1102439) B1102439
theorem B1652471 : Blo 734326 1652471 := bstep (se 1 (by rfl) ⟨1239353, by rfl⟩ : syracuseStep 1652471 = 2478707) B2478707
theorem B735047 : Blo 734326 735047 := bstep (se 1 (by rfl) ⟨551285, by rfl⟩ : syracuseStep 735047 = 1102571) B1102571
theorem B735067 : Blo 734326 735067 := bstep (se 1 (by rfl) ⟨551300, by rfl⟩ : syracuseStep 735067 = 1102601) B1102601
theorem B735135 : Blo 734326 735135 := bstep (se 1 (by rfl) ⟨551351, by rfl⟩ : syracuseStep 735135 = 1102703) B1102703
theorem B1652651 : Blo 734326 1652651 := bstep (se 1 (by rfl) ⟨1239488, by rfl⟩ : syracuseStep 1652651 = 2478977) B2478977
theorem B9418679 : Blo 734326 9418679 := bstep (se 1 (by rfl) ⟨7064009, by rfl⟩ : syracuseStep 9418679 = 14128019) B14128019
theorem B1652777 : Blo 734326 1652777 := bstep (se 2 (by rfl) ⟨619791, by rfl⟩ : syracuseStep 1652777 = 1239583) B1239583
theorem B735303 : Blo 734326 735303 := bstep (se 1 (by rfl) ⟨551477, by rfl⟩ : syracuseStep 735303 = 1102955) B1102955
theorem B5978195 : Blo 734326 5978195 := bstep (se 1 (by rfl) ⟨4483646, by rfl⟩ : syracuseStep 5978195 = 8967293) B8967293
theorem B2799755 : Blo 734326 2799755 := bstep (se 1 (by rfl) ⟨2099816, by rfl⟩ : syracuseStep 2799755 = 4199633) B4199633
theorem B7977151 : Blo 734326 7977151 := bstep (se 1 (by rfl) ⟨5982863, by rfl⟩ : syracuseStep 7977151 = 11965727) B11965727
theorem B735463 : Blo 734326 735463 := bstep (se 1 (by rfl) ⟨551597, by rfl⟩ : syracuseStep 735463 = 1103195) B1103195
theorem B735647 : Blo 734326 735647 := bstep (se 1 (by rfl) ⟨551735, by rfl⟩ : syracuseStep 735647 = 1103471) B1103471
theorem B7092647 : Blo 734326 7092647 := bstep (se 1 (by rfl) ⟨5319485, by rfl⟩ : syracuseStep 7092647 = 10638971) B10638971
theorem B1653191 : Blo 734326 1653191 := bstep (se 1 (by rfl) ⟨1239893, by rfl⟩ : syracuseStep 1653191 = 2479787) B2479787
theorem B735695 : Blo 734326 735695 := bstep (se 1 (by rfl) ⟨551771, by rfl⟩ : syracuseStep 735695 = 1103543) B1103543
theorem B735719 : Blo 734326 735719 := bstep (se 1 (by rfl) ⟨551789, by rfl⟩ : syracuseStep 735719 = 1103579) B1103579
theorem B735835 : Blo 734326 735835 := bstep (se 1 (by rfl) ⟨551876, by rfl⟩ : syracuseStep 735835 = 1103753) B1103753
theorem B1653353 : Blo 734326 1653353 := bstep (se 2 (by rfl) ⟨620007, by rfl⟩ : syracuseStep 1653353 = 1240015) B1240015
theorem B2800271 : Blo 734326 2800271 := bstep (se 1 (by rfl) ⟨2100203, by rfl⟩ : syracuseStep 2800271 = 4200407) B4200407
theorem B1653407 : Blo 734326 1653407 := bstep (se 1 (by rfl) ⟨1240055, by rfl⟩ : syracuseStep 1653407 = 2480111) B2480111
theorem B735903 : Blo 734326 735903 := bstep (se 1 (by rfl) ⟨551927, by rfl⟩ : syracuseStep 735903 = 1103855) B1103855
theorem B1653551 : Blo 734326 1653551 := bstep (se 1 (by rfl) ⟨1240163, by rfl⟩ : syracuseStep 1653551 = 2480327) B2480327
theorem B736071 : Blo 734326 736071 := bstep (se 1 (by rfl) ⟨552053, by rfl⟩ : syracuseStep 736071 = 1104107) B1104107
theorem B736111 : Blo 734326 736111 := bstep (se 1 (by rfl) ⟨552083, by rfl⟩ : syracuseStep 736111 = 1104167) B1104167
theorem B7060355 : Blo 734326 7060355 := bstep (se 1 (by rfl) ⟨5295266, by rfl⟩ : syracuseStep 7060355 = 10590533) B10590533
theorem B9419651 : Blo 734326 9419651 := bstep (se 1 (by rfl) ⟨7064738, by rfl⟩ : syracuseStep 9419651 = 14129477) B14129477
theorem B736167 : Blo 734326 736167 := bstep (se 1 (by rfl) ⟨552125, by rfl⟩ : syracuseStep 736167 = 1104251) B1104251
theorem B736347 : Blo 734326 736347 := bstep (se 1 (by rfl) ⟨552260, by rfl⟩ : syracuseStep 736347 = 1104521) B1104521
theorem B736463 : Blo 734326 736463 := bstep (se 1 (by rfl) ⟨552347, by rfl⟩ : syracuseStep 736463 = 1104695) B1104695
theorem B1653983 : Blo 734326 1653983 := bstep (se 1 (by rfl) ⟨1240487, by rfl⟩ : syracuseStep 1653983 = 2480975) B2480975
theorem B736487 : Blo 734326 736487 := bstep (se 1 (by rfl) ⟨552365, by rfl⟩ : syracuseStep 736487 = 1104731) B1104731
theorem B736583 : Blo 734326 736583 := bstep (se 1 (by rfl) ⟨552437, by rfl⟩ : syracuseStep 736583 = 1104875) B1104875
theorem B1654199 : Blo 734326 1654199 := bstep (se 1 (by rfl) ⟨1240649, by rfl⟩ : syracuseStep 1654199 = 2481299) B2481299
theorem B736719 : Blo 734326 736719 := bstep (se 1 (by rfl) ⟨552539, by rfl⟩ : syracuseStep 736719 = 1105079) B1105079
theorem B1654379 : Blo 734326 1654379 := bstep (se 1 (by rfl) ⟨1240784, by rfl⟩ : syracuseStep 1654379 = 2481569) B2481569
theorem B736879 : Blo 734326 736879 := bstep (se 1 (by rfl) ⟨552659, by rfl⟩ : syracuseStep 736879 = 1105319) B1105319
theorem B736935 : Blo 734326 736935 := bstep (se 1 (by rfl) ⟨552701, by rfl⟩ : syracuseStep 736935 = 1105403) B1105403
theorem B736999 : Blo 734326 736999 := bstep (se 1 (by rfl) ⟨552749, by rfl⟩ : syracuseStep 736999 = 1105499) B1105499
theorem B737055 : Blo 734326 737055 := bstep (se 1 (by rfl) ⟨552791, by rfl⟩ : syracuseStep 737055 = 1105583) B1105583
theorem B737135 : Blo 734326 737135 := bstep (se 1 (by rfl) ⟨552851, by rfl⟩ : syracuseStep 737135 = 1105703) B1105703
theorem B1654649 : Blo 734326 1654649 := bstep (se 2 (by rfl) ⟨620493, by rfl⟩ : syracuseStep 1654649 = 1240987) B1240987
theorem B737191 : Blo 734326 737191 := bstep (se 1 (by rfl) ⟨552893, by rfl⟩ : syracuseStep 737191 = 1105787) B1105787
theorem B1654739 : Blo 734326 1654739 := bstep (se 1 (by rfl) ⟨1241054, by rfl⟩ : syracuseStep 1654739 = 2482109) B2482109
theorem B12566501 : Blo 734326 12566501 := bstep (se 4 (by rfl) ⟨1178109, by rfl⟩ : syracuseStep 12566501 = 2356219) B2356219
theorem B737471 : Blo 734326 737471 := bstep (se 1 (by rfl) ⟨553103, by rfl⟩ : syracuseStep 737471 = 1106207) B1106207
theorem B737487 : Blo 734326 737487 := bstep (se 1 (by rfl) ⟨553115, by rfl⟩ : syracuseStep 737487 = 1106231) B1106231
theorem B737535 : Blo 734326 737535 := bstep (se 1 (by rfl) ⟨553151, by rfl⟩ : syracuseStep 737535 = 1106303) B1106303
theorem B737583 : Blo 734326 737583 := bstep (se 1 (by rfl) ⟨553187, by rfl⟩ : syracuseStep 737583 = 1106375) B1106375
theorem B12763453 : Blo 734326 12763453 := bstep (se 3 (by rfl) ⟨2393147, by rfl⟩ : syracuseStep 12763453 = 4786295) B4786295
theorem B2834785 : Blo 734326 2834785 := bstep (se 2 (by rfl) ⟨1063044, by rfl⟩ : syracuseStep 2834785 = 2126089) B2126089
theorem B737819 : Blo 734326 737819 := bstep (se 1 (by rfl) ⟨553364, by rfl⟩ : syracuseStep 737819 = 1106729) B1106729
theorem B737823 : Blo 734326 737823 := bstep (se 1 (by rfl) ⟨553367, by rfl⟩ : syracuseStep 737823 = 1106735) B1106735
theorem B737903 : Blo 734326 737903 := bstep (se 1 (by rfl) ⟨553427, by rfl⟩ : syracuseStep 737903 = 1106855) B1106855
theorem B737959 : Blo 734326 737959 := bstep (se 1 (by rfl) ⟨553469, by rfl⟩ : syracuseStep 737959 = 1106939) B1106939
theorem B737999 : Blo 734326 737999 := bstep (se 1 (by rfl) ⟨553499, by rfl⟩ : syracuseStep 737999 = 1106999) B1106999
theorem B738079 : Blo 734326 738079 := bstep (se 1 (by rfl) ⟨553559, by rfl⟩ : syracuseStep 738079 = 1107119) B1107119
theorem B5981309 : Blo 734326 5981309 := bstep (se 3 (by rfl) ⟨1121495, by rfl⟩ : syracuseStep 5981309 = 2242991) B2242991
theorem B1655999 : Blo 734326 1655999 := bstep (se 1 (by rfl) ⟨1241999, by rfl⟩ : syracuseStep 1655999 = 2483999) B2483999
theorem B1656143 : Blo 734326 1656143 := bstep (se 1 (by rfl) ⟨1242107, by rfl⟩ : syracuseStep 1656143 = 2484215) B2484215
theorem B1656233 : Blo 734326 1656233 := bstep (se 2 (by rfl) ⟨621087, by rfl⟩ : syracuseStep 1656233 = 1242175) B1242175
theorem B9553427 : Blo 734326 9553427 := bstep (se 1 (by rfl) ⟨7165070, by rfl⟩ : syracuseStep 9553427 = 14330141) B14330141
theorem B1394471 : Blo 734326 1394471 := bstep (se 1 (by rfl) ⟨1045853, by rfl⟩ : syracuseStep 1394471 = 2091707) B2091707
theorem B1656719 : Blo 734326 1656719 := bstep (se 1 (by rfl) ⟨1242539, by rfl⟩ : syracuseStep 1656719 = 2485079) B2485079
theorem B1656863 : Blo 734326 1656863 := bstep (se 1 (by rfl) ⟨1242647, by rfl⟩ : syracuseStep 1656863 = 2485295) B2485295
theorem B1394911 : Blo 734326 1394911 := bstep (se 1 (by rfl) ⟨1046183, by rfl⟩ : syracuseStep 1394911 = 2092367) B2092367
theorem B1657115 : Blo 734326 1657115 := bstep (se 1 (by rfl) ⟨1242836, by rfl⟩ : syracuseStep 1657115 = 2485673) B2485673
theorem B9456041 : Blo 734326 9456041 := bstep (se 2 (by rfl) ⟨3546015, by rfl⟩ : syracuseStep 9456041 = 7092031) B7092031
theorem B2837063 : Blo 734326 2837063 := bstep (se 1 (by rfl) ⟨2127797, by rfl⟩ : syracuseStep 2837063 = 4255595) B4255595
theorem B1657439 : Blo 734326 1657439 := bstep (se 1 (by rfl) ⟨1243079, by rfl⟩ : syracuseStep 1657439 = 2486159) B2486159
theorem B14174837 : Blo 734326 14174837 := bstep (se 5 (by rfl) ⟨664445, by rfl⟩ : syracuseStep 14174837 = 1328891) B1328891
theorem B1657691 : Blo 734326 1657691 := bstep (se 1 (by rfl) ⟨1243268, by rfl⟩ : syracuseStep 1657691 = 2486537) B2486537
theorem B1395625 : Blo 734326 1395625 := bstep (se 2 (by rfl) ⟨523359, by rfl⟩ : syracuseStep 1395625 = 1046719) B1046719
theorem B1658447 : Blo 734326 1658447 := bstep (se 1 (by rfl) ⟨1243835, by rfl⟩ : syracuseStep 1658447 = 2487671) B2487671
theorem B1101695 : Blo 734326 1101695 := bstep (se 1 (by rfl) ⟨826271, by rfl⟩ : syracuseStep 1101695 = 1652543) B1652543
theorem B15945659 : Blo 734326 15945659 := bstep (se 1 (by rfl) ⟨11959244, by rfl⟩ : syracuseStep 15945659 = 23918489) B23918489
theorem B1101887 : Blo 734326 1101887 := bstep (se 1 (by rfl) ⟨826415, by rfl⟩ : syracuseStep 1101887 = 1652831) B1652831
theorem B1658987 : Blo 734326 1658987 := bstep (se 1 (by rfl) ⟨1244240, by rfl⟩ : syracuseStep 1658987 = 2488481) B2488481
theorem B1659041 : Blo 734326 1659041 := bstep (se 2 (by rfl) ⟨622140, by rfl⟩ : syracuseStep 1659041 = 1244281) B1244281
theorem B1659167 : Blo 734326 1659167 := bstep (se 1 (by rfl) ⟨1244375, by rfl⟩ : syracuseStep 1659167 = 2488751) B2488751
theorem B1102121 : Blo 734326 1102121 := bstep (se 2 (by rfl) ⟨413295, by rfl⟩ : syracuseStep 1102121 = 826591) B826591
theorem B3723731 : Blo 734326 3723731 := bstep (se 1 (by rfl) ⟨2792798, by rfl⟩ : syracuseStep 3723731 = 5585597) B5585597
theorem B1102391 : Blo 734326 1102391 := bstep (se 1 (by rfl) ⟨826793, by rfl⟩ : syracuseStep 1102391 = 1653587) B1653587
theorem B1102751 : Blo 734326 1102751 := bstep (se 1 (by rfl) ⟨827063, by rfl⟩ : syracuseStep 1102751 = 1654127) B1654127
theorem B1397729 : Blo 734326 1397729 := bstep (se 2 (by rfl) ⟨524148, by rfl⟩ : syracuseStep 1397729 = 1048297) B1048297
theorem B1659887 : Blo 734326 1659887 := bstep (se 1 (by rfl) ⟨1244915, by rfl⟩ : syracuseStep 1659887 = 2489831) B2489831
theorem B1102943 : Blo 734326 1102943 := bstep (se 1 (by rfl) ⟨827207, by rfl⟩ : syracuseStep 1102943 = 1654415) B1654415
theorem B4183163 : Blo 734326 4183163 := bstep (se 1 (by rfl) ⟨3137372, by rfl⟩ : syracuseStep 4183163 = 6274745) B6274745
theorem B1103003 : Blo 734326 1103003 := bstep (se 1 (by rfl) ⟨827252, by rfl⟩ : syracuseStep 1103003 = 1654505) B1654505
theorem B3724541 : Blo 734326 3724541 := bstep (se 3 (by rfl) ⟨698351, by rfl⟩ : syracuseStep 3724541 = 1396703) B1396703
theorem B13981081 : Blo 734326 13981081 := bstep (se 2 (by rfl) ⟨5242905, by rfl⟩ : syracuseStep 13981081 = 10485811) B10485811
theorem B1660391 : Blo 734326 1660391 := bstep (se 1 (by rfl) ⟨1245293, by rfl⟩ : syracuseStep 1660391 = 2490587) B2490587
theorem B1660553 : Blo 734326 1660553 := bstep (se 2 (by rfl) ⟨622707, by rfl⟩ : syracuseStep 1660553 = 1245415) B1245415
theorem B1660571 : Blo 734326 1660571 := bstep (se 1 (by rfl) ⟨1245428, by rfl⟩ : syracuseStep 1660571 = 2490857) B2490857
theorem B1103687 : Blo 734326 1103687 := bstep (se 1 (by rfl) ⟨827765, by rfl⟩ : syracuseStep 1103687 = 1655531) B1655531
theorem B17028953 : Blo 734326 17028953 := bstep (se 2 (by rfl) ⟨6385857, by rfl⟩ : syracuseStep 17028953 = 12771715) B12771715
theorem B1660769 : Blo 734326 1660769 := bstep (se 2 (by rfl) ⟨622788, by rfl⟩ : syracuseStep 1660769 = 1245577) B1245577
theorem B3725351 : Blo 734326 3725351 := bstep (se 1 (by rfl) ⟨2794013, by rfl⟩ : syracuseStep 3725351 = 5588027) B5588027
theorem B1660967 : Blo 734326 1660967 := bstep (se 1 (by rfl) ⟨1245725, by rfl⟩ : syracuseStep 1660967 = 2491451) B2491451
theorem B9558161 : Blo 734326 9558161 := bstep (se 2 (by rfl) ⟨3584310, by rfl⟩ : syracuseStep 9558161 = 7168621) B7168621
theorem B1661147 : Blo 734326 1661147 := bstep (se 1 (by rfl) ⟨1245860, by rfl⟩ : syracuseStep 1661147 = 2491721) B2491721
theorem B2480543 : Blo 734326 2480543 := bstep (se 1 (by rfl) ⟨1860407, by rfl⟩ : syracuseStep 2480543 = 3720815) B3720815
theorem B1104287 : Blo 734326 1104287 := bstep (se 1 (by rfl) ⟨828215, by rfl⟩ : syracuseStep 1104287 = 1656431) B1656431
theorem B1104359 : Blo 734326 1104359 := bstep (se 1 (by rfl) ⟨828269, by rfl⟩ : syracuseStep 1104359 = 1656539) B1656539
theorem B1399855 : Blo 734326 1399855 := bstep (se 1 (by rfl) ⟨1049891, by rfl⟩ : syracuseStep 1399855 = 2099783) B2099783
theorem B1105103 : Blo 734326 1105103 := bstep (se 1 (by rfl) ⟨828827, by rfl⟩ : syracuseStep 1105103 = 1657655) B1657655
theorem B1105223 : Blo 734326 1105223 := bstep (se 1 (by rfl) ⟨828917, by rfl⟩ : syracuseStep 1105223 = 1657835) B1657835
theorem B2481515 : Blo 734326 2481515 := bstep (se 1 (by rfl) ⟨1861136, by rfl⟩ : syracuseStep 2481515 = 3722273) B3722273
theorem B3136877 : Blo 734326 3136877 := bstep (se 3 (by rfl) ⟨588164, by rfl⟩ : syracuseStep 3136877 = 1176329) B1176329
theorem B1105385 : Blo 734326 1105385 := bstep (se 2 (by rfl) ⟨414519, by rfl⟩ : syracuseStep 1105385 = 829039) B829039
theorem B5168731 : Blo 734326 5168731 := bstep (se 1 (by rfl) ⟨3876548, by rfl⟩ : syracuseStep 5168731 = 7753097) B7753097
theorem B2481785 : Blo 734326 2481785 := bstep (se 2 (by rfl) ⟨930669, by rfl⟩ : syracuseStep 2481785 = 1861339) B1861339
theorem B1105529 : Blo 734326 1105529 := bstep (se 2 (by rfl) ⟨414573, by rfl⟩ : syracuseStep 1105529 = 829147) B829147
theorem B1105775 : Blo 734326 1105775 := bstep (se 1 (by rfl) ⟨829331, by rfl⟩ : syracuseStep 1105775 = 1658663) B1658663
theorem B2482163 : Blo 734326 2482163 := bstep (se 1 (by rfl) ⟨1861622, by rfl⟩ : syracuseStep 2482163 = 3723245) B3723245
theorem B2482703 : Blo 734326 2482703 := bstep (se 1 (by rfl) ⟨1862027, by rfl⟩ : syracuseStep 2482703 = 3724055) B3724055
theorem B1106459 : Blo 734326 1106459 := bstep (se 1 (by rfl) ⟨829844, by rfl⟩ : syracuseStep 1106459 = 1659689) B1659689
theorem B1106639 : Blo 734326 1106639 := bstep (se 1 (by rfl) ⟨829979, by rfl⟩ : syracuseStep 1106639 = 1659959) B1659959
theorem B1106651 : Blo 734326 1106651 := bstep (se 1 (by rfl) ⟨829988, by rfl⟩ : syracuseStep 1106651 = 1659977) B1659977
theorem B1401563 : Blo 734326 1401563 := bstep (se 1 (by rfl) ⟨1051172, by rfl⟩ : syracuseStep 1401563 = 2102345) B2102345
theorem B3531755 : Blo 734326 3531755 := bstep (se 1 (by rfl) ⟨2648816, by rfl⟩ : syracuseStep 3531755 = 5297633) B5297633
theorem B1107065 : Blo 734326 1107065 := bstep (se 2 (by rfl) ⟨415149, by rfl⟩ : syracuseStep 1107065 = 830299) B830299
theorem B2483513 : Blo 734326 2483513 := bstep (se 2 (by rfl) ⟨931317, by rfl⟩ : syracuseStep 2483513 = 1862635) B1862635
theorem B3728915 : Blo 734326 3728915 := bstep (se 1 (by rfl) ⟨2796686, by rfl⟩ : syracuseStep 3728915 = 5593373) B5593373
theorem B2483783 : Blo 734326 2483783 := bstep (se 1 (by rfl) ⟨1862837, by rfl⟩ : syracuseStep 2483783 = 3725675) B3725675
theorem B2483837 : Blo 734326 2483837 := bstep (se 3 (by rfl) ⟨465719, by rfl⟩ : syracuseStep 2483837 = 931439) B931439
theorem B2484107 : Blo 734326 2484107 := bstep (se 1 (by rfl) ⟨1863080, by rfl⟩ : syracuseStep 2484107 = 3726161) B3726161
theorem B1861775 : Blo 734326 1861775 := bstep (se 1 (by rfl) ⟨1396331, by rfl⟩ : syracuseStep 1861775 = 2792663) B2792663
theorem B2484755 : Blo 734326 2484755 := bstep (se 1 (by rfl) ⟨1863566, by rfl⟩ : syracuseStep 2484755 = 3727133) B3727133
theorem B2517551 : Blo 734326 2517551 := bstep (se 1 (by rfl) ⟨1888163, by rfl⟩ : syracuseStep 2517551 = 3776327) B3776327
theorem B2485727 : Blo 734326 2485727 := bstep (se 1 (by rfl) ⟨1864295, by rfl⟩ : syracuseStep 2485727 = 3728591) B3728591
theorem B7073351 : Blo 734326 7073351 := bstep (se 1 (by rfl) ⟨5305013, by rfl⟩ : syracuseStep 7073351 = 10610027) B10610027
theorem B53079715 : Blo 734326 53079715 := bstep (se 1 (by rfl) ⟨39809786, by rfl⟩ : syracuseStep 53079715 = 79619573) B79619573
theorem B1568489 : Blo 734326 1568489 := bstep (se 2 (by rfl) ⟨588183, by rfl⟩ : syracuseStep 1568489 = 1176367) B1176367
theorem B2354939 : Blo 734326 2354939 := bstep (se 1 (by rfl) ⟨1766204, by rfl⟩ : syracuseStep 2354939 = 3532409) B3532409
theorem B1568575 : Blo 734326 1568575 := bstep (se 1 (by rfl) ⟨1176431, by rfl⟩ : syracuseStep 1568575 = 2352863) B2352863
theorem B1437839 : Blo 734326 1437839 := bstep (se 1 (by rfl) ⟨1078379, by rfl⟩ : syracuseStep 1437839 = 2156759) B2156759
theorem B4485401 : Blo 734326 4485401 := bstep (se 2 (by rfl) ⟨1682025, by rfl⟩ : syracuseStep 4485401 = 3364051) B3364051
theorem B6287867 : Blo 734326 6287867 := bstep (se 1 (by rfl) ⟨4715900, by rfl⟩ : syracuseStep 6287867 = 9431801) B9431801
theorem B3535483 : Blo 734326 3535483 := bstep (se 1 (by rfl) ⟨2651612, by rfl⟩ : syracuseStep 3535483 = 5303225) B5303225
theorem B1995499 : Blo 734326 1995499 := bstep (se 1 (by rfl) ⟨1496624, by rfl⟩ : syracuseStep 1995499 = 2993249) B2993249
theorem B1241851 : Blo 734326 1241851 := bstep (se 1 (by rfl) ⟨931388, by rfl⟩ : syracuseStep 1241851 = 1862777) B1862777
theorem B434664305 : Blo 734326 434664305 := bstep (se 2 (by rfl) ⟨162999114, by rfl⟩ : syracuseStep 434664305 = 325998229) B325998229
theorem B1241993 : Blo 734326 1241993 := bstep (se 2 (by rfl) ⟨465747, by rfl⟩ : syracuseStep 1241993 = 931495) B931495
theorem B7074809 : Blo 734326 7074809 := bstep (se 2 (by rfl) ⟨2653053, by rfl⟩ : syracuseStep 7074809 = 5306107) B5306107
theorem B1274951 : Blo 734326 1274951 := bstep (se 1 (by rfl) ⟨956213, by rfl⟩ : syracuseStep 1274951 = 1912427) B1912427
theorem B1963271 : Blo 734326 1963271 := bstep (se 1 (by rfl) ⟨1472453, by rfl⟩ : syracuseStep 1963271 = 2944907) B2944907
theorem B7566655 : Blo 734326 7566655 := bstep (se 1 (by rfl) ⟨5674991, by rfl⟩ : syracuseStep 7566655 = 11349983) B11349983
theorem B849215 : Blo 734326 849215 := bstep (se 1 (by rfl) ⟨636911, by rfl⟩ : syracuseStep 849215 = 1273823) B1273823
theorem B1570259 : Blo 734326 1570259 := bstep (se 1 (by rfl) ⟨1177694, by rfl⟩ : syracuseStep 1570259 = 2355389) B2355389
theorem B1242715 : Blo 734326 1242715 := bstep (se 1 (by rfl) ⟨932036, by rfl⟩ : syracuseStep 1242715 = 1864073) B1864073
theorem B1242857 : Blo 734326 1242857 := bstep (se 2 (by rfl) ⟨466071, by rfl⟩ : syracuseStep 1242857 = 932143) B932143
theorem B1865551 : Blo 734326 1865551 := bstep (se 1 (by rfl) ⟨1399163, by rfl⟩ : syracuseStep 1865551 = 2798327) B2798327
theorem B7272337 : Blo 734326 7272337 := bstep (se 2 (by rfl) ⟨2727126, by rfl⟩ : syracuseStep 7272337 = 5454253) B5454253
theorem B33094277 : Blo 734326 33094277 := bstep (se 4 (by rfl) ⟨3102588, by rfl⟩ : syracuseStep 33094277 = 6205177) B6205177
theorem B1243883 : Blo 734326 1243883 := bstep (se 1 (by rfl) ⟨932912, by rfl⟩ : syracuseStep 1243883 = 1865825) B1865825
theorem B232815779 : Blo 734326 232815779 := bstep (se 1 (by rfl) ⟨174611834, by rfl⟩ : syracuseStep 232815779 = 349223669) B349223669
theorem B1703339 : Blo 734326 1703339 := bstep (se 1 (by rfl) ⟨1277504, by rfl⟩ : syracuseStep 1703339 = 2555009) B2555009
theorem B1867283 : Blo 734326 1867283 := bstep (se 1 (by rfl) ⟨1400462, by rfl⟩ : syracuseStep 1867283 = 2800925) B2800925
theorem B1867495 : Blo 734326 1867495 := bstep (se 1 (by rfl) ⟨1400621, by rfl⟩ : syracuseStep 1867495 = 2801243) B2801243
theorem B1180327 : Blo 734326 1180327 := bstep (se 1 (by rfl) ⟨885245, by rfl⟩ : syracuseStep 1180327 = 1770491) B1770491
theorem B10748713 : Blo 734326 10748713 := bstep (se 2 (by rfl) ⟨4030767, by rfl⟩ : syracuseStep 10748713 = 8061535) B8061535
theorem B1049851 : Blo 734326 1049851 := bstep (se 1 (by rfl) ⟨787388, by rfl⟩ : syracuseStep 1049851 = 1574777) B1574777
theorem B1574633 : Blo 734326 1574633 := bstep (se 2 (by rfl) ⟨590487, by rfl⟩ : syracuseStep 1574633 = 1180975) B1180975
theorem B3737501 : Blo 734326 3737501 := bstep (se 3 (by rfl) ⟨700781, by rfl⟩ : syracuseStep 3737501 = 1401563) B1401563
theorem B4197743 : Blo 734326 4197743 := bstep (se 1 (by rfl) ⟨3148307, by rfl⟩ : syracuseStep 4197743 = 6296615) B6296615
theorem B2788775 : Blo 734326 2788775 := bstep (se 1 (by rfl) ⟨2091581, by rfl⟩ : syracuseStep 2788775 = 4183163) B4183163
theorem B2264573 : Blo 734326 2264573 := bstep (se 3 (by rfl) ⟨424607, by rfl⟩ : syracuseStep 2264573 = 849215) B849215
theorem B2101241 : Blo 734326 2101241 := bstep (se 2 (by rfl) ⟨787965, by rfl⟩ : syracuseStep 2101241 = 1575931) B1575931
theorem B1118443 : Blo 734326 1118443 := bstep (se 1 (by rfl) ⟨838832, by rfl⟩ : syracuseStep 1118443 = 1677665) B1677665
theorem B2101889 : Blo 734326 2101889 := bstep (se 2 (by rfl) ⟨788208, by rfl⟩ : syracuseStep 2101889 = 1576417) B1576417
theorem B5576363 : Blo 734326 5576363 := bstep (se 1 (by rfl) ⟨4182272, by rfl⟩ : syracuseStep 5576363 = 8364545) B8364545
theorem B4200659 : Blo 734326 4200659 := bstep (se 1 (by rfl) ⟨3150494, by rfl⟩ : syracuseStep 4200659 = 6300989) B6300989
theorem B20126483 : Blo 734326 20126483 := bstep (se 1 (by rfl) ⟨15094862, by rfl⟩ : syracuseStep 20126483 = 30189725) B30189725
theorem B1678367 : Blo 734326 1678367 := bstep (se 1 (by rfl) ⟨1258775, by rfl⟩ : syracuseStep 1678367 = 2517551) B2517551
theorem B9444559 : Blo 734326 9444559 := bstep (se 1 (by rfl) ⟨7083419, by rfl⟩ : syracuseStep 9444559 = 14166839) B14166839
theorem B4726025 : Blo 734326 4726025 := bstep (se 2 (by rfl) ⟨1772259, by rfl⟩ : syracuseStep 4726025 = 3544519) B3544519
theorem B958559 : Blo 734326 958559 := bstep (se 1 (by rfl) ⟨718919, by rfl⟩ : syracuseStep 958559 = 1437839) B1437839
theorem B2990267 : Blo 734326 2990267 := bstep (se 1 (by rfl) ⟨2242700, by rfl⟩ : syracuseStep 2990267 = 4485401) B4485401
theorem B289776203 : Blo 734326 289776203 := bstep (se 1 (by rfl) ⟨217332152, by rfl⟩ : syracuseStep 289776203 = 434664305) B434664305
theorem B827995 : Blo 734326 827995 := bstep (se 1 (by rfl) ⟨620996, by rfl⟩ : syracuseStep 827995 = 1241993) B1241993
theorem B7971965 : Blo 734326 7971965 := bstep (se 3 (by rfl) ⟨1494743, by rfl⟩ : syracuseStep 7971965 = 2989487) B2989487
theorem B828571 : Blo 734326 828571 := bstep (se 1 (by rfl) ⟨621428, by rfl⟩ : syracuseStep 828571 = 1242857) B1242857
theorem B4728431 : Blo 734326 4728431 := bstep (se 1 (by rfl) ⟨3546323, by rfl⟩ : syracuseStep 4728431 = 7092647) B7092647
theorem B22062851 : Blo 734326 22062851 := bstep (se 1 (by rfl) ⟨16547138, by rfl⟩ : syracuseStep 22062851 = 33094277) B33094277
theorem B829255 : Blo 734326 829255 := bstep (se 1 (by rfl) ⟨621941, by rfl⟩ : syracuseStep 829255 = 1243883) B1243883
theorem B6891641 : Blo 734326 6891641 := bstep (se 2 (by rfl) ⟨2584365, by rfl⟩ : syracuseStep 6891641 = 5168731) B5168731
theorem B3778973 : Blo 734326 3778973 := bstep (se 3 (by rfl) ⟨708557, by rfl⟩ : syracuseStep 3778973 = 1417115) B1417115
theorem B4729661 : Blo 734326 4729661 := bstep (se 3 (by rfl) ⟨886811, by rfl⟩ : syracuseStep 4729661 = 1773623) B1773623
theorem B830407 : Blo 734326 830407 := bstep (se 1 (by rfl) ⟨622805, by rfl⟩ : syracuseStep 830407 = 1245611) B1245611
theorem B17017937 : Blo 734326 17017937 := bstep (se 2 (by rfl) ⟨6381726, by rfl⟩ : syracuseStep 17017937 = 12763453) B12763453
theorem B3779713 : Blo 734326 3779713 := bstep (se 2 (by rfl) ⟨1417392, by rfl⟩ : syracuseStep 3779713 = 2834785) B2834785
theorem B2272607 : Blo 734326 2272607 := bstep (se 1 (by rfl) ⟨1704455, by rfl⟩ : syracuseStep 2272607 = 3408911) B3408911
theorem B2797051 : Blo 734326 2797051 := bstep (se 1 (by rfl) ⟨2097788, by rfl⟩ : syracuseStep 2797051 = 4195577) B4195577
theorem B6368951 : Blo 734326 6368951 := bstep (se 1 (by rfl) ⟨4776713, by rfl⟩ : syracuseStep 6368951 = 9553427) B9553427
theorem B929647 : Blo 734326 929647 := bstep (se 1 (by rfl) ⟨697235, by rfl⟩ : syracuseStep 929647 = 1394471) B1394471
theorem B6304027 : Blo 734326 6304027 := bstep (se 1 (by rfl) ⟨4728020, by rfl⟩ : syracuseStep 6304027 = 9456041) B9456041
theorem B9449891 : Blo 734326 9449891 := bstep (se 1 (by rfl) ⟨7087418, by rfl⟩ : syracuseStep 9449891 = 14174837) B14174837
theorem B24228503 : Blo 734326 24228503 := bstep (se 1 (by rfl) ⟨18171377, by rfl⟩ : syracuseStep 24228503 = 36342755) B36342755
theorem B5026585 : Blo 734326 5026585 := bstep (se 2 (by rfl) ⟨1884969, by rfl⟩ : syracuseStep 5026585 = 3769939) B3769939
theorem B734463 : Blo 734326 734463 := bstep (se 1 (by rfl) ⟨550847, by rfl⟩ : syracuseStep 734463 = 1101695) B1101695
theorem B10630439 : Blo 734326 10630439 := bstep (se 1 (by rfl) ⟨7972829, by rfl⟩ : syracuseStep 10630439 = 15945659) B15945659
theorem B734591 : Blo 734326 734591 := bstep (se 1 (by rfl) ⟨550943, by rfl⟩ : syracuseStep 734591 = 1101887) B1101887
theorem B734747 : Blo 734326 734747 := bstep (se 1 (by rfl) ⟨551060, by rfl⟩ : syracuseStep 734747 = 1102121) B1102121
theorem B734927 : Blo 734326 734927 := bstep (se 1 (by rfl) ⟨551195, by rfl⟩ : syracuseStep 734927 = 1102391) B1102391
theorem B735167 : Blo 734326 735167 := bstep (se 1 (by rfl) ⟨551375, by rfl⟩ : syracuseStep 735167 = 1102751) B1102751
theorem B931819 : Blo 734326 931819 := bstep (se 1 (by rfl) ⟨698864, by rfl⟩ : syracuseStep 931819 = 1397729) B1397729
theorem B735295 : Blo 734326 735295 := bstep (se 1 (by rfl) ⟨551471, by rfl⟩ : syracuseStep 735295 = 1102943) B1102943
theorem B735335 : Blo 734326 735335 := bstep (se 1 (by rfl) ⟨551501, by rfl⟩ : syracuseStep 735335 = 1103003) B1103003
theorem B23837003 : Blo 734326 23837003 := bstep (se 1 (by rfl) ⟨17877752, by rfl⟩ : syracuseStep 23837003 = 35755505) B35755505
theorem B735791 : Blo 734326 735791 := bstep (se 1 (by rfl) ⟨551843, by rfl⟩ : syracuseStep 735791 = 1103687) B1103687
theorem B11352635 : Blo 734326 11352635 := bstep (se 1 (by rfl) ⟨8514476, by rfl⟩ : syracuseStep 11352635 = 17028953) B17028953
theorem B3684989 : Blo 734326 3684989 := bstep (se 3 (by rfl) ⟨690935, by rfl⟩ : syracuseStep 3684989 = 1381871) B1381871
theorem B6273683 : Blo 734326 6273683 := bstep (se 1 (by rfl) ⟨4705262, by rfl⟩ : syracuseStep 6273683 = 9410525) B9410525
theorem B6372107 : Blo 734326 6372107 := bstep (se 1 (by rfl) ⟨4779080, by rfl⟩ : syracuseStep 6372107 = 9558161) B9558161
theorem B1653695 : Blo 734326 1653695 := bstep (se 1 (by rfl) ⟨1240271, by rfl⟩ : syracuseStep 1653695 = 2480543) B2480543
theorem B736191 : Blo 734326 736191 := bstep (se 1 (by rfl) ⟨552143, by rfl⟩ : syracuseStep 736191 = 1104287) B1104287
theorem B736239 : Blo 734326 736239 := bstep (se 1 (by rfl) ⟨552179, by rfl⟩ : syracuseStep 736239 = 1104359) B1104359
theorem B2800939 : Blo 734326 2800939 := bstep (se 1 (by rfl) ⟨2100704, by rfl⟩ : syracuseStep 2800939 = 4201409) B4201409
theorem B736735 : Blo 734326 736735 := bstep (se 1 (by rfl) ⟨552551, by rfl⟩ : syracuseStep 736735 = 1105103) B1105103
theorem B736815 : Blo 734326 736815 := bstep (se 1 (by rfl) ⟨552611, by rfl⟩ : syracuseStep 736815 = 1105223) B1105223
theorem B1654343 : Blo 734326 1654343 := bstep (se 1 (by rfl) ⟨1240757, by rfl⟩ : syracuseStep 1654343 = 2481515) B2481515
theorem B736923 : Blo 734326 736923 := bstep (se 1 (by rfl) ⟨552692, by rfl⟩ : syracuseStep 736923 = 1105385) B1105385
theorem B1654523 : Blo 734326 1654523 := bstep (se 1 (by rfl) ⟨1240892, by rfl⟩ : syracuseStep 1654523 = 2481785) B2481785
theorem B737019 : Blo 734326 737019 := bstep (se 1 (by rfl) ⟨552764, by rfl⟩ : syracuseStep 737019 = 1105529) B1105529
theorem B737183 : Blo 734326 737183 := bstep (se 1 (by rfl) ⟨552887, by rfl⟩ : syracuseStep 737183 = 1105775) B1105775
theorem B1654775 : Blo 734326 1654775 := bstep (se 1 (by rfl) ⟨1241081, by rfl⟩ : syracuseStep 1654775 = 2482163) B2482163
theorem B1655135 : Blo 734326 1655135 := bstep (se 1 (by rfl) ⟨1241351, by rfl⟩ : syracuseStep 1655135 = 2482703) B2482703
theorem B737639 : Blo 734326 737639 := bstep (se 1 (by rfl) ⟨553229, by rfl⟩ : syracuseStep 737639 = 1106459) B1106459
theorem B737759 : Blo 734326 737759 := bstep (se 1 (by rfl) ⟨553319, by rfl⟩ : syracuseStep 737759 = 1106639) B1106639
theorem B737767 : Blo 734326 737767 := bstep (se 1 (by rfl) ⟨553325, by rfl⟩ : syracuseStep 737767 = 1106651) B1106651
theorem B738043 : Blo 734326 738043 := bstep (se 1 (by rfl) ⟨553532, by rfl⟩ : syracuseStep 738043 = 1107065) B1107065
theorem B1655675 : Blo 734326 1655675 := bstep (se 1 (by rfl) ⟨1241756, by rfl⟩ : syracuseStep 1655675 = 2483513) B2483513
theorem B1655801 : Blo 734326 1655801 := bstep (se 2 (by rfl) ⟨620925, by rfl⟩ : syracuseStep 1655801 = 1241851) B1241851
theorem B1655855 : Blo 734326 1655855 := bstep (se 1 (by rfl) ⟨1241891, by rfl⟩ : syracuseStep 1655855 = 2483783) B2483783
theorem B1655891 : Blo 734326 1655891 := bstep (se 1 (by rfl) ⟨1241918, by rfl⟩ : syracuseStep 1655891 = 2483837) B2483837
theorem B43042051 : Blo 734326 43042051 := bstep (se 1 (by rfl) ⟨32281538, by rfl⟩ : syracuseStep 43042051 = 64563077) B64563077
theorem B1656071 : Blo 734326 1656071 := bstep (se 1 (by rfl) ⟨1242053, by rfl⟩ : syracuseStep 1656071 = 2484107) B2484107
theorem B1656503 : Blo 734326 1656503 := bstep (se 1 (by rfl) ⟨1242377, by rfl⟩ : syracuseStep 1656503 = 2484755) B2484755
theorem B1656953 : Blo 734326 1656953 := bstep (se 2 (by rfl) ⟨621357, by rfl⟩ : syracuseStep 1656953 = 1242715) B1242715
theorem B8964377 : Blo 734326 8964377 := bstep (se 2 (by rfl) ⟨3361641, by rfl⟩ : syracuseStep 8964377 = 6723283) B6723283
theorem B1657151 : Blo 734326 1657151 := bstep (se 1 (by rfl) ⟨1242863, by rfl⟩ : syracuseStep 1657151 = 2485727) B2485727
theorem B10636201 : Blo 734326 10636201 := bstep (se 2 (by rfl) ⟨3988575, by rfl⟩ : syracuseStep 10636201 = 7977151) B7977151
theorem B3722759 : Blo 734326 3722759 := bstep (se 1 (by rfl) ⟨2792069, by rfl⟩ : syracuseStep 3722759 = 5584139) B5584139
theorem B7982687 : Blo 734326 7982687 := bstep (se 1 (by rfl) ⟨5987015, by rfl⟩ : syracuseStep 7982687 = 11974031) B11974031
theorem B839279 : Blo 734326 839279 := bstep (se 1 (by rfl) ⟨629459, by rfl⟩ : syracuseStep 839279 = 1258919) B1258919
theorem B8507123 : Blo 734326 8507123 := bstep (se 1 (by rfl) ⟨6380342, by rfl⟩ : syracuseStep 8507123 = 12760685) B12760685
theorem B1101647 : Blo 734326 1101647 := bstep (se 1 (by rfl) ⟨826235, by rfl⟩ : syracuseStep 1101647 = 1652471) B1652471
theorem B1101767 : Blo 734326 1101767 := bstep (se 1 (by rfl) ⟨826325, by rfl⟩ : syracuseStep 1101767 = 1652651) B1652651
theorem B6279119 : Blo 734326 6279119 := bstep (se 1 (by rfl) ⟨4709339, by rfl⟩ : syracuseStep 6279119 = 9418679) B9418679
theorem B1101851 : Blo 734326 1101851 := bstep (se 1 (by rfl) ⟨826388, by rfl⟩ : syracuseStep 1101851 = 1652777) B1652777
theorem B3985463 : Blo 734326 3985463 := bstep (se 1 (by rfl) ⟨2989097, by rfl⟩ : syracuseStep 3985463 = 5978195) B5978195
theorem B1102127 : Blo 734326 1102127 := bstep (se 1 (by rfl) ⟨826595, by rfl⟩ : syracuseStep 1102127 = 1653191) B1653191
theorem B9458045 : Blo 734326 9458045 := bstep (se 3 (by rfl) ⟨1773383, by rfl⟩ : syracuseStep 9458045 = 3546767) B3546767
theorem B1102235 : Blo 734326 1102235 := bstep (se 1 (by rfl) ⟨826676, by rfl⟩ : syracuseStep 1102235 = 1653353) B1653353
theorem B1102271 : Blo 734326 1102271 := bstep (se 1 (by rfl) ⟨826703, by rfl⟩ : syracuseStep 1102271 = 1653407) B1653407
theorem B1102367 : Blo 734326 1102367 := bstep (se 1 (by rfl) ⟨826775, by rfl⟩ : syracuseStep 1102367 = 1653551) B1653551
theorem B4706903 : Blo 734326 4706903 := bstep (se 1 (by rfl) ⟨3530177, by rfl⟩ : syracuseStep 4706903 = 7060355) B7060355
theorem B6279767 : Blo 734326 6279767 := bstep (se 1 (by rfl) ⟨4709825, by rfl⟩ : syracuseStep 6279767 = 9419651) B9419651
theorem B4182637 : Blo 734326 4182637 := bstep (se 3 (by rfl) ⟨784244, by rfl⟩ : syracuseStep 4182637 = 1568489) B1568489
theorem B155210519 : Blo 734326 155210519 := bstep (se 1 (by rfl) ⟨116407889, by rfl⟩ : syracuseStep 155210519 = 232815779) B232815779
theorem B1102655 : Blo 734326 1102655 := bstep (se 1 (by rfl) ⟨826991, by rfl⟩ : syracuseStep 1102655 = 1653983) B1653983
theorem B1135559 : Blo 734326 1135559 := bstep (se 1 (by rfl) ⟨851669, by rfl⟩ : syracuseStep 1135559 = 1703339) B1703339
theorem B1102799 : Blo 734326 1102799 := bstep (se 1 (by rfl) ⟨827099, by rfl⟩ : syracuseStep 1102799 = 1654199) B1654199
theorem B1102889 : Blo 734326 1102889 := bstep (se 2 (by rfl) ⟨413583, by rfl⟩ : syracuseStep 1102889 = 827167) B827167
theorem B1102919 : Blo 734326 1102919 := bstep (se 1 (by rfl) ⟨827189, by rfl⟩ : syracuseStep 1102919 = 1654379) B1654379
theorem B1103099 : Blo 734326 1103099 := bstep (se 1 (by rfl) ⟨827324, by rfl⟩ : syracuseStep 1103099 = 1654649) B1654649
theorem B1103159 : Blo 734326 1103159 := bstep (se 1 (by rfl) ⟨827369, by rfl⟩ : syracuseStep 1103159 = 1654739) B1654739
theorem B8377667 : Blo 734326 8377667 := bstep (se 1 (by rfl) ⟨6283250, by rfl⟩ : syracuseStep 8377667 = 12566501) B12566501
theorem B1103465 : Blo 734326 1103465 := bstep (se 2 (by rfl) ⟨413799, by rfl⟩ : syracuseStep 1103465 = 827599) B827599
theorem B1660607 : Blo 734326 1660607 := bstep (se 1 (by rfl) ⟨1245455, by rfl⟩ : syracuseStep 1660607 = 2490911) B2490911
theorem B3987539 : Blo 734326 3987539 := bstep (se 1 (by rfl) ⟨2990654, by rfl⟩ : syracuseStep 3987539 = 5981309) B5981309
theorem B1103999 : Blo 734326 1103999 := bstep (se 1 (by rfl) ⟨827999, by rfl⟩ : syracuseStep 1103999 = 1655999) B1655999
theorem B1104095 : Blo 734326 1104095 := bstep (se 1 (by rfl) ⟨828071, by rfl⟩ : syracuseStep 1104095 = 1656143) B1656143
theorem B1104155 : Blo 734326 1104155 := bstep (se 1 (by rfl) ⟨828116, by rfl⟩ : syracuseStep 1104155 = 1656233) B1656233
theorem B1104479 : Blo 734326 1104479 := bstep (se 1 (by rfl) ⟨828359, by rfl⟩ : syracuseStep 1104479 = 1656719) B1656719
theorem B1104575 : Blo 734326 1104575 := bstep (se 1 (by rfl) ⟨828431, by rfl⟩ : syracuseStep 1104575 = 1656863) B1656863
theorem B1104617 : Blo 734326 1104617 := bstep (se 2 (by rfl) ⟨414231, by rfl⟩ : syracuseStep 1104617 = 828463) B828463
theorem B1104743 : Blo 734326 1104743 := bstep (se 1 (by rfl) ⟨828557, by rfl⟩ : syracuseStep 1104743 = 1657115) B1657115
theorem B1104809 : Blo 734326 1104809 := bstep (se 2 (by rfl) ⟨414303, by rfl⟩ : syracuseStep 1104809 = 828607) B828607
theorem B1104959 : Blo 734326 1104959 := bstep (se 1 (by rfl) ⟨828719, by rfl⟩ : syracuseStep 1104959 = 1657439) B1657439
theorem B1105001 : Blo 734326 1105001 := bstep (se 2 (by rfl) ⟨414375, by rfl⟩ : syracuseStep 1105001 = 828751) B828751
theorem B1105127 : Blo 734326 1105127 := bstep (se 1 (by rfl) ⟨828845, by rfl⟩ : syracuseStep 1105127 = 1657691) B1657691
theorem B5594345 : Blo 734326 5594345 := bstep (se 2 (by rfl) ⟨2097879, by rfl⟩ : syracuseStep 5594345 = 4195759) B4195759
theorem B3595529 : Blo 734326 3595529 := bstep (se 2 (by rfl) ⟨1348323, by rfl⟩ : syracuseStep 3595529 = 2696647) B2696647
theorem B1105631 : Blo 734326 1105631 := bstep (se 1 (by rfl) ⟨829223, by rfl⟩ : syracuseStep 1105631 = 1658447) B1658447
theorem B31842173 : Blo 734326 31842173 := bstep (se 3 (by rfl) ⟨5970407, by rfl⟩ : syracuseStep 31842173 = 11940815) B11940815
theorem B1400743 : Blo 734326 1400743 := bstep (se 1 (by rfl) ⟨1050557, by rfl⟩ : syracuseStep 1400743 = 2101115) B2101115
theorem B1105961 : Blo 734326 1105961 := bstep (se 2 (by rfl) ⟨414735, by rfl⟩ : syracuseStep 1105961 = 829471) B829471
theorem B1105991 : Blo 734326 1105991 := bstep (se 1 (by rfl) ⟨829493, by rfl⟩ : syracuseStep 1105991 = 1658987) B1658987
theorem B1106027 : Blo 734326 1106027 := bstep (se 1 (by rfl) ⟨829520, by rfl⟩ : syracuseStep 1106027 = 1659041) B1659041
theorem B1106111 : Blo 734326 1106111 := bstep (se 1 (by rfl) ⟨829583, by rfl⟩ : syracuseStep 1106111 = 1659167) B1659167
theorem B1859881 : Blo 734326 1859881 := bstep (se 2 (by rfl) ⟨697455, by rfl⟩ : syracuseStep 1859881 = 1394911) B1394911
theorem B2482487 : Blo 734326 2482487 := bstep (se 1 (by rfl) ⟨1861865, by rfl⟩ : syracuseStep 2482487 = 3723731) B3723731
theorem B1106297 : Blo 734326 1106297 := bstep (se 2 (by rfl) ⟨414861, by rfl⟩ : syracuseStep 1106297 = 829723) B829723
theorem B1106591 : Blo 734326 1106591 := bstep (se 1 (by rfl) ⟨829943, by rfl⟩ : syracuseStep 1106591 = 1659887) B1659887
theorem B2483027 : Blo 734326 2483027 := bstep (se 1 (by rfl) ⟨1862270, by rfl⟩ : syracuseStep 2483027 = 3724541) B3724541
theorem B1106927 : Blo 734326 1106927 := bstep (se 1 (by rfl) ⟨830195, by rfl⟩ : syracuseStep 1106927 = 1660391) B1660391
theorem B1107035 : Blo 734326 1107035 := bstep (se 1 (by rfl) ⟨830276, by rfl⟩ : syracuseStep 1107035 = 1660553) B1660553
theorem B1107047 : Blo 734326 1107047 := bstep (se 1 (by rfl) ⟨830285, by rfl⟩ : syracuseStep 1107047 = 1660571) B1660571
theorem B1860833 : Blo 734326 1860833 := bstep (se 2 (by rfl) ⟨697812, by rfl⟩ : syracuseStep 1860833 = 1395625) B1395625
theorem B10642661 : Blo 734326 10642661 := bstep (se 4 (by rfl) ⟨997749, by rfl⟩ : syracuseStep 10642661 = 1995499) B1995499
theorem B1107179 : Blo 734326 1107179 := bstep (se 1 (by rfl) ⟨830384, by rfl⟩ : syracuseStep 1107179 = 1660769) B1660769
theorem B2483567 : Blo 734326 2483567 := bstep (se 1 (by rfl) ⟨1862675, by rfl⟩ : syracuseStep 2483567 = 3725351) B3725351
theorem B1107311 : Blo 734326 1107311 := bstep (se 1 (by rfl) ⟨830483, by rfl⟩ : syracuseStep 1107311 = 1660967) B1660967
theorem B1107431 : Blo 734326 1107431 := bstep (se 1 (by rfl) ⟨830573, by rfl⟩ : syracuseStep 1107431 = 1661147) B1661147
theorem B1861663 : Blo 734326 1861663 := bstep (se 1 (by rfl) ⟨1396247, by rfl⟩ : syracuseStep 1861663 = 2792495) B2792495
theorem B70772953 : Blo 734326 70772953 := bstep (se 2 (by rfl) ⟨26539857, by rfl⟩ : syracuseStep 70772953 = 53079715) B53079715
theorem B2091251 : Blo 734326 2091251 := bstep (se 1 (by rfl) ⟨1568438, by rfl⟩ : syracuseStep 2091251 = 3136877) B3136877
theorem B2091433 : Blo 734326 2091433 := bstep (se 2 (by rfl) ⟨784287, by rfl⟩ : syracuseStep 2091433 = 1568575) B1568575
theorem B1010279 : Blo 734326 1010279 := bstep (se 1 (by rfl) ⟨757709, by rfl⟩ : syracuseStep 1010279 = 1515419) B1515419
theorem B3730697 : Blo 734326 3730697 := bstep (se 2 (by rfl) ⟨1399011, by rfl⟩ : syracuseStep 3730697 = 2798023) B2798023
theorem B2354503 : Blo 734326 2354503 := bstep (se 1 (by rfl) ⟨1765877, by rfl⟩ : syracuseStep 2354503 = 3531755) B3531755
theorem B4713977 : Blo 734326 4713977 := bstep (se 2 (by rfl) ⟨1767741, by rfl⟩ : syracuseStep 4713977 = 3535483) B3535483
theorem B2485943 : Blo 734326 2485943 := bstep (se 1 (by rfl) ⟨1864457, by rfl⟩ : syracuseStep 2485943 = 3728915) B3728915
theorem B1994711 : Blo 734326 1994711 := bstep (se 1 (by rfl) ⟨1496033, by rfl⟩ : syracuseStep 1994711 = 2992067) B2992067
theorem B1863719 : Blo 734326 1863719 := bstep (se 1 (by rfl) ⟨1397789, by rfl⟩ : syracuseStep 1863719 = 2795579) B2795579
theorem B1241183 : Blo 734326 1241183 := bstep (se 1 (by rfl) ⟨930887, by rfl⟩ : syracuseStep 1241183 = 1861775) B1861775
theorem B7565501 : Blo 734326 7565501 := bstep (se 3 (by rfl) ⟨1418531, by rfl⟩ : syracuseStep 7565501 = 2837063) B2837063
theorem B10088873 : Blo 734326 10088873 := bstep (se 2 (by rfl) ⟨3783327, by rfl⟩ : syracuseStep 10088873 = 7566655) B7566655
theorem B18641441 : Blo 734326 18641441 := bstep (se 2 (by rfl) ⟨6990540, by rfl⟩ : syracuseStep 18641441 = 13981081) B13981081
theorem B1864559 : Blo 734326 1864559 := bstep (se 1 (by rfl) ⟨1398419, by rfl⟩ : syracuseStep 1864559 = 2796839) B2796839
theorem B4715567 : Blo 734326 4715567 := bstep (se 1 (by rfl) ⟨3536675, by rfl⟩ : syracuseStep 4715567 = 7073351) B7073351
theorem B2487401 : Blo 734326 2487401 := bstep (se 2 (by rfl) ⟨932775, by rfl⟩ : syracuseStep 2487401 = 1865551) B1865551
theorem B1569959 : Blo 734326 1569959 := bstep (se 1 (by rfl) ⟨1177469, by rfl⟩ : syracuseStep 1569959 = 2354939) B2354939
theorem B9696449 : Blo 734326 9696449 := bstep (se 2 (by rfl) ⟨3636168, by rfl⟩ : syracuseStep 9696449 = 7272337) B7272337
theorem B4191911 : Blo 734326 4191911 := bstep (se 1 (by rfl) ⟨3143933, by rfl⟩ : syracuseStep 4191911 = 6287867) B6287867
theorem B4716539 : Blo 734326 4716539 := bstep (se 1 (by rfl) ⟨3537404, by rfl⟩ : syracuseStep 4716539 = 7074809) B7074809
theorem B849967 : Blo 734326 849967 := bstep (se 1 (by rfl) ⟨637475, by rfl⟩ : syracuseStep 849967 = 1274951) B1274951
theorem B1308847 : Blo 734326 1308847 := bstep (se 1 (by rfl) ⟨981635, by rfl⟩ : syracuseStep 1308847 = 1963271) B1963271
theorem B1046839 : Blo 734326 1046839 := bstep (se 1 (by rfl) ⟨785129, by rfl⟩ : syracuseStep 1046839 = 1570259) B1570259
theorem B1866473 : Blo 734326 1866473 := bstep (se 2 (by rfl) ⟨699927, by rfl⟩ : syracuseStep 1866473 = 1399855) B1399855
theorem B1866503 : Blo 734326 1866503 := bstep (se 1 (by rfl) ⟨1399877, by rfl⟩ : syracuseStep 1866503 = 2799755) B2799755
theorem B1866847 : Blo 734326 1866847 := bstep (se 1 (by rfl) ⟨1400135, by rfl⟩ : syracuseStep 1866847 = 2800271) B2800271
theorem B5307781 : Blo 734326 5307781 := bstep (se 4 (by rfl) ⟨497604, by rfl⟩ : syracuseStep 5307781 = 995209) B995209
theorem B2489993 : Blo 734326 2489993 := bstep (se 2 (by rfl) ⟨933747, by rfl⟩ : syracuseStep 2489993 = 1867495) B1867495
theorem B1244855 : Blo 734326 1244855 := bstep (se 1 (by rfl) ⟨933641, by rfl⟩ : syracuseStep 1244855 = 1867283) B1867283
theorem B1573769 : Blo 734326 1573769 := bstep (se 2 (by rfl) ⟨590163, by rfl⟩ : syracuseStep 1573769 = 1180327) B1180327
theorem B10224629 : Blo 734326 10224629 := bstep (se 5 (by rfl) ⟨479279, by rfl⟩ : syracuseStep 10224629 = 958559) B958559
theorem B1049755 : Blo 734326 1049755 := bstep (se 1 (by rfl) ⟨787316, by rfl⟩ : syracuseStep 1049755 = 1574633) B1574633
theorem B2491667 : Blo 734326 2491667 := bstep (se 1 (by rfl) ⟨1868750, by rfl⟩ : syracuseStep 2491667 = 3737501) B3737501
theorem B5605037 : Blo 734326 5605037 := bstep (se 3 (by rfl) ⟨1050944, by rfl⟩ : syracuseStep 5605037 = 2101889) B2101889
theorem B413894717 : Blo 734326 413894717 := bstep (se 3 (by rfl) ⟨77605259, by rfl⟩ : syracuseStep 413894717 = 155210519) B155210519
theorem B1509715 : Blo 734326 1509715 := bstep (se 1 (by rfl) ⟨1132286, by rfl⟩ : syracuseStep 1509715 = 2264573) B2264573
theorem B5671415 : Blo 734326 5671415 := bstep (se 1 (by rfl) ⟨4253561, by rfl⟩ : syracuseStep 5671415 = 8507123) B8507123
theorem B2656975 : Blo 734326 2656975 := bstep (se 1 (by rfl) ⟨1992731, by rfl⟩ : syracuseStep 2656975 = 3985463) B3985463
theorem B25857197 : Blo 734326 25857197 := bstep (se 3 (by rfl) ⟨4848224, by rfl⟩ : syracuseStep 25857197 = 9696449) B9696449
theorem B2788577 : Blo 734326 2788577 := bstep (se 2 (by rfl) ⟨1045716, by rfl⟩ : syracuseStep 2788577 = 2091433) B2091433
theorem B2658359 : Blo 734326 2658359 := bstep (se 1 (by rfl) ⟨1993769, by rfl⟩ : syracuseStep 2658359 = 3987539) B3987539
theorem B3150683 : Blo 734326 3150683 := bstep (se 1 (by rfl) ⟨2363012, by rfl⟩ : syracuseStep 3150683 = 4726025) B4726025
theorem B2397019 : Blo 734326 2397019 := bstep (se 1 (by rfl) ⟨1797764, by rfl⟩ : syracuseStep 2397019 = 3595529) B3595529
theorem B20158469 : Blo 734326 20158469 := bstep (se 4 (by rfl) ⟨1889856, by rfl⟩ : syracuseStep 20158469 = 3779713) B3779713
theorem B5314643 : Blo 734326 5314643 := bstep (se 1 (by rfl) ⟨3985982, by rfl⟩ : syracuseStep 5314643 = 7971965) B7971965
theorem B5576849 : Blo 734326 5576849 := bstep (se 2 (by rfl) ⟨2091318, by rfl⟩ : syracuseStep 5576849 = 4182637) B4182637
theorem B3152287 : Blo 734326 3152287 := bstep (se 1 (by rfl) ⟨2364215, by rfl⟩ : syracuseStep 3152287 = 4728431) B4728431
theorem B4594427 : Blo 734326 4594427 := bstep (se 1 (by rfl) ⟨3445820, by rfl⟩ : syracuseStep 4594427 = 6891641) B6891641
theorem B2694077 : Blo 734326 2694077 := bstep (se 3 (by rfl) ⟨505139, by rfl⟩ : syracuseStep 2694077 = 1010279) B1010279
theorem B3153107 : Blo 734326 3153107 := bstep (se 1 (by rfl) ⟨2364830, by rfl⟩ : syracuseStep 3153107 = 4729661) B4729661
theorem B11345291 : Blo 734326 11345291 := bstep (se 1 (by rfl) ⟨8508968, by rfl⟩ : syracuseStep 11345291 = 17017937) B17017937
theorem B1515071 : Blo 734326 1515071 := bstep (se 1 (by rfl) ⟨1136303, by rfl⟩ : syracuseStep 1515071 = 2272607) B2272607
theorem B827455 : Blo 734326 827455 := bstep (se 1 (by rfl) ⟨620591, by rfl⟩ : syracuseStep 827455 = 1241183) B1241183
theorem B1745129 : Blo 734326 1745129 := bstep (se 2 (by rfl) ⟨654423, by rfl⟩ : syracuseStep 1745129 = 1308847) B1308847
theorem B6299927 : Blo 734326 6299927 := bstep (se 1 (by rfl) ⟨4724945, by rfl⟩ : syracuseStep 6299927 = 9449891) B9449891
theorem B6725915 : Blo 734326 6725915 := bstep (se 1 (by rfl) ⟨5044436, by rfl⟩ : syracuseStep 6725915 = 10088873) B10088873
theorem B12427627 : Blo 734326 12427627 := bstep (se 1 (by rfl) ⟨9320720, by rfl⟩ : syracuseStep 12427627 = 18641441) B18641441
theorem B7086959 : Blo 734326 7086959 := bstep (se 1 (by rfl) ⟨5315219, by rfl⟩ : syracuseStep 7086959 = 10630439) B10630439
theorem B2794607 : Blo 734326 2794607 := bstep (se 1 (by rfl) ⟨2095955, by rfl⟩ : syracuseStep 2794607 = 4191911) B4191911
theorem B12592745 : Blo 734326 12592745 := bstep (se 2 (by rfl) ⟨4722279, by rfl⟩ : syracuseStep 12592745 = 9444559) B9444559
theorem B2238077 : Blo 734326 2238077 := bstep (se 3 (by rfl) ⟨419639, by rfl⟩ : syracuseStep 2238077 = 839279) B839279
theorem B829903 : Blo 734326 829903 := bstep (se 1 (by rfl) ⟨622427, by rfl⟩ : syracuseStep 829903 = 1244855) B1244855
theorem B5319229 : Blo 734326 5319229 := bstep (se 3 (by rfl) ⟨997355, by rfl⟩ : syracuseStep 5319229 = 1994711) B1994711
theorem B4533157 : Blo 734326 4533157 := bstep (se 4 (by rfl) ⟨424983, by rfl⟩ : syracuseStep 4533157 = 849967) B849967
theorem B14331617 : Blo 734326 14331617 := bstep (se 2 (by rfl) ⟨5374356, by rfl⟩ : syracuseStep 14331617 = 10748713) B10748713
theorem B5976251 : Blo 734326 5976251 := bstep (se 1 (by rfl) ⟨4482188, by rfl⟩ : syracuseStep 5976251 = 8964377) B8964377
theorem B57389401 : Blo 734326 57389401 := bstep (se 2 (by rfl) ⟨21521025, by rfl⟩ : syracuseStep 57389401 = 43042051) B43042051
theorem B2798495 : Blo 734326 2798495 := bstep (se 1 (by rfl) ⟨2098871, by rfl⟩ : syracuseStep 2798495 = 4197743) B4197743
theorem B5321791 : Blo 734326 5321791 := bstep (se 1 (by rfl) ⟨3991343, by rfl⟩ : syracuseStep 5321791 = 7982687) B7982687
theorem B3028157 : Blo 734326 3028157 := bstep (se 3 (by rfl) ⟨567779, by rfl⟩ : syracuseStep 3028157 = 1135559) B1135559
theorem B734431 : Blo 734326 734431 := bstep (se 1 (by rfl) ⟨550823, by rfl⟩ : syracuseStep 734431 = 1101647) B1101647
theorem B734511 : Blo 734326 734511 := bstep (se 1 (by rfl) ⟨550883, by rfl⟩ : syracuseStep 734511 = 1101767) B1101767
theorem B734567 : Blo 734326 734567 := bstep (se 1 (by rfl) ⟨550925, by rfl⟩ : syracuseStep 734567 = 1101851) B1101851
theorem B734751 : Blo 734326 734751 := bstep (se 1 (by rfl) ⟨551063, by rfl⟩ : syracuseStep 734751 = 1102127) B1102127
theorem B6305363 : Blo 734326 6305363 := bstep (se 1 (by rfl) ⟨4729022, by rfl⟩ : syracuseStep 6305363 = 9458045) B9458045
theorem B734823 : Blo 734326 734823 := bstep (se 1 (by rfl) ⟨551117, by rfl⟩ : syracuseStep 734823 = 1102235) B1102235
theorem B734847 : Blo 734326 734847 := bstep (se 1 (by rfl) ⟨551135, by rfl⟩ : syracuseStep 734847 = 1102271) B1102271
theorem B734911 : Blo 734326 734911 := bstep (se 1 (by rfl) ⟨551183, by rfl⟩ : syracuseStep 734911 = 1102367) B1102367
theorem B735103 : Blo 734326 735103 := bstep (se 1 (by rfl) ⟨551327, by rfl⟩ : syracuseStep 735103 = 1102655) B1102655
theorem B735199 : Blo 734326 735199 := bstep (se 1 (by rfl) ⟨551399, by rfl⟩ : syracuseStep 735199 = 1102799) B1102799
theorem B735259 : Blo 734326 735259 := bstep (se 1 (by rfl) ⟨551444, by rfl⟩ : syracuseStep 735259 = 1102889) B1102889
theorem B735279 : Blo 734326 735279 := bstep (se 1 (by rfl) ⟨551459, by rfl⟩ : syracuseStep 735279 = 1102919) B1102919
theorem B735399 : Blo 734326 735399 := bstep (se 1 (by rfl) ⟨551549, by rfl⟩ : syracuseStep 735399 = 1103099) B1103099
theorem B735439 : Blo 734326 735439 := bstep (se 1 (by rfl) ⟨551579, by rfl⟩ : syracuseStep 735439 = 1103159) B1103159
theorem B5585111 : Blo 734326 5585111 := bstep (se 1 (by rfl) ⟨4188833, by rfl⟩ : syracuseStep 5585111 = 8377667) B8377667
theorem B735643 : Blo 734326 735643 := bstep (se 1 (by rfl) ⟨551732, by rfl⟩ : syracuseStep 735643 = 1103465) B1103465
theorem B3717575 : Blo 734326 3717575 := bstep (se 1 (by rfl) ⟨2788181, by rfl⟩ : syracuseStep 3717575 = 5576363) B5576363
theorem B735999 : Blo 734326 735999 := bstep (se 1 (by rfl) ⟨551999, by rfl⟩ : syracuseStep 735999 = 1103999) B1103999
theorem B2800439 : Blo 734326 2800439 := bstep (se 1 (by rfl) ⟨2100329, by rfl⟩ : syracuseStep 2800439 = 4200659) B4200659
theorem B736063 : Blo 734326 736063 := bstep (se 1 (by rfl) ⟨552047, by rfl⟩ : syracuseStep 736063 = 1104095) B1104095
theorem B736103 : Blo 734326 736103 := bstep (se 1 (by rfl) ⟨552077, by rfl⟩ : syracuseStep 736103 = 1104155) B1104155
theorem B736319 : Blo 734326 736319 := bstep (se 1 (by rfl) ⟨552239, by rfl⟩ : syracuseStep 736319 = 1104479) B1104479
theorem B736383 : Blo 734326 736383 := bstep (se 1 (by rfl) ⟨552287, by rfl⟩ : syracuseStep 736383 = 1104575) B1104575
theorem B736411 : Blo 734326 736411 := bstep (se 1 (by rfl) ⟨552308, by rfl⟩ : syracuseStep 736411 = 1104617) B1104617
theorem B13417655 : Blo 734326 13417655 := bstep (se 1 (by rfl) ⟨10063241, by rfl⟩ : syracuseStep 13417655 = 20126483) B20126483
theorem B736495 : Blo 734326 736495 := bstep (se 1 (by rfl) ⟨552371, by rfl⟩ : syracuseStep 736495 = 1104743) B1104743
theorem B736539 : Blo 734326 736539 := bstep (se 1 (by rfl) ⟨552404, by rfl⟩ : syracuseStep 736539 = 1104809) B1104809
theorem B736639 : Blo 734326 736639 := bstep (se 1 (by rfl) ⟨552479, by rfl⟩ : syracuseStep 736639 = 1104959) B1104959
theorem B736667 : Blo 734326 736667 := bstep (se 1 (by rfl) ⟨552500, by rfl⟩ : syracuseStep 736667 = 1105001) B1105001
theorem B736751 : Blo 734326 736751 := bstep (se 1 (by rfl) ⟨552563, by rfl⟩ : syracuseStep 736751 = 1105127) B1105127
theorem B737087 : Blo 734326 737087 := bstep (se 1 (by rfl) ⟨552815, by rfl⟩ : syracuseStep 737087 = 1105631) B1105631
theorem B737307 : Blo 734326 737307 := bstep (se 1 (by rfl) ⟨552980, by rfl⟩ : syracuseStep 737307 = 1105961) B1105961
theorem B737327 : Blo 734326 737327 := bstep (se 1 (by rfl) ⟨552995, by rfl⟩ : syracuseStep 737327 = 1105991) B1105991
theorem B737351 : Blo 734326 737351 := bstep (se 1 (by rfl) ⟨553013, by rfl⟩ : syracuseStep 737351 = 1106027) B1106027
theorem B737407 : Blo 734326 737407 := bstep (se 1 (by rfl) ⟨553055, by rfl⟩ : syracuseStep 737407 = 1106111) B1106111
theorem B1654991 : Blo 734326 1654991 := bstep (se 1 (by rfl) ⟨1241243, by rfl⟩ : syracuseStep 1654991 = 2482487) B2482487
theorem B737531 : Blo 734326 737531 := bstep (se 1 (by rfl) ⟨553148, by rfl⟩ : syracuseStep 737531 = 1106297) B1106297
theorem B1491257 : Blo 734326 1491257 := bstep (se 2 (by rfl) ⟨559221, by rfl⟩ : syracuseStep 1491257 = 1118443) B1118443
theorem B8405369 : Blo 734326 8405369 := bstep (se 2 (by rfl) ⟨3152013, by rfl⟩ : syracuseStep 8405369 = 6304027) B6304027
theorem B193184135 : Blo 734326 193184135 := bstep (se 1 (by rfl) ⟨144888101, by rfl⟩ : syracuseStep 193184135 = 289776203) B289776203
theorem B737727 : Blo 734326 737727 := bstep (se 1 (by rfl) ⟨553295, by rfl⟩ : syracuseStep 737727 = 1106591) B1106591
theorem B1655351 : Blo 734326 1655351 := bstep (se 1 (by rfl) ⟨1241513, by rfl⟩ : syracuseStep 1655351 = 2483027) B2483027
theorem B737951 : Blo 734326 737951 := bstep (se 1 (by rfl) ⟨553463, by rfl⟩ : syracuseStep 737951 = 1106927) B1106927
theorem B738023 : Blo 734326 738023 := bstep (se 1 (by rfl) ⟨553517, by rfl⟩ : syracuseStep 738023 = 1107035) B1107035
theorem B738031 : Blo 734326 738031 := bstep (se 1 (by rfl) ⟨553523, by rfl⟩ : syracuseStep 738031 = 1107047) B1107047
theorem B738119 : Blo 734326 738119 := bstep (se 1 (by rfl) ⟨553589, by rfl⟩ : syracuseStep 738119 = 1107179) B1107179
theorem B7095107 : Blo 734326 7095107 := bstep (se 1 (by rfl) ⟨5321330, by rfl⟩ : syracuseStep 7095107 = 10642661) B10642661
theorem B1655711 : Blo 734326 1655711 := bstep (se 1 (by rfl) ⟨1241783, by rfl⟩ : syracuseStep 1655711 = 2483567) B2483567
theorem B738207 : Blo 734326 738207 := bstep (se 1 (by rfl) ⟨553655, by rfl⟩ : syracuseStep 738207 = 1107311) B1107311
theorem B738287 : Blo 734326 738287 := bstep (se 1 (by rfl) ⟨553715, by rfl⟩ : syracuseStep 738287 = 1107431) B1107431
theorem B6702113 : Blo 734326 6702113 := bstep (se 2 (by rfl) ⟨2513292, by rfl⟩ : syracuseStep 6702113 = 5026585) B5026585
theorem B1394167 : Blo 734326 1394167 := bstep (se 1 (by rfl) ⟨1045625, by rfl⟩ : syracuseStep 1394167 = 2091251) B2091251
theorem B4245967 : Blo 734326 4245967 := bstep (se 1 (by rfl) ⟨3184475, by rfl⟩ : syracuseStep 4245967 = 6368951) B6368951
theorem B1657295 : Blo 734326 1657295 := bstep (se 1 (by rfl) ⟨1242971, by rfl⟩ : syracuseStep 1657295 = 2485943) B2485943
theorem B4475645 : Blo 734326 4475645 := bstep (se 3 (by rfl) ⟨839183, by rfl⟩ : syracuseStep 4475645 = 1678367) B1678367
theorem B1395785 : Blo 734326 1395785 := bstep (se 2 (by rfl) ⟨523419, by rfl⟩ : syracuseStep 1395785 = 1046839) B1046839
theorem B1658267 : Blo 734326 1658267 := bstep (se 1 (by rfl) ⟨1243700, by rfl⟩ : syracuseStep 1658267 = 2487401) B2487401
theorem B4182455 : Blo 734326 4182455 := bstep (se 1 (by rfl) ⟨3136841, by rfl⟩ : syracuseStep 4182455 = 6273683) B6273683
theorem B4248071 : Blo 734326 4248071 := bstep (se 1 (by rfl) ⟨3186053, by rfl⟩ : syracuseStep 4248071 = 6372107) B6372107
theorem B1102463 : Blo 734326 1102463 := bstep (se 1 (by rfl) ⟨826847, by rfl⟩ : syracuseStep 1102463 = 1653695) B1653695
theorem B1102895 : Blo 734326 1102895 := bstep (se 1 (by rfl) ⟨827171, by rfl⟩ : syracuseStep 1102895 = 1654343) B1654343
theorem B1659995 : Blo 734326 1659995 := bstep (se 1 (by rfl) ⟨1244996, by rfl⟩ : syracuseStep 1659995 = 2489993) B2489993
theorem B1103015 : Blo 734326 1103015 := bstep (se 1 (by rfl) ⟨827261, by rfl⟩ : syracuseStep 1103015 = 1654523) B1654523
theorem B1103183 : Blo 734326 1103183 := bstep (se 1 (by rfl) ⟨827387, by rfl⟩ : syracuseStep 1103183 = 1654775) B1654775
theorem B1103423 : Blo 734326 1103423 := bstep (se 1 (by rfl) ⟨827567, by rfl⟩ : syracuseStep 1103423 = 1655135) B1655135
theorem B2479841 : Blo 734326 2479841 := bstep (se 2 (by rfl) ⟨929940, by rfl⟩ : syracuseStep 2479841 = 1859881) B1859881
theorem B1103783 : Blo 734326 1103783 := bstep (se 1 (by rfl) ⟨827837, by rfl⟩ : syracuseStep 1103783 = 1655675) B1655675
theorem B1103867 : Blo 734326 1103867 := bstep (se 1 (by rfl) ⟨827900, by rfl⟩ : syracuseStep 1103867 = 1655801) B1655801
theorem B1103903 : Blo 734326 1103903 := bstep (se 1 (by rfl) ⟨827927, by rfl⟩ : syracuseStep 1103903 = 1655855) B1655855
theorem B1103927 : Blo 734326 1103927 := bstep (se 1 (by rfl) ⟨827945, by rfl⟩ : syracuseStep 1103927 = 1655891) B1655891
theorem B1103993 : Blo 734326 1103993 := bstep (se 2 (by rfl) ⟨413997, by rfl⟩ : syracuseStep 1103993 = 827995) B827995
theorem B1104047 : Blo 734326 1104047 := bstep (se 1 (by rfl) ⟨828035, by rfl⟩ : syracuseStep 1104047 = 1656071) B1656071
theorem B1104335 : Blo 734326 1104335 := bstep (se 1 (by rfl) ⟨828251, by rfl⟩ : syracuseStep 1104335 = 1656503) B1656503
theorem B1104635 : Blo 734326 1104635 := bstep (se 1 (by rfl) ⟨828476, by rfl⟩ : syracuseStep 1104635 = 1656953) B1656953
theorem B1104761 : Blo 734326 1104761 := bstep (se 2 (by rfl) ⟨414285, by rfl⟩ : syracuseStep 1104761 = 828571) B828571
theorem B1104767 : Blo 734326 1104767 := bstep (se 1 (by rfl) ⟨828575, by rfl⟩ : syracuseStep 1104767 = 1657151) B1657151
theorem B1859183 : Blo 734326 1859183 := bstep (se 1 (by rfl) ⟨1394387, by rfl⟩ : syracuseStep 1859183 = 2788775) B2788775
theorem B2481839 : Blo 734326 2481839 := bstep (se 1 (by rfl) ⟨1861379, by rfl⟩ : syracuseStep 2481839 = 3722759) B3722759
theorem B1105673 : Blo 734326 1105673 := bstep (se 2 (by rfl) ⟨414627, by rfl⟩ : syracuseStep 1105673 = 829255) B829255
theorem B4186079 : Blo 734326 4186079 := bstep (se 1 (by rfl) ⟨3139559, by rfl⟩ : syracuseStep 4186079 = 6279119) B6279119
theorem B1400827 : Blo 734326 1400827 := bstep (se 1 (by rfl) ⟨1050620, by rfl⟩ : syracuseStep 1400827 = 2101241) B2101241
theorem B2482217 : Blo 734326 2482217 := bstep (se 2 (by rfl) ⟨930831, by rfl⟩ : syracuseStep 2482217 = 1861663) B1861663
theorem B94363937 : Blo 734326 94363937 := bstep (se 2 (by rfl) ⟨35386476, by rfl⟩ : syracuseStep 94363937 = 70772953) B70772953
theorem B3137935 : Blo 734326 3137935 := bstep (se 1 (by rfl) ⟨2353451, by rfl⟩ : syracuseStep 3137935 = 4706903) B4706903
theorem B4186511 : Blo 734326 4186511 := bstep (se 1 (by rfl) ⟨3139883, by rfl⟩ : syracuseStep 4186511 = 6279767) B6279767
theorem B1107071 : Blo 734326 1107071 := bstep (se 1 (by rfl) ⟨830303, by rfl⟩ : syracuseStep 1107071 = 1660607) B1660607
theorem B14181601 : Blo 734326 14181601 := bstep (se 2 (by rfl) ⟨5318100, by rfl⟩ : syracuseStep 14181601 = 10636201) B10636201
theorem B1107209 : Blo 734326 1107209 := bstep (se 2 (by rfl) ⟨415203, by rfl⟩ : syracuseStep 1107209 = 830407) B830407
theorem B3139337 : Blo 734326 3139337 := bstep (se 2 (by rfl) ⟨1177251, by rfl⟩ : syracuseStep 3139337 = 2354503) B2354503
theorem B3729401 : Blo 734326 3729401 := bstep (se 2 (by rfl) ⟨1398525, by rfl⟩ : syracuseStep 3729401 = 2797051) B2797051
theorem B3729563 : Blo 734326 3729563 := bstep (se 1 (by rfl) ⟨2797172, by rfl⟩ : syracuseStep 3729563 = 5594345) B5594345
theorem B1239529 : Blo 734326 1239529 := bstep (se 2 (by rfl) ⟨464823, by rfl⟩ : syracuseStep 1239529 = 929647) B929647
theorem B21228115 : Blo 734326 21228115 := bstep (se 1 (by rfl) ⟨15921086, by rfl⟩ : syracuseStep 21228115 = 31842173) B31842173
theorem B1993511 : Blo 734326 1993511 := bstep (se 1 (by rfl) ⟨1495133, by rfl⟩ : syracuseStep 1993511 = 2990267) B2990267
theorem B1240555 : Blo 734326 1240555 := bstep (se 1 (by rfl) ⟨930416, by rfl⟩ : syracuseStep 1240555 = 1860833) B1860833
theorem B14708567 : Blo 734326 14708567 := bstep (se 1 (by rfl) ⟨11031425, by rfl⟩ : syracuseStep 14708567 = 22062851) B22062851
theorem B5599205 : Blo 734326 5599205 := bstep (se 4 (by rfl) ⟨524925, by rfl⟩ : syracuseStep 5599205 = 1049851) B1049851
theorem B2519315 : Blo 734326 2519315 := bstep (se 1 (by rfl) ⟨1889486, by rfl⟩ : syracuseStep 2519315 = 3778973) B3778973
theorem B2487131 : Blo 734326 2487131 := bstep (se 1 (by rfl) ⟨1865348, by rfl⟩ : syracuseStep 2487131 = 3730697) B3730697
theorem B3142651 : Blo 734326 3142651 := bstep (se 1 (by rfl) ⟨2356988, by rfl⟩ : syracuseStep 3142651 = 4713977) B4713977
theorem B1242425 : Blo 734326 1242425 := bstep (se 2 (by rfl) ⟨465909, by rfl⟩ : syracuseStep 1242425 = 931819) B931819
theorem B1242479 : Blo 734326 1242479 := bstep (se 1 (by rfl) ⟨931859, by rfl⟩ : syracuseStep 1242479 = 1863719) B1863719
theorem B5043667 : Blo 734326 5043667 := bstep (se 1 (by rfl) ⟨3782750, by rfl⟩ : syracuseStep 5043667 = 7565501) B7565501
theorem B16152335 : Blo 734326 16152335 := bstep (se 1 (by rfl) ⟨12114251, by rfl⟩ : syracuseStep 16152335 = 24228503) B24228503
theorem B1243039 : Blo 734326 1243039 := bstep (se 1 (by rfl) ⟨932279, by rfl⟩ : syracuseStep 1243039 = 1864559) B1864559
theorem B3143711 : Blo 734326 3143711 := bstep (se 1 (by rfl) ⟨2357783, by rfl⟩ : syracuseStep 3143711 = 4715567) B4715567
theorem B1046639 : Blo 734326 1046639 := bstep (se 1 (by rfl) ⟨784979, by rfl⟩ : syracuseStep 1046639 = 1569959) B1569959
theorem B3144359 : Blo 734326 3144359 := bstep (se 1 (by rfl) ⟨2358269, by rfl⟩ : syracuseStep 3144359 = 4716539) B4716539
theorem B2489129 : Blo 734326 2489129 := bstep (se 2 (by rfl) ⟨933423, by rfl⟩ : syracuseStep 2489129 = 1866847) B1866847
theorem B15891335 : Blo 734326 15891335 := bstep (se 1 (by rfl) ⟨11918501, by rfl⟩ : syracuseStep 15891335 = 23837003) B23837003
theorem B7568423 : Blo 734326 7568423 := bstep (se 1 (by rfl) ⟨5676317, by rfl⟩ : syracuseStep 7568423 = 11352635) B11352635
theorem B3734585 : Blo 734326 3734585 := bstep (se 2 (by rfl) ⟨1400469, by rfl⟩ : syracuseStep 3734585 = 2800939) B2800939
theorem B2456659 : Blo 734326 2456659 := bstep (se 1 (by rfl) ⟨1842494, by rfl⟩ : syracuseStep 2456659 = 3684989) B3684989
theorem B1244315 : Blo 734326 1244315 := bstep (se 1 (by rfl) ⟨933236, by rfl⟩ : syracuseStep 1244315 = 1866473) B1866473
theorem B1244335 : Blo 734326 1244335 := bstep (se 1 (by rfl) ⟨933251, by rfl⟩ : syracuseStep 1244335 = 1866503) B1866503
theorem B7077041 : Blo 734326 7077041 := bstep (se 2 (by rfl) ⟨2653890, by rfl⟩ : syracuseStep 7077041 = 5307781) B5307781
theorem B1867657 : Blo 734326 1867657 := bstep (se 2 (by rfl) ⟨700371, by rfl⟩ : syracuseStep 1867657 = 1400743) B1400743
theorem B5603579 : Blo 734326 5603579 := bstep (se 1 (by rfl) ⟨4202684, by rfl⟩ : syracuseStep 5603579 = 8405369) B8405369
theorem B4653677 : Blo 734326 4653677 := bstep (se 3 (by rfl) ⟨872564, by rfl⟩ : syracuseStep 4653677 = 1745129) B1745129
theorem B6816419 : Blo 734326 6816419 := bstep (se 1 (by rfl) ⟨5112314, by rfl⟩ : syracuseStep 6816419 = 10224629) B10224629
theorem B3736691 : Blo 734326 3736691 := bstep (se 1 (by rfl) ⟨2802518, by rfl⟩ : syracuseStep 3736691 = 5605037) B5605037
theorem B18908801 : Blo 734326 18908801 := bstep (se 2 (by rfl) ⟨7090800, by rfl⟩ : syracuseStep 18908801 = 14181601) B14181601
theorem B2983763 : Blo 734326 2983763 := bstep (se 1 (by rfl) ⟨2237822, by rfl⟩ : syracuseStep 2983763 = 4475645) B4475645
theorem B17238131 : Blo 734326 17238131 := bstep (se 1 (by rfl) ⟨12928598, by rfl⟩ : syracuseStep 17238131 = 25857197) B25857197
theorem B4196717 : Blo 734326 4196717 := bstep (se 3 (by rfl) ⟨786884, by rfl⟩ : syracuseStep 4196717 = 1573769) B1573769
theorem B2788303 : Blo 734326 2788303 := bstep (se 1 (by rfl) ⟨2091227, by rfl⟩ : syracuseStep 2788303 = 4182455) B4182455
theorem B2100455 : Blo 734326 2100455 := bstep (se 1 (by rfl) ⟨1575341, by rfl⟩ : syracuseStep 2100455 = 3150683) B3150683
theorem B3542633 : Blo 734326 3542633 := bstep (se 2 (by rfl) ⟨1328487, by rfl⟩ : syracuseStep 3542633 = 2656975) B2656975
theorem B13438979 : Blo 734326 13438979 := bstep (se 1 (by rfl) ⟨10079234, by rfl⟩ : syracuseStep 13438979 = 20158469) B20158469
theorem B3543095 : Blo 734326 3543095 := bstep (se 1 (by rfl) ⟨2657321, by rfl⟩ : syracuseStep 3543095 = 5314643) B5314643
theorem B5968205 : Blo 734326 5968205 := bstep (se 3 (by rfl) ⟨1119038, by rfl⟩ : syracuseStep 5968205 = 2238077) B2238077
theorem B2790719 : Blo 734326 2790719 := bstep (se 1 (by rfl) ⟨2093039, by rfl⟩ : syracuseStep 2790719 = 4186079) B4186079
theorem B4199951 : Blo 734326 4199951 := bstep (se 1 (by rfl) ⟨3149963, by rfl⟩ : syracuseStep 4199951 = 6299927) B6299927
theorem B2791007 : Blo 734326 2791007 := bstep (se 1 (by rfl) ⟨2093255, by rfl⟩ : syracuseStep 2791007 = 4186511) B4186511
theorem B2791037 : Blo 734326 2791037 := bstep (se 3 (by rfl) ⟨523319, by rfl⟩ : syracuseStep 2791037 = 1046639) B1046639
theorem B28382885 : Blo 734326 28382885 := bstep (se 4 (by rfl) ⟨2660895, by rfl⟩ : syracuseStep 28382885 = 5321791) B5321791
theorem B76519201 : Blo 734326 76519201 := bstep (se 2 (by rfl) ⟨28694700, by rfl⟩ : syracuseStep 76519201 = 57389401) B57389401
theorem B4724639 : Blo 734326 4724639 := bstep (se 1 (by rfl) ⟨3543479, by rfl⟩ : syracuseStep 4724639 = 7086959) B7086959
theorem B8395163 : Blo 734326 8395163 := bstep (se 1 (by rfl) ⟨6296372, by rfl⟩ : syracuseStep 8395163 = 12592745) B12592745
theorem B6724889 : Blo 734326 6724889 := bstep (se 2 (by rfl) ⟨2521833, by rfl⟩ : syracuseStep 6724889 = 5043667) B5043667
theorem B5316029 : Blo 734326 5316029 := bstep (se 3 (by rfl) ⟨996755, by rfl⟩ : syracuseStep 5316029 = 1993511) B1993511
theorem B9805711 : Blo 734326 9805711 := bstep (se 1 (by rfl) ⟨7354283, by rfl⟩ : syracuseStep 9805711 = 14708567) B14708567
theorem B1679543 : Blo 734326 1679543 := bstep (se 1 (by rfl) ⟨1259657, by rfl⟩ : syracuseStep 1679543 = 2519315) B2519315
theorem B4203049 : Blo 734326 4203049 := bstep (se 2 (by rfl) ⟨1576143, by rfl⟩ : syracuseStep 4203049 = 3152287) B3152287
theorem B828283 : Blo 734326 828283 := bstep (se 1 (by rfl) ⟨621212, by rfl⟩ : syracuseStep 828283 = 1242425) B1242425
theorem B828319 : Blo 734326 828319 := bstep (se 1 (by rfl) ⟨621239, by rfl⟩ : syracuseStep 828319 = 1242479) B1242479
theorem B4203575 : Blo 734326 4203575 := bstep (se 1 (by rfl) ⟨3152681, by rfl⟩ : syracuseStep 4203575 = 6305363) B6305363
theorem B4040189 : Blo 734326 4040189 := bstep (se 3 (by rfl) ⟨757535, by rfl⟩ : syracuseStep 4040189 = 1515071) B1515071
theorem B10594223 : Blo 734326 10594223 := bstep (se 1 (by rfl) ⟨7945667, by rfl⟩ : syracuseStep 10594223 = 15891335) B15891335
theorem B829543 : Blo 734326 829543 := bstep (se 1 (by rfl) ⟨622157, by rfl⟩ : syracuseStep 829543 = 1244315) B1244315
theorem B7088957 : Blo 734326 7088957 := bstep (se 3 (by rfl) ⟨1329179, by rfl⟩ : syracuseStep 7088957 = 2658359) B2658359
theorem B128789423 : Blo 734326 128789423 := bstep (se 1 (by rfl) ⟨96592067, by rfl⟩ : syracuseStep 128789423 = 193184135) B193184135
theorem B4730071 : Blo 734326 4730071 := bstep (se 1 (by rfl) ⟨3547553, by rfl⟩ : syracuseStep 4730071 = 7095107) B7095107
theorem B3976685 : Blo 734326 3976685 := bstep (se 3 (by rfl) ⟨745628, by rfl⟩ : syracuseStep 3976685 = 1491257) B1491257
theorem B930523 : Blo 734326 930523 := bstep (se 1 (by rfl) ⟨697892, by rfl⟩ : syracuseStep 930523 = 1395785) B1395785
theorem B17872301 : Blo 734326 17872301 := bstep (se 3 (by rfl) ⟨3351056, by rfl⟩ : syracuseStep 17872301 = 6702113) B6702113
theorem B2832047 : Blo 734326 2832047 := bstep (se 1 (by rfl) ⟨2124035, by rfl⟩ : syracuseStep 2832047 = 4248071) B4248071
theorem B734975 : Blo 734326 734975 := bstep (se 1 (by rfl) ⟨551231, by rfl⟩ : syracuseStep 734975 = 1102463) B1102463
theorem B2012953 : Blo 734326 2012953 := bstep (se 2 (by rfl) ⟨754857, by rfl⟩ : syracuseStep 2012953 = 1509715) B1509715
theorem B1652705 : Blo 734326 1652705 := bstep (se 2 (by rfl) ⟨619764, by rfl⟩ : syracuseStep 1652705 = 1239529) B1239529
theorem B735263 : Blo 734326 735263 := bstep (se 1 (by rfl) ⟨551447, by rfl⟩ : syracuseStep 735263 = 1102895) B1102895
theorem B7092305 : Blo 734326 7092305 := bstep (se 2 (by rfl) ⟨2659614, by rfl⟩ : syracuseStep 7092305 = 5319229) B5319229
theorem B735343 : Blo 734326 735343 := bstep (se 1 (by rfl) ⟨551507, by rfl⟩ : syracuseStep 735343 = 1103015) B1103015
theorem B735455 : Blo 734326 735455 := bstep (se 1 (by rfl) ⟨551591, by rfl⟩ : syracuseStep 735455 = 1103183) B1103183
theorem B735615 : Blo 734326 735615 := bstep (se 1 (by rfl) ⟨551711, by rfl⟩ : syracuseStep 735615 = 1103423) B1103423
theorem B1653227 : Blo 734326 1653227 := bstep (se 1 (by rfl) ⟨1239920, by rfl⟩ : syracuseStep 1653227 = 2479841) B2479841
theorem B735855 : Blo 734326 735855 := bstep (se 1 (by rfl) ⟨551891, by rfl⟩ : syracuseStep 735855 = 1103783) B1103783
theorem B735911 : Blo 734326 735911 := bstep (se 1 (by rfl) ⟨551933, by rfl⟩ : syracuseStep 735911 = 1103867) B1103867
theorem B735935 : Blo 734326 735935 := bstep (se 1 (by rfl) ⟨551951, by rfl⟩ : syracuseStep 735935 = 1103903) B1103903
theorem B735951 : Blo 734326 735951 := bstep (se 1 (by rfl) ⟨551963, by rfl⟩ : syracuseStep 735951 = 1103927) B1103927
theorem B735995 : Blo 734326 735995 := bstep (se 1 (by rfl) ⟨551996, by rfl⟩ : syracuseStep 735995 = 1103993) B1103993
theorem B3717899 : Blo 734326 3717899 := bstep (se 1 (by rfl) ⟨2788424, by rfl⟩ : syracuseStep 3717899 = 5576849) B5576849
theorem B736031 : Blo 734326 736031 := bstep (se 1 (by rfl) ⟨552023, by rfl⟩ : syracuseStep 736031 = 1104047) B1104047
theorem B736223 : Blo 734326 736223 := bstep (se 1 (by rfl) ⟨552167, by rfl⟩ : syracuseStep 736223 = 1104335) B1104335
theorem B3062951 : Blo 734326 3062951 := bstep (se 1 (by rfl) ⟨2297213, by rfl⟩ : syracuseStep 3062951 = 4594427) B4594427
theorem B736423 : Blo 734326 736423 := bstep (se 1 (by rfl) ⟨552317, by rfl⟩ : syracuseStep 736423 = 1104635) B1104635
theorem B736507 : Blo 734326 736507 := bstep (se 1 (by rfl) ⟨552380, by rfl⟩ : syracuseStep 736507 = 1104761) B1104761
theorem B736511 : Blo 734326 736511 := bstep (se 1 (by rfl) ⟨552383, by rfl⟩ : syracuseStep 736511 = 1104767) B1104767
theorem B1654073 : Blo 734326 1654073 := bstep (se 2 (by rfl) ⟨620277, by rfl⟩ : syracuseStep 1654073 = 1240555) B1240555
theorem B1654559 : Blo 734326 1654559 := bstep (se 1 (by rfl) ⟨1240919, by rfl⟩ : syracuseStep 1654559 = 2481839) B2481839
theorem B737115 : Blo 734326 737115 := bstep (se 1 (by rfl) ⟨552836, by rfl⟩ : syracuseStep 737115 = 1105673) B1105673
theorem B1654811 : Blo 734326 1654811 := bstep (se 1 (by rfl) ⟨1241108, by rfl⟩ : syracuseStep 1654811 = 2482217) B2482217
theorem B738047 : Blo 734326 738047 := bstep (se 1 (by rfl) ⟨553535, by rfl⟩ : syracuseStep 738047 = 1107071) B1107071
theorem B738139 : Blo 734326 738139 := bstep (se 1 (by rfl) ⟨553604, by rfl⟩ : syracuseStep 738139 = 1107209) B1107209
theorem B3196025 : Blo 734326 3196025 := bstep (se 2 (by rfl) ⟨1198509, by rfl⟩ : syracuseStep 3196025 = 2397019) B2397019
theorem B15123773 : Blo 734326 15123773 := bstep (se 3 (by rfl) ⟨2835707, by rfl⟩ : syracuseStep 15123773 = 5671415) B5671415
theorem B9554411 : Blo 734326 9554411 := bstep (se 1 (by rfl) ⟨7165808, by rfl⟩ : syracuseStep 9554411 = 14331617) B14331617
theorem B1657385 : Blo 734326 1657385 := bstep (se 2 (by rfl) ⟨621519, by rfl⟩ : syracuseStep 1657385 = 1243039) B1243039
theorem B3984167 : Blo 734326 3984167 := bstep (se 1 (by rfl) ⟨2988125, by rfl⟩ : syracuseStep 3984167 = 5976251) B5976251
theorem B8408285 : Blo 734326 8408285 := bstep (se 3 (by rfl) ⟨1576553, by rfl⟩ : syracuseStep 8408285 = 3153107) B3153107
theorem B1658087 : Blo 734326 1658087 := bstep (se 1 (by rfl) ⟨1243565, by rfl⟩ : syracuseStep 1658087 = 2487131) B2487131
theorem B2018771 : Blo 734326 2018771 := bstep (se 1 (by rfl) ⟨1514078, by rfl⟩ : syracuseStep 2018771 = 3028157) B3028157
theorem B10768223 : Blo 734326 10768223 := bstep (se 1 (by rfl) ⟨8076167, by rfl⟩ : syracuseStep 10768223 = 16152335) B16152335
theorem B3723407 : Blo 734326 3723407 := bstep (se 1 (by rfl) ⟨2792555, by rfl⟩ : syracuseStep 3723407 = 5585111) B5585111
theorem B1659113 : Blo 734326 1659113 := bstep (se 2 (by rfl) ⟨622167, by rfl⟩ : syracuseStep 1659113 = 1244335) B1244335
theorem B2478383 : Blo 734326 2478383 := bstep (se 1 (by rfl) ⟨1858787, by rfl⟩ : syracuseStep 2478383 = 3717575) B3717575
theorem B1659419 : Blo 734326 1659419 := bstep (se 1 (by rfl) ⟨1244564, by rfl⟩ : syracuseStep 1659419 = 2489129) B2489129
theorem B1103273 : Blo 734326 1103273 := bstep (se 2 (by rfl) ⟨413727, by rfl⟩ : syracuseStep 1103273 = 827455) B827455
theorem B1103327 : Blo 734326 1103327 := bstep (se 1 (by rfl) ⟨827495, by rfl⟩ : syracuseStep 1103327 = 1654991) B1654991
theorem B1103567 : Blo 734326 1103567 := bstep (se 1 (by rfl) ⟨827675, by rfl⟩ : syracuseStep 1103567 = 1655351) B1655351
theorem B16570169 : Blo 734326 16570169 := bstep (se 2 (by rfl) ⟨6213813, by rfl⟩ : syracuseStep 16570169 = 12427627) B12427627
theorem B4183913 : Blo 734326 4183913 := bstep (se 2 (by rfl) ⟨1568967, by rfl⟩ : syracuseStep 4183913 = 3137935) B3137935
theorem B1103807 : Blo 734326 1103807 := bstep (se 1 (by rfl) ⟨827855, by rfl⟩ : syracuseStep 1103807 = 1655711) B1655711
theorem B1661111 : Blo 734326 1661111 := bstep (se 1 (by rfl) ⟨1245833, by rfl⟩ : syracuseStep 1661111 = 2491667) B2491667
theorem B275929811 : Blo 734326 275929811 := bstep (se 1 (by rfl) ⟨206947358, by rfl⟩ : syracuseStep 275929811 = 413894717) B413894717
theorem B1399673 : Blo 734326 1399673 := bstep (se 2 (by rfl) ⟨524877, by rfl⟩ : syracuseStep 1399673 = 1049755) B1049755
theorem B1104863 : Blo 734326 1104863 := bstep (se 1 (by rfl) ⟨828647, by rfl⟩ : syracuseStep 1104863 = 1657295) B1657295
theorem B1858889 : Blo 734326 1858889 := bstep (se 2 (by rfl) ⟨697083, by rfl⟩ : syracuseStep 1858889 = 1394167) B1394167
theorem B1859051 : Blo 734326 1859051 := bstep (se 1 (by rfl) ⟨1394288, by rfl⟩ : syracuseStep 1859051 = 2788577) B2788577
theorem B1105511 : Blo 734326 1105511 := bstep (se 1 (by rfl) ⟨829133, by rfl⟩ : syracuseStep 1105511 = 1658267) B1658267
theorem B5661289 : Blo 734326 5661289 := bstep (se 2 (by rfl) ⟨2122983, by rfl⟩ : syracuseStep 5661289 = 4245967) B4245967
theorem B1106537 : Blo 734326 1106537 := bstep (se 2 (by rfl) ⟨414951, by rfl⟩ : syracuseStep 1106537 = 829903) B829903
theorem B1106663 : Blo 734326 1106663 := bstep (se 1 (by rfl) ⟨829997, by rfl⟩ : syracuseStep 1106663 = 1659995) B1659995
theorem B28304153 : Blo 734326 28304153 := bstep (se 2 (by rfl) ⟨10614057, by rfl⟩ : syracuseStep 28304153 = 21228115) B21228115
theorem B1796051 : Blo 734326 1796051 := bstep (se 1 (by rfl) ⟨1347038, by rfl⟩ : syracuseStep 1796051 = 2694077) B2694077
theorem B24176837 : Blo 734326 24176837 := bstep (se 4 (by rfl) ⟨2266578, by rfl⟩ : syracuseStep 24176837 = 4533157) B4533157
theorem B7563527 : Blo 734326 7563527 := bstep (se 1 (by rfl) ⟨5672645, by rfl⟩ : syracuseStep 7563527 = 11345291) B11345291
theorem B1239455 : Blo 734326 1239455 := bstep (se 1 (by rfl) ⟨929591, by rfl⟩ : syracuseStep 1239455 = 1859183) B1859183
theorem B4483943 : Blo 734326 4483943 := bstep (se 1 (by rfl) ⟨3362957, by rfl⟩ : syracuseStep 4483943 = 6725915) B6725915
theorem B62909291 : Blo 734326 62909291 := bstep (se 1 (by rfl) ⟨47181968, by rfl⟩ : syracuseStep 62909291 = 94363937) B94363937
theorem B13102181 : Blo 734326 13102181 := bstep (se 4 (by rfl) ⟨1228329, by rfl⟩ : syracuseStep 13102181 = 2456659) B2456659
theorem B1863071 : Blo 734326 1863071 := bstep (se 1 (by rfl) ⟨1397303, by rfl⟩ : syracuseStep 1863071 = 2794607) B2794607
theorem B2092891 : Blo 734326 2092891 := bstep (se 1 (by rfl) ⟨1569668, by rfl⟩ : syracuseStep 2092891 = 3139337) B3139337
theorem B4190201 : Blo 734326 4190201 := bstep (se 2 (by rfl) ⟨1571325, by rfl⟩ : syracuseStep 4190201 = 3142651) B3142651
theorem B2486267 : Blo 734326 2486267 := bstep (se 1 (by rfl) ⟨1864700, by rfl⟩ : syracuseStep 2486267 = 3729401) B3729401
theorem B2486375 : Blo 734326 2486375 := bstep (se 1 (by rfl) ⟨1864781, by rfl⟩ : syracuseStep 2486375 = 3729563) B3729563
theorem B8384957 : Blo 734326 8384957 := bstep (se 3 (by rfl) ⟨1572179, by rfl⟩ : syracuseStep 8384957 = 3144359) B3144359
theorem B3732803 : Blo 734326 3732803 := bstep (se 1 (by rfl) ⟨2799602, by rfl⟩ : syracuseStep 3732803 = 5599205) B5599205
theorem B35780413 : Blo 734326 35780413 := bstep (se 3 (by rfl) ⟨6708827, by rfl⟩ : syracuseStep 35780413 = 13417655) B13417655
theorem B1865663 : Blo 734326 1865663 := bstep (se 1 (by rfl) ⟨1399247, by rfl⟩ : syracuseStep 1865663 = 2798495) B2798495
theorem B2095807 : Blo 734326 2095807 := bstep (se 1 (by rfl) ⟨1571855, by rfl⟩ : syracuseStep 2095807 = 3143711) B3143711
theorem B1866959 : Blo 734326 1866959 := bstep (se 1 (by rfl) ⟨1400219, by rfl⟩ : syracuseStep 1866959 = 2800439) B2800439
theorem B5045615 : Blo 734326 5045615 := bstep (se 1 (by rfl) ⟨3784211, by rfl⟩ : syracuseStep 5045615 = 7568423) B7568423
theorem B2489723 : Blo 734326 2489723 := bstep (se 1 (by rfl) ⟨1867292, by rfl⟩ : syracuseStep 2489723 = 3734585) B3734585
theorem B4718027 : Blo 734326 4718027 := bstep (se 1 (by rfl) ⟨3538520, by rfl⟩ : syracuseStep 4718027 = 7077041) B7077041
theorem B2490209 : Blo 734326 2490209 := bstep (se 2 (by rfl) ⟨933828, by rfl⟩ : syracuseStep 2490209 = 1867657) B1867657
theorem B1867769 : Blo 734326 1867769 := bstep (se 2 (by rfl) ⟨700413, by rfl⟩ : syracuseStep 1867769 = 1400827) B1400827
theorem B3735719 : Blo 734326 3735719 := bstep (se 1 (by rfl) ⟨2801789, by rfl⟩ : syracuseStep 3735719 = 5603579) B5603579
theorem B5604065 : Blo 734326 5604065 := bstep (se 2 (by rfl) ⟨2101524, by rfl⟩ : syracuseStep 5604065 = 4203049) B4203049
theorem B2491127 : Blo 734326 2491127 := bstep (se 1 (by rfl) ⟨1868345, by rfl⟩ : syracuseStep 2491127 = 3736691) B3736691
theorem B2130683 : Blo 734326 2130683 := bstep (se 1 (by rfl) ⟨1598012, by rfl⟩ : syracuseStep 2130683 = 3196025) B3196025
theorem B5605523 : Blo 734326 5605523 := bstep (se 1 (by rfl) ⟨4204142, by rfl⟩ : syracuseStep 5605523 = 8408285) B8408285
theorem B1345847 : Blo 734326 1345847 := bstep (se 1 (by rfl) ⟨1009385, by rfl⟩ : syracuseStep 1345847 = 2018771) B2018771
theorem B2361755 : Blo 734326 2361755 := bstep (se 1 (by rfl) ⟨1771316, by rfl⟩ : syracuseStep 2361755 = 3542633) B3542633
theorem B7178815 : Blo 734326 7178815 := bstep (se 1 (by rfl) ⟨5384111, by rfl⟩ : syracuseStep 7178815 = 10768223) B10768223
theorem B2362063 : Blo 734326 2362063 := bstep (se 1 (by rfl) ⟨1771547, by rfl⟩ : syracuseStep 2362063 = 3543095) B3543095
theorem B11046779 : Blo 734326 11046779 := bstep (se 1 (by rfl) ⟨8285084, by rfl⟩ : syracuseStep 11046779 = 16570169) B16570169
theorem B2789275 : Blo 734326 2789275 := bstep (se 1 (by rfl) ⟨2091956, by rfl⟩ : syracuseStep 2789275 = 4183913) B4183913
theorem B3149759 : Blo 734326 3149759 := bstep (se 1 (by rfl) ⟨2362319, by rfl⟩ : syracuseStep 3149759 = 4724639) B4724639
theorem B3544019 : Blo 734326 3544019 := bstep (se 1 (by rfl) ⟨2658014, by rfl⟩ : syracuseStep 3544019 = 5316029) B5316029
theorem B2790521 : Blo 734326 2790521 := bstep (se 2 (by rfl) ⟨1046445, by rfl⟩ : syracuseStep 2790521 = 2092891) B2092891
theorem B4789469 : Blo 734326 4789469 := bstep (se 3 (by rfl) ⟨898025, by rfl⟩ : syracuseStep 4789469 = 1796051) B1796051
theorem B1119695 : Blo 734326 1119695 := bstep (se 1 (by rfl) ⟨839771, by rfl⟩ : syracuseStep 1119695 = 1679543) B1679543
theorem B2693459 : Blo 734326 2693459 := bstep (se 1 (by rfl) ⟨2020094, by rfl⟩ : syracuseStep 2693459 = 4040189) B4040189
theorem B826303 : Blo 734326 826303 := bstep (se 1 (by rfl) ⟨619727, by rfl⟩ : syracuseStep 826303 = 1239455) B1239455
theorem B4725971 : Blo 734326 4725971 := bstep (se 1 (by rfl) ⟨3544478, by rfl⟩ : syracuseStep 4725971 = 7088957) B7088957
theorem B2989295 : Blo 734326 2989295 := bstep (se 1 (by rfl) ⟨2241971, by rfl⟩ : syracuseStep 2989295 = 4483943) B4483943
theorem B85859615 : Blo 734326 85859615 := bstep (se 1 (by rfl) ⟨64394711, by rfl⟩ : syracuseStep 85859615 = 128789423) B128789423
theorem B10624445 : Blo 734326 10624445 := bstep (se 3 (by rfl) ⟨1992083, by rfl⟩ : syracuseStep 10624445 = 3984167) B3984167
theorem B2793467 : Blo 734326 2793467 := bstep (se 1 (by rfl) ⟨2095100, by rfl⟩ : syracuseStep 2793467 = 4190201) B4190201
theorem B2794409 : Blo 734326 2794409 := bstep (se 2 (by rfl) ⟨1047903, by rfl⟩ : syracuseStep 2794409 = 2095807) B2095807
theorem B4728203 : Blo 734326 4728203 := bstep (se 1 (by rfl) ⟨3546152, by rfl⟩ : syracuseStep 4728203 = 7092305) B7092305
theorem B2041967 : Blo 734326 2041967 := bstep (se 1 (by rfl) ⟨1531475, by rfl⟩ : syracuseStep 2041967 = 3062951) B3062951
theorem B7548385 : Blo 734326 7548385 := bstep (se 2 (by rfl) ⟨2830644, by rfl⟩ : syracuseStep 7548385 = 5661289) B5661289
theorem B183873397 : Blo 734326 183873397 := bstep (se 5 (by rfl) ⟨8619065, by rfl⟩ : syracuseStep 183873397 = 17238131) B17238131
theorem B2797811 : Blo 734326 2797811 := bstep (se 1 (by rfl) ⟨2098358, by rfl⟩ : syracuseStep 2797811 = 4196717) B4196717
theorem B6369607 : Blo 734326 6369607 := bstep (se 1 (by rfl) ⟨4777205, by rfl⟩ : syracuseStep 6369607 = 9554411) B9554411
theorem B8959319 : Blo 734326 8959319 := bstep (se 1 (by rfl) ⟨6719489, by rfl⟩ : syracuseStep 8959319 = 13438979) B13438979
theorem B1652255 : Blo 734326 1652255 := bstep (se 1 (by rfl) ⟨1239191, by rfl⟩ : syracuseStep 1652255 = 2478383) B2478383
theorem B3978803 : Blo 734326 3978803 := bstep (se 1 (by rfl) ⟨2984102, by rfl⟩ : syracuseStep 3978803 = 5968205) B5968205
theorem B735515 : Blo 734326 735515 := bstep (se 1 (by rfl) ⟨551636, by rfl⟩ : syracuseStep 735515 = 1103273) B1103273
theorem B735551 : Blo 734326 735551 := bstep (se 1 (by rfl) ⟨551663, by rfl⟩ : syracuseStep 735551 = 1103327) B1103327
theorem B2799967 : Blo 734326 2799967 := bstep (se 1 (by rfl) ⟨2099975, by rfl⟩ : syracuseStep 2799967 = 4199951) B4199951
theorem B18921923 : Blo 734326 18921923 := bstep (se 1 (by rfl) ⟨14191442, by rfl⟩ : syracuseStep 18921923 = 28382885) B28382885
theorem B735711 : Blo 734326 735711 := bstep (se 1 (by rfl) ⟨551783, by rfl⟩ : syracuseStep 735711 = 1103567) B1103567
theorem B3717737 : Blo 734326 3717737 := bstep (se 2 (by rfl) ⟨1394151, by rfl⟩ : syracuseStep 3717737 = 2788303) B2788303
theorem B735871 : Blo 734326 735871 := bstep (se 1 (by rfl) ⟨551903, by rfl⟩ : syracuseStep 735871 = 1103807) B1103807
theorem B6306761 : Blo 734326 6306761 := bstep (se 2 (by rfl) ⟨2365035, by rfl⟩ : syracuseStep 6306761 = 4730071) B4730071
theorem B933115 : Blo 734326 933115 := bstep (se 1 (by rfl) ⟨699836, by rfl⟩ : syracuseStep 933115 = 1399673) B1399673
theorem B736575 : Blo 734326 736575 := bstep (se 1 (by rfl) ⟨552431, by rfl⟩ : syracuseStep 736575 = 1104863) B1104863
theorem B737007 : Blo 734326 737007 := bstep (se 1 (by rfl) ⟨552755, by rfl⟩ : syracuseStep 737007 = 1105511) B1105511
theorem B737691 : Blo 734326 737691 := bstep (se 1 (by rfl) ⟨553268, by rfl⟩ : syracuseStep 737691 = 1106537) B1106537
theorem B737775 : Blo 734326 737775 := bstep (se 1 (by rfl) ⟨553331, by rfl⟩ : syracuseStep 737775 = 1106663) B1106663
theorem B64471565 : Blo 734326 64471565 := bstep (se 3 (by rfl) ⟨12088418, by rfl⟩ : syracuseStep 64471565 = 24176837) B24176837
theorem B2802383 : Blo 734326 2802383 := bstep (se 1 (by rfl) ⟨2101787, by rfl⟩ : syracuseStep 2802383 = 4203575) B4203575
theorem B7062815 : Blo 734326 7062815 := bstep (se 1 (by rfl) ⟨5297111, by rfl⟩ : syracuseStep 7062815 = 10594223) B10594223
theorem B8734787 : Blo 734326 8734787 := bstep (se 1 (by rfl) ⟨6551090, by rfl⟩ : syracuseStep 8734787 = 13102181) B13102181
theorem B102025601 : Blo 734326 102025601 := bstep (se 2 (by rfl) ⟨38259600, by rfl⟩ : syracuseStep 102025601 = 76519201) B76519201
theorem B1657511 : Blo 734326 1657511 := bstep (se 1 (by rfl) ⟨1243133, by rfl⟩ : syracuseStep 1657511 = 2486267) B2486267
theorem B1657583 : Blo 734326 1657583 := bstep (se 1 (by rfl) ⟨1243187, by rfl⟩ : syracuseStep 1657583 = 2486375) B2486375
theorem B5589971 : Blo 734326 5589971 := bstep (se 1 (by rfl) ⟨4192478, by rfl⟩ : syracuseStep 5589971 = 8384957) B8384957
theorem B11914867 : Blo 734326 11914867 := bstep (se 1 (by rfl) ⟨8936150, by rfl⟩ : syracuseStep 11914867 = 17872301) B17872301
theorem B1888031 : Blo 734326 1888031 := bstep (se 1 (by rfl) ⟨1416023, by rfl⟩ : syracuseStep 1888031 = 2832047) B2832047
theorem B1101803 : Blo 734326 1101803 := bstep (se 1 (by rfl) ⟨826352, by rfl⟩ : syracuseStep 1101803 = 1652705) B1652705
theorem B1102151 : Blo 734326 1102151 := bstep (se 1 (by rfl) ⟨826613, by rfl⟩ : syracuseStep 1102151 = 1653227) B1653227
theorem B2478599 : Blo 734326 2478599 := bstep (se 1 (by rfl) ⟨1858949, by rfl⟩ : syracuseStep 2478599 = 3717899) B3717899
theorem B1102715 : Blo 734326 1102715 := bstep (se 1 (by rfl) ⟨827036, by rfl⟩ : syracuseStep 1102715 = 1654073) B1654073
theorem B3363743 : Blo 734326 3363743 := bstep (se 1 (by rfl) ⟨2522807, by rfl⟩ : syracuseStep 3363743 = 5045615) B5045615
theorem B1659815 : Blo 734326 1659815 := bstep (se 1 (by rfl) ⟨1244861, by rfl⟩ : syracuseStep 1659815 = 2489723) B2489723
theorem B1103039 : Blo 734326 1103039 := bstep (se 1 (by rfl) ⟨827279, by rfl⟩ : syracuseStep 1103039 = 1654559) B1654559
theorem B1660139 : Blo 734326 1660139 := bstep (se 1 (by rfl) ⟨1245104, by rfl⟩ : syracuseStep 1660139 = 2490209) B2490209
theorem B1103207 : Blo 734326 1103207 := bstep (se 1 (by rfl) ⟨827405, by rfl⟩ : syracuseStep 1103207 = 1654811) B1654811
theorem B4544279 : Blo 734326 4544279 := bstep (se 1 (by rfl) ⟨3408209, by rfl⟩ : syracuseStep 4544279 = 6816419) B6816419
theorem B10082515 : Blo 734326 10082515 := bstep (se 1 (by rfl) ⟨7561886, by rfl⟩ : syracuseStep 10082515 = 15123773) B15123773
theorem B12605867 : Blo 734326 12605867 := bstep (se 1 (by rfl) ⟨9454400, by rfl⟩ : syracuseStep 12605867 = 18908801) B18908801
theorem B1104377 : Blo 734326 1104377 := bstep (se 2 (by rfl) ⟨414141, by rfl⟩ : syracuseStep 1104377 = 828283) B828283
theorem B1104425 : Blo 734326 1104425 := bstep (se 2 (by rfl) ⟨414159, by rfl⟩ : syracuseStep 1104425 = 828319) B828319
theorem B12409805 : Blo 734326 12409805 := bstep (se 3 (by rfl) ⟨2326838, by rfl⟩ : syracuseStep 12409805 = 4653677) B4653677
theorem B1104923 : Blo 734326 1104923 := bstep (se 1 (by rfl) ⟨828692, by rfl⟩ : syracuseStep 1104923 = 1657385) B1657385
theorem B1105391 : Blo 734326 1105391 := bstep (se 1 (by rfl) ⟨829043, by rfl⟩ : syracuseStep 1105391 = 1658087) B1658087
theorem B1400303 : Blo 734326 1400303 := bstep (se 1 (by rfl) ⟨1050227, by rfl⟩ : syracuseStep 1400303 = 2100455) B2100455
theorem B2482271 : Blo 734326 2482271 := bstep (se 1 (by rfl) ⟨1861703, by rfl⟩ : syracuseStep 2482271 = 3723407) B3723407
theorem B1106057 : Blo 734326 1106057 := bstep (se 2 (by rfl) ⟨414771, by rfl⟩ : syracuseStep 1106057 = 829543) B829543
theorem B1106075 : Blo 734326 1106075 := bstep (se 1 (by rfl) ⟨829556, by rfl⟩ : syracuseStep 1106075 = 1659113) B1659113
theorem B1106279 : Blo 734326 1106279 := bstep (se 1 (by rfl) ⟨829709, by rfl⟩ : syracuseStep 1106279 = 1659419) B1659419
theorem B1860479 : Blo 734326 1860479 := bstep (se 1 (by rfl) ⟨1395359, by rfl⟩ : syracuseStep 1860479 = 2790719) B2790719
theorem B1860671 : Blo 734326 1860671 := bstep (se 1 (by rfl) ⟨1395503, by rfl⟩ : syracuseStep 1860671 = 2791007) B2791007
theorem B1860691 : Blo 734326 1860691 := bstep (se 1 (by rfl) ⟨1395518, by rfl⟩ : syracuseStep 1860691 = 2791037) B2791037
theorem B1107407 : Blo 734326 1107407 := bstep (se 1 (by rfl) ⟨830555, by rfl⟩ : syracuseStep 1107407 = 1661111) B1661111
theorem B5596775 : Blo 734326 5596775 := bstep (se 1 (by rfl) ⟨4197581, by rfl⟩ : syracuseStep 5596775 = 8395163) B8395163
theorem B183953207 : Blo 734326 183953207 := bstep (se 1 (by rfl) ⟨137964905, by rfl⟩ : syracuseStep 183953207 = 275929811) B275929811
theorem B4483259 : Blo 734326 4483259 := bstep (se 1 (by rfl) ⟨3362444, by rfl⟩ : syracuseStep 4483259 = 6724889) B6724889
theorem B1239259 : Blo 734326 1239259 := bstep (se 1 (by rfl) ⟨929444, by rfl⟩ : syracuseStep 1239259 = 1858889) B1858889
theorem B7956701 : Blo 734326 7956701 := bstep (se 3 (by rfl) ⟨1491881, by rfl⟩ : syracuseStep 7956701 = 2983763) B2983763
theorem B1239367 : Blo 734326 1239367 := bstep (se 1 (by rfl) ⟨929525, by rfl⟩ : syracuseStep 1239367 = 1859051) B1859051
theorem B18869435 : Blo 734326 18869435 := bstep (se 1 (by rfl) ⟨14152076, by rfl⟩ : syracuseStep 18869435 = 28304153) B28304153
theorem B1240697 : Blo 734326 1240697 := bstep (se 2 (by rfl) ⟨465261, by rfl⟩ : syracuseStep 1240697 = 930523) B930523
theorem B5042351 : Blo 734326 5042351 := bstep (se 1 (by rfl) ⟨3781763, by rfl⟩ : syracuseStep 5042351 = 7563527) B7563527
theorem B41939527 : Blo 734326 41939527 := bstep (se 1 (by rfl) ⟨31454645, by rfl⟩ : syracuseStep 41939527 = 62909291) B62909291
theorem B1242047 : Blo 734326 1242047 := bstep (se 1 (by rfl) ⟨931535, by rfl⟩ : syracuseStep 1242047 = 1863071) B1863071
theorem B2651123 : Blo 734326 2651123 := bstep (se 1 (by rfl) ⟨1988342, by rfl⟩ : syracuseStep 2651123 = 3976685) B3976685
theorem B2683937 : Blo 734326 2683937 := bstep (se 2 (by rfl) ⟨1006476, by rfl⟩ : syracuseStep 2683937 = 2012953) B2012953
theorem B47707217 : Blo 734326 47707217 := bstep (se 2 (by rfl) ⟨17890206, by rfl⟩ : syracuseStep 47707217 = 35780413) B35780413
theorem B2488535 : Blo 734326 2488535 := bstep (se 1 (by rfl) ⟨1866401, by rfl⟩ : syracuseStep 2488535 = 3732803) B3732803
theorem B1243775 : Blo 734326 1243775 := bstep (se 1 (by rfl) ⟨932831, by rfl⟩ : syracuseStep 1243775 = 1865663) B1865663
theorem B1244639 : Blo 734326 1244639 := bstep (se 1 (by rfl) ⟨933479, by rfl⟩ : syracuseStep 1244639 = 1866959) B1866959
theorem B3145351 : Blo 734326 3145351 := bstep (se 1 (by rfl) ⟨2359013, by rfl⟩ : syracuseStep 3145351 = 4718027) B4718027
theorem B13074281 : Blo 734326 13074281 := bstep (se 2 (by rfl) ⟨4902855, by rfl⟩ : syracuseStep 13074281 = 9805711) B9805711
theorem B1245179 : Blo 734326 1245179 := bstep (se 1 (by rfl) ⟨933884, by rfl⟩ : syracuseStep 1245179 = 1867769) B1867769
theorem B2490479 : Blo 734326 2490479 := bstep (se 1 (by rfl) ⟨1867859, by rfl⟩ : syracuseStep 2490479 = 3735719) B3735719
theorem B1868255 : Blo 734326 1868255 := bstep (se 1 (by rfl) ⟨1401191, by rfl⟩ : syracuseStep 1868255 = 2802383) B2802383
theorem B3736043 : Blo 734326 3736043 := bstep (se 1 (by rfl) ⟨2802032, by rfl⟩ : syracuseStep 3736043 = 5604065) B5604065
theorem B3737015 : Blo 734326 3737015 := bstep (se 1 (by rfl) ⟨2802761, by rfl⟩ : syracuseStep 3737015 = 5605523) B5605523
theorem B2099839 : Blo 734326 2099839 := bstep (se 1 (by rfl) ⟨1574879, by rfl⟩ : syracuseStep 2099839 = 3149759) B3149759
theorem B14355701 : Blo 734326 14355701 := bstep (se 5 (by rfl) ⟨672923, by rfl⟩ : syracuseStep 14355701 = 1345847) B1345847
theorem B2362679 : Blo 734326 2362679 := bstep (se 1 (by rfl) ⟨1772009, by rfl⟩ : syracuseStep 2362679 = 3544019) B3544019
theorem B9571753 : Blo 734326 9571753 := bstep (se 2 (by rfl) ⟨3589407, by rfl⟩ : syracuseStep 9571753 = 7178815) B7178815
theorem B3149417 : Blo 734326 3149417 := bstep (se 2 (by rfl) ⟨1181031, by rfl⟩ : syracuseStep 3149417 = 2362063) B2362063
theorem B10064513 : Blo 734326 10064513 := bstep (se 2 (by rfl) ⟨3774192, by rfl⟩ : syracuseStep 10064513 = 7548385) B7548385
theorem B3150647 : Blo 734326 3150647 := bstep (se 1 (by rfl) ⟨2362985, by rfl⟩ : syracuseStep 3150647 = 4725971) B4725971
theorem B7082963 : Blo 734326 7082963 := bstep (se 1 (by rfl) ⟨5312222, by rfl⟩ : syracuseStep 7082963 = 10624445) B10624445
theorem B5445245 : Blo 734326 5445245 := bstep (se 3 (by rfl) ⟨1020983, by rfl⟩ : syracuseStep 5445245 = 2041967) B2041967
theorem B8492809 : Blo 734326 8492809 := bstep (se 2 (by rfl) ⟨3184803, by rfl⟩ : syracuseStep 8492809 = 6369607) B6369607
theorem B7182557 : Blo 734326 7182557 := bstep (se 3 (by rfl) ⟨1346729, by rfl⟩ : syracuseStep 7182557 = 2693459) B2693459
theorem B3152135 : Blo 734326 3152135 := bstep (se 1 (by rfl) ⟨2364101, by rfl⟩ : syracuseStep 3152135 = 4728203) B4728203
theorem B6298013 : Blo 734326 6298013 := bstep (se 3 (by rfl) ⟨1180877, by rfl⟩ : syracuseStep 6298013 = 2361755) B2361755
theorem B2988839 : Blo 734326 2988839 := bstep (se 1 (by rfl) ⟨2241629, by rfl⟩ : syracuseStep 2988839 = 4483259) B4483259
theorem B827131 : Blo 734326 827131 := bstep (se 1 (by rfl) ⟨620348, by rfl⟩ : syracuseStep 827131 = 1240697) B1240697
theorem B13443353 : Blo 734326 13443353 := bstep (se 2 (by rfl) ⟨5041257, by rfl⟩ : syracuseStep 13443353 = 10082515) B10082515
theorem B828031 : Blo 734326 828031 := bstep (se 1 (by rfl) ⟨621023, by rfl⟩ : syracuseStep 828031 = 1242047) B1242047
theorem B5972879 : Blo 734326 5972879 := bstep (se 1 (by rfl) ⟨4479659, by rfl⟩ : syracuseStep 5972879 = 8959319) B8959319
theorem B829183 : Blo 734326 829183 := bstep (se 1 (by rfl) ⟨621887, by rfl⟩ : syracuseStep 829183 = 1243775) B1243775
theorem B4204507 : Blo 734326 4204507 := bstep (se 1 (by rfl) ⟨3153380, by rfl⟩ : syracuseStep 4204507 = 6306761) B6306761
theorem B829759 : Blo 734326 829759 := bstep (se 1 (by rfl) ⟨622319, by rfl⟩ : syracuseStep 829759 = 1244639) B1244639
theorem B830119 : Blo 734326 830119 := bstep (se 1 (by rfl) ⟨622589, by rfl⟩ : syracuseStep 830119 = 1245179) B1245179
theorem B13446269 : Blo 734326 13446269 := bstep (se 3 (by rfl) ⟨2521175, by rfl⟩ : syracuseStep 13446269 = 5042351) B5042351
theorem B5681821 : Blo 734326 5681821 := bstep (se 3 (by rfl) ⟨1065341, by rfl⟩ : syracuseStep 5681821 = 2130683) B2130683
theorem B1258687 : Blo 734326 1258687 := bstep (se 1 (by rfl) ⟨944015, by rfl⟩ : syracuseStep 1258687 = 1888031) B1888031
theorem B734535 : Blo 734326 734535 := bstep (se 1 (by rfl) ⟨550901, by rfl⟩ : syracuseStep 734535 = 1101803) B1101803
theorem B734767 : Blo 734326 734767 := bstep (se 1 (by rfl) ⟨551075, by rfl⟩ : syracuseStep 734767 = 1102151) B1102151
theorem B1652345 : Blo 734326 1652345 := bstep (se 2 (by rfl) ⟨619629, by rfl⟩ : syracuseStep 1652345 = 1239259) B1239259
theorem B1652399 : Blo 734326 1652399 := bstep (se 1 (by rfl) ⟨1239299, by rfl⟩ : syracuseStep 1652399 = 2478599) B2478599
theorem B1652489 : Blo 734326 1652489 := bstep (se 2 (by rfl) ⟨619683, by rfl⟩ : syracuseStep 1652489 = 1239367) B1239367
theorem B735143 : Blo 734326 735143 := bstep (se 1 (by rfl) ⟨551357, by rfl⟩ : syracuseStep 735143 = 1102715) B1102715
theorem B2242495 : Blo 734326 2242495 := bstep (se 1 (by rfl) ⟨1681871, by rfl⟩ : syracuseStep 2242495 = 3363743) B3363743
theorem B735359 : Blo 734326 735359 := bstep (se 1 (by rfl) ⟨551519, by rfl⟩ : syracuseStep 735359 = 1103039) B1103039
theorem B3192979 : Blo 734326 3192979 := bstep (se 1 (by rfl) ⟨2394734, by rfl⟩ : syracuseStep 3192979 = 4789469) B4789469
theorem B735471 : Blo 734326 735471 := bstep (se 1 (by rfl) ⟨551603, by rfl⟩ : syracuseStep 735471 = 1103207) B1103207
theorem B3029519 : Blo 734326 3029519 := bstep (se 1 (by rfl) ⟨2272139, by rfl⟩ : syracuseStep 3029519 = 4544279) B4544279
theorem B8403911 : Blo 734326 8403911 := bstep (se 1 (by rfl) ⟨6302933, by rfl⟩ : syracuseStep 8403911 = 12605867) B12605867
theorem B736251 : Blo 734326 736251 := bstep (se 1 (by rfl) ⟨552188, by rfl⟩ : syracuseStep 736251 = 1104377) B1104377
theorem B736283 : Blo 734326 736283 := bstep (se 1 (by rfl) ⟨552212, by rfl⟩ : syracuseStep 736283 = 1104425) B1104425
theorem B736615 : Blo 734326 736615 := bstep (se 1 (by rfl) ⟨552461, by rfl⟩ : syracuseStep 736615 = 1104923) B1104923
theorem B11943413 : Blo 734326 11943413 := bstep (se 5 (by rfl) ⟨559847, by rfl⟩ : syracuseStep 11943413 = 1119695) B1119695
theorem B736927 : Blo 734326 736927 := bstep (se 1 (by rfl) ⟨552695, by rfl⟩ : syracuseStep 736927 = 1105391) B1105391
theorem B933535 : Blo 734326 933535 := bstep (se 1 (by rfl) ⟨700151, by rfl⟩ : syracuseStep 933535 = 1400303) B1400303
theorem B3719033 : Blo 734326 3719033 := bstep (se 2 (by rfl) ⟨1394637, by rfl⟩ : syracuseStep 3719033 = 2789275) B2789275
theorem B1654847 : Blo 734326 1654847 := bstep (se 1 (by rfl) ⟨1241135, by rfl⟩ : syracuseStep 1654847 = 2482271) B2482271
theorem B737371 : Blo 734326 737371 := bstep (se 1 (by rfl) ⟨553028, by rfl⟩ : syracuseStep 737371 = 1106057) B1106057
theorem B737383 : Blo 734326 737383 := bstep (se 1 (by rfl) ⟨553037, by rfl⟩ : syracuseStep 737383 = 1106075) B1106075
theorem B737519 : Blo 734326 737519 := bstep (se 1 (by rfl) ⟨553139, by rfl⟩ : syracuseStep 737519 = 1106279) B1106279
theorem B55919369 : Blo 734326 55919369 := bstep (se 2 (by rfl) ⟨20969763, by rfl⟩ : syracuseStep 55919369 = 41939527) B41939527
theorem B738271 : Blo 734326 738271 := bstep (se 1 (by rfl) ⟨553703, by rfl⟩ : syracuseStep 738271 = 1107407) B1107407
theorem B122635471 : Blo 734326 122635471 := bstep (se 1 (by rfl) ⟨91976603, by rfl⟩ : syracuseStep 122635471 = 183953207) B183953207
theorem B1789291 : Blo 734326 1789291 := bstep (se 1 (by rfl) ⟨1341968, by rfl⟩ : syracuseStep 1789291 = 2683937) B2683937
theorem B31804811 : Blo 734326 31804811 := bstep (se 1 (by rfl) ⟨23853608, by rfl⟩ : syracuseStep 31804811 = 47707217) B47707217
theorem B1101503 : Blo 734326 1101503 := bstep (se 1 (by rfl) ⟨826127, by rfl⟩ : syracuseStep 1101503 = 1652255) B1652255
theorem B1101737 : Blo 734326 1101737 := bstep (se 2 (by rfl) ⟨413151, by rfl⟩ : syracuseStep 1101737 = 826303) B826303
theorem B1659023 : Blo 734326 1659023 := bstep (se 1 (by rfl) ⟨1244267, by rfl⟩ : syracuseStep 1659023 = 2488535) B2488535
theorem B2478491 : Blo 734326 2478491 := bstep (se 1 (by rfl) ⟨1858868, by rfl⟩ : syracuseStep 2478491 = 3717737) B3717737
theorem B42981043 : Blo 734326 42981043 := bstep (se 1 (by rfl) ⟨32235782, by rfl⟩ : syracuseStep 42981043 = 64471565) B64471565
theorem B1660751 : Blo 734326 1660751 := bstep (se 1 (by rfl) ⟨1245563, by rfl⟩ : syracuseStep 1660751 = 2491127) B2491127
theorem B4708543 : Blo 734326 4708543 := bstep (se 1 (by rfl) ⟨3531407, by rfl⟩ : syracuseStep 4708543 = 7062815) B7062815
theorem B5823191 : Blo 734326 5823191 := bstep (se 1 (by rfl) ⟨4367393, by rfl⟩ : syracuseStep 5823191 = 8734787) B8734787
theorem B2480921 : Blo 734326 2480921 := bstep (se 2 (by rfl) ⟨930345, by rfl⟩ : syracuseStep 2480921 = 1860691) B1860691
theorem B68017067 : Blo 734326 68017067 := bstep (se 1 (by rfl) ⟨51012800, by rfl⟩ : syracuseStep 68017067 = 102025601) B102025601
theorem B1105007 : Blo 734326 1105007 := bstep (se 1 (by rfl) ⟨828755, by rfl⟩ : syracuseStep 1105007 = 1657511) B1657511
theorem B1105055 : Blo 734326 1105055 := bstep (se 1 (by rfl) ⟨828791, by rfl⟩ : syracuseStep 1105055 = 1657583) B1657583
theorem B3726647 : Blo 734326 3726647 := bstep (se 1 (by rfl) ⟨2794985, by rfl⟩ : syracuseStep 3726647 = 5589971) B5589971
theorem B7364519 : Blo 734326 7364519 := bstep (se 1 (by rfl) ⟨5523389, by rfl⟩ : syracuseStep 7364519 = 11046779) B11046779
theorem B1106543 : Blo 734326 1106543 := bstep (se 1 (by rfl) ⟨829907, by rfl⟩ : syracuseStep 1106543 = 1659815) B1659815
theorem B1860347 : Blo 734326 1860347 := bstep (se 1 (by rfl) ⟨1395260, by rfl⟩ : syracuseStep 1860347 = 2790521) B2790521
theorem B1106759 : Blo 734326 1106759 := bstep (se 1 (by rfl) ⟨830069, by rfl⟩ : syracuseStep 1106759 = 1660139) B1660139
theorem B15886489 : Blo 734326 15886489 := bstep (se 2 (by rfl) ⟨5957433, by rfl⟩ : syracuseStep 15886489 = 11914867) B11914867
theorem B1992863 : Blo 734326 1992863 := bstep (se 1 (by rfl) ⟨1494647, by rfl⟩ : syracuseStep 1992863 = 2989295) B2989295
theorem B57239743 : Blo 734326 57239743 := bstep (se 1 (by rfl) ⟨42929807, by rfl⟩ : syracuseStep 57239743 = 85859615) B85859615
theorem B245164529 : Blo 734326 245164529 := bstep (se 2 (by rfl) ⟨91936698, by rfl⟩ : syracuseStep 245164529 = 183873397) B183873397
theorem B1862311 : Blo 734326 1862311 := bstep (se 1 (by rfl) ⟨1396733, by rfl⟩ : syracuseStep 1862311 = 2793467) B2793467
theorem B1240319 : Blo 734326 1240319 := bstep (se 1 (by rfl) ⟨930239, by rfl⟩ : syracuseStep 1240319 = 1860479) B1860479
theorem B1862939 : Blo 734326 1862939 := bstep (se 1 (by rfl) ⟨1397204, by rfl⟩ : syracuseStep 1862939 = 2794409) B2794409
theorem B1240447 : Blo 734326 1240447 := bstep (se 1 (by rfl) ⟨930335, by rfl⟩ : syracuseStep 1240447 = 1860671) B1860671
theorem B3731183 : Blo 734326 3731183 := bstep (se 1 (by rfl) ⟨2798387, by rfl⟩ : syracuseStep 3731183 = 5596775) B5596775
theorem B5304467 : Blo 734326 5304467 := bstep (se 1 (by rfl) ⟨3978350, by rfl⟩ : syracuseStep 5304467 = 7956701) B7956701
theorem B12579623 : Blo 734326 12579623 := bstep (se 1 (by rfl) ⟨9434717, by rfl⟩ : syracuseStep 12579623 = 18869435) B18869435
theorem B33092813 : Blo 734326 33092813 := bstep (se 3 (by rfl) ⟨6204902, by rfl⟩ : syracuseStep 33092813 = 12409805) B12409805
theorem B1865207 : Blo 734326 1865207 := bstep (se 1 (by rfl) ⟨1398905, by rfl⟩ : syracuseStep 1865207 = 2797811) B2797811
theorem B3733289 : Blo 734326 3733289 := bstep (se 2 (by rfl) ⟨1399983, by rfl⟩ : syracuseStep 3733289 = 2799967) B2799967
theorem B1767415 : Blo 734326 1767415 := bstep (se 1 (by rfl) ⟨1325561, by rfl⟩ : syracuseStep 1767415 = 2651123) B2651123
theorem B2652535 : Blo 734326 2652535 := bstep (se 1 (by rfl) ⟨1989401, by rfl⟩ : syracuseStep 2652535 = 3978803) B3978803
theorem B12614615 : Blo 734326 12614615 := bstep (se 1 (by rfl) ⟨9460961, by rfl⟩ : syracuseStep 12614615 = 18921923) B18921923
theorem B1244153 : Blo 734326 1244153 := bstep (se 2 (by rfl) ⟨466557, by rfl⟩ : syracuseStep 1244153 = 933115) B933115
theorem B4193801 : Blo 734326 4193801 := bstep (se 2 (by rfl) ⟨1572675, by rfl⟩ : syracuseStep 4193801 = 3145351) B3145351
theorem B8716187 : Blo 734326 8716187 := bstep (se 1 (by rfl) ⟨6537140, by rfl⟩ : syracuseStep 8716187 = 13074281) B13074281
theorem B1245503 : Blo 734326 1245503 := bstep (se 1 (by rfl) ⟨934127, by rfl⟩ : syracuseStep 1245503 = 1868255) B1868255
theorem B2490695 : Blo 734326 2490695 := bstep (se 1 (by rfl) ⟨1868021, by rfl⟩ : syracuseStep 2490695 = 3736043) B3736043
theorem B2491343 : Blo 734326 2491343 := bstep (se 1 (by rfl) ⟨1868507, by rfl⟩ : syracuseStep 2491343 = 3737015) B3737015
theorem B163513961 : Blo 734326 163513961 := bstep (se 2 (by rfl) ⟨61317735, by rfl⟩ : syracuseStep 163513961 = 122635471) B122635471
theorem B9570467 : Blo 734326 9570467 := bstep (se 1 (by rfl) ⟨7177850, by rfl⟩ : syracuseStep 9570467 = 14355701) B14355701
theorem B1575119 : Blo 734326 1575119 := bstep (se 1 (by rfl) ⟨1181339, by rfl⟩ : syracuseStep 1575119 = 2362679) B2362679
theorem B21203207 : Blo 734326 21203207 := bstep (se 1 (by rfl) ⟨15902405, by rfl⟩ : syracuseStep 21203207 = 31804811) B31804811
theorem B2099611 : Blo 734326 2099611 := bstep (se 1 (by rfl) ⟨1574708, by rfl⟩ : syracuseStep 2099611 = 3149417) B3149417
theorem B5606009 : Blo 734326 5606009 := bstep (se 2 (by rfl) ⟨2102253, by rfl⟩ : syracuseStep 5606009 = 4204507) B4204507
theorem B76319657 : Blo 734326 76319657 := bstep (se 2 (by rfl) ⟨28619871, by rfl⟩ : syracuseStep 76319657 = 57239743) B57239743
theorem B88247501 : Blo 734326 88247501 := bstep (se 3 (by rfl) ⟨16546406, by rfl⟩ : syracuseStep 88247501 = 33092813) B33092813
theorem B2100431 : Blo 734326 2100431 := bstep (se 1 (by rfl) ⟨1575323, by rfl⟩ : syracuseStep 2100431 = 3150647) B3150647
theorem B4721975 : Blo 734326 4721975 := bstep (se 1 (by rfl) ⟨3541481, by rfl⟩ : syracuseStep 4721975 = 7082963) B7082963
theorem B4788371 : Blo 734326 4788371 := bstep (se 1 (by rfl) ⟨3591278, by rfl⟩ : syracuseStep 4788371 = 7182557) B7182557
theorem B2101423 : Blo 734326 2101423 := bstep (se 1 (by rfl) ⟨1576067, by rfl⟩ : syracuseStep 2101423 = 3152135) B3152135
theorem B4198675 : Blo 734326 4198675 := bstep (se 1 (by rfl) ⟨3149006, by rfl⟩ : syracuseStep 4198675 = 6298013) B6298013
theorem B14520653 : Blo 734326 14520653 := bstep (se 3 (by rfl) ⟨2722622, by rfl⟩ : syracuseStep 14520653 = 5445245) B5445245
theorem B7575761 : Blo 734326 7575761 := bstep (se 2 (by rfl) ⟨2840910, by rfl⟩ : syracuseStep 7575761 = 5681821) B5681821
theorem B1678249 : Blo 734326 1678249 := bstep (se 2 (by rfl) ⟨629343, by rfl⟩ : syracuseStep 1678249 = 1258687) B1258687
theorem B826879 : Blo 734326 826879 := bstep (se 1 (by rfl) ⟨620159, by rfl⟩ : syracuseStep 826879 = 1240319) B1240319
theorem B2989993 : Blo 734326 2989993 := bstep (se 2 (by rfl) ⟨1121247, by rfl⟩ : syracuseStep 2989993 = 2242495) B2242495
theorem B829435 : Blo 734326 829435 := bstep (se 1 (by rfl) ⟨622076, by rfl⟩ : syracuseStep 829435 = 1244153) B1244153
theorem B2795867 : Blo 734326 2795867 := bstep (se 1 (by rfl) ⟨2096900, by rfl⟩ : syracuseStep 2795867 = 4193801) B4193801
theorem B5810791 : Blo 734326 5810791 := bstep (se 1 (by rfl) ⟨4358093, by rfl⟩ : syracuseStep 5810791 = 8716187) B8716187
theorem B734335 : Blo 734326 734335 := bstep (se 1 (by rfl) ⟨550751, by rfl⟩ : syracuseStep 734335 = 1101503) B1101503
theorem B734491 : Blo 734326 734491 := bstep (se 1 (by rfl) ⟨550868, by rfl⟩ : syracuseStep 734491 = 1101737) B1101737
theorem B21181985 : Blo 734326 21181985 := bstep (se 2 (by rfl) ⟨7943244, by rfl⟩ : syracuseStep 21181985 = 15886489) B15886489
theorem B1652327 : Blo 734326 1652327 := bstep (se 1 (by rfl) ⟨1239245, by rfl⟩ : syracuseStep 1652327 = 2478491) B2478491
theorem B2799785 : Blo 734326 2799785 := bstep (se 2 (by rfl) ⟨1049919, by rfl⟩ : syracuseStep 2799785 = 2099839) B2099839
theorem B3882127 : Blo 734326 3882127 := bstep (se 1 (by rfl) ⟨2911595, by rfl⟩ : syracuseStep 3882127 = 5823191) B5823191
theorem B1653929 : Blo 734326 1653929 := bstep (se 2 (by rfl) ⟨620223, by rfl⟩ : syracuseStep 1653929 = 1240447) B1240447
theorem B1653947 : Blo 734326 1653947 := bstep (se 1 (by rfl) ⟨1240460, by rfl⟩ : syracuseStep 1653947 = 2480921) B2480921
theorem B736671 : Blo 734326 736671 := bstep (se 1 (by rfl) ⟨552503, by rfl⟩ : syracuseStep 736671 = 1105007) B1105007
theorem B736703 : Blo 734326 736703 := bstep (se 1 (by rfl) ⟨552527, by rfl⟩ : syracuseStep 736703 = 1105055) B1105055
theorem B8962235 : Blo 734326 8962235 := bstep (se 1 (by rfl) ⟨6721676, by rfl⟩ : syracuseStep 8962235 = 13443353) B13443353
theorem B737695 : Blo 734326 737695 := bstep (se 1 (by rfl) ⟨553271, by rfl⟩ : syracuseStep 737695 = 1106543) B1106543
theorem B737839 : Blo 734326 737839 := bstep (se 1 (by rfl) ⟨553379, by rfl⟩ : syracuseStep 737839 = 1106759) B1106759
theorem B3981919 : Blo 734326 3981919 := bstep (se 1 (by rfl) ⟨2986439, by rfl⟩ : syracuseStep 3981919 = 5972879) B5972879
theorem B8078717 : Blo 734326 8078717 := bstep (se 3 (by rfl) ⟨1514759, by rfl⟩ : syracuseStep 8078717 = 3029519) B3029519
theorem B1328575 : Blo 734326 1328575 := bstep (se 1 (by rfl) ⟨996431, by rfl⟩ : syracuseStep 1328575 = 1992863) B1992863
theorem B8964179 : Blo 734326 8964179 := bstep (se 1 (by rfl) ⟨6723134, by rfl⟩ : syracuseStep 8964179 = 13446269) B13446269
theorem B11323745 : Blo 734326 11323745 := bstep (se 2 (by rfl) ⟨4246404, by rfl⟩ : syracuseStep 11323745 = 8492809) B8492809
theorem B6278057 : Blo 734326 6278057 := bstep (se 2 (by rfl) ⟨2354271, by rfl⟩ : syracuseStep 6278057 = 4708543) B4708543
theorem B1101563 : Blo 734326 1101563 := bstep (se 1 (by rfl) ⟨826172, by rfl⟩ : syracuseStep 1101563 = 1652345) B1652345
theorem B1101599 : Blo 734326 1101599 := bstep (se 1 (by rfl) ⟨826199, by rfl⟩ : syracuseStep 1101599 = 1652399) B1652399
theorem B1101659 : Blo 734326 1101659 := bstep (se 1 (by rfl) ⟨826244, by rfl⟩ : syracuseStep 1101659 = 1652489) B1652489
theorem B8409743 : Blo 734326 8409743 := bstep (se 1 (by rfl) ⟨6307307, by rfl⟩ : syracuseStep 8409743 = 12614615) B12614615
theorem B1102841 : Blo 734326 1102841 := bstep (se 2 (by rfl) ⟨413565, by rfl⟩ : syracuseStep 1102841 = 827131) B827131
theorem B2479355 : Blo 734326 2479355 := bstep (se 1 (by rfl) ⟨1859516, by rfl⟩ : syracuseStep 2479355 = 3719033) B3719033
theorem B1103231 : Blo 734326 1103231 := bstep (se 1 (by rfl) ⟨827423, by rfl⟩ : syracuseStep 1103231 = 1654847) B1654847
theorem B1660319 : Blo 734326 1660319 := bstep (se 1 (by rfl) ⟨1245239, by rfl⟩ : syracuseStep 1660319 = 2490479) B2490479
theorem B1104041 : Blo 734326 1104041 := bstep (se 2 (by rfl) ⟨414015, by rfl⟩ : syracuseStep 1104041 = 828031) B828031
theorem B149118317 : Blo 734326 149118317 := bstep (se 3 (by rfl) ⟨27959684, by rfl⟩ : syracuseStep 149118317 = 55919369) B55919369
theorem B1105577 : Blo 734326 1105577 := bstep (se 2 (by rfl) ⟨414591, by rfl⟩ : syracuseStep 1105577 = 829183) B829183
theorem B1106015 : Blo 734326 1106015 := bstep (se 1 (by rfl) ⟨829511, by rfl⟩ : syracuseStep 1106015 = 1659023) B1659023
theorem B1106345 : Blo 734326 1106345 := bstep (se 2 (by rfl) ⟨414879, by rfl⟩ : syracuseStep 1106345 = 829759) B829759
theorem B6709675 : Blo 734326 6709675 := bstep (se 1 (by rfl) ⟨5032256, by rfl⟩ : syracuseStep 6709675 = 10064513) B10064513
theorem B2483081 : Blo 734326 2483081 := bstep (se 2 (by rfl) ⟨931155, by rfl⟩ : syracuseStep 2483081 = 1862311) B1862311
theorem B1106825 : Blo 734326 1106825 := bstep (se 2 (by rfl) ⟨415059, by rfl⟩ : syracuseStep 1106825 = 830119) B830119
theorem B1107167 : Blo 734326 1107167 := bstep (se 1 (by rfl) ⟨830375, by rfl⟩ : syracuseStep 1107167 = 1660751) B1660751
theorem B2385721 : Blo 734326 2385721 := bstep (se 2 (by rfl) ⟨894645, by rfl⟩ : syracuseStep 2385721 = 1789291) B1789291
theorem B1992559 : Blo 734326 1992559 := bstep (se 1 (by rfl) ⟨1494419, by rfl⟩ : syracuseStep 1992559 = 2988839) B2988839
theorem B45344711 : Blo 734326 45344711 := bstep (se 1 (by rfl) ⟨34008533, by rfl⟩ : syracuseStep 45344711 = 68017067) B68017067
theorem B2484431 : Blo 734326 2484431 := bstep (se 1 (by rfl) ⟨1863323, by rfl⟩ : syracuseStep 2484431 = 3726647) B3726647
theorem B4909679 : Blo 734326 4909679 := bstep (se 1 (by rfl) ⟨3682259, by rfl⟩ : syracuseStep 4909679 = 7364519) B7364519
theorem B1240231 : Blo 734326 1240231 := bstep (se 1 (by rfl) ⟨930173, by rfl⟩ : syracuseStep 1240231 = 1860347) B1860347
theorem B163443019 : Blo 734326 163443019 := bstep (se 1 (by rfl) ⟨122582264, by rfl⟩ : syracuseStep 163443019 = 245164529) B245164529
theorem B1241959 : Blo 734326 1241959 := bstep (se 1 (by rfl) ⟨931469, by rfl⟩ : syracuseStep 1241959 = 1862939) B1862939
theorem B51049349 : Blo 734326 51049349 := bstep (se 4 (by rfl) ⟨4785876, by rfl⟩ : syracuseStep 51049349 = 9571753) B9571753
theorem B57308057 : Blo 734326 57308057 := bstep (se 2 (by rfl) ⟨21490521, by rfl⟩ : syracuseStep 57308057 = 42981043) B42981043
theorem B2487455 : Blo 734326 2487455 := bstep (se 1 (by rfl) ⟨1865591, by rfl⟩ : syracuseStep 2487455 = 3731183) B3731183
theorem B2356553 : Blo 734326 2356553 := bstep (se 2 (by rfl) ⟨883707, by rfl⟩ : syracuseStep 2356553 = 1767415) B1767415
theorem B3536311 : Blo 734326 3536311 := bstep (se 1 (by rfl) ⟨2652233, by rfl⟩ : syracuseStep 3536311 = 5304467) B5304467
theorem B4257305 : Blo 734326 4257305 := bstep (se 2 (by rfl) ⟨1596489, by rfl⟩ : syracuseStep 4257305 = 3192979) B3192979
theorem B3536713 : Blo 734326 3536713 := bstep (se 2 (by rfl) ⟨1326267, by rfl⟩ : syracuseStep 3536713 = 2652535) B2652535
theorem B8386415 : Blo 734326 8386415 := bstep (se 1 (by rfl) ⟨6289811, by rfl⟩ : syracuseStep 8386415 = 12579623) B12579623
theorem B1243471 : Blo 734326 1243471 := bstep (se 1 (by rfl) ⟨932603, by rfl⟩ : syracuseStep 1243471 = 1865207) B1865207
theorem B2488859 : Blo 734326 2488859 := bstep (se 1 (by rfl) ⟨1866644, by rfl⟩ : syracuseStep 2488859 = 3733289) B3733289
theorem B5602607 : Blo 734326 5602607 := bstep (se 1 (by rfl) ⟨4201955, by rfl⟩ : syracuseStep 5602607 = 8403911) B8403911
theorem B1244713 : Blo 734326 1244713 := bstep (se 2 (by rfl) ⟨466767, by rfl⟩ : syracuseStep 1244713 = 933535) B933535
theorem B7962275 : Blo 734326 7962275 := bstep (se 1 (by rfl) ⟨5971706, by rfl⟩ : syracuseStep 7962275 = 11943413) B11943413
theorem B8946233 : Blo 734326 8946233 := bstep (se 2 (by rfl) ⟨3354837, by rfl⟩ : syracuseStep 8946233 = 6709675) B6709675
theorem B5309225 : Blo 734326 5309225 := bstep (se 2 (by rfl) ⟨1990959, by rfl⟩ : syracuseStep 5309225 = 3981919) B3981919
theorem B1050079 : Blo 734326 1050079 := bstep (se 1 (by rfl) ⟨787559, by rfl⟩ : syracuseStep 1050079 = 1575119) B1575119
theorem B3737339 : Blo 734326 3737339 := bstep (se 1 (by rfl) ⟨2803004, by rfl⟩ : syracuseStep 3737339 = 5606009) B5606009
theorem B1771433 : Blo 734326 1771433 := bstep (se 2 (by rfl) ⟨664287, by rfl⟩ : syracuseStep 1771433 = 1328575) B1328575
theorem B3147983 : Blo 734326 3147983 := bstep (se 1 (by rfl) ⟨2360987, by rfl⟩ : syracuseStep 3147983 = 4721975) B4721975
theorem B3180961 : Blo 734326 3180961 := bstep (se 2 (by rfl) ⟨1192860, by rfl⟩ : syracuseStep 3180961 = 2385721) B2385721
theorem B2656745 : Blo 734326 2656745 := bstep (se 2 (by rfl) ⟨996279, by rfl⟩ : syracuseStep 2656745 = 1992559) B1992559
theorem B5606495 : Blo 734326 5606495 := bstep (se 1 (by rfl) ⟨4204871, by rfl⟩ : syracuseStep 5606495 = 8409743) B8409743
theorem B5050507 : Blo 734326 5050507 := bstep (se 1 (by rfl) ⟨3787880, by rfl⟩ : syracuseStep 5050507 = 7575761) B7575761
theorem B8950661 : Blo 734326 8950661 := bstep (se 4 (by rfl) ⟨839124, by rfl⟩ : syracuseStep 8950661 = 1678249) B1678249
theorem B5974823 : Blo 734326 5974823 := bstep (se 1 (by rfl) ⟨4481117, by rfl⟩ : syracuseStep 5974823 = 8962235) B8962235
theorem B830335 : Blo 734326 830335 := bstep (se 1 (by rfl) ⟨622751, by rfl⟩ : syracuseStep 830335 = 1245503) B1245503
theorem B5385811 : Blo 734326 5385811 := bstep (se 1 (by rfl) ⟨4039358, by rfl⟩ : syracuseStep 5385811 = 8078717) B8078717
theorem B5976119 : Blo 734326 5976119 := bstep (se 1 (by rfl) ⟨4482089, by rfl⟩ : syracuseStep 5976119 = 8964179) B8964179
theorem B14135471 : Blo 734326 14135471 := bstep (se 1 (by rfl) ⟨10601603, by rfl⟩ : syracuseStep 14135471 = 21203207) B21203207
theorem B7549163 : Blo 734326 7549163 := bstep (se 1 (by rfl) ⟨5661872, by rfl⟩ : syracuseStep 7549163 = 11323745) B11323745
theorem B58831667 : Blo 734326 58831667 := bstep (se 1 (by rfl) ⟨44123750, by rfl⟩ : syracuseStep 58831667 = 88247501) B88247501
theorem B734375 : Blo 734326 734375 := bstep (se 1 (by rfl) ⟨550781, by rfl⟩ : syracuseStep 734375 = 1101563) B1101563
theorem B734399 : Blo 734326 734399 := bstep (se 1 (by rfl) ⟨550799, by rfl⟩ : syracuseStep 734399 = 1101599) B1101599
theorem B734439 : Blo 734326 734439 := bstep (se 1 (by rfl) ⟨550829, by rfl⟩ : syracuseStep 734439 = 1101659) B1101659
theorem B3192247 : Blo 734326 3192247 := bstep (se 1 (by rfl) ⟨2394185, by rfl⟩ : syracuseStep 3192247 = 4788371) B4788371
theorem B9680435 : Blo 734326 9680435 := bstep (se 1 (by rfl) ⟨7260326, by rfl⟩ : syracuseStep 9680435 = 14520653) B14520653
theorem B2799481 : Blo 734326 2799481 := bstep (se 2 (by rfl) ⟨1049805, by rfl⟩ : syracuseStep 2799481 = 2099611) B2099611
theorem B735227 : Blo 734326 735227 := bstep (se 1 (by rfl) ⟨551420, by rfl⟩ : syracuseStep 735227 = 1102841) B1102841
theorem B7747721 : Blo 734326 7747721 := bstep (se 2 (by rfl) ⟨2905395, by rfl⟩ : syracuseStep 7747721 = 5810791) B5810791
theorem B1652903 : Blo 734326 1652903 := bstep (se 1 (by rfl) ⟨1239677, by rfl⟩ : syracuseStep 1652903 = 2479355) B2479355
theorem B735487 : Blo 734326 735487 := bstep (se 1 (by rfl) ⟨551615, by rfl⟩ : syracuseStep 735487 = 1103231) B1103231
theorem B736027 : Blo 734326 736027 := bstep (se 1 (by rfl) ⟨552020, by rfl⟩ : syracuseStep 736027 = 1104041) B1104041
theorem B1653641 : Blo 734326 1653641 := bstep (se 2 (by rfl) ⟨620115, by rfl⟩ : syracuseStep 1653641 = 1240231) B1240231
theorem B737051 : Blo 734326 737051 := bstep (se 1 (by rfl) ⟨552788, by rfl⟩ : syracuseStep 737051 = 1105577) B1105577
theorem B737343 : Blo 734326 737343 := bstep (se 1 (by rfl) ⟨553007, by rfl⟩ : syracuseStep 737343 = 1106015) B1106015
theorem B2801897 : Blo 734326 2801897 := bstep (se 2 (by rfl) ⟨1050711, by rfl⟩ : syracuseStep 2801897 = 2101423) B2101423
theorem B737563 : Blo 734326 737563 := bstep (se 1 (by rfl) ⟨553172, by rfl⟩ : syracuseStep 737563 = 1106345) B1106345
theorem B217924025 : Blo 734326 217924025 := bstep (se 2 (by rfl) ⟨81721509, by rfl⟩ : syracuseStep 217924025 = 163443019) B163443019
theorem B1655387 : Blo 734326 1655387 := bstep (se 1 (by rfl) ⟨1241540, by rfl⟩ : syracuseStep 1655387 = 2483081) B2483081
theorem B737883 : Blo 734326 737883 := bstep (se 1 (by rfl) ⟨553412, by rfl⟩ : syracuseStep 737883 = 1106825) B1106825
theorem B738111 : Blo 734326 738111 := bstep (se 1 (by rfl) ⟨553583, by rfl⟩ : syracuseStep 738111 = 1107167) B1107167
theorem B1655945 : Blo 734326 1655945 := bstep (se 2 (by rfl) ⟨620979, by rfl⟩ : syracuseStep 1655945 = 1241959) B1241959
theorem B30229807 : Blo 734326 30229807 := bstep (se 1 (by rfl) ⟨22672355, by rfl⟩ : syracuseStep 30229807 = 45344711) B45344711
theorem B1656287 : Blo 734326 1656287 := bstep (se 1 (by rfl) ⟨1242215, by rfl⟩ : syracuseStep 1656287 = 2484431) B2484431
theorem B1657961 : Blo 734326 1657961 := bstep (se 2 (by rfl) ⟨621735, by rfl⟩ : syracuseStep 1657961 = 1243471) B1243471
theorem B34032899 : Blo 734326 34032899 := bstep (se 1 (by rfl) ⟨25524674, by rfl⟩ : syracuseStep 34032899 = 51049349) B51049349
theorem B1658303 : Blo 734326 1658303 := bstep (se 1 (by rfl) ⟨1243727, by rfl⟩ : syracuseStep 1658303 = 2487455) B2487455
theorem B2838203 : Blo 734326 2838203 := bstep (se 1 (by rfl) ⟨2128652, by rfl⟩ : syracuseStep 2838203 = 4257305) B4257305
theorem B1101551 : Blo 734326 1101551 := bstep (se 1 (by rfl) ⟨826163, by rfl⟩ : syracuseStep 1101551 = 1652327) B1652327
theorem B5590943 : Blo 734326 5590943 := bstep (se 1 (by rfl) ⟨4193207, by rfl⟩ : syracuseStep 5590943 = 8386415) B8386415
theorem B1659239 : Blo 734326 1659239 := bstep (se 1 (by rfl) ⟨1244429, by rfl⟩ : syracuseStep 1659239 = 2488859) B2488859
theorem B1102505 : Blo 734326 1102505 := bstep (se 2 (by rfl) ⟨413439, by rfl⟩ : syracuseStep 1102505 = 826879) B826879
theorem B1659617 : Blo 734326 1659617 := bstep (se 2 (by rfl) ⟨622356, by rfl⟩ : syracuseStep 1659617 = 1244713) B1244713
theorem B1102619 : Blo 734326 1102619 := bstep (se 1 (by rfl) ⟨826964, by rfl⟩ : syracuseStep 1102619 = 1653929) B1653929
theorem B1102631 : Blo 734326 1102631 := bstep (se 1 (by rfl) ⟨826973, by rfl⟩ : syracuseStep 1102631 = 1653947) B1653947
theorem B3986657 : Blo 734326 3986657 := bstep (se 2 (by rfl) ⟨1494996, by rfl⟩ : syracuseStep 3986657 = 2989993) B2989993
theorem B1660463 : Blo 734326 1660463 := bstep (se 1 (by rfl) ⟨1245347, by rfl⟩ : syracuseStep 1660463 = 2490695) B2490695
theorem B1660895 : Blo 734326 1660895 := bstep (se 1 (by rfl) ⟨1245671, by rfl⟩ : syracuseStep 1660895 = 2491343) B2491343
theorem B109009307 : Blo 734326 109009307 := bstep (se 1 (by rfl) ⟨81756980, by rfl⟩ : syracuseStep 109009307 = 163513961) B163513961
theorem B6380311 : Blo 734326 6380311 := bstep (se 1 (by rfl) ⟨4785233, by rfl⟩ : syracuseStep 6380311 = 9570467) B9570467
theorem B50879771 : Blo 734326 50879771 := bstep (se 1 (by rfl) ⟨38159828, by rfl⟩ : syracuseStep 50879771 = 76319657) B76319657
theorem B4185371 : Blo 734326 4185371 := bstep (se 1 (by rfl) ⟨3139028, by rfl⟩ : syracuseStep 4185371 = 6278057) B6278057
theorem B1105913 : Blo 734326 1105913 := bstep (se 2 (by rfl) ⟨414717, by rfl⟩ : syracuseStep 1105913 = 829435) B829435
theorem B6284141 : Blo 734326 6284141 := bstep (se 3 (by rfl) ⟨1178276, by rfl⟩ : syracuseStep 6284141 = 2356553) B2356553
theorem B1106879 : Blo 734326 1106879 := bstep (se 1 (by rfl) ⟨830159, by rfl⟩ : syracuseStep 1106879 = 1660319) B1660319
theorem B99412211 : Blo 734326 99412211 := bstep (se 1 (by rfl) ⟨74559158, by rfl⟩ : syracuseStep 99412211 = 149118317) B149118317
theorem B5598233 : Blo 734326 5598233 := bstep (se 2 (by rfl) ⟨2099337, by rfl⟩ : syracuseStep 5598233 = 4198675) B4198675
theorem B1863911 : Blo 734326 1863911 := bstep (se 1 (by rfl) ⟨1397933, by rfl⟩ : syracuseStep 1863911 = 2795867) B2795867
theorem B3273119 : Blo 734326 3273119 := bstep (se 1 (by rfl) ⟨2454839, by rfl⟩ : syracuseStep 3273119 = 4909679) B4909679
theorem B4715081 : Blo 734326 4715081 := bstep (se 2 (by rfl) ⟨1768155, by rfl⟩ : syracuseStep 4715081 = 3536311) B3536311
theorem B4715617 : Blo 734326 4715617 := bstep (se 2 (by rfl) ⟨1768356, by rfl⟩ : syracuseStep 4715617 = 3536713) B3536713
theorem B5601149 : Blo 734326 5601149 := bstep (se 3 (by rfl) ⟨1050215, by rfl⟩ : syracuseStep 5601149 = 2100431) B2100431
theorem B38205371 : Blo 734326 38205371 := bstep (se 1 (by rfl) ⟨28654028, by rfl⟩ : syracuseStep 38205371 = 57308057) B57308057
theorem B14121323 : Blo 734326 14121323 := bstep (se 1 (by rfl) ⟨10590992, by rfl⟩ : syracuseStep 14121323 = 21181985) B21181985
theorem B1866523 : Blo 734326 1866523 := bstep (se 1 (by rfl) ⟨1399892, by rfl⟩ : syracuseStep 1866523 = 2799785) B2799785
theorem B5176169 : Blo 734326 5176169 := bstep (se 2 (by rfl) ⟨1941063, by rfl⟩ : syracuseStep 5176169 = 3882127) B3882127
theorem B3735071 : Blo 734326 3735071 := bstep (se 1 (by rfl) ⟨2801303, by rfl⟩ : syracuseStep 3735071 = 5602607) B5602607
theorem B5308183 : Blo 734326 5308183 := bstep (se 1 (by rfl) ⟨3981137, by rfl⟩ : syracuseStep 5308183 = 7962275) B7962275
theorem B1867931 : Blo 734326 1867931 := bstep (se 1 (by rfl) ⟨1400948, by rfl⟩ : syracuseStep 1867931 = 2801897) B2801897
theorem B5964155 : Blo 734326 5964155 := bstep (se 1 (by rfl) ⟨4473116, by rfl⟩ : syracuseStep 5964155 = 8946233) B8946233
theorem B3539483 : Blo 734326 3539483 := bstep (se 1 (by rfl) ⟨2654612, by rfl⟩ : syracuseStep 3539483 = 5309225) B5309225
theorem B2491559 : Blo 734326 2491559 := bstep (se 1 (by rfl) ⟨1868669, by rfl⟩ : syracuseStep 2491559 = 3737339) B3737339
theorem B1180955 : Blo 734326 1180955 := bstep (se 1 (by rfl) ⟨885716, by rfl⟩ : syracuseStep 1180955 = 1771433) B1771433
theorem B2098655 : Blo 734326 2098655 := bstep (se 1 (by rfl) ⟨1573991, by rfl⟩ : syracuseStep 2098655 = 3147983) B3147983
theorem B1771163 : Blo 734326 1771163 := bstep (se 1 (by rfl) ⟨1328372, by rfl⟩ : syracuseStep 1771163 = 2656745) B2656745
theorem B40306409 : Blo 734326 40306409 := bstep (se 2 (by rfl) ⟨15114903, by rfl⟩ : syracuseStep 40306409 = 30229807) B30229807
theorem B3737663 : Blo 734326 3737663 := bstep (se 1 (by rfl) ⟨2803247, by rfl⟩ : syracuseStep 3737663 = 5606495) B5606495
theorem B5967107 : Blo 734326 5967107 := bstep (se 1 (by rfl) ⟨4475330, by rfl⟩ : syracuseStep 5967107 = 8950661) B8950661
theorem B2657771 : Blo 734326 2657771 := bstep (se 1 (by rfl) ⟨1993328, by rfl⟩ : syracuseStep 2657771 = 3986657) B3986657
theorem B7181081 : Blo 734326 7181081 := bstep (se 2 (by rfl) ⟨2692905, by rfl⟩ : syracuseStep 7181081 = 5385811) B5385811
theorem B33919847 : Blo 734326 33919847 := bstep (se 1 (by rfl) ⟨25439885, by rfl⟩ : syracuseStep 33919847 = 50879771) B50879771
theorem B2790247 : Blo 734326 2790247 := bstep (se 1 (by rfl) ⟨2092685, by rfl⟩ : syracuseStep 2790247 = 4185371) B4185371
theorem B25470247 : Blo 734326 25470247 := bstep (se 1 (by rfl) ⟨19102685, by rfl⟩ : syracuseStep 25470247 = 38205371) B38205371
theorem B9414215 : Blo 734326 9414215 := bstep (se 1 (by rfl) ⟨7060661, by rfl⟩ : syracuseStep 9414215 = 14121323) B14121323
theorem B3450779 : Blo 734326 3450779 := bstep (se 1 (by rfl) ⟨2588084, by rfl⟩ : syracuseStep 3450779 = 5176169) B5176169
theorem B22688599 : Blo 734326 22688599 := bstep (se 1 (by rfl) ⟨17016449, by rfl⟩ : syracuseStep 22688599 = 34032899) B34032899
theorem B734367 : Blo 734326 734367 := bstep (se 1 (by rfl) ⟨550775, by rfl⟩ : syracuseStep 734367 = 1101551) B1101551
theorem B735003 : Blo 734326 735003 := bstep (se 1 (by rfl) ⟨551252, by rfl⟩ : syracuseStep 735003 = 1102505) B1102505
theorem B735079 : Blo 734326 735079 := bstep (se 1 (by rfl) ⟨551309, by rfl⟩ : syracuseStep 735079 = 1102619) B1102619
theorem B735087 : Blo 734326 735087 := bstep (se 1 (by rfl) ⟨551315, by rfl⟩ : syracuseStep 735087 = 1102631) B1102631
theorem B4241281 : Blo 734326 4241281 := bstep (se 2 (by rfl) ⟨1590480, by rfl⟩ : syracuseStep 4241281 = 3180961) B3180961
theorem B737275 : Blo 734326 737275 := bstep (se 1 (by rfl) ⟨552956, by rfl⟩ : syracuseStep 737275 = 1105913) B1105913
theorem B6734009 : Blo 734326 6734009 := bstep (se 2 (by rfl) ⟨2525253, by rfl⟩ : syracuseStep 6734009 = 5050507) B5050507
theorem B737919 : Blo 734326 737919 := bstep (se 1 (by rfl) ⟨553439, by rfl⟩ : syracuseStep 737919 = 1106879) B1106879
theorem B66274807 : Blo 734326 66274807 := bstep (se 1 (by rfl) ⟨49706105, by rfl⟩ : syracuseStep 66274807 = 99412211) B99412211
theorem B3983215 : Blo 734326 3983215 := bstep (se 1 (by rfl) ⟨2987411, by rfl⟩ : syracuseStep 3983215 = 5974823) B5974823
theorem B3984079 : Blo 734326 3984079 := bstep (se 1 (by rfl) ⟨2988059, by rfl⟩ : syracuseStep 3984079 = 5976119) B5976119
theorem B9423647 : Blo 734326 9423647 := bstep (se 1 (by rfl) ⟨7067735, by rfl⟩ : syracuseStep 9423647 = 14135471) B14135471
theorem B5032775 : Blo 734326 5032775 := bstep (se 1 (by rfl) ⟨3774581, by rfl⟩ : syracuseStep 5032775 = 7549163) B7549163
theorem B2182079 : Blo 734326 2182079 := bstep (se 1 (by rfl) ⟨1636559, by rfl⟩ : syracuseStep 2182079 = 3273119) B3273119
theorem B8507081 : Blo 734326 8507081 := bstep (se 2 (by rfl) ⟨3190155, by rfl⟩ : syracuseStep 8507081 = 6380311) B6380311
theorem B5165147 : Blo 734326 5165147 := bstep (se 1 (by rfl) ⟨3873860, by rfl⟩ : syracuseStep 5165147 = 7747721) B7747721
theorem B1101935 : Blo 734326 1101935 := bstep (se 1 (by rfl) ⟨826451, by rfl⟩ : syracuseStep 1101935 = 1652903) B1652903
theorem B1102427 : Blo 734326 1102427 := bstep (se 1 (by rfl) ⟨826820, by rfl⟩ : syracuseStep 1102427 = 1653641) B1653641
theorem B1103591 : Blo 734326 1103591 := bstep (se 1 (by rfl) ⟨827693, by rfl⟩ : syracuseStep 1103591 = 1655387) B1655387
theorem B1103963 : Blo 734326 1103963 := bstep (se 1 (by rfl) ⟨827972, by rfl⟩ : syracuseStep 1103963 = 1655945) B1655945
theorem B1104191 : Blo 734326 1104191 := bstep (se 1 (by rfl) ⟨828143, by rfl⟩ : syracuseStep 1104191 = 1656287) B1656287
theorem B1400105 : Blo 734326 1400105 := bstep (se 2 (by rfl) ⟨525039, by rfl⟩ : syracuseStep 1400105 = 1050079) B1050079
theorem B1105307 : Blo 734326 1105307 := bstep (se 1 (by rfl) ⟨828980, by rfl⟩ : syracuseStep 1105307 = 1657961) B1657961
theorem B1105535 : Blo 734326 1105535 := bstep (se 1 (by rfl) ⟨829151, by rfl⟩ : syracuseStep 1105535 = 1658303) B1658303
theorem B1892135 : Blo 734326 1892135 := bstep (se 1 (by rfl) ⟨1419101, by rfl⟩ : syracuseStep 1892135 = 2838203) B2838203
theorem B3727295 : Blo 734326 3727295 := bstep (se 1 (by rfl) ⟨2795471, by rfl⟩ : syracuseStep 3727295 = 5590943) B5590943
theorem B1106159 : Blo 734326 1106159 := bstep (se 1 (by rfl) ⟨829619, by rfl⟩ : syracuseStep 1106159 = 1659239) B1659239
theorem B1106411 : Blo 734326 1106411 := bstep (se 1 (by rfl) ⟨829808, by rfl⟩ : syracuseStep 1106411 = 1659617) B1659617
theorem B1106975 : Blo 734326 1106975 := bstep (se 1 (by rfl) ⟨830231, by rfl⟩ : syracuseStep 1106975 = 1660463) B1660463
theorem B1107113 : Blo 734326 1107113 := bstep (se 2 (by rfl) ⟨415167, by rfl⟩ : syracuseStep 1107113 = 830335) B830335
theorem B1107263 : Blo 734326 1107263 := bstep (se 1 (by rfl) ⟨830447, by rfl⟩ : syracuseStep 1107263 = 1660895) B1660895
theorem B72672871 : Blo 734326 72672871 := bstep (se 1 (by rfl) ⟨54504653, by rfl⟩ : syracuseStep 72672871 = 109009307) B109009307
theorem B2324522933 : Blo 734326 2324522933 := bstep (se 5 (by rfl) ⟨108962012, by rfl⟩ : syracuseStep 2324522933 = 217924025) B217924025
theorem B4189427 : Blo 734326 4189427 := bstep (se 1 (by rfl) ⟨3142070, by rfl⟩ : syracuseStep 4189427 = 6284141) B6284141
theorem B6287489 : Blo 734326 6287489 := bstep (se 2 (by rfl) ⟨2357808, by rfl⟩ : syracuseStep 6287489 = 4715617) B4715617
theorem B4256329 : Blo 734326 4256329 := bstep (se 2 (by rfl) ⟨1596123, by rfl⟩ : syracuseStep 4256329 = 3192247) B3192247
theorem B3732155 : Blo 734326 3732155 := bstep (se 1 (by rfl) ⟨2799116, by rfl⟩ : syracuseStep 3732155 = 5598233) B5598233
theorem B3732641 : Blo 734326 3732641 := bstep (se 2 (by rfl) ⟨1399740, by rfl⟩ : syracuseStep 3732641 = 2799481) B2799481
theorem B1242607 : Blo 734326 1242607 := bstep (se 1 (by rfl) ⟨931955, by rfl⟩ : syracuseStep 1242607 = 1863911) B1863911
theorem B3143387 : Blo 734326 3143387 := bstep (se 1 (by rfl) ⟨2357540, by rfl⟩ : syracuseStep 3143387 = 4715081) B4715081
theorem B39221111 : Blo 734326 39221111 := bstep (se 1 (by rfl) ⟨29415833, by rfl⟩ : syracuseStep 39221111 = 58831667) B58831667
theorem B6453623 : Blo 734326 6453623 := bstep (se 1 (by rfl) ⟨4840217, by rfl⟩ : syracuseStep 6453623 = 9680435) B9680435
theorem B2488697 : Blo 734326 2488697 := bstep (se 2 (by rfl) ⟨933261, by rfl⟩ : syracuseStep 2488697 = 1866523) B1866523
theorem B3734099 : Blo 734326 3734099 := bstep (se 1 (by rfl) ⟨2800574, by rfl⟩ : syracuseStep 3734099 = 5601149) B5601149
theorem B2490047 : Blo 734326 2490047 := bstep (se 1 (by rfl) ⟨1867535, by rfl⟩ : syracuseStep 2490047 = 3735071) B3735071
theorem B7077577 : Blo 734326 7077577 := bstep (se 2 (by rfl) ⟨2654091, by rfl⟩ : syracuseStep 7077577 = 5308183) B5308183
theorem B1245287 : Blo 734326 1245287 := bstep (se 1 (by rfl) ⟨933965, by rfl⟩ : syracuseStep 1245287 = 1867931) B1867931
theorem B4489339 : Blo 734326 4489339 := bstep (se 1 (by rfl) ⟨3367004, by rfl⟩ : syracuseStep 4489339 = 6734009) B6734009
theorem B2359655 : Blo 734326 2359655 := bstep (se 1 (by rfl) ⟨1769741, by rfl⟩ : syracuseStep 2359655 = 3539483) B3539483
theorem B787303 : Blo 734326 787303 := bstep (se 1 (by rfl) ⟨590477, by rfl⟩ : syracuseStep 787303 = 1180955) B1180955
theorem B1180775 : Blo 734326 1180775 := bstep (se 1 (by rfl) ⟨885581, by rfl⟩ : syracuseStep 1180775 = 1771163) B1771163
theorem B26870939 : Blo 734326 26870939 := bstep (se 1 (by rfl) ⟨20153204, by rfl⟩ : syracuseStep 26870939 = 40306409) B40306409
theorem B2491775 : Blo 734326 2491775 := bstep (se 1 (by rfl) ⟨1868831, by rfl⟩ : syracuseStep 2491775 = 3737663) B3737663
theorem B96897161 : Blo 734326 96897161 := bstep (se 2 (by rfl) ⟨36336435, by rfl⟩ : syracuseStep 96897161 = 72672871) B72672871
theorem B1771847 : Blo 734326 1771847 := bstep (se 1 (by rfl) ⟨1328885, by rfl⟩ : syracuseStep 1771847 = 2657771) B2657771
theorem B5671387 : Blo 734326 5671387 := bstep (se 1 (by rfl) ⟨4253540, by rfl⟩ : syracuseStep 5671387 = 8507081) B8507081
theorem B5310953 : Blo 734326 5310953 := bstep (se 2 (by rfl) ⟨1991607, by rfl⟩ : syracuseStep 5310953 = 3983215) B3983215
theorem B4787387 : Blo 734326 4787387 := bstep (se 1 (by rfl) ⟨3590540, by rfl⟩ : syracuseStep 4787387 = 7181081) B7181081
theorem B22613231 : Blo 734326 22613231 := bstep (se 1 (by rfl) ⟨16959923, by rfl⟩ : syracuseStep 22613231 = 33919847) B33919847
theorem B5312105 : Blo 734326 5312105 := bstep (se 2 (by rfl) ⟨1992039, by rfl⟩ : syracuseStep 5312105 = 3984079) B3984079
theorem B5675105 : Blo 734326 5675105 := bstep (se 2 (by rfl) ⟨2128164, by rfl⟩ : syracuseStep 5675105 = 4256329) B4256329
theorem B30251465 : Blo 734326 30251465 := bstep (se 2 (by rfl) ⟨11344299, by rfl⟩ : syracuseStep 30251465 = 22688599) B22688599
theorem B2300519 : Blo 734326 2300519 := bstep (se 1 (by rfl) ⟨1725389, by rfl⟩ : syracuseStep 2300519 = 3450779) B3450779
theorem B2792951 : Blo 734326 2792951 := bstep (se 1 (by rfl) ⟨2094713, by rfl⟩ : syracuseStep 2792951 = 4189427) B4189427
theorem B4302415 : Blo 734326 4302415 := bstep (se 1 (by rfl) ⟨3226811, by rfl⟩ : syracuseStep 4302415 = 6453623) B6453623
theorem B13773725 : Blo 734326 13773725 := bstep (se 3 (by rfl) ⟨2582573, by rfl⟩ : syracuseStep 13773725 = 5165147) B5165147
theorem B3976103 : Blo 734326 3976103 := bstep (se 1 (by rfl) ⟨2982077, by rfl⟩ : syracuseStep 3976103 = 5964155) B5964155
theorem B33960329 : Blo 734326 33960329 := bstep (se 2 (by rfl) ⟨12735123, by rfl⟩ : syracuseStep 33960329 = 25470247) B25470247
theorem B3355183 : Blo 734326 3355183 := bstep (se 1 (by rfl) ⟨2516387, by rfl⟩ : syracuseStep 3355183 = 5032775) B5032775
theorem B3978071 : Blo 734326 3978071 := bstep (se 1 (by rfl) ⟨2983553, by rfl⟩ : syracuseStep 3978071 = 5967107) B5967107
theorem B734623 : Blo 734326 734623 := bstep (se 1 (by rfl) ⟨550967, by rfl⟩ : syracuseStep 734623 = 1101935) B1101935
theorem B734951 : Blo 734326 734951 := bstep (se 1 (by rfl) ⟨551213, by rfl⟩ : syracuseStep 734951 = 1102427) B1102427
theorem B735727 : Blo 734326 735727 := bstep (se 1 (by rfl) ⟨551795, by rfl⟩ : syracuseStep 735727 = 1103591) B1103591
theorem B735975 : Blo 734326 735975 := bstep (se 1 (by rfl) ⟨551981, by rfl⟩ : syracuseStep 735975 = 1103963) B1103963
theorem B736127 : Blo 734326 736127 := bstep (se 1 (by rfl) ⟨552095, by rfl⟩ : syracuseStep 736127 = 1104191) B1104191
theorem B736871 : Blo 734326 736871 := bstep (se 1 (by rfl) ⟨552653, by rfl⟩ : syracuseStep 736871 = 1105307) B1105307
theorem B737023 : Blo 734326 737023 := bstep (se 1 (by rfl) ⟨552767, by rfl⟩ : syracuseStep 737023 = 1105535) B1105535
theorem B1261423 : Blo 734326 1261423 := bstep (se 1 (by rfl) ⟨946067, by rfl⟩ : syracuseStep 1261423 = 1892135) B1892135
theorem B737439 : Blo 734326 737439 := bstep (se 1 (by rfl) ⟨553079, by rfl⟩ : syracuseStep 737439 = 1106159) B1106159
theorem B737607 : Blo 734326 737607 := bstep (se 1 (by rfl) ⟨553205, by rfl⟩ : syracuseStep 737607 = 1106411) B1106411
theorem B737983 : Blo 734326 737983 := bstep (se 1 (by rfl) ⟨553487, by rfl⟩ : syracuseStep 737983 = 1106975) B1106975
theorem B738075 : Blo 734326 738075 := bstep (se 1 (by rfl) ⟨553556, by rfl⟩ : syracuseStep 738075 = 1107113) B1107113
theorem B738175 : Blo 734326 738175 := bstep (se 1 (by rfl) ⟨553631, by rfl⟩ : syracuseStep 738175 = 1107263) B1107263
theorem B6276143 : Blo 734326 6276143 := bstep (se 1 (by rfl) ⟨4707107, by rfl⟩ : syracuseStep 6276143 = 9414215) B9414215
theorem B3720329 : Blo 734326 3720329 := bstep (se 2 (by rfl) ⟨1395123, by rfl⟩ : syracuseStep 3720329 = 2790247) B2790247
theorem B1549681955 : Blo 734326 1549681955 := bstep (se 1 (by rfl) ⟨1162261466, by rfl⟩ : syracuseStep 1549681955 = 2324522933) B2324522933
theorem B1656809 : Blo 734326 1656809 := bstep (se 2 (by rfl) ⟨621303, by rfl⟩ : syracuseStep 1656809 = 1242607) B1242607
theorem B5818877 : Blo 734326 5818877 := bstep (se 3 (by rfl) ⟨1091039, by rfl⟩ : syracuseStep 5818877 = 2182079) B2182079
theorem B5655041 : Blo 734326 5655041 := bstep (se 2 (by rfl) ⟨2120640, by rfl⟩ : syracuseStep 5655041 = 4241281) B4241281
theorem B1659131 : Blo 734326 1659131 := bstep (se 1 (by rfl) ⟨1244348, by rfl⟩ : syracuseStep 1659131 = 2488697) B2488697
theorem B1660031 : Blo 734326 1660031 := bstep (se 1 (by rfl) ⟨1245023, by rfl⟩ : syracuseStep 1660031 = 2490047) B2490047
theorem B1661039 : Blo 734326 1661039 := bstep (se 1 (by rfl) ⟨1245779, by rfl⟩ : syracuseStep 1661039 = 2491559) B2491559
theorem B1399103 : Blo 734326 1399103 := bstep (se 1 (by rfl) ⟨1049327, by rfl⟩ : syracuseStep 1399103 = 2098655) B2098655
theorem B6282431 : Blo 734326 6282431 := bstep (se 1 (by rfl) ⟨4711823, by rfl⟩ : syracuseStep 6282431 = 9423647) B9423647
theorem B88366409 : Blo 734326 88366409 := bstep (se 2 (by rfl) ⟨33137403, by rfl⟩ : syracuseStep 88366409 = 66274807) B66274807
theorem B2484863 : Blo 734326 2484863 := bstep (se 1 (by rfl) ⟨1863647, by rfl⟩ : syracuseStep 2484863 = 3727295) B3727295
theorem B4191659 : Blo 734326 4191659 := bstep (se 1 (by rfl) ⟨3143744, by rfl⟩ : syracuseStep 4191659 = 6287489) B6287489
theorem B2488103 : Blo 734326 2488103 := bstep (se 1 (by rfl) ⟨1866077, by rfl⟩ : syracuseStep 2488103 = 3732155) B3732155
theorem B2488427 : Blo 734326 2488427 := bstep (se 1 (by rfl) ⟨1866320, by rfl⟩ : syracuseStep 2488427 = 3732641) B3732641
theorem B3733613 : Blo 734326 3733613 := bstep (se 3 (by rfl) ⟨700052, by rfl⟩ : syracuseStep 3733613 = 1400105) B1400105
theorem B2095591 : Blo 734326 2095591 := bstep (se 1 (by rfl) ⟨1571693, by rfl⟩ : syracuseStep 2095591 = 3143387) B3143387
theorem B26147407 : Blo 734326 26147407 := bstep (se 1 (by rfl) ⟨19610555, by rfl⟩ : syracuseStep 26147407 = 39221111) B39221111
theorem B2489399 : Blo 734326 2489399 := bstep (se 1 (by rfl) ⟨1867049, by rfl⟩ : syracuseStep 2489399 = 3734099) B3734099
theorem B9436769 : Blo 734326 9436769 := bstep (se 2 (by rfl) ⟨3538788, by rfl⟩ : syracuseStep 9436769 = 7077577) B7077577
theorem B1573103 : Blo 734326 1573103 := bstep (se 1 (by rfl) ⟨1179827, by rfl⟩ : syracuseStep 1573103 = 2359655) B2359655
theorem B1181231 : Blo 734326 1181231 := bstep (se 1 (by rfl) ⟨885923, by rfl⟩ : syracuseStep 1181231 = 1771847) B1771847
theorem B3540635 : Blo 734326 3540635 := bstep (se 1 (by rfl) ⟨2655476, by rfl⟩ : syracuseStep 3540635 = 5310953) B5310953
theorem B3770027 : Blo 734326 3770027 := bstep (se 1 (by rfl) ⟨2827520, by rfl⟩ : syracuseStep 3770027 = 5655041) B5655041
theorem B5736553 : Blo 734326 5736553 := bstep (se 2 (by rfl) ⟨2151207, by rfl⟩ : syracuseStep 5736553 = 4302415) B4302415
theorem B15075487 : Blo 734326 15075487 := bstep (se 1 (by rfl) ⟨11306615, by rfl⟩ : syracuseStep 15075487 = 22613231) B22613231
theorem B3541403 : Blo 734326 3541403 := bstep (se 1 (by rfl) ⟨2656052, by rfl⟩ : syracuseStep 3541403 = 5312105) B5312105
theorem B3148733 : Blo 734326 3148733 := bstep (se 3 (by rfl) ⟨590387, by rfl⟩ : syracuseStep 3148733 = 1180775) B1180775
theorem B4198949 : Blo 734326 4198949 := bstep (se 4 (by rfl) ⟨393651, by rfl⟩ : syracuseStep 4198949 = 787303) B787303
theorem B6134717 : Blo 734326 6134717 := bstep (se 3 (by rfl) ⟨1150259, by rfl⟩ : syracuseStep 6134717 = 2300519) B2300519
theorem B9182483 : Blo 734326 9182483 := bstep (se 1 (by rfl) ⟨6886862, by rfl⟩ : syracuseStep 9182483 = 13773725) B13773725
theorem B2794121 : Blo 734326 2794121 := bstep (se 2 (by rfl) ⟨1047795, by rfl⟩ : syracuseStep 2794121 = 2095591) B2095591
theorem B2794439 : Blo 734326 2794439 := bstep (se 1 (by rfl) ⟨2095829, by rfl⟩ : syracuseStep 2794439 = 4191659) B4191659
theorem B6727589 : Blo 734326 6727589 := bstep (se 4 (by rfl) ⟨630711, by rfl⟩ : syracuseStep 6727589 = 1261423) B1261423
theorem B830191 : Blo 734326 830191 := bstep (se 1 (by rfl) ⟨622643, by rfl⟩ : syracuseStep 830191 = 1245287) B1245287
theorem B1033121303 : Blo 734326 1033121303 := bstep (se 1 (by rfl) ⟨774840977, by rfl⟩ : syracuseStep 1033121303 = 1549681955) B1549681955
theorem B3879251 : Blo 734326 3879251 := bstep (se 1 (by rfl) ⟨2909438, by rfl⟩ : syracuseStep 3879251 = 5818877) B5818877
theorem B3191591 : Blo 734326 3191591 := bstep (se 1 (by rfl) ⟨2393693, by rfl⟩ : syracuseStep 3191591 = 4787387) B4787387
theorem B932735 : Blo 734326 932735 := bstep (se 1 (by rfl) ⟨699551, by rfl⟩ : syracuseStep 932735 = 1399103) B1399103
theorem B20167643 : Blo 734326 20167643 := bstep (se 1 (by rfl) ⟨15125732, by rfl⟩ : syracuseStep 20167643 = 30251465) B30251465
theorem B258392429 : Blo 734326 258392429 := bstep (se 3 (by rfl) ⟨48448580, by rfl⟩ : syracuseStep 258392429 = 96897161) B96897161
theorem B4473577 : Blo 734326 4473577 := bstep (se 2 (by rfl) ⟨1677591, by rfl⟩ : syracuseStep 4473577 = 3355183) B3355183
theorem B1656575 : Blo 734326 1656575 := bstep (se 1 (by rfl) ⟨1242431, by rfl⟩ : syracuseStep 1656575 = 2484863) B2484863
theorem B1658735 : Blo 734326 1658735 := bstep (se 1 (by rfl) ⟨1244051, by rfl⟩ : syracuseStep 1658735 = 2488103) B2488103
theorem B1658951 : Blo 734326 1658951 := bstep (se 1 (by rfl) ⟨1244213, by rfl⟩ : syracuseStep 1658951 = 2488427) B2488427
theorem B1659599 : Blo 734326 1659599 := bstep (se 1 (by rfl) ⟨1244699, by rfl⟩ : syracuseStep 1659599 = 2489399) B2489399
theorem B5985785 : Blo 734326 5985785 := bstep (se 2 (by rfl) ⟨2244669, by rfl⟩ : syracuseStep 5985785 = 4489339) B4489339
theorem B4184095 : Blo 734326 4184095 := bstep (se 1 (by rfl) ⟨3138071, by rfl⟩ : syracuseStep 4184095 = 6276143) B6276143
theorem B2480219 : Blo 734326 2480219 := bstep (se 1 (by rfl) ⟨1860164, by rfl⟩ : syracuseStep 2480219 = 3720329) B3720329
theorem B17913959 : Blo 734326 17913959 := bstep (se 1 (by rfl) ⟨13435469, by rfl⟩ : syracuseStep 17913959 = 26870939) B26870939
theorem B1661183 : Blo 734326 1661183 := bstep (se 1 (by rfl) ⟨1245887, by rfl⟩ : syracuseStep 1661183 = 2491775) B2491775
theorem B1104539 : Blo 734326 1104539 := bstep (se 1 (by rfl) ⟨828404, by rfl⟩ : syracuseStep 1104539 = 1656809) B1656809
theorem B1106087 : Blo 734326 1106087 := bstep (se 1 (by rfl) ⟨829565, by rfl⟩ : syracuseStep 1106087 = 1659131) B1659131
theorem B7561849 : Blo 734326 7561849 := bstep (se 2 (by rfl) ⟨2835693, by rfl⟩ : syracuseStep 7561849 = 5671387) B5671387
theorem B1106687 : Blo 734326 1106687 := bstep (se 1 (by rfl) ⟨830015, by rfl⟩ : syracuseStep 1106687 = 1660031) B1660031
theorem B1107359 : Blo 734326 1107359 := bstep (se 1 (by rfl) ⟨830519, by rfl⟩ : syracuseStep 1107359 = 1661039) B1661039
theorem B4188287 : Blo 734326 4188287 := bstep (se 1 (by rfl) ⟨3141215, by rfl⟩ : syracuseStep 4188287 = 6282431) B6282431
theorem B58910939 : Blo 734326 58910939 := bstep (se 1 (by rfl) ⟨44183204, by rfl⟩ : syracuseStep 58910939 = 88366409) B88366409
theorem B1861967 : Blo 734326 1861967 := bstep (se 1 (by rfl) ⟨1396475, by rfl⟩ : syracuseStep 1861967 = 2792951) B2792951
theorem B15133613 : Blo 734326 15133613 := bstep (se 3 (by rfl) ⟨2837552, by rfl⟩ : syracuseStep 15133613 = 5675105) B5675105
theorem B2650735 : Blo 734326 2650735 := bstep (se 1 (by rfl) ⟨1988051, by rfl⟩ : syracuseStep 2650735 = 3976103) B3976103
theorem B22640219 : Blo 734326 22640219 := bstep (se 1 (by rfl) ⟨16980164, by rfl⟩ : syracuseStep 22640219 = 33960329) B33960329
theorem B2652047 : Blo 734326 2652047 := bstep (se 1 (by rfl) ⟨1989035, by rfl⟩ : syracuseStep 2652047 = 3978071) B3978071
theorem B34863209 : Blo 734326 34863209 := bstep (se 2 (by rfl) ⟨13073703, by rfl⟩ : syracuseStep 34863209 = 26147407) B26147407
theorem B2489075 : Blo 734326 2489075 := bstep (se 1 (by rfl) ⟨1866806, by rfl⟩ : syracuseStep 2489075 = 3733613) B3733613
theorem B6291179 : Blo 734326 6291179 := bstep (se 1 (by rfl) ⟨4718384, by rfl⟩ : syracuseStep 6291179 = 9436769) B9436769
theorem B1048735 : Blo 734326 1048735 := bstep (se 1 (by rfl) ⟨786551, by rfl⟩ : syracuseStep 1048735 = 1573103) B1573103
theorem B172261619 : Blo 734326 172261619 := bstep (se 1 (by rfl) ⟨129196214, by rfl⟩ : syracuseStep 172261619 = 258392429) B258392429
theorem B5964769 : Blo 734326 5964769 := bstep (se 2 (by rfl) ⟨2236788, by rfl⟩ : syracuseStep 5964769 = 4473577) B4473577
theorem B787487 : Blo 734326 787487 := bstep (se 1 (by rfl) ⟨590615, by rfl⟩ : syracuseStep 787487 = 1181231) B1181231
theorem B2360423 : Blo 734326 2360423 := bstep (se 1 (by rfl) ⟨1770317, by rfl⟩ : syracuseStep 2360423 = 3540635) B3540635
theorem B2360935 : Blo 734326 2360935 := bstep (se 1 (by rfl) ⟨1770701, by rfl⟩ : syracuseStep 2360935 = 3541403) B3541403
theorem B15962093 : Blo 734326 15962093 := bstep (se 3 (by rfl) ⟨2992892, by rfl⟩ : syracuseStep 15962093 = 5985785) B5985785
theorem B2792191 : Blo 734326 2792191 := bstep (se 1 (by rfl) ⟨2094143, by rfl⟩ : syracuseStep 2792191 = 4188287) B4188287
theorem B8396621 : Blo 734326 8396621 := bstep (se 3 (by rfl) ⟨1574366, by rfl⟩ : syracuseStep 8396621 = 3148733) B3148733
theorem B53780381 : Blo 734326 53780381 := bstep (se 3 (by rfl) ⟨10083821, by rfl⟩ : syracuseStep 53780381 = 20167643) B20167643
theorem B5578793 : Blo 734326 5578793 := bstep (se 2 (by rfl) ⟨2092047, by rfl⟩ : syracuseStep 5578793 = 4184095) B4184095
theorem B23242139 : Blo 734326 23242139 := bstep (se 1 (by rfl) ⟨17431604, by rfl⟩ : syracuseStep 23242139 = 34863209) B34863209
theorem B20100649 : Blo 734326 20100649 := bstep (se 2 (by rfl) ⟨7537743, by rfl⟩ : syracuseStep 20100649 = 15075487) B15075487
theorem B2799299 : Blo 734326 2799299 := bstep (se 1 (by rfl) ⟨2099474, by rfl⟩ : syracuseStep 2799299 = 4198949) B4198949
theorem B1653479 : Blo 734326 1653479 := bstep (se 1 (by rfl) ⟨1240109, by rfl⟩ : syracuseStep 1653479 = 2480219) B2480219
theorem B11942639 : Blo 734326 11942639 := bstep (se 1 (by rfl) ⟨8956979, by rfl⟩ : syracuseStep 11942639 = 17913959) B17913959
theorem B736359 : Blo 734326 736359 := bstep (se 1 (by rfl) ⟨552269, by rfl⟩ : syracuseStep 736359 = 1104539) B1104539
theorem B737391 : Blo 734326 737391 := bstep (se 1 (by rfl) ⟨553043, by rfl⟩ : syracuseStep 737391 = 1106087) B1106087
theorem B737791 : Blo 734326 737791 := bstep (se 1 (by rfl) ⟨553343, by rfl⟩ : syracuseStep 737791 = 1106687) B1106687
theorem B738239 : Blo 734326 738239 := bstep (se 1 (by rfl) ⟨553679, by rfl⟩ : syracuseStep 738239 = 1107359) B1107359
theorem B39273959 : Blo 734326 39273959 := bstep (se 1 (by rfl) ⟨29455469, by rfl⟩ : syracuseStep 39273959 = 58910939) B58910939
theorem B40356301 : Blo 734326 40356301 := bstep (se 3 (by rfl) ⟨7566806, by rfl⟩ : syracuseStep 40356301 = 15133613) B15133613
theorem B15093479 : Blo 734326 15093479 := bstep (se 1 (by rfl) ⟨11320109, by rfl⟩ : syracuseStep 15093479 = 22640219) B22640219
theorem B1659383 : Blo 734326 1659383 := bstep (se 1 (by rfl) ⟨1244537, by rfl⟩ : syracuseStep 1659383 = 2489075) B2489075
theorem B10082465 : Blo 734326 10082465 := bstep (se 2 (by rfl) ⟨3780924, by rfl⟩ : syracuseStep 10082465 = 7561849) B7561849
theorem B2513351 : Blo 734326 2513351 := bstep (se 1 (by rfl) ⟨1885013, by rfl⟩ : syracuseStep 2513351 = 3770027) B3770027
theorem B1104383 : Blo 734326 1104383 := bstep (se 1 (by rfl) ⟨828287, by rfl⟩ : syracuseStep 1104383 = 1656575) B1656575
theorem B122379797 : Blo 734326 122379797 := bstep (se 6 (by rfl) ⟨2868276, by rfl⟩ : syracuseStep 122379797 = 5736553) B5736553
theorem B1105823 : Blo 734326 1105823 := bstep (se 1 (by rfl) ⟨829367, by rfl⟩ : syracuseStep 1105823 = 1658735) B1658735
theorem B1105967 : Blo 734326 1105967 := bstep (se 1 (by rfl) ⟨829475, by rfl⟩ : syracuseStep 1105967 = 1658951) B1658951
theorem B1106399 : Blo 734326 1106399 := bstep (se 1 (by rfl) ⟨829799, by rfl⟩ : syracuseStep 1106399 = 1659599) B1659599
theorem B1106921 : Blo 734326 1106921 := bstep (se 2 (by rfl) ⟨415095, by rfl⟩ : syracuseStep 1106921 = 830191) B830191
theorem B1107455 : Blo 734326 1107455 := bstep (se 1 (by rfl) ⟨830591, by rfl⟩ : syracuseStep 1107455 = 1661183) B1661183
theorem B4089811 : Blo 734326 4089811 := bstep (se 1 (by rfl) ⟨3067358, by rfl⟩ : syracuseStep 4089811 = 6134717) B6134717
theorem B6121655 : Blo 734326 6121655 := bstep (se 1 (by rfl) ⟨4591241, by rfl⟩ : syracuseStep 6121655 = 9182483) B9182483
theorem B1862747 : Blo 734326 1862747 := bstep (se 1 (by rfl) ⟨1397060, by rfl⟩ : syracuseStep 1862747 = 2794121) B2794121
theorem B1862959 : Blo 734326 1862959 := bstep (se 1 (by rfl) ⟨1397219, by rfl⟩ : syracuseStep 1862959 = 2794439) B2794439
theorem B3534313 : Blo 734326 3534313 := bstep (se 2 (by rfl) ⟨1325367, by rfl⟩ : syracuseStep 3534313 = 2650735) B2650735
theorem B4485059 : Blo 734326 4485059 := bstep (se 1 (by rfl) ⟨3363794, by rfl⟩ : syracuseStep 4485059 = 6727589) B6727589
theorem B1241311 : Blo 734326 1241311 := bstep (se 1 (by rfl) ⟨930983, by rfl⟩ : syracuseStep 1241311 = 1861967) B1861967
theorem B2487293 : Blo 734326 2487293 := bstep (se 3 (by rfl) ⟨466367, by rfl⟩ : syracuseStep 2487293 = 932735) B932735
theorem B688747535 : Blo 734326 688747535 := bstep (se 1 (by rfl) ⟨516560651, by rfl⟩ : syracuseStep 688747535 = 1033121303) B1033121303
theorem B2586167 : Blo 734326 2586167 := bstep (se 1 (by rfl) ⟨1939625, by rfl⟩ : syracuseStep 2586167 = 3879251) B3879251
theorem B2127727 : Blo 734326 2127727 := bstep (se 1 (by rfl) ⟨1595795, by rfl⟩ : syracuseStep 2127727 = 3191591) B3191591
theorem B1768031 : Blo 734326 1768031 := bstep (se 1 (by rfl) ⟨1326023, by rfl⟩ : syracuseStep 1768031 = 2652047) B2652047
theorem B4194119 : Blo 734326 4194119 := bstep (se 1 (by rfl) ⟨3145589, by rfl⟩ : syracuseStep 4194119 = 6291179) B6291179
theorem B1573615 : Blo 734326 1573615 := bstep (se 1 (by rfl) ⟨1180211, by rfl⟩ : syracuseStep 1573615 = 2360423) B2360423
theorem B26182639 : Blo 734326 26182639 := bstep (se 1 (by rfl) ⟨19636979, by rfl⟩ : syracuseStep 26182639 = 39273959) B39273959
theorem B3147913 : Blo 734326 3147913 := bstep (se 2 (by rfl) ⟨1180467, by rfl⟩ : syracuseStep 3147913 = 2360935) B2360935
theorem B10062319 : Blo 734326 10062319 := bstep (se 1 (by rfl) ⟨7546739, by rfl⟩ : syracuseStep 10062319 = 15093479) B15093479
theorem B2099965 : Blo 734326 2099965 := bstep (se 3 (by rfl) ⟨393743, by rfl⟩ : syracuseStep 2099965 = 787487) B787487
theorem B53808401 : Blo 734326 53808401 := bstep (se 2 (by rfl) ⟨20178150, by rfl⟩ : syracuseStep 53808401 = 40356301) B40356301
theorem B6721643 : Blo 734326 6721643 := bstep (se 1 (by rfl) ⟨5041232, by rfl⟩ : syracuseStep 6721643 = 10082465) B10082465
theorem B1675567 : Blo 734326 1675567 := bstep (se 1 (by rfl) ⟨1256675, by rfl⟩ : syracuseStep 1675567 = 2513351) B2513351
theorem B35853587 : Blo 734326 35853587 := bstep (se 1 (by rfl) ⟨26890190, by rfl⟩ : syracuseStep 35853587 = 53780381) B53780381
theorem B2990039 : Blo 734326 2990039 := bstep (se 1 (by rfl) ⟨2242529, by rfl⟩ : syracuseStep 2990039 = 4485059) B4485059
theorem B11347877 : Blo 734326 11347877 := bstep (se 4 (by rfl) ⟨1063863, by rfl⟩ : syracuseStep 11347877 = 2127727) B2127727
theorem B2796079 : Blo 734326 2796079 := bstep (se 1 (by rfl) ⟨2097059, by rfl⟩ : syracuseStep 2796079 = 4194119) B4194119
theorem B5453081 : Blo 734326 5453081 := bstep (se 2 (by rfl) ⟨2044905, by rfl⟩ : syracuseStep 5453081 = 4089811) B4089811
theorem B736255 : Blo 734326 736255 := bstep (se 1 (by rfl) ⟨552191, by rfl⟩ : syracuseStep 736255 = 1104383) B1104383
theorem B737215 : Blo 734326 737215 := bstep (se 1 (by rfl) ⟨552911, by rfl⟩ : syracuseStep 737215 = 1105823) B1105823
theorem B3719195 : Blo 734326 3719195 := bstep (se 1 (by rfl) ⟨2789396, by rfl⟩ : syracuseStep 3719195 = 5578793) B5578793
theorem B737311 : Blo 734326 737311 := bstep (se 1 (by rfl) ⟨552983, by rfl⟩ : syracuseStep 737311 = 1105967) B1105967
theorem B1655081 : Blo 734326 1655081 := bstep (se 2 (by rfl) ⟨620655, by rfl⟩ : syracuseStep 1655081 = 1241311) B1241311
theorem B737599 : Blo 734326 737599 := bstep (se 1 (by rfl) ⟨553199, by rfl⟩ : syracuseStep 737599 = 1106399) B1106399
theorem B737947 : Blo 734326 737947 := bstep (se 1 (by rfl) ⟨553460, by rfl⟩ : syracuseStep 737947 = 1106921) B1106921
theorem B738303 : Blo 734326 738303 := bstep (se 1 (by rfl) ⟨553727, by rfl⟩ : syracuseStep 738303 = 1107455) B1107455
theorem B4081103 : Blo 734326 4081103 := bstep (se 1 (by rfl) ⟨3060827, by rfl⟩ : syracuseStep 4081103 = 6121655) B6121655
theorem B1658195 : Blo 734326 1658195 := bstep (se 1 (by rfl) ⟨1243646, by rfl⟩ : syracuseStep 1658195 = 2487293) B2487293
theorem B459165023 : Blo 734326 459165023 := bstep (se 1 (by rfl) ⟨344373767, by rfl⟩ : syracuseStep 459165023 = 688747535) B688747535
theorem B3722921 : Blo 734326 3722921 := bstep (se 2 (by rfl) ⟨1396095, by rfl⟩ : syracuseStep 3722921 = 2792191) B2792191
theorem B1724111 : Blo 734326 1724111 := bstep (se 1 (by rfl) ⟨1293083, by rfl⟩ : syracuseStep 1724111 = 2586167) B2586167
theorem B1102319 : Blo 734326 1102319 := bstep (se 1 (by rfl) ⟨826739, by rfl⟩ : syracuseStep 1102319 = 1653479) B1653479
theorem B114841079 : Blo 734326 114841079 := bstep (se 1 (by rfl) ⟨86130809, by rfl⟩ : syracuseStep 114841079 = 172261619) B172261619
theorem B1398313 : Blo 734326 1398313 := bstep (se 2 (by rfl) ⟨524367, by rfl⟩ : syracuseStep 1398313 = 1048735) B1048735
theorem B7953025 : Blo 734326 7953025 := bstep (se 2 (by rfl) ⟨2982384, by rfl⟩ : syracuseStep 7953025 = 5964769) B5964769
theorem B10641395 : Blo 734326 10641395 := bstep (se 1 (by rfl) ⟨7981046, by rfl⟩ : syracuseStep 10641395 = 15962093) B15962093
theorem B1106255 : Blo 734326 1106255 := bstep (se 1 (by rfl) ⟨829691, by rfl⟩ : syracuseStep 1106255 = 1659383) B1659383
theorem B2483945 : Blo 734326 2483945 := bstep (se 2 (by rfl) ⟨931479, by rfl⟩ : syracuseStep 2483945 = 1862959) B1862959
theorem B4712417 : Blo 734326 4712417 := bstep (se 2 (by rfl) ⟨1767156, by rfl⟩ : syracuseStep 4712417 = 3534313) B3534313
theorem B81586531 : Blo 734326 81586531 := bstep (se 1 (by rfl) ⟨61189898, by rfl⟩ : syracuseStep 81586531 = 122379797) B122379797
theorem B5597747 : Blo 734326 5597747 := bstep (se 1 (by rfl) ⟨4198310, by rfl⟩ : syracuseStep 5597747 = 8396621) B8396621
theorem B15494759 : Blo 734326 15494759 := bstep (se 1 (by rfl) ⟨11621069, by rfl⟩ : syracuseStep 15494759 = 23242139) B23242139
theorem B26800865 : Blo 734326 26800865 := bstep (se 2 (by rfl) ⟨10050324, by rfl⟩ : syracuseStep 26800865 = 20100649) B20100649
theorem B1241831 : Blo 734326 1241831 := bstep (se 1 (by rfl) ⟨931373, by rfl⟩ : syracuseStep 1241831 = 1862747) B1862747
theorem B1866199 : Blo 734326 1866199 := bstep (se 1 (by rfl) ⟨1399649, by rfl⟩ : syracuseStep 1866199 = 2799299) B2799299
theorem B1178687 : Blo 734326 1178687 := bstep (se 1 (by rfl) ⟨884015, by rfl⟩ : syracuseStep 1178687 = 1768031) B1768031
theorem B7961759 : Blo 734326 7961759 := bstep (se 1 (by rfl) ⟨5971319, by rfl⟩ : syracuseStep 7961759 = 11942639) B11942639
theorem B2720735 : Blo 734326 2720735 := bstep (se 1 (by rfl) ⟨2040551, by rfl⟩ : syracuseStep 2720735 = 4081103) B4081103
theorem B2098153 : Blo 734326 2098153 := bstep (se 2 (by rfl) ⟨786807, by rfl⟩ : syracuseStep 2098153 = 1573615) B1573615
theorem B1149407 : Blo 734326 1149407 := bstep (se 1 (by rfl) ⟨862055, by rfl⟩ : syracuseStep 1149407 = 1724111) B1724111
theorem B4197217 : Blo 734326 4197217 := bstep (se 2 (by rfl) ⟨1573956, by rfl⟩ : syracuseStep 4197217 = 3147913) B3147913
theorem B2234089 : Blo 734326 2234089 := bstep (se 2 (by rfl) ⟨837783, by rfl⟩ : syracuseStep 2234089 = 1675567) B1675567
theorem B10329839 : Blo 734326 10329839 := bstep (se 1 (by rfl) ⟨7747379, by rfl⟩ : syracuseStep 10329839 = 15494759) B15494759
theorem B17867243 : Blo 734326 17867243 := bstep (se 1 (by rfl) ⟨13400432, by rfl⟩ : syracuseStep 17867243 = 26800865) B26800865
theorem B827887 : Blo 734326 827887 := bstep (se 1 (by rfl) ⟨620915, by rfl⟩ : syracuseStep 827887 = 1241831) B1241831
theorem B7973437 : Blo 734326 7973437 := bstep (se 3 (by rfl) ⟨1495019, by rfl⟩ : syracuseStep 7973437 = 2990039) B2990039
theorem B34910185 : Blo 734326 34910185 := bstep (se 2 (by rfl) ⟨13091319, by rfl⟩ : syracuseStep 34910185 = 26182639) B26182639
theorem B734879 : Blo 734326 734879 := bstep (se 1 (by rfl) ⟨551159, by rfl⟩ : syracuseStep 734879 = 1102319) B1102319
theorem B13416425 : Blo 734326 13416425 := bstep (se 2 (by rfl) ⟨5031159, by rfl⟩ : syracuseStep 13416425 = 10062319) B10062319
theorem B23902391 : Blo 734326 23902391 := bstep (se 1 (by rfl) ⟨17926793, by rfl⟩ : syracuseStep 23902391 = 35853587) B35853587
theorem B76560719 : Blo 734326 76560719 := bstep (se 1 (by rfl) ⟨57420539, by rfl⟩ : syracuseStep 76560719 = 114841079) B114841079
theorem B2799953 : Blo 734326 2799953 := bstep (se 2 (by rfl) ⟨1049982, by rfl⟩ : syracuseStep 2799953 = 2099965) B2099965
theorem B7094263 : Blo 734326 7094263 := bstep (se 1 (by rfl) ⟨5320697, by rfl⟩ : syracuseStep 7094263 = 10641395) B10641395
theorem B737503 : Blo 734326 737503 := bstep (se 1 (by rfl) ⟨553127, by rfl⟩ : syracuseStep 737503 = 1106255) B1106255
theorem B1655963 : Blo 734326 1655963 := bstep (se 1 (by rfl) ⟨1241972, by rfl⟩ : syracuseStep 1655963 = 2483945) B2483945
theorem B10604033 : Blo 734326 10604033 := bstep (se 2 (by rfl) ⟨3976512, by rfl⟩ : syracuseStep 10604033 = 7953025) B7953025
theorem B2479463 : Blo 734326 2479463 := bstep (se 1 (by rfl) ⟨1859597, by rfl⟩ : syracuseStep 2479463 = 3719195) B3719195
theorem B1103387 : Blo 734326 1103387 := bstep (se 1 (by rfl) ⟨827540, by rfl⟩ : syracuseStep 1103387 = 1655081) B1655081
theorem B1105463 : Blo 734326 1105463 := bstep (se 1 (by rfl) ⟨829097, by rfl⟩ : syracuseStep 1105463 = 1658195) B1658195
theorem B306110015 : Blo 734326 306110015 := bstep (se 1 (by rfl) ⟨229582511, by rfl⟩ : syracuseStep 306110015 = 459165023) B459165023
theorem B2481947 : Blo 734326 2481947 := bstep (se 1 (by rfl) ⟨1861460, by rfl⟩ : syracuseStep 2481947 = 3722921) B3722921
theorem B4481095 : Blo 734326 4481095 := bstep (se 1 (by rfl) ⟨3360821, by rfl⟩ : syracuseStep 4481095 = 6721643) B6721643
theorem B108782041 : Blo 734326 108782041 := bstep (se 2 (by rfl) ⟨40793265, by rfl⟩ : syracuseStep 108782041 = 81586531) B81586531
theorem B3728105 : Blo 734326 3728105 := bstep (se 2 (by rfl) ⟨1398039, by rfl⟩ : syracuseStep 3728105 = 2796079) B2796079
theorem B7565251 : Blo 734326 7565251 := bstep (se 1 (by rfl) ⟨5673938, by rfl⟩ : syracuseStep 7565251 = 11347877) B11347877
theorem B3141611 : Blo 734326 3141611 := bstep (se 1 (by rfl) ⟨2356208, by rfl⟩ : syracuseStep 3141611 = 4712417) B4712417
theorem B3731831 : Blo 734326 3731831 := bstep (se 1 (by rfl) ⟨2798873, by rfl⟩ : syracuseStep 3731831 = 5597747) B5597747
theorem B1864417 : Blo 734326 1864417 := bstep (se 2 (by rfl) ⟨699156, by rfl⟩ : syracuseStep 1864417 = 1398313) B1398313
theorem B2488265 : Blo 734326 2488265 := bstep (se 2 (by rfl) ⟨933099, by rfl⟩ : syracuseStep 2488265 = 1866199) B1866199
theorem B143489069 : Blo 734326 143489069 := bstep (se 3 (by rfl) ⟨26904200, by rfl⟩ : syracuseStep 143489069 = 53808401) B53808401
theorem B3635387 : Blo 734326 3635387 := bstep (se 1 (by rfl) ⟨2726540, by rfl⟩ : syracuseStep 3635387 = 5453081) B5453081
theorem B785791 : Blo 734326 785791 := bstep (se 1 (by rfl) ⟨589343, by rfl⟩ : syracuseStep 785791 = 1178687) B1178687
theorem B5307839 : Blo 734326 5307839 := bstep (se 1 (by rfl) ⟨3980879, by rfl⟩ : syracuseStep 5307839 = 7961759) B7961759
theorem B47645981 : Blo 734326 47645981 := bstep (se 3 (by rfl) ⟨8933621, by rfl⟩ : syracuseStep 47645981 = 17867243) B17867243
theorem B6886559 : Blo 734326 6886559 := bstep (se 1 (by rfl) ⟨5164919, by rfl⟩ : syracuseStep 6886559 = 10329839) B10329839
theorem B95659379 : Blo 734326 95659379 := bstep (se 1 (by rfl) ⟨71744534, by rfl⟩ : syracuseStep 95659379 = 143489069) B143489069
theorem B15934927 : Blo 734326 15934927 := bstep (se 1 (by rfl) ⟨11951195, by rfl⟩ : syracuseStep 15934927 = 23902391) B23902391
theorem B5974793 : Blo 734326 5974793 := bstep (se 2 (by rfl) ⟨2240547, by rfl⟩ : syracuseStep 5974793 = 4481095) B4481095
theorem B145042721 : Blo 734326 145042721 := bstep (se 2 (by rfl) ⟨54391020, by rfl⟩ : syracuseStep 145042721 = 108782041) B108782041
theorem B1813823 : Blo 734326 1813823 := bstep (se 1 (by rfl) ⟨1360367, by rfl⟩ : syracuseStep 1813823 = 2720735) B2720735
theorem B2797537 : Blo 734326 2797537 := bstep (se 2 (by rfl) ⟨1049076, by rfl⟩ : syracuseStep 2797537 = 2098153) B2098153
theorem B766271 : Blo 734326 766271 := bstep (se 1 (by rfl) ⟨574703, by rfl⟩ : syracuseStep 766271 = 1149407) B1149407
theorem B10631249 : Blo 734326 10631249 := bstep (se 2 (by rfl) ⟨3986718, by rfl⟩ : syracuseStep 10631249 = 7973437) B7973437
theorem B1652975 : Blo 734326 1652975 := bstep (se 1 (by rfl) ⟨1239731, by rfl⟩ : syracuseStep 1652975 = 2479463) B2479463
theorem B735591 : Blo 734326 735591 := bstep (se 1 (by rfl) ⟨551693, by rfl⟩ : syracuseStep 735591 = 1103387) B1103387
theorem B736975 : Blo 734326 736975 := bstep (se 1 (by rfl) ⟨552731, by rfl⟩ : syracuseStep 736975 = 1105463) B1105463
theorem B1654631 : Blo 734326 1654631 := bstep (se 1 (by rfl) ⟨1240973, by rfl⟩ : syracuseStep 1654631 = 2481947) B2481947
theorem B46546913 : Blo 734326 46546913 := bstep (se 2 (by rfl) ⟨17455092, by rfl⟩ : syracuseStep 46546913 = 34910185) B34910185
theorem B204161917 : Blo 734326 204161917 := bstep (se 3 (by rfl) ⟨38280359, by rfl⟩ : syracuseStep 204161917 = 76560719) B76560719
theorem B1658843 : Blo 734326 1658843 := bstep (se 1 (by rfl) ⟨1244132, by rfl⟩ : syracuseStep 1658843 = 2488265) B2488265
theorem B9459017 : Blo 734326 9459017 := bstep (se 2 (by rfl) ⟨3547131, by rfl⟩ : syracuseStep 9459017 = 7094263) B7094263
theorem B1103849 : Blo 734326 1103849 := bstep (se 2 (by rfl) ⟨413943, by rfl⟩ : syracuseStep 1103849 = 827887) B827887
theorem B1103975 : Blo 734326 1103975 := bstep (se 1 (by rfl) ⟨827981, by rfl⟩ : syracuseStep 1103975 = 1655963) B1655963
theorem B7069355 : Blo 734326 7069355 := bstep (se 1 (by rfl) ⟨5302016, by rfl⟩ : syracuseStep 7069355 = 10604033) B10604033
theorem B5596289 : Blo 734326 5596289 := bstep (se 2 (by rfl) ⟨2098608, by rfl⟩ : syracuseStep 5596289 = 4197217) B4197217
theorem B204073343 : Blo 734326 204073343 := bstep (se 1 (by rfl) ⟨153055007, by rfl⟩ : syracuseStep 204073343 = 306110015) B306110015
theorem B10087001 : Blo 734326 10087001 := bstep (se 2 (by rfl) ⟨3782625, by rfl⟩ : syracuseStep 10087001 = 7565251) B7565251
theorem B2485403 : Blo 734326 2485403 := bstep (se 1 (by rfl) ⟨1864052, by rfl⟩ : syracuseStep 2485403 = 3728105) B3728105
theorem B2485889 : Blo 734326 2485889 := bstep (se 2 (by rfl) ⟨932208, by rfl⟩ : syracuseStep 2485889 = 1864417) B1864417
theorem B4190885 : Blo 734326 4190885 := bstep (se 4 (by rfl) ⟨392895, by rfl⟩ : syracuseStep 4190885 = 785791) B785791
theorem B2978785 : Blo 734326 2978785 := bstep (se 2 (by rfl) ⟨1117044, by rfl⟩ : syracuseStep 2978785 = 2234089) B2234089
theorem B2094407 : Blo 734326 2094407 := bstep (se 1 (by rfl) ⟨1570805, by rfl⟩ : syracuseStep 2094407 = 3141611) B3141611
theorem B2487887 : Blo 734326 2487887 := bstep (se 1 (by rfl) ⟨1865915, by rfl⟩ : syracuseStep 2487887 = 3731831) B3731831
theorem B8944283 : Blo 734326 8944283 := bstep (se 1 (by rfl) ⟨6708212, by rfl⟩ : syracuseStep 8944283 = 13416425) B13416425
theorem B2423591 : Blo 734326 2423591 := bstep (se 1 (by rfl) ⟨1817693, by rfl⟩ : syracuseStep 2423591 = 3635387) B3635387
theorem B1866635 : Blo 734326 1866635 := bstep (se 1 (by rfl) ⟨1399976, by rfl⟩ : syracuseStep 1866635 = 2799953) B2799953
theorem B3538559 : Blo 734326 3538559 := bstep (se 1 (by rfl) ⟨2653919, by rfl⟩ : syracuseStep 3538559 = 5307839) B5307839
theorem B63772919 : Blo 734326 63772919 := bstep (se 1 (by rfl) ⟨47829689, by rfl⟩ : syracuseStep 63772919 = 95659379) B95659379
theorem B3971713 : Blo 734326 3971713 := bstep (se 2 (by rfl) ⟨1489392, by rfl⟩ : syracuseStep 3971713 = 2978785) B2978785
theorem B6724667 : Blo 734326 6724667 := bstep (se 1 (by rfl) ⟨5043500, by rfl⟩ : syracuseStep 6724667 = 10087001) B10087001
theorem B2793923 : Blo 734326 2793923 := bstep (se 1 (by rfl) ⟨2095442, by rfl⟩ : syracuseStep 2793923 = 4190885) B4190885
theorem B7087499 : Blo 734326 7087499 := bstep (se 1 (by rfl) ⟨5315624, by rfl⟩ : syracuseStep 7087499 = 10631249) B10631249
theorem B1615727 : Blo 734326 1615727 := bstep (se 1 (by rfl) ⟨1211795, by rfl⟩ : syracuseStep 1615727 = 2423591) B2423591
theorem B2043389 : Blo 734326 2043389 := bstep (se 3 (by rfl) ⟨383135, by rfl⟩ : syracuseStep 2043389 = 766271) B766271
theorem B31763987 : Blo 734326 31763987 := bstep (se 1 (by rfl) ⟨23822990, by rfl⟩ : syracuseStep 31763987 = 47645981) B47645981
theorem B272215889 : Blo 734326 272215889 := bstep (se 2 (by rfl) ⟨102080958, by rfl⟩ : syracuseStep 272215889 = 204161917) B204161917
theorem B21246569 : Blo 734326 21246569 := bstep (se 2 (by rfl) ⟨7967463, by rfl⟩ : syracuseStep 21246569 = 15934927) B15934927
theorem B18364157 : Blo 734326 18364157 := bstep (se 3 (by rfl) ⟨3443279, by rfl⟩ : syracuseStep 18364157 = 6886559) B6886559
theorem B6306011 : Blo 734326 6306011 := bstep (se 1 (by rfl) ⟨4729508, by rfl⟩ : syracuseStep 6306011 = 9459017) B9459017
theorem B735899 : Blo 734326 735899 := bstep (se 1 (by rfl) ⟨551924, by rfl⟩ : syracuseStep 735899 = 1103849) B1103849
theorem B735983 : Blo 734326 735983 := bstep (se 1 (by rfl) ⟨551987, by rfl⟩ : syracuseStep 735983 = 1103975) B1103975
theorem B3983195 : Blo 734326 3983195 := bstep (se 1 (by rfl) ⟨2987396, by rfl⟩ : syracuseStep 3983195 = 5974793) B5974793
theorem B1656935 : Blo 734326 1656935 := bstep (se 1 (by rfl) ⟨1242701, by rfl⟩ : syracuseStep 1656935 = 2485403) B2485403
theorem B1657259 : Blo 734326 1657259 := bstep (se 1 (by rfl) ⟨1242944, by rfl⟩ : syracuseStep 1657259 = 2485889) B2485889
theorem B1396271 : Blo 734326 1396271 := bstep (se 1 (by rfl) ⟨1047203, by rfl⟩ : syracuseStep 1396271 = 2094407) B2094407
theorem B1658591 : Blo 734326 1658591 := bstep (se 1 (by rfl) ⟨1243943, by rfl⟩ : syracuseStep 1658591 = 2487887) B2487887
theorem B1101983 : Blo 734326 1101983 := bstep (se 1 (by rfl) ⟨826487, by rfl⟩ : syracuseStep 1101983 = 1652975) B1652975
theorem B1103087 : Blo 734326 1103087 := bstep (se 1 (by rfl) ⟨827315, by rfl⟩ : syracuseStep 1103087 = 1654631) B1654631
theorem B1105895 : Blo 734326 1105895 := bstep (se 1 (by rfl) ⟨829421, by rfl⟩ : syracuseStep 1105895 = 1658843) B1658843
theorem B4712903 : Blo 734326 4712903 := bstep (se 1 (by rfl) ⟨3534677, by rfl⟩ : syracuseStep 4712903 = 7069355) B7069355
theorem B3730049 : Blo 734326 3730049 := bstep (se 2 (by rfl) ⟨1398768, by rfl⟩ : syracuseStep 3730049 = 2797537) B2797537
theorem B3730859 : Blo 734326 3730859 := bstep (se 1 (by rfl) ⟨2798144, by rfl⟩ : syracuseStep 3730859 = 5596289) B5596289
theorem B136048895 : Blo 734326 136048895 := bstep (se 1 (by rfl) ⟨102036671, by rfl⟩ : syracuseStep 136048895 = 204073343) B204073343
theorem B23851421 : Blo 734326 23851421 := bstep (se 3 (by rfl) ⟨4472141, by rfl⟩ : syracuseStep 23851421 = 8944283) B8944283
theorem B96695147 : Blo 734326 96695147 := bstep (se 1 (by rfl) ⟨72521360, by rfl⟩ : syracuseStep 96695147 = 145042721) B145042721
theorem B1209215 : Blo 734326 1209215 := bstep (se 1 (by rfl) ⟨906911, by rfl⟩ : syracuseStep 1209215 = 1813823) B1813823
theorem B1244423 : Blo 734326 1244423 := bstep (se 1 (by rfl) ⟨933317, by rfl⟩ : syracuseStep 1244423 = 1866635) B1866635
theorem B2359039 : Blo 734326 2359039 := bstep (se 1 (by rfl) ⟨1769279, by rfl⟩ : syracuseStep 2359039 = 3538559) B3538559
theorem B31031275 : Blo 734326 31031275 := bstep (se 1 (by rfl) ⟨23273456, by rfl⟩ : syracuseStep 31031275 = 46546913) B46546913
theorem B2655463 : Blo 734326 2655463 := bstep (se 1 (by rfl) ⟨1991597, by rfl⟩ : syracuseStep 2655463 = 3983195) B3983195
theorem B257853725 : Blo 734326 257853725 := bstep (se 3 (by rfl) ⟨48347573, by rfl⟩ : syracuseStep 257853725 = 96695147) B96695147
theorem B4724999 : Blo 734326 4724999 := bstep (se 1 (by rfl) ⟨3543749, by rfl⟩ : syracuseStep 4724999 = 7087499) B7087499
theorem B21175991 : Blo 734326 21175991 := bstep (se 1 (by rfl) ⟨15881993, by rfl⟩ : syracuseStep 21175991 = 31763987) B31763987
theorem B181477259 : Blo 734326 181477259 := bstep (se 1 (by rfl) ⟨136107944, by rfl⟩ : syracuseStep 181477259 = 272215889) B272215889
theorem B15900947 : Blo 734326 15900947 := bstep (se 1 (by rfl) ⟨11925710, by rfl⟩ : syracuseStep 15900947 = 23851421) B23851421
theorem B14164379 : Blo 734326 14164379 := bstep (se 1 (by rfl) ⟨10623284, by rfl⟩ : syracuseStep 14164379 = 21246569) B21246569
theorem B5449037 : Blo 734326 5449037 := bstep (se 3 (by rfl) ⟨1021694, by rfl⟩ : syracuseStep 5449037 = 2043389) B2043389
theorem B4204007 : Blo 734326 4204007 := bstep (se 1 (by rfl) ⟨3153005, by rfl⟩ : syracuseStep 4204007 = 6306011) B6306011
theorem B829615 : Blo 734326 829615 := bstep (se 1 (by rfl) ⟨622211, by rfl⟩ : syracuseStep 829615 = 1244423) B1244423
theorem B3224573 : Blo 734326 3224573 := bstep (se 3 (by rfl) ⟨604607, by rfl⟩ : syracuseStep 3224573 = 1209215) B1209215
theorem B930847 : Blo 734326 930847 := bstep (se 1 (by rfl) ⟨698135, by rfl⟩ : syracuseStep 930847 = 1396271) B1396271
theorem B734655 : Blo 734326 734655 := bstep (se 1 (by rfl) ⟨550991, by rfl⟩ : syracuseStep 734655 = 1101983) B1101983
theorem B735391 : Blo 734326 735391 := bstep (se 1 (by rfl) ⟨551543, by rfl⟩ : syracuseStep 735391 = 1103087) B1103087
theorem B42515279 : Blo 734326 42515279 := bstep (se 1 (by rfl) ⟨31886459, by rfl⟩ : syracuseStep 42515279 = 63772919) B63772919
theorem B737263 : Blo 734326 737263 := bstep (se 1 (by rfl) ⟨552947, by rfl⟩ : syracuseStep 737263 = 1105895) B1105895
theorem B5295617 : Blo 734326 5295617 := bstep (se 2 (by rfl) ⟨1985856, by rfl⟩ : syracuseStep 5295617 = 3971713) B3971713
theorem B12242771 : Blo 734326 12242771 := bstep (se 1 (by rfl) ⟨9182078, by rfl⟩ : syracuseStep 12242771 = 18364157) B18364157
theorem B41375033 : Blo 734326 41375033 := bstep (se 2 (by rfl) ⟨15515637, by rfl⟩ : syracuseStep 41375033 = 31031275) B31031275
theorem B1104623 : Blo 734326 1104623 := bstep (se 1 (by rfl) ⟨828467, by rfl⟩ : syracuseStep 1104623 = 1656935) B1656935
theorem B1104839 : Blo 734326 1104839 := bstep (se 1 (by rfl) ⟨828629, by rfl⟩ : syracuseStep 1104839 = 1657259) B1657259
theorem B1105727 : Blo 734326 1105727 := bstep (se 1 (by rfl) ⟨829295, by rfl⟩ : syracuseStep 1105727 = 1658591) B1658591
theorem B4483111 : Blo 734326 4483111 := bstep (se 1 (by rfl) ⟨3362333, by rfl⟩ : syracuseStep 4483111 = 6724667) B6724667
theorem B1862615 : Blo 734326 1862615 := bstep (se 1 (by rfl) ⟨1396961, by rfl⟩ : syracuseStep 1862615 = 2793923) B2793923
theorem B1077151 : Blo 734326 1077151 := bstep (se 1 (by rfl) ⟨807863, by rfl⟩ : syracuseStep 1077151 = 1615727) B1615727
theorem B3141935 : Blo 734326 3141935 := bstep (se 1 (by rfl) ⟨2356451, by rfl⟩ : syracuseStep 3141935 = 4712903) B4712903
theorem B2486699 : Blo 734326 2486699 := bstep (se 1 (by rfl) ⟨1865024, by rfl⟩ : syracuseStep 2486699 = 3730049) B3730049
theorem B2487239 : Blo 734326 2487239 := bstep (se 1 (by rfl) ⟨1865429, by rfl⟩ : syracuseStep 2487239 = 3730859) B3730859
theorem B90699263 : Blo 734326 90699263 := bstep (se 1 (by rfl) ⟨68024447, by rfl⟩ : syracuseStep 90699263 = 136048895) B136048895
theorem B3145385 : Blo 734326 3145385 := bstep (se 2 (by rfl) ⟨1179519, by rfl⟩ : syracuseStep 3145385 = 2359039) B2359039
theorem B171902483 : Blo 734326 171902483 := bstep (se 1 (by rfl) ⟨128926862, by rfl⟩ : syracuseStep 171902483 = 257853725) B257853725
theorem B3540617 : Blo 734326 3540617 := bstep (se 2 (by rfl) ⟨1327731, by rfl⟩ : syracuseStep 3540617 = 2655463) B2655463
theorem B8161847 : Blo 734326 8161847 := bstep (se 1 (by rfl) ⟨6121385, by rfl⟩ : syracuseStep 8161847 = 12242771) B12242771
theorem B3149999 : Blo 734326 3149999 := bstep (se 1 (by rfl) ⟨2362499, by rfl⟩ : syracuseStep 3149999 = 4724999) B4724999
theorem B120984839 : Blo 734326 120984839 := bstep (se 1 (by rfl) ⟨90738629, by rfl⟩ : syracuseStep 120984839 = 181477259) B181477259
theorem B9442919 : Blo 734326 9442919 := bstep (se 1 (by rfl) ⟨7082189, by rfl⟩ : syracuseStep 9442919 = 14164379) B14164379
theorem B60466175 : Blo 734326 60466175 := bstep (se 1 (by rfl) ⟨45349631, by rfl⟩ : syracuseStep 60466175 = 90699263) B90699263
theorem B5977481 : Blo 734326 5977481 := bstep (se 2 (by rfl) ⟨2241555, by rfl⟩ : syracuseStep 5977481 = 4483111) B4483111
theorem B14530765 : Blo 734326 14530765 := bstep (se 3 (by rfl) ⟨2724518, by rfl⟩ : syracuseStep 14530765 = 5449037) B5449037
theorem B736415 : Blo 734326 736415 := bstep (se 1 (by rfl) ⟨552311, by rfl⟩ : syracuseStep 736415 = 1104623) B1104623
theorem B736559 : Blo 734326 736559 := bstep (se 1 (by rfl) ⟨552419, by rfl⟩ : syracuseStep 736559 = 1104839) B1104839
theorem B737151 : Blo 734326 737151 := bstep (se 1 (by rfl) ⟨552863, by rfl⟩ : syracuseStep 737151 = 1105727) B1105727
theorem B10600631 : Blo 734326 10600631 := bstep (se 1 (by rfl) ⟨7950473, by rfl⟩ : syracuseStep 10600631 = 15900947) B15900947
theorem B2802671 : Blo 734326 2802671 := bstep (se 1 (by rfl) ⟨2102003, by rfl⟩ : syracuseStep 2802671 = 4204007) B4204007
theorem B1657799 : Blo 734326 1657799 := bstep (se 1 (by rfl) ⟨1243349, by rfl⟩ : syracuseStep 1657799 = 2486699) B2486699
theorem B1658159 : Blo 734326 1658159 := bstep (se 1 (by rfl) ⟨1243619, by rfl⟩ : syracuseStep 1658159 = 2487239) B2487239
theorem B2149715 : Blo 734326 2149715 := bstep (se 1 (by rfl) ⟨1612286, by rfl⟩ : syracuseStep 2149715 = 3224573) B3224573
theorem B3530411 : Blo 734326 3530411 := bstep (se 1 (by rfl) ⟨2647808, by rfl⟩ : syracuseStep 3530411 = 5295617) B5295617
theorem B1106153 : Blo 734326 1106153 := bstep (se 2 (by rfl) ⟨414807, by rfl⟩ : syracuseStep 1106153 = 829615) B829615
theorem B27583355 : Blo 734326 27583355 := bstep (se 1 (by rfl) ⟨20687516, by rfl⟩ : syracuseStep 27583355 = 41375033) B41375033
theorem B14117327 : Blo 734326 14117327 := bstep (se 1 (by rfl) ⟨10587995, by rfl⟩ : syracuseStep 14117327 = 21175991) B21175991
theorem B1436201 : Blo 734326 1436201 := bstep (se 2 (by rfl) ⟨538575, by rfl⟩ : syracuseStep 1436201 = 1077151) B1077151
theorem B1241129 : Blo 734326 1241129 := bstep (se 2 (by rfl) ⟨465423, by rfl⟩ : syracuseStep 1241129 = 930847) B930847
theorem B1241743 : Blo 734326 1241743 := bstep (se 1 (by rfl) ⟨931307, by rfl⟩ : syracuseStep 1241743 = 1862615) B1862615
theorem B2094623 : Blo 734326 2094623 := bstep (se 1 (by rfl) ⟨1570967, by rfl⟩ : syracuseStep 2094623 = 3141935) B3141935
theorem B28343519 : Blo 734326 28343519 := bstep (se 1 (by rfl) ⟨21257639, by rfl⟩ : syracuseStep 28343519 = 42515279) B42515279
theorem B2096923 : Blo 734326 2096923 := bstep (se 1 (by rfl) ⟨1572692, by rfl⟩ : syracuseStep 2096923 = 3145385) B3145385
theorem B1868447 : Blo 734326 1868447 := bstep (se 1 (by rfl) ⟨1401335, by rfl⟩ : syracuseStep 1868447 = 2802671) B2802671
theorem B2360411 : Blo 734326 2360411 := bstep (se 1 (by rfl) ⟨1770308, by rfl⟩ : syracuseStep 2360411 = 3540617) B3540617
theorem B5441231 : Blo 734326 5441231 := bstep (se 1 (by rfl) ⟨4080923, by rfl⟩ : syracuseStep 5441231 = 8161847) B8161847
theorem B2099999 : Blo 734326 2099999 := bstep (se 1 (by rfl) ⟨1574999, by rfl⟩ : syracuseStep 2099999 = 3149999) B3149999
theorem B6295279 : Blo 734326 6295279 := bstep (se 1 (by rfl) ⟨4721459, by rfl⟩ : syracuseStep 6295279 = 9442919) B9442919
theorem B40310783 : Blo 734326 40310783 := bstep (se 1 (by rfl) ⟨30233087, by rfl⟩ : syracuseStep 40310783 = 60466175) B60466175
theorem B9411551 : Blo 734326 9411551 := bstep (se 1 (by rfl) ⟨7058663, by rfl⟩ : syracuseStep 9411551 = 14117327) B14117327
theorem B957467 : Blo 734326 957467 := bstep (se 1 (by rfl) ⟨718100, by rfl⟩ : syracuseStep 957467 = 1436201) B1436201
theorem B827419 : Blo 734326 827419 := bstep (se 1 (by rfl) ⟨620564, by rfl⟩ : syracuseStep 827419 = 1241129) B1241129
theorem B19374353 : Blo 734326 19374353 := bstep (se 2 (by rfl) ⟨7265382, by rfl⟩ : syracuseStep 19374353 = 14530765) B14530765
theorem B2795897 : Blo 734326 2795897 := bstep (se 2 (by rfl) ⟨1048461, by rfl⟩ : syracuseStep 2795897 = 2096923) B2096923
theorem B114601655 : Blo 734326 114601655 := bstep (se 1 (by rfl) ⟨85951241, by rfl⟩ : syracuseStep 114601655 = 171902483) B171902483
theorem B80656559 : Blo 734326 80656559 := bstep (se 1 (by rfl) ⟨60492419, by rfl⟩ : syracuseStep 80656559 = 120984839) B120984839
theorem B15939949 : Blo 734326 15939949 := bstep (se 3 (by rfl) ⟨2988740, by rfl⟩ : syracuseStep 15939949 = 5977481) B5977481
theorem B737435 : Blo 734326 737435 := bstep (se 1 (by rfl) ⟨553076, by rfl⟩ : syracuseStep 737435 = 1106153) B1106153
theorem B1655657 : Blo 734326 1655657 := bstep (se 2 (by rfl) ⟨620871, by rfl⟩ : syracuseStep 1655657 = 1241743) B1241743
theorem B1396415 : Blo 734326 1396415 := bstep (se 1 (by rfl) ⟨1047311, by rfl⟩ : syracuseStep 1396415 = 2094623) B2094623
theorem B18895679 : Blo 734326 18895679 := bstep (se 1 (by rfl) ⟨14171759, by rfl⟩ : syracuseStep 18895679 = 28343519) B28343519
theorem B7067087 : Blo 734326 7067087 := bstep (se 1 (by rfl) ⟨5300315, by rfl⟩ : syracuseStep 7067087 = 10600631) B10600631
theorem B1105199 : Blo 734326 1105199 := bstep (se 1 (by rfl) ⟨828899, by rfl⟩ : syracuseStep 1105199 = 1657799) B1657799
theorem B1105439 : Blo 734326 1105439 := bstep (se 1 (by rfl) ⟨829079, by rfl⟩ : syracuseStep 1105439 = 1658159) B1658159
theorem B1433143 : Blo 734326 1433143 := bstep (se 1 (by rfl) ⟨1074857, by rfl⟩ : syracuseStep 1433143 = 2149715) B2149715
theorem B73555613 : Blo 734326 73555613 := bstep (se 3 (by rfl) ⟨13791677, by rfl⟩ : syracuseStep 73555613 = 27583355) B27583355
theorem B2353607 : Blo 734326 2353607 := bstep (se 1 (by rfl) ⟨1765205, by rfl⟩ : syracuseStep 2353607 = 3530411) B3530411
theorem B1245631 : Blo 734326 1245631 := bstep (se 1 (by rfl) ⟨934223, by rfl⟩ : syracuseStep 1245631 = 1868447) B1868447
theorem B1573607 : Blo 734326 1573607 := bstep (se 1 (by rfl) ⟨1180205, by rfl⟩ : syracuseStep 1573607 = 2360411) B2360411
theorem B26873855 : Blo 734326 26873855 := bstep (se 1 (by rfl) ⟨20155391, by rfl⟩ : syracuseStep 26873855 = 40310783) B40310783
theorem B8393705 : Blo 734326 8393705 := bstep (se 2 (by rfl) ⟨3147639, by rfl⟩ : syracuseStep 8393705 = 6295279) B6295279
theorem B12916235 : Blo 734326 12916235 := bstep (se 1 (by rfl) ⟨9687176, by rfl⟩ : syracuseStep 12916235 = 19374353) B19374353
theorem B7643429 : Blo 734326 7643429 := bstep (se 4 (by rfl) ⟨716571, by rfl⟩ : syracuseStep 7643429 = 1433143) B1433143
theorem B930943 : Blo 734326 930943 := bstep (se 1 (by rfl) ⟨698207, by rfl⟩ : syracuseStep 930943 = 1396415) B1396415
theorem B12597119 : Blo 734326 12597119 := bstep (se 1 (by rfl) ⟨9447839, by rfl⟩ : syracuseStep 12597119 = 18895679) B18895679
theorem B6274367 : Blo 734326 6274367 := bstep (se 1 (by rfl) ⟨4705775, by rfl⟩ : syracuseStep 6274367 = 9411551) B9411551
theorem B736799 : Blo 734326 736799 := bstep (se 1 (by rfl) ⟨552599, by rfl⟩ : syracuseStep 736799 = 1105199) B1105199
theorem B736959 : Blo 734326 736959 := bstep (se 1 (by rfl) ⟨552719, by rfl⟩ : syracuseStep 736959 = 1105439) B1105439
theorem B49037075 : Blo 734326 49037075 := bstep (se 1 (by rfl) ⟨36777806, by rfl⟩ : syracuseStep 49037075 = 73555613) B73555613
theorem B76401103 : Blo 734326 76401103 := bstep (se 1 (by rfl) ⟨57300827, by rfl⟩ : syracuseStep 76401103 = 114601655) B114601655
theorem B21253265 : Blo 734326 21253265 := bstep (se 2 (by rfl) ⟨7969974, by rfl⟩ : syracuseStep 21253265 = 15939949) B15939949
theorem B1103225 : Blo 734326 1103225 := bstep (se 2 (by rfl) ⟨413709, by rfl⟩ : syracuseStep 1103225 = 827419) B827419
theorem B1103771 : Blo 734326 1103771 := bstep (se 1 (by rfl) ⟨827828, by rfl⟩ : syracuseStep 1103771 = 1655657) B1655657
theorem B3627487 : Blo 734326 3627487 := bstep (se 1 (by rfl) ⟨2720615, by rfl⟩ : syracuseStep 3627487 = 5441231) B5441231
theorem B1399999 : Blo 734326 1399999 := bstep (se 1 (by rfl) ⟨1049999, by rfl⟩ : syracuseStep 1399999 = 2099999) B2099999
theorem B4711391 : Blo 734326 4711391 := bstep (se 1 (by rfl) ⟨3533543, by rfl⟩ : syracuseStep 4711391 = 7067087) B7067087
theorem B1863931 : Blo 734326 1863931 := bstep (se 1 (by rfl) ⟨1397948, by rfl⟩ : syracuseStep 1863931 = 2795897) B2795897
theorem B1569071 : Blo 734326 1569071 := bstep (se 1 (by rfl) ⟨1176803, by rfl⟩ : syracuseStep 1569071 = 2353607) B2353607
theorem B2553245 : Blo 734326 2553245 := bstep (se 3 (by rfl) ⟨478733, by rfl⟩ : syracuseStep 2553245 = 957467) B957467
theorem B53771039 : Blo 734326 53771039 := bstep (se 1 (by rfl) ⟨40328279, by rfl⟩ : syracuseStep 53771039 = 80656559) B80656559
theorem B4196285 : Blo 734326 4196285 := bstep (se 3 (by rfl) ⟨786803, by rfl⟩ : syracuseStep 4196285 = 1573607) B1573607
theorem B8398079 : Blo 734326 8398079 := bstep (se 1 (by rfl) ⟨6298559, by rfl⟩ : syracuseStep 8398079 = 12597119) B12597119
theorem B14168843 : Blo 734326 14168843 := bstep (se 1 (by rfl) ⟨10626632, by rfl⟩ : syracuseStep 14168843 = 21253265) B21253265
theorem B19346597 : Blo 734326 19346597 := bstep (se 4 (by rfl) ⟨1813743, by rfl⟩ : syracuseStep 19346597 = 3627487) B3627487
theorem B735483 : Blo 734326 735483 := bstep (se 1 (by rfl) ⟨551612, by rfl⟩ : syracuseStep 735483 = 1103225) B1103225
theorem B735847 : Blo 734326 735847 := bstep (se 1 (by rfl) ⟨551885, by rfl⟩ : syracuseStep 735847 = 1103771) B1103771
theorem B5095619 : Blo 734326 5095619 := bstep (se 1 (by rfl) ⟨3821714, by rfl⟩ : syracuseStep 5095619 = 7643429) B7643429
theorem B4182911 : Blo 734326 4182911 := bstep (se 1 (by rfl) ⟨3137183, by rfl⟩ : syracuseStep 4182911 = 6274367) B6274367
theorem B32691383 : Blo 734326 32691383 := bstep (se 1 (by rfl) ⟨24518537, by rfl⟩ : syracuseStep 32691383 = 49037075) B49037075
theorem B1660841 : Blo 734326 1660841 := bstep (se 2 (by rfl) ⟨622815, by rfl⟩ : syracuseStep 1660841 = 1245631) B1245631
theorem B17915903 : Blo 734326 17915903 := bstep (se 1 (by rfl) ⟨13436927, by rfl⟩ : syracuseStep 17915903 = 26873855) B26873855
theorem B101868137 : Blo 734326 101868137 := bstep (se 2 (by rfl) ⟨38200551, by rfl⟩ : syracuseStep 101868137 = 76401103) B76401103
theorem B5595803 : Blo 734326 5595803 := bstep (se 1 (by rfl) ⟨4196852, by rfl⟩ : syracuseStep 5595803 = 8393705) B8393705
theorem B8610823 : Blo 734326 8610823 := bstep (se 1 (by rfl) ⟨6458117, by rfl⟩ : syracuseStep 8610823 = 12916235) B12916235
theorem B2485241 : Blo 734326 2485241 := bstep (se 2 (by rfl) ⟨931965, by rfl⟩ : syracuseStep 2485241 = 1863931) B1863931
theorem B3140927 : Blo 734326 3140927 := bstep (se 1 (by rfl) ⟨2355695, by rfl⟩ : syracuseStep 3140927 = 4711391) B4711391
theorem B1241257 : Blo 734326 1241257 := bstep (se 2 (by rfl) ⟨465471, by rfl⟩ : syracuseStep 1241257 = 930943) B930943
theorem B1046047 : Blo 734326 1046047 := bstep (se 1 (by rfl) ⟨784535, by rfl⟩ : syracuseStep 1046047 = 1569071) B1569071
theorem B1702163 : Blo 734326 1702163 := bstep (se 1 (by rfl) ⟨1276622, by rfl⟩ : syracuseStep 1702163 = 2553245) B2553245
theorem B1866665 : Blo 734326 1866665 := bstep (se 2 (by rfl) ⟨699999, by rfl⟩ : syracuseStep 1866665 = 1399999) B1399999
theorem B35847359 : Blo 734326 35847359 := bstep (se 1 (by rfl) ⟨26885519, by rfl⟩ : syracuseStep 35847359 = 53771039) B53771039
theorem B2788607 : Blo 734326 2788607 := bstep (se 1 (by rfl) ⟨2091455, by rfl⟩ : syracuseStep 2788607 = 4182911) B4182911
theorem B21794255 : Blo 734326 21794255 := bstep (se 1 (by rfl) ⟨16345691, by rfl⟩ : syracuseStep 21794255 = 32691383) B32691383
theorem B9445895 : Blo 734326 9445895 := bstep (se 1 (by rfl) ⟨7084421, by rfl⟩ : syracuseStep 9445895 = 14168843) B14168843
theorem B23898239 : Blo 734326 23898239 := bstep (se 1 (by rfl) ⟨17923679, by rfl⟩ : syracuseStep 23898239 = 35847359) B35847359
theorem B2797523 : Blo 734326 2797523 := bstep (se 1 (by rfl) ⟨2098142, by rfl⟩ : syracuseStep 2797523 = 4196285) B4196285
theorem B11481097 : Blo 734326 11481097 := bstep (se 2 (by rfl) ⟨4305411, by rfl⟩ : syracuseStep 11481097 = 8610823) B8610823
theorem B11943935 : Blo 734326 11943935 := bstep (se 1 (by rfl) ⟨8957951, by rfl⟩ : syracuseStep 11943935 = 17915903) B17915903
theorem B1655009 : Blo 734326 1655009 := bstep (se 2 (by rfl) ⟨620628, by rfl⟩ : syracuseStep 1655009 = 1241257) B1241257
theorem B67912091 : Blo 734326 67912091 := bstep (se 1 (by rfl) ⟨50934068, by rfl⟩ : syracuseStep 67912091 = 101868137) B101868137
theorem B1656827 : Blo 734326 1656827 := bstep (se 1 (by rfl) ⟨1242620, by rfl⟩ : syracuseStep 1656827 = 2485241) B2485241
theorem B1394729 : Blo 734326 1394729 := bstep (se 2 (by rfl) ⟨523023, by rfl⟩ : syracuseStep 1394729 = 1046047) B1046047
theorem B12897731 : Blo 734326 12897731 := bstep (se 1 (by rfl) ⟨9673298, by rfl⟩ : syracuseStep 12897731 = 19346597) B19346597
theorem B1134775 : Blo 734326 1134775 := bstep (se 1 (by rfl) ⟨851081, by rfl⟩ : syracuseStep 1134775 = 1702163) B1702163
theorem B3397079 : Blo 734326 3397079 := bstep (se 1 (by rfl) ⟨2547809, by rfl⟩ : syracuseStep 3397079 = 5095619) B5095619
theorem B1107227 : Blo 734326 1107227 := bstep (se 1 (by rfl) ⟨830420, by rfl⟩ : syracuseStep 1107227 = 1660841) B1660841
theorem B3730535 : Blo 734326 3730535 := bstep (se 1 (by rfl) ⟨2797901, by rfl⟩ : syracuseStep 3730535 = 5595803) B5595803
theorem B5598719 : Blo 734326 5598719 := bstep (se 1 (by rfl) ⟨4199039, by rfl⟩ : syracuseStep 5598719 = 8398079) B8398079
theorem B2093951 : Blo 734326 2093951 := bstep (se 1 (by rfl) ⟨1570463, by rfl⟩ : syracuseStep 2093951 = 3140927) B3140927
theorem B1244443 : Blo 734326 1244443 := bstep (se 1 (by rfl) ⟨933332, by rfl⟩ : syracuseStep 1244443 = 1866665) B1866665
theorem B2264719 : Blo 734326 2264719 := bstep (se 1 (by rfl) ⟨1698539, by rfl⟩ : syracuseStep 2264719 = 3397079) B3397079
theorem B15308129 : Blo 734326 15308129 := bstep (se 2 (by rfl) ⟨5740548, by rfl⟩ : syracuseStep 15308129 = 11481097) B11481097
theorem B1513033 : Blo 734326 1513033 := bstep (se 2 (by rfl) ⟨567387, by rfl⟩ : syracuseStep 1513033 = 1134775) B1134775
theorem B6297263 : Blo 734326 6297263 := bstep (se 1 (by rfl) ⟨4722947, by rfl⟩ : syracuseStep 6297263 = 9445895) B9445895
theorem B15932159 : Blo 734326 15932159 := bstep (se 1 (by rfl) ⟨11949119, by rfl⟩ : syracuseStep 15932159 = 23898239) B23898239
theorem B929819 : Blo 734326 929819 := bstep (se 1 (by rfl) ⟨697364, by rfl⟩ : syracuseStep 929819 = 1394729) B1394729
theorem B8598487 : Blo 734326 8598487 := bstep (se 1 (by rfl) ⟨6448865, by rfl⟩ : syracuseStep 8598487 = 12897731) B12897731
theorem B14529503 : Blo 734326 14529503 := bstep (se 1 (by rfl) ⟨10897127, by rfl⟩ : syracuseStep 14529503 = 21794255) B21794255
theorem B738151 : Blo 734326 738151 := bstep (se 1 (by rfl) ⟨553613, by rfl⟩ : syracuseStep 738151 = 1107227) B1107227
theorem B7962623 : Blo 734326 7962623 := bstep (se 1 (by rfl) ⟨5971967, by rfl⟩ : syracuseStep 7962623 = 11943935) B11943935
theorem B1395967 : Blo 734326 1395967 := bstep (se 1 (by rfl) ⟨1046975, by rfl⟩ : syracuseStep 1395967 = 2093951) B2093951
theorem B1659257 : Blo 734326 1659257 := bstep (se 2 (by rfl) ⟨622221, by rfl⟩ : syracuseStep 1659257 = 1244443) B1244443
theorem B1103339 : Blo 734326 1103339 := bstep (se 1 (by rfl) ⟨827504, by rfl⟩ : syracuseStep 1103339 = 1655009) B1655009
theorem B45274727 : Blo 734326 45274727 := bstep (se 1 (by rfl) ⟨33956045, by rfl⟩ : syracuseStep 45274727 = 67912091) B67912091
theorem B1104551 : Blo 734326 1104551 := bstep (se 1 (by rfl) ⟨828413, by rfl⟩ : syracuseStep 1104551 = 1656827) B1656827
theorem B1859071 : Blo 734326 1859071 := bstep (se 1 (by rfl) ⟨1394303, by rfl⟩ : syracuseStep 1859071 = 2788607) B2788607
theorem B2487023 : Blo 734326 2487023 := bstep (se 1 (by rfl) ⟨1865267, by rfl⟩ : syracuseStep 2487023 = 3730535) B3730535
theorem B3732479 : Blo 734326 3732479 := bstep (se 1 (by rfl) ⟨2799359, by rfl⟩ : syracuseStep 3732479 = 5598719) B5598719
theorem B1865015 : Blo 734326 1865015 := bstep (se 1 (by rfl) ⟨1398761, by rfl⟩ : syracuseStep 1865015 = 2797523) B2797523
theorem B4198175 : Blo 734326 4198175 := bstep (se 1 (by rfl) ⟨3148631, by rfl⟩ : syracuseStep 4198175 = 6297263) B6297263
theorem B10621439 : Blo 734326 10621439 := bstep (se 1 (by rfl) ⟨7966079, by rfl⟩ : syracuseStep 10621439 = 15932159) B15932159
theorem B3019625 : Blo 734326 3019625 := bstep (se 2 (by rfl) ⟨1132359, by rfl⟩ : syracuseStep 3019625 = 2264719) B2264719
theorem B8069509 : Blo 734326 8069509 := bstep (se 4 (by rfl) ⟨756516, by rfl⟩ : syracuseStep 8069509 = 1513033) B1513033
theorem B38745341 : Blo 734326 38745341 := bstep (se 3 (by rfl) ⟨7264751, by rfl⟩ : syracuseStep 38745341 = 14529503) B14529503
theorem B735559 : Blo 734326 735559 := bstep (se 1 (by rfl) ⟨551669, by rfl⟩ : syracuseStep 735559 = 1103339) B1103339
theorem B120732605 : Blo 734326 120732605 := bstep (se 3 (by rfl) ⟨22637363, by rfl⟩ : syracuseStep 120732605 = 45274727) B45274727
theorem B736367 : Blo 734326 736367 := bstep (se 1 (by rfl) ⟨552275, by rfl⟩ : syracuseStep 736367 = 1104551) B1104551
theorem B1658015 : Blo 734326 1658015 := bstep (se 1 (by rfl) ⟨1243511, by rfl⟩ : syracuseStep 1658015 = 2487023) B2487023
theorem B2478761 : Blo 734326 2478761 := bstep (se 2 (by rfl) ⟨929535, by rfl⟩ : syracuseStep 2478761 = 1859071) B1859071
theorem B2479517 : Blo 734326 2479517 := bstep (se 3 (by rfl) ⟨464909, by rfl⟩ : syracuseStep 2479517 = 929819) B929819
theorem B1106171 : Blo 734326 1106171 := bstep (se 1 (by rfl) ⟨829628, by rfl⟩ : syracuseStep 1106171 = 1659257) B1659257
theorem B40821677 : Blo 734326 40821677 := bstep (se 3 (by rfl) ⟨7654064, by rfl⟩ : syracuseStep 40821677 = 15308129) B15308129
theorem B1861289 : Blo 734326 1861289 := bstep (se 2 (by rfl) ⟨697983, by rfl⟩ : syracuseStep 1861289 = 1395967) B1395967
theorem B11464649 : Blo 734326 11464649 := bstep (se 2 (by rfl) ⟨4299243, by rfl⟩ : syracuseStep 11464649 = 8598487) B8598487
theorem B2488319 : Blo 734326 2488319 := bstep (se 1 (by rfl) ⟨1866239, by rfl⟩ : syracuseStep 2488319 = 3732479) B3732479
theorem B1243343 : Blo 734326 1243343 := bstep (se 1 (by rfl) ⟨932507, by rfl⟩ : syracuseStep 1243343 = 1865015) B1865015
theorem B5308415 : Blo 734326 5308415 := bstep (se 1 (by rfl) ⟨3981311, by rfl⟩ : syracuseStep 5308415 = 7962623) B7962623
theorem B7080959 : Blo 734326 7080959 := bstep (se 1 (by rfl) ⟨5310719, by rfl⟩ : syracuseStep 7080959 = 10621439) B10621439
theorem B7643099 : Blo 734326 7643099 := bstep (se 1 (by rfl) ⟨5732324, by rfl⟩ : syracuseStep 7643099 = 11464649) B11464649
theorem B25830227 : Blo 734326 25830227 := bstep (se 1 (by rfl) ⟨19372670, by rfl⟩ : syracuseStep 25830227 = 38745341) B38745341
theorem B828895 : Blo 734326 828895 := bstep (se 1 (by rfl) ⟨621671, by rfl⟩ : syracuseStep 828895 = 1243343) B1243343
theorem B80488403 : Blo 734326 80488403 := bstep (se 1 (by rfl) ⟨60366302, by rfl⟩ : syracuseStep 80488403 = 120732605) B120732605
theorem B3538943 : Blo 734326 3538943 := bstep (se 1 (by rfl) ⟨2654207, by rfl⟩ : syracuseStep 3538943 = 5308415) B5308415
theorem B43037381 : Blo 734326 43037381 := bstep (se 4 (by rfl) ⟨4034754, by rfl⟩ : syracuseStep 43037381 = 8069509) B8069509
theorem B2798783 : Blo 734326 2798783 := bstep (se 1 (by rfl) ⟨2099087, by rfl⟩ : syracuseStep 2798783 = 4198175) B4198175
theorem B1652507 : Blo 734326 1652507 := bstep (se 1 (by rfl) ⟨1239380, by rfl⟩ : syracuseStep 1652507 = 2478761) B2478761
theorem B2013083 : Blo 734326 2013083 := bstep (se 1 (by rfl) ⟨1509812, by rfl⟩ : syracuseStep 2013083 = 3019625) B3019625
theorem B1653011 : Blo 734326 1653011 := bstep (se 1 (by rfl) ⟨1239758, by rfl⟩ : syracuseStep 1653011 = 2479517) B2479517
theorem B737447 : Blo 734326 737447 := bstep (se 1 (by rfl) ⟨553085, by rfl⟩ : syracuseStep 737447 = 1106171) B1106171
theorem B27214451 : Blo 734326 27214451 := bstep (se 1 (by rfl) ⟨20410838, by rfl⟩ : syracuseStep 27214451 = 40821677) B40821677
theorem B1658879 : Blo 734326 1658879 := bstep (se 1 (by rfl) ⟨1244159, by rfl⟩ : syracuseStep 1658879 = 2488319) B2488319
theorem B1105343 : Blo 734326 1105343 := bstep (se 1 (by rfl) ⟨829007, by rfl⟩ : syracuseStep 1105343 = 1658015) B1658015
theorem B1240859 : Blo 734326 1240859 := bstep (se 1 (by rfl) ⟨930644, by rfl⟩ : syracuseStep 1240859 = 1861289) B1861289
theorem B827239 : Blo 734326 827239 := bstep (se 1 (by rfl) ⟨620429, by rfl⟩ : syracuseStep 827239 = 1240859) B1240859
theorem B2359295 : Blo 734326 2359295 := bstep (se 1 (by rfl) ⟨1769471, by rfl⟩ : syracuseStep 2359295 = 3538943) B3538943
theorem B18882557 : Blo 734326 18882557 := bstep (se 3 (by rfl) ⟨3540479, by rfl⟩ : syracuseStep 18882557 = 7080959) B7080959
theorem B736895 : Blo 734326 736895 := bstep (se 1 (by rfl) ⟨552671, by rfl⟩ : syracuseStep 736895 = 1105343) B1105343
theorem B5095399 : Blo 734326 5095399 := bstep (se 1 (by rfl) ⟨3821549, by rfl⟩ : syracuseStep 5095399 = 7643099) B7643099
theorem B17220151 : Blo 734326 17220151 := bstep (se 1 (by rfl) ⟨12915113, by rfl⟩ : syracuseStep 17220151 = 25830227) B25830227
theorem B53658935 : Blo 734326 53658935 := bstep (se 1 (by rfl) ⟨40244201, by rfl⟩ : syracuseStep 53658935 = 80488403) B80488403
theorem B28691587 : Blo 734326 28691587 := bstep (se 1 (by rfl) ⟨21518690, by rfl⟩ : syracuseStep 28691587 = 43037381) B43037381
theorem B1101671 : Blo 734326 1101671 := bstep (se 1 (by rfl) ⟨826253, by rfl⟩ : syracuseStep 1101671 = 1652507) B1652507
theorem B1102007 : Blo 734326 1102007 := bstep (se 1 (by rfl) ⟨826505, by rfl⟩ : syracuseStep 1102007 = 1653011) B1653011
theorem B18142967 : Blo 734326 18142967 := bstep (se 1 (by rfl) ⟨13607225, by rfl⟩ : syracuseStep 18142967 = 27214451) B27214451
theorem B1105193 : Blo 734326 1105193 := bstep (se 2 (by rfl) ⟨414447, by rfl⟩ : syracuseStep 1105193 = 828895) B828895
theorem B1105919 : Blo 734326 1105919 := bstep (se 1 (by rfl) ⟨829439, by rfl⟩ : syracuseStep 1105919 = 1658879) B1658879
theorem B1865855 : Blo 734326 1865855 := bstep (se 1 (by rfl) ⟨1399391, by rfl⟩ : syracuseStep 1865855 = 2798783) B2798783
theorem B1342055 : Blo 734326 1342055 := bstep (se 1 (by rfl) ⟨1006541, by rfl⟩ : syracuseStep 1342055 = 2013083) B2013083
theorem B12588371 : Blo 734326 12588371 := bstep (se 1 (by rfl) ⟨9441278, by rfl⟩ : syracuseStep 12588371 = 18882557) B18882557
theorem B3578813 : Blo 734326 3578813 := bstep (se 3 (by rfl) ⟨671027, by rfl⟩ : syracuseStep 3578813 = 1342055) B1342055
theorem B6793865 : Blo 734326 6793865 := bstep (se 2 (by rfl) ⟨2547699, by rfl⟩ : syracuseStep 6793865 = 5095399) B5095399
theorem B734447 : Blo 734326 734447 := bstep (se 1 (by rfl) ⟨550835, by rfl⟩ : syracuseStep 734447 = 1101671) B1101671
theorem B734671 : Blo 734326 734671 := bstep (se 1 (by rfl) ⟨551003, by rfl⟩ : syracuseStep 734671 = 1102007) B1102007
theorem B38255449 : Blo 734326 38255449 := bstep (se 2 (by rfl) ⟨14345793, by rfl⟩ : syracuseStep 38255449 = 28691587) B28691587
theorem B48381245 : Blo 734326 48381245 := bstep (se 3 (by rfl) ⟨9071483, by rfl⟩ : syracuseStep 48381245 = 18142967) B18142967
theorem B736795 : Blo 734326 736795 := bstep (se 1 (by rfl) ⟨552596, by rfl⟩ : syracuseStep 736795 = 1105193) B1105193
theorem B1572863 : Blo 734326 1572863 := bstep (se 1 (by rfl) ⟨1179647, by rfl⟩ : syracuseStep 1572863 = 2359295) B2359295
theorem B737279 : Blo 734326 737279 := bstep (se 1 (by rfl) ⟨552959, by rfl⟩ : syracuseStep 737279 = 1105919) B1105919
theorem B1102985 : Blo 734326 1102985 := bstep (se 2 (by rfl) ⟨413619, by rfl⟩ : syracuseStep 1102985 = 827239) B827239
theorem B22960201 : Blo 734326 22960201 := bstep (se 2 (by rfl) ⟨8610075, by rfl⟩ : syracuseStep 22960201 = 17220151) B17220151
theorem B35772623 : Blo 734326 35772623 := bstep (se 1 (by rfl) ⟨26829467, by rfl⟩ : syracuseStep 35772623 = 53658935) B53658935
theorem B1243903 : Blo 734326 1243903 := bstep (se 1 (by rfl) ⟨932927, by rfl⟩ : syracuseStep 1243903 = 1865855) B1865855
theorem B8392247 : Blo 734326 8392247 := bstep (se 1 (by rfl) ⟨6294185, by rfl⟩ : syracuseStep 8392247 = 12588371) B12588371
theorem B4529243 : Blo 734326 4529243 := bstep (se 1 (by rfl) ⟨3396932, by rfl⟩ : syracuseStep 4529243 = 6793865) B6793865
theorem B30613601 : Blo 734326 30613601 := bstep (se 2 (by rfl) ⟨11480100, by rfl⟩ : syracuseStep 30613601 = 22960201) B22960201
theorem B32254163 : Blo 734326 32254163 := bstep (se 1 (by rfl) ⟨24190622, by rfl⟩ : syracuseStep 32254163 = 48381245) B48381245
theorem B735323 : Blo 734326 735323 := bstep (se 1 (by rfl) ⟨551492, by rfl⟩ : syracuseStep 735323 = 1102985) B1102985
theorem B1658537 : Blo 734326 1658537 := bstep (se 2 (by rfl) ⟨621951, by rfl⟩ : syracuseStep 1658537 = 1243903) B1243903
theorem B51007265 : Blo 734326 51007265 := bstep (se 2 (by rfl) ⟨19127724, by rfl⟩ : syracuseStep 51007265 = 38255449) B38255449
theorem B23848415 : Blo 734326 23848415 := bstep (se 1 (by rfl) ⟨17886311, by rfl⟩ : syracuseStep 23848415 = 35772623) B35772623
theorem B2385875 : Blo 734326 2385875 := bstep (se 1 (by rfl) ⟨1789406, by rfl⟩ : syracuseStep 2385875 = 3578813) B3578813
theorem B4194301 : Blo 734326 4194301 := bstep (se 3 (by rfl) ⟨786431, by rfl⟩ : syracuseStep 4194301 = 1572863) B1572863
theorem B6362333 : Blo 734326 6362333 := bstep (se 3 (by rfl) ⟨1192937, by rfl⟩ : syracuseStep 6362333 = 2385875) B2385875
theorem B15898943 : Blo 734326 15898943 := bstep (se 1 (by rfl) ⟨11924207, by rfl⟩ : syracuseStep 15898943 = 23848415) B23848415
theorem B21502775 : Blo 734326 21502775 := bstep (se 1 (by rfl) ⟨16127081, by rfl⟩ : syracuseStep 21502775 = 32254163) B32254163
theorem B12077981 : Blo 734326 12077981 := bstep (se 3 (by rfl) ⟨2264621, by rfl⟩ : syracuseStep 12077981 = 4529243) B4529243
theorem B5592401 : Blo 734326 5592401 := bstep (se 2 (by rfl) ⟨2097150, by rfl⟩ : syracuseStep 5592401 = 4194301) B4194301
theorem B5594831 : Blo 734326 5594831 := bstep (se 1 (by rfl) ⟨4196123, by rfl⟩ : syracuseStep 5594831 = 8392247) B8392247
theorem B1105691 : Blo 734326 1105691 := bstep (se 1 (by rfl) ⟨829268, by rfl⟩ : syracuseStep 1105691 = 1658537) B1658537
theorem B34004843 : Blo 734326 34004843 := bstep (se 1 (by rfl) ⟨25503632, by rfl⟩ : syracuseStep 34004843 = 51007265) B51007265
theorem B20409067 : Blo 734326 20409067 := bstep (se 1 (by rfl) ⟨15306800, by rfl⟩ : syracuseStep 20409067 = 30613601) B30613601
theorem B4241555 : Blo 734326 4241555 := bstep (se 1 (by rfl) ⟨3181166, by rfl⟩ : syracuseStep 4241555 = 6362333) B6362333
theorem B14335183 : Blo 734326 14335183 := bstep (se 1 (by rfl) ⟨10751387, by rfl⟩ : syracuseStep 14335183 = 21502775) B21502775
theorem B737127 : Blo 734326 737127 := bstep (se 1 (by rfl) ⟨552845, by rfl⟩ : syracuseStep 737127 = 1105691) B1105691
theorem B8051987 : Blo 734326 8051987 := bstep (se 1 (by rfl) ⟨6038990, by rfl⟩ : syracuseStep 8051987 = 12077981) B12077981
theorem B3728267 : Blo 734326 3728267 := bstep (se 1 (by rfl) ⟨2796200, by rfl⟩ : syracuseStep 3728267 = 5592401) B5592401
theorem B108848357 : Blo 734326 108848357 := bstep (se 4 (by rfl) ⟨10204533, by rfl⟩ : syracuseStep 108848357 = 20409067) B20409067
theorem B3729887 : Blo 734326 3729887 := bstep (se 1 (by rfl) ⟨2797415, by rfl⟩ : syracuseStep 3729887 = 5594831) B5594831
theorem B22669895 : Blo 734326 22669895 := bstep (se 1 (by rfl) ⟨17002421, by rfl⟩ : syracuseStep 22669895 = 34004843) B34004843
theorem B42397181 : Blo 734326 42397181 := bstep (se 3 (by rfl) ⟨7949471, by rfl⟩ : syracuseStep 42397181 = 15898943) B15898943
theorem B15113263 : Blo 734326 15113263 := bstep (se 1 (by rfl) ⟨11334947, by rfl⟩ : syracuseStep 15113263 = 22669895) B22669895
theorem B2827703 : Blo 734326 2827703 := bstep (se 1 (by rfl) ⟨2120777, by rfl⟩ : syracuseStep 2827703 = 4241555) B4241555
theorem B19113577 : Blo 734326 19113577 := bstep (se 2 (by rfl) ⟨7167591, by rfl⟩ : syracuseStep 19113577 = 14335183) B14335183
theorem B72565571 : Blo 734326 72565571 := bstep (se 1 (by rfl) ⟨54424178, by rfl⟩ : syracuseStep 72565571 = 108848357) B108848357
theorem B28264787 : Blo 734326 28264787 := bstep (se 1 (by rfl) ⟨21198590, by rfl⟩ : syracuseStep 28264787 = 42397181) B42397181
theorem B5367991 : Blo 734326 5367991 := bstep (se 1 (by rfl) ⟨4025993, by rfl⟩ : syracuseStep 5367991 = 8051987) B8051987
theorem B2485511 : Blo 734326 2485511 := bstep (se 1 (by rfl) ⟨1864133, by rfl⟩ : syracuseStep 2485511 = 3728267) B3728267
theorem B2486591 : Blo 734326 2486591 := bstep (se 1 (by rfl) ⟨1864943, by rfl⟩ : syracuseStep 2486591 = 3729887) B3729887
theorem B18843191 : Blo 734326 18843191 := bstep (se 1 (by rfl) ⟨14132393, by rfl⟩ : syracuseStep 18843191 = 28264787) B28264787
theorem B193508189 : Blo 734326 193508189 := bstep (se 3 (by rfl) ⟨36282785, by rfl⟩ : syracuseStep 193508189 = 72565571) B72565571
theorem B7157321 : Blo 734326 7157321 := bstep (se 2 (by rfl) ⟨2683995, by rfl⟩ : syracuseStep 7157321 = 5367991) B5367991
theorem B1885135 : Blo 734326 1885135 := bstep (se 1 (by rfl) ⟨1413851, by rfl⟩ : syracuseStep 1885135 = 2827703) B2827703
theorem B1657007 : Blo 734326 1657007 := bstep (se 1 (by rfl) ⟨1242755, by rfl⟩ : syracuseStep 1657007 = 2485511) B2485511
theorem B1657727 : Blo 734326 1657727 := bstep (se 1 (by rfl) ⟨1243295, by rfl⟩ : syracuseStep 1657727 = 2486591) B2486591
theorem B101939077 : Blo 734326 101939077 := bstep (se 4 (by rfl) ⟨9556788, by rfl⟩ : syracuseStep 101939077 = 19113577) B19113577
theorem B20151017 : Blo 734326 20151017 := bstep (se 2 (by rfl) ⟨7556631, by rfl⟩ : syracuseStep 20151017 = 15113263) B15113263
theorem B12562127 : Blo 734326 12562127 := bstep (se 1 (by rfl) ⟨9421595, by rfl⟩ : syracuseStep 12562127 = 18843191) B18843191
theorem B4771547 : Blo 734326 4771547 := bstep (se 1 (by rfl) ⟨3578660, by rfl⟩ : syracuseStep 4771547 = 7157321) B7157321
theorem B2513513 : Blo 734326 2513513 := bstep (se 2 (by rfl) ⟨942567, by rfl⟩ : syracuseStep 2513513 = 1885135) B1885135
theorem B1104671 : Blo 734326 1104671 := bstep (se 1 (by rfl) ⟨828503, by rfl⟩ : syracuseStep 1104671 = 1657007) B1657007
theorem B1105151 : Blo 734326 1105151 := bstep (se 1 (by rfl) ⟨828863, by rfl⟩ : syracuseStep 1105151 = 1657727) B1657727
theorem B135918769 : Blo 734326 135918769 := bstep (se 2 (by rfl) ⟨50969538, by rfl⟩ : syracuseStep 135918769 = 101939077) B101939077
theorem B129005459 : Blo 734326 129005459 := bstep (se 1 (by rfl) ⟨96754094, by rfl⟩ : syracuseStep 129005459 = 193508189) B193508189
theorem B13434011 : Blo 734326 13434011 := bstep (se 1 (by rfl) ⟨10075508, by rfl⟩ : syracuseStep 13434011 = 20151017) B20151017
theorem B3181031 : Blo 734326 3181031 := bstep (se 1 (by rfl) ⟨2385773, by rfl⟩ : syracuseStep 3181031 = 4771547) B4771547
theorem B1675675 : Blo 734326 1675675 := bstep (se 1 (by rfl) ⟨1256756, by rfl⟩ : syracuseStep 1675675 = 2513513) B2513513
theorem B8956007 : Blo 734326 8956007 := bstep (se 1 (by rfl) ⟨6717005, by rfl⟩ : syracuseStep 8956007 = 13434011) B13434011
theorem B736447 : Blo 734326 736447 := bstep (se 1 (by rfl) ⟨552335, by rfl⟩ : syracuseStep 736447 = 1104671) B1104671
theorem B736767 : Blo 734326 736767 := bstep (se 1 (by rfl) ⟨552575, by rfl⟩ : syracuseStep 736767 = 1105151) B1105151
theorem B181225025 : Blo 734326 181225025 := bstep (se 2 (by rfl) ⟨67959384, by rfl⟩ : syracuseStep 181225025 = 135918769) B135918769
theorem B8374751 : Blo 734326 8374751 := bstep (se 1 (by rfl) ⟨6281063, by rfl⟩ : syracuseStep 8374751 = 12562127) B12562127
theorem B86003639 : Blo 734326 86003639 := bstep (se 1 (by rfl) ⟨64502729, by rfl⟩ : syracuseStep 86003639 = 129005459) B129005459
theorem B120816683 : Blo 734326 120816683 := bstep (se 1 (by rfl) ⟨90612512, by rfl⟩ : syracuseStep 120816683 = 181225025) B181225025
theorem B2234233 : Blo 734326 2234233 := bstep (se 2 (by rfl) ⟨837837, by rfl⟩ : syracuseStep 2234233 = 1675675) B1675675
theorem B5970671 : Blo 734326 5970671 := bstep (se 1 (by rfl) ⟨4478003, by rfl⟩ : syracuseStep 5970671 = 8956007) B8956007
theorem B5583167 : Blo 734326 5583167 := bstep (se 1 (by rfl) ⟨4187375, by rfl⟩ : syracuseStep 5583167 = 8374751) B8374751
theorem B2120687 : Blo 734326 2120687 := bstep (se 1 (by rfl) ⟨1590515, by rfl⟩ : syracuseStep 2120687 = 3181031) B3181031
theorem B57335759 : Blo 734326 57335759 := bstep (se 1 (by rfl) ⟨43001819, by rfl⟩ : syracuseStep 57335759 = 86003639) B86003639
theorem B80544455 : Blo 734326 80544455 := bstep (se 1 (by rfl) ⟨60408341, by rfl⟩ : syracuseStep 80544455 = 120816683) B120816683
theorem B1413791 : Blo 734326 1413791 := bstep (se 1 (by rfl) ⟨1060343, by rfl⟩ : syracuseStep 1413791 = 2120687) B2120687
theorem B3980447 : Blo 734326 3980447 := bstep (se 1 (by rfl) ⟨2985335, by rfl⟩ : syracuseStep 3980447 = 5970671) B5970671
theorem B38223839 : Blo 734326 38223839 := bstep (se 1 (by rfl) ⟨28667879, by rfl⟩ : syracuseStep 38223839 = 57335759) B57335759
theorem B3722111 : Blo 734326 3722111 := bstep (se 1 (by rfl) ⟨2791583, by rfl⟩ : syracuseStep 3722111 = 5583167) B5583167
theorem B2978977 : Blo 734326 2978977 := bstep (se 2 (by rfl) ⟨1117116, by rfl⟩ : syracuseStep 2978977 = 2234233) B2234233
theorem B3971969 : Blo 734326 3971969 := bstep (se 2 (by rfl) ⟨1489488, by rfl⟩ : syracuseStep 3971969 = 2978977) B2978977
theorem B25482559 : Blo 734326 25482559 := bstep (se 1 (by rfl) ⟨19111919, by rfl⟩ : syracuseStep 25482559 = 38223839) B38223839
theorem B53696303 : Blo 734326 53696303 := bstep (se 1 (by rfl) ⟨40272227, by rfl⟩ : syracuseStep 53696303 = 80544455) B80544455
theorem B2481407 : Blo 734326 2481407 := bstep (se 1 (by rfl) ⟨1861055, by rfl⟩ : syracuseStep 2481407 = 3722111) B3722111
theorem B942527 : Blo 734326 942527 := bstep (se 1 (by rfl) ⟨706895, by rfl⟩ : syracuseStep 942527 = 1413791) B1413791
theorem B2653631 : Blo 734326 2653631 := bstep (se 1 (by rfl) ⟨1990223, by rfl⟩ : syracuseStep 2653631 = 3980447) B3980447
theorem B35797535 : Blo 734326 35797535 := bstep (se 1 (by rfl) ⟨26848151, by rfl⟩ : syracuseStep 35797535 = 53696303) B53696303
theorem B1654271 : Blo 734326 1654271 := bstep (se 1 (by rfl) ⟨1240703, by rfl⟩ : syracuseStep 1654271 = 2481407) B2481407
theorem B2513405 : Blo 734326 2513405 := bstep (se 3 (by rfl) ⟨471263, by rfl⟩ : syracuseStep 2513405 = 942527) B942527
theorem B2647979 : Blo 734326 2647979 := bstep (se 1 (by rfl) ⟨1985984, by rfl⟩ : syracuseStep 2647979 = 3971969) B3971969
theorem B33976745 : Blo 734326 33976745 := bstep (se 2 (by rfl) ⟨12741279, by rfl⟩ : syracuseStep 33976745 = 25482559) B25482559
theorem B1769087 : Blo 734326 1769087 := bstep (se 1 (by rfl) ⟨1326815, by rfl⟩ : syracuseStep 1769087 = 2653631) B2653631
theorem B1675603 : Blo 734326 1675603 := bstep (se 1 (by rfl) ⟨1256702, by rfl⟩ : syracuseStep 1675603 = 2513405) B2513405
theorem B22651163 : Blo 734326 22651163 := bstep (se 1 (by rfl) ⟨16988372, by rfl⟩ : syracuseStep 22651163 = 33976745) B33976745
theorem B23865023 : Blo 734326 23865023 := bstep (se 1 (by rfl) ⟨17898767, by rfl⟩ : syracuseStep 23865023 = 35797535) B35797535
theorem B1102847 : Blo 734326 1102847 := bstep (se 1 (by rfl) ⟨827135, by rfl⟩ : syracuseStep 1102847 = 1654271) B1654271
theorem B1765319 : Blo 734326 1765319 := bstep (se 1 (by rfl) ⟨1323989, by rfl⟩ : syracuseStep 1765319 = 2647979) B2647979
theorem B4717565 : Blo 734326 4717565 := bstep (se 3 (by rfl) ⟨884543, by rfl⟩ : syracuseStep 4717565 = 1769087) B1769087
theorem B2234137 : Blo 734326 2234137 := bstep (se 2 (by rfl) ⟨837801, by rfl⟩ : syracuseStep 2234137 = 1675603) B1675603
theorem B735231 : Blo 734326 735231 := bstep (se 1 (by rfl) ⟨551423, by rfl⟩ : syracuseStep 735231 = 1102847) B1102847
theorem B15910015 : Blo 734326 15910015 := bstep (se 1 (by rfl) ⟨11932511, by rfl⟩ : syracuseStep 15910015 = 23865023) B23865023
theorem B18830069 : Blo 734326 18830069 := bstep (se 5 (by rfl) ⟨882659, by rfl⟩ : syracuseStep 18830069 = 1765319) B1765319
theorem B15100775 : Blo 734326 15100775 := bstep (se 1 (by rfl) ⟨11325581, by rfl⟩ : syracuseStep 15100775 = 22651163) B22651163
theorem B3145043 : Blo 734326 3145043 := bstep (se 1 (by rfl) ⟨2358782, by rfl⟩ : syracuseStep 3145043 = 4717565) B4717565
theorem B12553379 : Blo 734326 12553379 := bstep (se 1 (by rfl) ⟨9415034, by rfl⟩ : syracuseStep 12553379 = 18830069) B18830069
theorem B10067183 : Blo 734326 10067183 := bstep (se 1 (by rfl) ⟨7550387, by rfl⟩ : syracuseStep 10067183 = 15100775) B15100775
theorem B21213353 : Blo 734326 21213353 := bstep (se 2 (by rfl) ⟨7955007, by rfl⟩ : syracuseStep 21213353 = 15910015) B15910015
theorem B2978849 : Blo 734326 2978849 := bstep (se 2 (by rfl) ⟨1117068, by rfl⟩ : syracuseStep 2978849 = 2234137) B2234137
theorem B2096695 : Blo 734326 2096695 := bstep (se 1 (by rfl) ⟨1572521, by rfl⟩ : syracuseStep 2096695 = 3145043) B3145043
theorem B2795593 : Blo 734326 2795593 := bstep (se 2 (by rfl) ⟨1048347, by rfl⟩ : syracuseStep 2795593 = 2096695) B2096695
theorem B8368919 : Blo 734326 8368919 := bstep (se 1 (by rfl) ⟨6276689, by rfl⟩ : syracuseStep 8368919 = 12553379) B12553379
theorem B14142235 : Blo 734326 14142235 := bstep (se 1 (by rfl) ⟨10606676, by rfl⟩ : syracuseStep 14142235 = 21213353) B21213353
theorem B1985899 : Blo 734326 1985899 := bstep (se 1 (by rfl) ⟨1489424, by rfl⟩ : syracuseStep 1985899 = 2978849) B2978849
theorem B6711455 : Blo 734326 6711455 := bstep (se 1 (by rfl) ⟨5033591, by rfl⟩ : syracuseStep 6711455 = 10067183) B10067183
theorem B17897213 : Blo 734326 17897213 := bstep (se 3 (by rfl) ⟨3355727, by rfl⟩ : syracuseStep 17897213 = 6711455) B6711455
theorem B5579279 : Blo 734326 5579279 := bstep (se 1 (by rfl) ⟨4184459, by rfl⟩ : syracuseStep 5579279 = 8368919) B8368919
theorem B18856313 : Blo 734326 18856313 := bstep (se 2 (by rfl) ⟨7071117, by rfl⟩ : syracuseStep 18856313 = 14142235) B14142235
theorem B3727457 : Blo 734326 3727457 := bstep (se 2 (by rfl) ⟨1397796, by rfl⟩ : syracuseStep 3727457 = 2795593) B2795593
theorem B2647865 : Blo 734326 2647865 := bstep (se 2 (by rfl) ⟨992949, by rfl⟩ : syracuseStep 2647865 = 1985899) B1985899
theorem B11931475 : Blo 734326 11931475 := bstep (se 1 (by rfl) ⟨8948606, by rfl⟩ : syracuseStep 11931475 = 17897213) B17897213
theorem B3719519 : Blo 734326 3719519 := bstep (se 1 (by rfl) ⟨2789639, by rfl⟩ : syracuseStep 3719519 = 5579279) B5579279
theorem B12570875 : Blo 734326 12570875 := bstep (se 1 (by rfl) ⟨9428156, by rfl⟩ : syracuseStep 12570875 = 18856313) B18856313
theorem B2484971 : Blo 734326 2484971 := bstep (se 1 (by rfl) ⟨1863728, by rfl⟩ : syracuseStep 2484971 = 3727457) B3727457
theorem B1765243 : Blo 734326 1765243 := bstep (se 1 (by rfl) ⟨1323932, by rfl⟩ : syracuseStep 1765243 = 2647865) B2647865
theorem B15908633 : Blo 734326 15908633 := bstep (se 2 (by rfl) ⟨5965737, by rfl⟩ : syracuseStep 15908633 = 11931475) B11931475
theorem B1656647 : Blo 734326 1656647 := bstep (se 1 (by rfl) ⟨1242485, by rfl⟩ : syracuseStep 1656647 = 2484971) B2484971
theorem B2479679 : Blo 734326 2479679 := bstep (se 1 (by rfl) ⟨1859759, by rfl⟩ : syracuseStep 2479679 = 3719519) B3719519
theorem B8380583 : Blo 734326 8380583 := bstep (se 1 (by rfl) ⟨6285437, by rfl⟩ : syracuseStep 8380583 = 12570875) B12570875
theorem B2353657 : Blo 734326 2353657 := bstep (se 2 (by rfl) ⟨882621, by rfl⟩ : syracuseStep 2353657 = 1765243) B1765243
theorem B1653119 : Blo 734326 1653119 := bstep (se 1 (by rfl) ⟨1239839, by rfl⟩ : syracuseStep 1653119 = 2479679) B2479679
theorem B5587055 : Blo 734326 5587055 := bstep (se 1 (by rfl) ⟨4190291, by rfl⟩ : syracuseStep 5587055 = 8380583) B8380583
theorem B10605755 : Blo 734326 10605755 := bstep (se 1 (by rfl) ⟨7954316, by rfl⟩ : syracuseStep 10605755 = 15908633) B15908633
theorem B1104431 : Blo 734326 1104431 := bstep (se 1 (by rfl) ⟨828323, by rfl⟩ : syracuseStep 1104431 = 1656647) B1656647
theorem B3138209 : Blo 734326 3138209 := bstep (se 2 (by rfl) ⟨1176828, by rfl⟩ : syracuseStep 3138209 = 2353657) B2353657
theorem B736287 : Blo 734326 736287 := bstep (se 1 (by rfl) ⟨552215, by rfl⟩ : syracuseStep 736287 = 1104431) B1104431
theorem B1102079 : Blo 734326 1102079 := bstep (se 1 (by rfl) ⟨826559, by rfl⟩ : syracuseStep 1102079 = 1653119) B1653119
theorem B3724703 : Blo 734326 3724703 := bstep (se 1 (by rfl) ⟨2793527, by rfl⟩ : syracuseStep 3724703 = 5587055) B5587055
theorem B7070503 : Blo 734326 7070503 := bstep (se 1 (by rfl) ⟨5302877, by rfl⟩ : syracuseStep 7070503 = 10605755) B10605755
theorem B2092139 : Blo 734326 2092139 := bstep (se 1 (by rfl) ⟨1569104, by rfl⟩ : syracuseStep 2092139 = 3138209) B3138209
theorem B734719 : Blo 734326 734719 := bstep (se 1 (by rfl) ⟨551039, by rfl⟩ : syracuseStep 734719 = 1102079) B1102079
theorem B1394759 : Blo 734326 1394759 := bstep (se 1 (by rfl) ⟨1046069, by rfl⟩ : syracuseStep 1394759 = 2092139) B2092139
theorem B9427337 : Blo 734326 9427337 := bstep (se 2 (by rfl) ⟨3535251, by rfl⟩ : syracuseStep 9427337 = 7070503) B7070503
theorem B2483135 : Blo 734326 2483135 := bstep (se 1 (by rfl) ⟨1862351, by rfl⟩ : syracuseStep 2483135 = 3724703) B3724703
theorem B3719357 : Blo 734326 3719357 := bstep (se 3 (by rfl) ⟨697379, by rfl⟩ : syracuseStep 3719357 = 1394759) B1394759
theorem B1655423 : Blo 734326 1655423 := bstep (se 1 (by rfl) ⟨1241567, by rfl⟩ : syracuseStep 1655423 = 2483135) B2483135
theorem B6284891 : Blo 734326 6284891 := bstep (se 1 (by rfl) ⟨4713668, by rfl⟩ : syracuseStep 6284891 = 9427337) B9427337
theorem B2479571 : Blo 734326 2479571 := bstep (se 1 (by rfl) ⟨1859678, by rfl⟩ : syracuseStep 2479571 = 3719357) B3719357
theorem B1103615 : Blo 734326 1103615 := bstep (se 1 (by rfl) ⟨827711, by rfl⟩ : syracuseStep 1103615 = 1655423) B1655423
theorem B4189927 : Blo 734326 4189927 := bstep (se 1 (by rfl) ⟨3142445, by rfl⟩ : syracuseStep 4189927 = 6284891) B6284891
theorem B1653047 : Blo 734326 1653047 := bstep (se 1 (by rfl) ⟨1239785, by rfl⟩ : syracuseStep 1653047 = 2479571) B2479571
theorem B735743 : Blo 734326 735743 := bstep (se 1 (by rfl) ⟨551807, by rfl⟩ : syracuseStep 735743 = 1103615) B1103615
theorem B5586569 : Blo 734326 5586569 := bstep (se 2 (by rfl) ⟨2094963, by rfl⟩ : syracuseStep 5586569 = 4189927) B4189927
theorem B1102031 : Blo 734326 1102031 := bstep (se 1 (by rfl) ⟨826523, by rfl⟩ : syracuseStep 1102031 = 1653047) B1653047
theorem B3724379 : Blo 734326 3724379 := bstep (se 1 (by rfl) ⟨2793284, by rfl⟩ : syracuseStep 3724379 = 5586569) B5586569
theorem B734687 : Blo 734326 734687 := bstep (se 1 (by rfl) ⟨551015, by rfl⟩ : syracuseStep 734687 = 1102031) B1102031
theorem B2482919 : Blo 734326 2482919 := bstep (se 1 (by rfl) ⟨1862189, by rfl⟩ : syracuseStep 2482919 = 3724379) B3724379
theorem B1655279 : Blo 734326 1655279 := bstep (se 1 (by rfl) ⟨1241459, by rfl⟩ : syracuseStep 1655279 = 2482919) B2482919
theorem B1103519 : Blo 734326 1103519 := bstep (se 1 (by rfl) ⟨827639, by rfl⟩ : syracuseStep 1103519 = 1655279) B1655279
theorem B735679 : Blo 734326 735679 := bstep (se 1 (by rfl) ⟨551759, by rfl⟩ : syracuseStep 735679 = 1103519) B1103519

theorem C0 (j : ℕ) (h1 : 183581 ≤ j) (h2 : j ≤ 184280) : Blo 734326 (4 * j + 3) := by
  interval_cases j
  · exact B734327
  · exact B734331
  · exact B734335
  · exact B734339
  · exact B734343
  · exact B734347
  · exact B734351
  · exact B734355
  · exact B734359
  · exact B734363
  · exact B734367
  · exact B734371
  · exact B734375
  · exact B734379
  · exact B734383
  · exact B734387
  · exact B734391
  · exact B734395
  · exact B734399
  · exact B734403
  · exact B734407
  · exact B734411
  · exact B734415
  · exact B734419
  · exact B734423
  · exact B734427
  · exact B734431
  · exact B734435
  · exact B734439
  · exact B734443
  · exact B734447
  · exact B734451
  · exact B734455
  · exact B734459
  · exact B734463
  · exact B734467
  · exact B734471
  · exact B734475
  · exact B734479
  · exact B734483
  · exact B734487
  · exact B734491
  · exact B734495
  · exact B734499
  · exact B734503
  · exact B734507
  · exact B734511
  · exact B734515
  · exact B734519
  · exact B734523
  · exact B734527
  · exact B734531
  · exact B734535
  · exact B734539
  · exact B734543
  · exact B734547
  · exact B734551
  · exact B734555
  · exact B734559
  · exact B734563
  · exact B734567
  · exact B734571
  · exact B734575
  · exact B734579
  · exact B734583
  · exact B734587
  · exact B734591
  · exact B734595
  · exact B734599
  · exact B734603
  · exact B734607
  · exact B734611
  · exact B734615
  · exact B734619
  · exact B734623
  · exact B734627
  · exact B734631
  · exact B734635
  · exact B734639
  · exact B734643
  · exact B734647
  · exact B734651
  · exact B734655
  · exact B734659
  · exact B734663
  · exact B734667
  · exact B734671
  · exact B734675
  · exact B734679
  · exact B734683
  · exact B734687
  · exact B734691
  · exact B734695
  · exact B734699
  · exact B734703
  · exact B734707
  · exact B734711
  · exact B734715
  · exact B734719
  · exact B734723
  · exact B734727
  · exact B734731
  · exact B734735
  · exact B734739
  · exact B734743
  · exact B734747
  · exact B734751
  · exact B734755
  · exact B734759
  · exact B734763
  · exact B734767
  · exact B734771
  · exact B734775
  · exact B734779
  · exact B734783
  · exact B734787
  · exact B734791
  · exact B734795
  · exact B734799
  · exact B734803
  · exact B734807
  · exact B734811
  · exact B734815
  · exact B734819
  · exact B734823
  · exact B734827
  · exact B734831
  · exact B734835
  · exact B734839
  · exact B734843
  · exact B734847
  · exact B734851
  · exact B734855
  · exact B734859
  · exact B734863
  · exact B734867
  · exact B734871
  · exact B734875
  · exact B734879
  · exact B734883
  · exact B734887
  · exact B734891
  · exact B734895
  · exact B734899
  · exact B734903
  · exact B734907
  · exact B734911
  · exact B734915
  · exact B734919
  · exact B734923
  · exact B734927
  · exact B734931
  · exact B734935
  · exact B734939
  · exact B734943
  · exact B734947
  · exact B734951
  · exact B734955
  · exact B734959
  · exact B734963
  · exact B734967
  · exact B734971
  · exact B734975
  · exact B734979
  · exact B734983
  · exact B734987
  · exact B734991
  · exact B734995
  · exact B734999
  · exact B735003
  · exact B735007
  · exact B735011
  · exact B735015
  · exact B735019
  · exact B735023
  · exact B735027
  · exact B735031
  · exact B735035
  · exact B735039
  · exact B735043
  · exact B735047
  · exact B735051
  · exact B735055
  · exact B735059
  · exact B735063
  · exact B735067
  · exact B735071
  · exact B735075
  · exact B735079
  · exact B735083
  · exact B735087
  · exact B735091
  · exact B735095
  · exact B735099
  · exact B735103
  · exact B735107
  · exact B735111
  · exact B735115
  · exact B735119
  · exact B735123
  · exact B735127
  · exact B735131
  · exact B735135
  · exact B735139
  · exact B735143
  · exact B735147
  · exact B735151
  · exact B735155
  · exact B735159
  · exact B735163
  · exact B735167
  · exact B735171
  · exact B735175
  · exact B735179
  · exact B735183
  · exact B735187
  · exact B735191
  · exact B735195
  · exact B735199
  · exact B735203
  · exact B735207
  · exact B735211
  · exact B735215
  · exact B735219
  · exact B735223
  · exact B735227
  · exact B735231
  · exact B735235
  · exact B735239
  · exact B735243
  · exact B735247
  · exact B735251
  · exact B735255
  · exact B735259
  · exact B735263
  · exact B735267
  · exact B735271
  · exact B735275
  · exact B735279
  · exact B735283
  · exact B735287
  · exact B735291
  · exact B735295
  · exact B735299
  · exact B735303
  · exact B735307
  · exact B735311
  · exact B735315
  · exact B735319
  · exact B735323
  · exact B735327
  · exact B735331
  · exact B735335
  · exact B735339
  · exact B735343
  · exact B735347
  · exact B735351
  · exact B735355
  · exact B735359
  · exact B735363
  · exact B735367
  · exact B735371
  · exact B735375
  · exact B735379
  · exact B735383
  · exact B735387
  · exact B735391
  · exact B735395
  · exact B735399
  · exact B735403
  · exact B735407
  · exact B735411
  · exact B735415
  · exact B735419
  · exact B735423
  · exact B735427
  · exact B735431
  · exact B735435
  · exact B735439
  · exact B735443
  · exact B735447
  · exact B735451
  · exact B735455
  · exact B735459
  · exact B735463
  · exact B735467
  · exact B735471
  · exact B735475
  · exact B735479
  · exact B735483
  · exact B735487
  · exact B735491
  · exact B735495
  · exact B735499
  · exact B735503
  · exact B735507
  · exact B735511
  · exact B735515
  · exact B735519
  · exact B735523
  · exact B735527
  · exact B735531
  · exact B735535
  · exact B735539
  · exact B735543
  · exact B735547
  · exact B735551
  · exact B735555
  · exact B735559
  · exact B735563
  · exact B735567
  · exact B735571
  · exact B735575
  · exact B735579
  · exact B735583
  · exact B735587
  · exact B735591
  · exact B735595
  · exact B735599
  · exact B735603
  · exact B735607
  · exact B735611
  · exact B735615
  · exact B735619
  · exact B735623
  · exact B735627
  · exact B735631
  · exact B735635
  · exact B735639
  · exact B735643
  · exact B735647
  · exact B735651
  · exact B735655
  · exact B735659
  · exact B735663
  · exact B735667
  · exact B735671
  · exact B735675
  · exact B735679
  · exact B735683
  · exact B735687
  · exact B735691
  · exact B735695
  · exact B735699
  · exact B735703
  · exact B735707
  · exact B735711
  · exact B735715
  · exact B735719
  · exact B735723
  · exact B735727
  · exact B735731
  · exact B735735
  · exact B735739
  · exact B735743
  · exact B735747
  · exact B735751
  · exact B735755
  · exact B735759
  · exact B735763
  · exact B735767
  · exact B735771
  · exact B735775
  · exact B735779
  · exact B735783
  · exact B735787
  · exact B735791
  · exact B735795
  · exact B735799
  · exact B735803
  · exact B735807
  · exact B735811
  · exact B735815
  · exact B735819
  · exact B735823
  · exact B735827
  · exact B735831
  · exact B735835
  · exact B735839
  · exact B735843
  · exact B735847
  · exact B735851
  · exact B735855
  · exact B735859
  · exact B735863
  · exact B735867
  · exact B735871
  · exact B735875
  · exact B735879
  · exact B735883
  · exact B735887
  · exact B735891
  · exact B735895
  · exact B735899
  · exact B735903
  · exact B735907
  · exact B735911
  · exact B735915
  · exact B735919
  · exact B735923
  · exact B735927
  · exact B735931
  · exact B735935
  · exact B735939
  · exact B735943
  · exact B735947
  · exact B735951
  · exact B735955
  · exact B735959
  · exact B735963
  · exact B735967
  · exact B735971
  · exact B735975
  · exact B735979
  · exact B735983
  · exact B735987
  · exact B735991
  · exact B735995
  · exact B735999
  · exact B736003
  · exact B736007
  · exact B736011
  · exact B736015
  · exact B736019
  · exact B736023
  · exact B736027
  · exact B736031
  · exact B736035
  · exact B736039
  · exact B736043
  · exact B736047
  · exact B736051
  · exact B736055
  · exact B736059
  · exact B736063
  · exact B736067
  · exact B736071
  · exact B736075
  · exact B736079
  · exact B736083
  · exact B736087
  · exact B736091
  · exact B736095
  · exact B736099
  · exact B736103
  · exact B736107
  · exact B736111
  · exact B736115
  · exact B736119
  · exact B736123
  · exact B736127
  · exact B736131
  · exact B736135
  · exact B736139
  · exact B736143
  · exact B736147
  · exact B736151
  · exact B736155
  · exact B736159
  · exact B736163
  · exact B736167
  · exact B736171
  · exact B736175
  · exact B736179
  · exact B736183
  · exact B736187
  · exact B736191
  · exact B736195
  · exact B736199
  · exact B736203
  · exact B736207
  · exact B736211
  · exact B736215
  · exact B736219
  · exact B736223
  · exact B736227
  · exact B736231
  · exact B736235
  · exact B736239
  · exact B736243
  · exact B736247
  · exact B736251
  · exact B736255
  · exact B736259
  · exact B736263
  · exact B736267
  · exact B736271
  · exact B736275
  · exact B736279
  · exact B736283
  · exact B736287
  · exact B736291
  · exact B736295
  · exact B736299
  · exact B736303
  · exact B736307
  · exact B736311
  · exact B736315
  · exact B736319
  · exact B736323
  · exact B736327
  · exact B736331
  · exact B736335
  · exact B736339
  · exact B736343
  · exact B736347
  · exact B736351
  · exact B736355
  · exact B736359
  · exact B736363
  · exact B736367
  · exact B736371
  · exact B736375
  · exact B736379
  · exact B736383
  · exact B736387
  · exact B736391
  · exact B736395
  · exact B736399
  · exact B736403
  · exact B736407
  · exact B736411
  · exact B736415
  · exact B736419
  · exact B736423
  · exact B736427
  · exact B736431
  · exact B736435
  · exact B736439
  · exact B736443
  · exact B736447
  · exact B736451
  · exact B736455
  · exact B736459
  · exact B736463
  · exact B736467
  · exact B736471
  · exact B736475
  · exact B736479
  · exact B736483
  · exact B736487
  · exact B736491
  · exact B736495
  · exact B736499
  · exact B736503
  · exact B736507
  · exact B736511
  · exact B736515
  · exact B736519
  · exact B736523
  · exact B736527
  · exact B736531
  · exact B736535
  · exact B736539
  · exact B736543
  · exact B736547
  · exact B736551
  · exact B736555
  · exact B736559
  · exact B736563
  · exact B736567
  · exact B736571
  · exact B736575
  · exact B736579
  · exact B736583
  · exact B736587
  · exact B736591
  · exact B736595
  · exact B736599
  · exact B736603
  · exact B736607
  · exact B736611
  · exact B736615
  · exact B736619
  · exact B736623
  · exact B736627
  · exact B736631
  · exact B736635
  · exact B736639
  · exact B736643
  · exact B736647
  · exact B736651
  · exact B736655
  · exact B736659
  · exact B736663
  · exact B736667
  · exact B736671
  · exact B736675
  · exact B736679
  · exact B736683
  · exact B736687
  · exact B736691
  · exact B736695
  · exact B736699
  · exact B736703
  · exact B736707
  · exact B736711
  · exact B736715
  · exact B736719
  · exact B736723
  · exact B736727
  · exact B736731
  · exact B736735
  · exact B736739
  · exact B736743
  · exact B736747
  · exact B736751
  · exact B736755
  · exact B736759
  · exact B736763
  · exact B736767
  · exact B736771
  · exact B736775
  · exact B736779
  · exact B736783
  · exact B736787
  · exact B736791
  · exact B736795
  · exact B736799
  · exact B736803
  · exact B736807
  · exact B736811
  · exact B736815
  · exact B736819
  · exact B736823
  · exact B736827
  · exact B736831
  · exact B736835
  · exact B736839
  · exact B736843
  · exact B736847
  · exact B736851
  · exact B736855
  · exact B736859
  · exact B736863
  · exact B736867
  · exact B736871
  · exact B736875
  · exact B736879
  · exact B736883
  · exact B736887
  · exact B736891
  · exact B736895
  · exact B736899
  · exact B736903
  · exact B736907
  · exact B736911
  · exact B736915
  · exact B736919
  · exact B736923
  · exact B736927
  · exact B736931
  · exact B736935
  · exact B736939
  · exact B736943
  · exact B736947
  · exact B736951
  · exact B736955
  · exact B736959
  · exact B736963
  · exact B736967
  · exact B736971
  · exact B736975
  · exact B736979
  · exact B736983
  · exact B736987
  · exact B736991
  · exact B736995
  · exact B736999
  · exact B737003
  · exact B737007
  · exact B737011
  · exact B737015
  · exact B737019
  · exact B737023
  · exact B737027
  · exact B737031
  · exact B737035
  · exact B737039
  · exact B737043
  · exact B737047
  · exact B737051
  · exact B737055
  · exact B737059
  · exact B737063
  · exact B737067
  · exact B737071
  · exact B737075
  · exact B737079
  · exact B737083
  · exact B737087
  · exact B737091
  · exact B737095
  · exact B737099
  · exact B737103
  · exact B737107
  · exact B737111
  · exact B737115
  · exact B737119
  · exact B737123

theorem C1 (j : ℕ) (h1 : 184281 ≤ j) (h2 : j ≤ 184580) : Blo 734326 (4 * j + 3) := by
  interval_cases j
  · exact B737127
  · exact B737131
  · exact B737135
  · exact B737139
  · exact B737143
  · exact B737147
  · exact B737151
  · exact B737155
  · exact B737159
  · exact B737163
  · exact B737167
  · exact B737171
  · exact B737175
  · exact B737179
  · exact B737183
  · exact B737187
  · exact B737191
  · exact B737195
  · exact B737199
  · exact B737203
  · exact B737207
  · exact B737211
  · exact B737215
  · exact B737219
  · exact B737223
  · exact B737227
  · exact B737231
  · exact B737235
  · exact B737239
  · exact B737243
  · exact B737247
  · exact B737251
  · exact B737255
  · exact B737259
  · exact B737263
  · exact B737267
  · exact B737271
  · exact B737275
  · exact B737279
  · exact B737283
  · exact B737287
  · exact B737291
  · exact B737295
  · exact B737299
  · exact B737303
  · exact B737307
  · exact B737311
  · exact B737315
  · exact B737319
  · exact B737323
  · exact B737327
  · exact B737331
  · exact B737335
  · exact B737339
  · exact B737343
  · exact B737347
  · exact B737351
  · exact B737355
  · exact B737359
  · exact B737363
  · exact B737367
  · exact B737371
  · exact B737375
  · exact B737379
  · exact B737383
  · exact B737387
  · exact B737391
  · exact B737395
  · exact B737399
  · exact B737403
  · exact B737407
  · exact B737411
  · exact B737415
  · exact B737419
  · exact B737423
  · exact B737427
  · exact B737431
  · exact B737435
  · exact B737439
  · exact B737443
  · exact B737447
  · exact B737451
  · exact B737455
  · exact B737459
  · exact B737463
  · exact B737467
  · exact B737471
  · exact B737475
  · exact B737479
  · exact B737483
  · exact B737487
  · exact B737491
  · exact B737495
  · exact B737499
  · exact B737503
  · exact B737507
  · exact B737511
  · exact B737515
  · exact B737519
  · exact B737523
  · exact B737527
  · exact B737531
  · exact B737535
  · exact B737539
  · exact B737543
  · exact B737547
  · exact B737551
  · exact B737555
  · exact B737559
  · exact B737563
  · exact B737567
  · exact B737571
  · exact B737575
  · exact B737579
  · exact B737583
  · exact B737587
  · exact B737591
  · exact B737595
  · exact B737599
  · exact B737603
  · exact B737607
  · exact B737611
  · exact B737615
  · exact B737619
  · exact B737623
  · exact B737627
  · exact B737631
  · exact B737635
  · exact B737639
  · exact B737643
  · exact B737647
  · exact B737651
  · exact B737655
  · exact B737659
  · exact B737663
  · exact B737667
  · exact B737671
  · exact B737675
  · exact B737679
  · exact B737683
  · exact B737687
  · exact B737691
  · exact B737695
  · exact B737699
  · exact B737703
  · exact B737707
  · exact B737711
  · exact B737715
  · exact B737719
  · exact B737723
  · exact B737727
  · exact B737731
  · exact B737735
  · exact B737739
  · exact B737743
  · exact B737747
  · exact B737751
  · exact B737755
  · exact B737759
  · exact B737763
  · exact B737767
  · exact B737771
  · exact B737775
  · exact B737779
  · exact B737783
  · exact B737787
  · exact B737791
  · exact B737795
  · exact B737799
  · exact B737803
  · exact B737807
  · exact B737811
  · exact B737815
  · exact B737819
  · exact B737823
  · exact B737827
  · exact B737831
  · exact B737835
  · exact B737839
  · exact B737843
  · exact B737847
  · exact B737851
  · exact B737855
  · exact B737859
  · exact B737863
  · exact B737867
  · exact B737871
  · exact B737875
  · exact B737879
  · exact B737883
  · exact B737887
  · exact B737891
  · exact B737895
  · exact B737899
  · exact B737903
  · exact B737907
  · exact B737911
  · exact B737915
  · exact B737919
  · exact B737923
  · exact B737927
  · exact B737931
  · exact B737935
  · exact B737939
  · exact B737943
  · exact B737947
  · exact B737951
  · exact B737955
  · exact B737959
  · exact B737963
  · exact B737967
  · exact B737971
  · exact B737975
  · exact B737979
  · exact B737983
  · exact B737987
  · exact B737991
  · exact B737995
  · exact B737999
  · exact B738003
  · exact B738007
  · exact B738011
  · exact B738015
  · exact B738019
  · exact B738023
  · exact B738027
  · exact B738031
  · exact B738035
  · exact B738039
  · exact B738043
  · exact B738047
  · exact B738051
  · exact B738055
  · exact B738059
  · exact B738063
  · exact B738067
  · exact B738071
  · exact B738075
  · exact B738079
  · exact B738083
  · exact B738087
  · exact B738091
  · exact B738095
  · exact B738099
  · exact B738103
  · exact B738107
  · exact B738111
  · exact B738115
  · exact B738119
  · exact B738123
  · exact B738127
  · exact B738131
  · exact B738135
  · exact B738139
  · exact B738143
  · exact B738147
  · exact B738151
  · exact B738155
  · exact B738159
  · exact B738163
  · exact B738167
  · exact B738171
  · exact B738175
  · exact B738179
  · exact B738183
  · exact B738187
  · exact B738191
  · exact B738195
  · exact B738199
  · exact B738203
  · exact B738207
  · exact B738211
  · exact B738215
  · exact B738219
  · exact B738223
  · exact B738227
  · exact B738231
  · exact B738235
  · exact B738239
  · exact B738243
  · exact B738247
  · exact B738251
  · exact B738255
  · exact B738259
  · exact B738263
  · exact B738267
  · exact B738271
  · exact B738275
  · exact B738279
  · exact B738283
  · exact B738287
  · exact B738291
  · exact B738295
  · exact B738299
  · exact B738303
  · exact B738307
  · exact B738311
  · exact B738315
  · exact B738319
  · exact B738323

theorem solution (m : ℕ) (hlo : 734326 ≤ m) (hhi : m ≤ 738326) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 183581 ≤ j := by omega
    have hj2 : j ≤ 184580 := by omega
    have hb : Blo 734326 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 184281 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
