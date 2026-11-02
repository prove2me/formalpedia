-- Prove2me | solution 1 for gpy_defectOffPart_eq_tied_sum_general
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T08:11:14.30119+00:00
-- url     : https://prove2.me/submissions/49cd5ee9-ccf4-4a8b-9978-4ed0c3853ff1

/- Submission file for `gpy` publish batch `gpy_defectOffPart_eq_tied_sum_general`.
   Self-contained: imports Mathlib only. Top-level `theorem solution`
   is the general off-part tied-sum identity from GPYDefectSmall.lean
   (`defectOffPart_eq_tied_sum_general`), in fully unfolded
   Mathlib-only terms (support set written out as a piFinset filter).
   UNCONDITIONAL: no squarefree hypothesis. No defect smallness is
   claimed: this is an exact decomposition, not a bound. -/
import Mathlib

open scoped BigOperators
open scoped Function
open Classical

set_option autoImplicit false


theorem prime_dvd_lcm_aux {p m n : ℕ} (hp : Nat.Prime p) (h : p ∣ Nat.lcm m n) :
    p ∣ m ∨ p ∣ n := by
  by_contra hc
  have hc1 : ¬ p ∣ m := fun h => hc (Or.inl h)
  have hc2 : ¬ p ∣ n := fun h => hc (Or.inr h)
  have hcm : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hc1
  have hcn : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd hp).mpr hc2
  have hcop : Nat.Coprime p (m * n) := hcm.mul_right hcn
  have hdvd : Nat.lcm m n ∣ m * n :=
    ⟨Nat.gcd m n, (Nat.gcd_mul_lcm m n).symm.trans (mul_comm _ _)⟩
  exact ((Nat.Prime.coprime_iff_not_dvd hp).mp hcop) (dvd_trans h hdvd)

theorem prime_dvd_finset_lcm_aux {ι : Type*} {s : Finset ι} {f : ι → ℕ} {p : ℕ}
    (hp : Nat.Prime p) (h : p ∣ s.lcm f) : ∃ j ∈ s, p ∣ f j := by
  induction s using Finset.induction with
  | empty =>
    rw [Finset.lcm_empty] at h
    have h1 := Nat.dvd_one.mp h
    have h2 := hp.one_lt
    omega
  | insert a s ha ih =>
    rw [Finset.lcm_insert] at h
    rcases prime_dvd_lcm_aux hp h with h1 | h2
    · exact ⟨a, Finset.mem_insert_self a s, h1⟩
    · obtain ⟨j, hj, hjf⟩ := ih h2
      exact ⟨j, Finset.mem_insert_of_mem hj, hjf⟩

theorem gcd_lcm_distrib_aux {a b c : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    Nat.gcd (Nat.lcm a b) c = Nat.lcm (Nat.gcd a c) (Nat.gcd b c) := by
  have hlab : Nat.lcm a b ≠ 0 := Nat.lcm_ne_zero ha hb
  have hgac : Nat.gcd a c ≠ 0 := by
    intro h; rw [Nat.gcd_eq_zero_iff] at h; exact hc h.2
  have hgbc : Nat.gcd b c ≠ 0 := by
    intro h; rw [Nat.gcd_eq_zero_iff] at h; exact hc h.2
  refine Nat.eq_of_factorization_eq ?_ ?_ ?_
  · intro h; rw [Nat.gcd_eq_zero_iff] at h; exact hc h.2
  · exact Nat.lcm_ne_zero hgac hgbc
  · intro p
    rw [Nat.factorization_gcd hlab hc, Nat.factorization_lcm ha hb,
        Nat.factorization_lcm hgac hgbc, Nat.factorization_gcd ha hc,
        Nat.factorization_gcd hb hc]
    simp only [Finsupp.inf_apply, Finsupp.sup_apply]
    omega

/-! ### Finset versions: gcd distributes over `Finset.lcm`, and ModEq lifts to it -/

/-- `gcd` distributes over a `Finset.lcm` (by induction, using the binary case). -/
theorem gcd_finset_lcm_aux {k : ℕ} (s : Finset (Fin k)) {m : Fin k → ℕ} {n : ℕ} :
    (∀ i ∈ s, m i ≠ 0) → n ≠ 0 →
    Nat.gcd (s.lcm m) n = s.lcm (fun i => Nat.gcd (m i) n) := by
  induction s using Finset.induction with
  | empty =>
    intro _ _
    rw [Finset.lcm_empty, Finset.lcm_empty, Nat.gcd_one_left]
  | @insert j s hj ih =>
    intro hm' hn'
    have hm_s : ∀ i ∈ s, m i ≠ 0 := fun i hi => hm' i (Finset.mem_insert_of_mem hi)
    have hj_ne : m j ≠ 0 := hm' j (Finset.mem_insert_self j s)
    have hLs_ne : s.lcm m ≠ 0 := Finset.lcm_ne_zero_iff.mpr hm_s
    calc Nat.gcd ((insert j s).lcm m) n
        = Nat.gcd (Nat.lcm (m j) (s.lcm m)) n := by
          rw [Finset.lcm_insert, lcm_eq_nat_lcm]
      _ = Nat.lcm (Nat.gcd (m j) n) (Nat.gcd (s.lcm m) n) :=
          gcd_lcm_distrib_aux hj_ne hLs_ne hn'
      _ = Nat.lcm (Nat.gcd (m j) n) (s.lcm (fun i => Nat.gcd (m i) n)) := by
          rw [ih hm_s hn']
      _ = (insert j s).lcm (fun i => Nat.gcd (m i) n) := by
          rw [Finset.lcm_insert, lcm_eq_nat_lcm]

/-- Simultaneous congruences mod each `m i` combine to a congruence mod `s.lcm m`. -/
theorem modEq_finset_lcm_aux {k : ℕ} (s : Finset (Fin k)) {m : Fin k → ℕ} {a b : ℕ} :
    (∀ i ∈ s, a ≡ b [MOD m i]) → a ≡ b [MOD s.lcm m] := by
  induction s using Finset.induction with
  | empty =>
    intro _
    rw [Finset.lcm_empty]
    exact Nat.modEq_one
  | @insert j s hj ih =>
    intro h'
    have h1 : a ≡ b [MOD m j] := h' j (Finset.mem_insert_self j s)
    have h2 : a ≡ b [MOD s.lcm m] :=
      ih (fun i hi => h' i (Finset.mem_insert_of_mem hi))
    rw [Finset.lcm_insert, lcm_eq_nat_lcm]
    exact Nat.mod_lcm h1 h2

/-! ### General (non-coprime) Chinese remainder theorem -/

/-- General CRT, residue form: compatible residues have a simultaneous solution.
    The two-modulus step is `Nat.chineseRemainder'`; the transfer of the
    induction hypothesis to the combined modulus uses `gcd_finset_lcm_aux`
    and `modEq_finset_lcm_aux`. -/
theorem exists_modEq_of_compatible_aux {k : ℕ} {m r : Fin k → ℕ} :
    (∀ i, m i ≠ 0) → (∀ i j, r i ≡ r j [MOD Nat.gcd (m i) (m j)]) →
    ∃ a, ∀ i, a ≡ r i [MOD m i] := by
  intro hm hcompat
  have key : ∀ s : Finset (Fin k), (∀ i ∈ s, m i ≠ 0) →
      (∀ i ∈ s, ∀ j ∈ s, r i ≡ r j [MOD Nat.gcd (m i) (m j)]) →
      ∃ a, ∀ i ∈ s, a ≡ r i [MOD m i] := by
    intro s
    induction s using Finset.induction with
    | empty =>
      intro _ _
      exact ⟨0, fun i hi => absurd hi (Finset.notMem_empty i)⟩
    | @insert j s hj ih =>
      intro hm' hcompat'
      have hm_s : ∀ i ∈ s, m i ≠ 0 := fun i hi => hm' i (Finset.mem_insert_of_mem hi)
      have hcompat_s : ∀ i ∈ s, ∀ j ∈ s, r i ≡ r j [MOD Nat.gcd (m i) (m j)] :=
        fun i hi j hj' => hcompat' i (Finset.mem_insert_of_mem hi) j
          (Finset.mem_insert_of_mem hj')
      obtain ⟨a, ha⟩ := ih hm_s hcompat_s
      have htransfer : a ≡ r j [MOD Nat.gcd (s.lcm m) (m j)] := by
        have h1 : ∀ i ∈ s, a ≡ r j [MOD Nat.gcd (m i) (m j)] := by
          intro i hi
          have hai : a ≡ r i [MOD m i] := ha i hi
          have h2 : a ≡ r i [MOD Nat.gcd (m i) (m j)] :=
            Nat.ModEq.of_dvd (Nat.gcd_dvd_left _ _) hai
          have h3 : r i ≡ r j [MOD Nat.gcd (m i) (m j)] :=
            hcompat' i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_self j s)
          exact h2.trans h3
        have h2 := modEq_finset_lcm_aux s (m := fun i => Nat.gcd (m i) (m j)) h1
        rw [← gcd_finset_lcm_aux s hm_s (hm' j (Finset.mem_insert_self j s))] at h2
        exact h2
      obtain ⟨b, hb⟩ := Nat.chineseRemainder' htransfer
      refine ⟨b, fun i hi => ?_⟩
      rw [Finset.mem_insert] at hi
      rcases hi with rfl | hi
      · exact hb.2
      · have h1 : b ≡ a [MOD m i] := Nat.ModEq.of_dvd (Finset.dvd_lcm hi) hb.1
        exact h1.trans (ha i hi)
  obtain ⟨a, ha⟩ := key Finset.univ (fun i _ => hm i) (fun i _ j _ => hcompat i j)
  exact ⟨a, fun i => ha i (Finset.mem_univ i)⟩

/-- General CRT, divisibility form: a compatible family of shifts has a common
    `a` with every `m i ∣ a + h i`. Residues are `m i - h i % m i`. -/
theorem exists_dvd_of_compatible_aux {k : ℕ} {m h : Fin k → ℕ} :
    (∀ i, m i ≠ 0) → (∀ i j, h i ≡ h j [MOD Nat.gcd (m i) (m j)]) →
    ∃ a, ∀ i, m i ∣ a + h i := by
  intro hm hcompat
  have hri : ∀ i, m i ∣ (m i - h i % m i) + h i := by
    intro i
    have h3 : (m i - h i % m i) + h i = m i * (h i / m i + 1) := by
      have h1 := Nat.div_add_mod (h i) (m i)
      have h2 : h i % m i ≤ m i := (Nat.mod_lt (h i) (Nat.pos_of_ne_zero (hm i))).le
      calc (m i - h i % m i) + h i
          = (m i - h i % m i) + (m i * (h i / m i) + h i % m i) := by rw [h1]
        _ = m i * (h i / m i) + m i := by
            rw [Nat.add_comm (m i - h i % m i) (m i * (h i / m i) + h i % m i),
              Nat.add_assoc, Nat.add_sub_cancel' h2]
        _ = m i * (h i / m i + 1) := by rw [Nat.mul_add, Nat.mul_one]
    rw [h3]
    exact dvd_mul_right _ _
  have hcompat_r : ∀ i j, (m i - h i % m i) ≡ (m j - h j % m j)
      [MOD Nat.gcd (m i) (m j)] := by
    intro i j
    have g1 : (m i - h i % m i) + h i ≡ 0 [MOD Nat.gcd (m i) (m j)] :=
      Nat.ModEq.of_dvd (Nat.gcd_dvd_left _ _)
        (Nat.modEq_zero_iff_dvd.mpr (hri i))
    have g2 : (m j - h j % m j) + h j ≡ 0 [MOD Nat.gcd (m i) (m j)] :=
      Nat.ModEq.of_dvd (Nat.gcd_dvd_right _ _)
        (Nat.modEq_zero_iff_dvd.mpr (hri j))
    have h3 : (m i - h i % m i) + h i ≡ (m j - h j % m j) + h j
        [MOD Nat.gcd (m i) (m j)] :=
      g1.trans g2.symm
    have h4 : (m j - h j % m j) + h j ≡ (m j - h j % m j) + h i
        [MOD Nat.gcd (m i) (m j)] := by
      rw [Nat.gcd_comm (m i) (m j)]
      exact (hcompat j i).add_left _
    exact Nat.ModEq.add_right_cancel' (h i) (h3.trans h4)
  obtain ⟨a, ha⟩ := exists_modEq_of_compatible_aux hm hcompat_r
  refine ⟨a, fun i => ?_⟩
  have h1 : a + h i ≡ (m i - h i % m i) + h i [MOD m i] := (ha i).add_right (h i)
  have h2 : (m i - h i % m i) + h i ≡ 0 [MOD m i] :=
    Nat.modEq_zero_iff_dvd.mpr (hri i)
  exact Nat.modEq_zero_iff_dvd.mp (h1.trans h2)

theorem goodPair_noncong_aux {k : ℕ} {h d e : Fin k → ℕ} {i : Fin k}
    {p : ℕ} (hp : Nat.Prime p) (hg : (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))) {j : Fin k}
    (hj : p ∣ Nat.lcm (d j) (e j)) : ¬ h i ≡ h j [MOD p] := by
  intro hcong
  obtain ⟨w, hw, hcop⟩ := hg
  have hpw : p ∣ w + h j := dvd_trans hj (hw j)
  have hpwi : p ∣ w + h i :=
    Nat.modEq_zero_iff_dvd.mp
      ((Nat.ModEq.add_left w hcong).trans (Nat.modEq_zero_iff_dvd.mpr hpw))
  have hpL : p ∣ Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) :=
    dvd_trans hj (Finset.dvd_lcm (Finset.mem_univ j))
  have hpgcd : p ∣ Nat.gcd (w + h i)
      (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) :=
    Nat.dvd_gcd hpwi hpL
  rw [hcop.gcd_eq_one] at hpgcd
  exact hp.not_dvd_one hpgcd

theorem not_goodPair_of_prime_cong_aux {k : ℕ} {h d e : Fin k → ℕ} {i : Fin k}
    {p : ℕ} (hp : Nat.Prime p) {j : Fin k}
    (hj : p ∣ Nat.lcm (d j) (e j)) (hcong : h i ≡ h j [MOD p]) :
    ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
      Nat.Coprime (w + h i)
        (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) :=
  fun hg => goodPair_noncong_aux hp hg hj hcong

theorem prime_dvd_natAbs_diff_of_modEq_aux {p : ℕ} (_hp : Nat.Prime p)
    {a b : ℕ} (hcong : a ≡ b [MOD p]) :
    p ∣ Int.natAbs ((a : ℤ) - (b : ℤ)) := by
  rcases le_total b a with hle | hle
  · have h1 : Int.natAbs ((a : ℤ) - (b : ℤ)) = a - b := by
      rw [← Nat.cast_sub hle, Int.natAbs_natCast]
    rw [h1]
    exact (Nat.modEq_iff_dvd' hle).mp hcong.symm
  · have h1 : Int.natAbs ((a : ℤ) - (b : ℤ)) = b - a := by
      have e : (a : ℤ) - (b : ℤ) = -((b : ℤ) - (a : ℤ)) := by ring
      rw [e, Int.natAbs_neg, ← Nat.cast_sub hle, Int.natAbs_natCast]
    rw [h1]
    exact (Nat.modEq_iff_dvd' hle).mp hcong

/-- Conversely, `p` dividing the absolute integer difference gives
    the congruence mod `p`. -/
theorem modEq_of_prime_dvd_natAbs_diff_aux {p : ℕ} (_hp : Nat.Prime p)
    {a b : ℕ} (hdvd : p ∣ Int.natAbs ((a : ℤ) - (b : ℤ))) :
    a ≡ b [MOD p] := by
  rcases le_total b a with hle | hle
  · have h1 : Int.natAbs ((a : ℤ) - (b : ℤ)) = a - b := by
      rw [← Nat.cast_sub hle, Int.natAbs_natCast]
    rw [h1] at hdvd
    exact ((Nat.modEq_iff_dvd' hle).mpr hdvd).symm
  · have h1 : Int.natAbs ((a : ℤ) - (b : ℤ)) = b - a := by
      have e : (a : ℤ) - (b : ℤ) = -((b : ℤ) - (a : ℤ)) := by ring
      rw [e, Int.natAbs_neg, ← Nat.cast_sub hle, Int.natAbs_natCast]
    rw [h1] at hdvd
    exact (Nat.modEq_iff_dvd' hle).mpr hdvd

theorem defect_prime_general_aux {k : ℕ} {h d e : Fin k → ℕ} {i : Fin k}
    (hm : ∀ j, Nat.lcm (d j) (e j) ≠ 0)
    (hcompat : ∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
      h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))])
    (hnotgood : ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
      Nat.Coprime (w + h i)
        (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))) :
    ∃ p, Nat.Prime p ∧
      p ∣ Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) ∧
      (p ∣ Nat.lcm (d i) (e i) ∨
        ∃ j, j ≠ i ∧ p ∣ Nat.lcm (d j) (e j) ∧ h i ≡ h j [MOD p]) := by
  obtain ⟨a, ha⟩ := exists_dvd_of_compatible_aux hm
    (fun i' j' => hcompat i' (Finset.mem_univ i') j' (Finset.mem_univ j'))
  have hncop : ¬ Nat.Coprime (a + h i)
      (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) :=
    fun hcop => hnotgood ⟨a, ha, hcop⟩
  have hgcd : Nat.gcd (a + h i)
      (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) ≠ 1 :=
    fun hg => hncop (Nat.coprime_iff_gcd_eq_one.mpr hg)
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hgcd
  have hpL : p ∣ Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) :=
    dvd_trans hpdvd (Nat.gcd_dvd_right _ _)
  have hpwi : p ∣ a + h i := dvd_trans hpdvd (Nat.gcd_dvd_left _ _)
  obtain ⟨j, -, hj⟩ := prime_dvd_finset_lcm_aux hp hpL
  have hpwj : p ∣ a + h j := dvd_trans hj (ha j)
  have hcong : h i ≡ h j [MOD p] := by
    have e1 : a + h i ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr hpwi
    have e2 : a + h j ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr hpwj
    exact Nat.ModEq.add_left_cancel' a (e1.trans e2.symm)
  refine ⟨p, hp, hpL, ?_⟩
  by_cases hji : j = i
  · left
    rw [hji] at hj
    exact hj
  · right
    exact ⟨j, hji, hj, hcong⟩

theorem compat_not_good_lcm_one_iff_tied_general_aux {k : ℕ} {h d e : Fin k → ℕ}
    {i : Fin k} (hm : ∀ j, Nat.lcm (d j) (e j) ≠ 0) :
    ((∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
      h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧
      ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
        Nat.Coprime (w + h i)
          (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) ∧
      Nat.lcm (d i) (e i) = 1) ↔
    ((∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
      h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧
      Nat.lcm (d i) (e i) = 1 ∧
      ∃ p j, Nat.Prime p ∧ j ≠ i ∧ p ∣ Nat.lcm (d j) (e j) ∧
        (h j = h i ∨
          p ∈ (Int.natAbs ((h i : ℤ) - (h j : ℤ))).primeFactors)) := by
  constructor
  · rintro ⟨hcompat, hnotgood, hlcm⟩
    obtain ⟨p, hp, -, hdisj⟩ := defect_prime_general_aux hm hcompat hnotgood
    refine ⟨hcompat, hlcm, ?_⟩
    rcases hdisj with hp_i | ⟨j, hne, hj, hcong⟩
    · rw [hlcm] at hp_i
      exact absurd hp_i hp.not_dvd_one
    · refine ⟨p, j, hp, hne, hj, ?_⟩
      by_cases heq : h j = h i
      · left
        exact heq
      · right
        have hdvd : p ∣ Int.natAbs ((h i : ℤ) - (h j : ℤ)) :=
          prime_dvd_natAbs_diff_of_modEq_aux hp hcong
        have hne0 : Int.natAbs ((h i : ℤ) - (h j : ℤ)) ≠ 0 := by
          intro h0
          apply heq
          have hdiff : (h i : ℤ) - (h j : ℤ) = 0 := Int.natAbs_eq_zero.mp h0
          have hcast : (h i : ℤ) = (h j : ℤ) := sub_eq_zero.mp hdiff
          exact (Nat.cast_inj.mp hcast).symm
        exact Nat.mem_primeFactors.mpr ⟨hp, hdvd, hne0⟩
  · rintro ⟨hcompat, hlcm, p, j, hp, hne, hj, hdisj⟩
    refine ⟨hcompat, ?_, hlcm⟩
    apply not_goodPair_of_prime_cong_aux hp hj
    rcases hdisj with heq | hmem
    · show h i % p = h j % p
      rw [heq]
    · exact modEq_of_prime_dvd_natAbs_diff_aux hp
        (Nat.mem_primeFactors.mp hmem).2.1

/-- The off-part of the defect is exactly the tied sum, over the
    full support — no squarefree restriction anywhere. -/
theorem defectOffPart_eq_tied_sum_general_aux {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (i : Fin k) :
    (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
      ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
            h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
              Nat.Coprime (w + h i)
                (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) ∧ Nat.lcm (d i) (e i) = 1 then
          lam d * lam e / Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
         else 0)) =
      (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
      ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
            h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ Nat.lcm (d i) (e i) = 1 ∧
          (∃ p j, Nat.Prime p ∧ j ≠ i ∧ p ∣ Nat.lcm (d j) (e j) ∧
            (h j = h i ∨
              p ∈ (Int.natAbs ((h i : ℤ) - (h j : ℤ))).primeFactors)) then
          lam d * lam e / Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
         else 0)) := by
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  have hdpi : d ∈ Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R) :=
    (Finset.mem_filter.mp hd).1
  have hepi : e ∈ Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R) :=
    (Finset.mem_filter.mp he).1
  have hd1 : ∀ j, 1 ≤ d j :=
    fun j => (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hdpi j)).1
  have he1 : ∀ j, 1 ≤ e j :=
    fun j => (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hepi j)).1
  have hm : ∀ j, Nat.lcm (d j) (e j) ≠ 0 :=
    fun j => Nat.lcm_ne_zero (by have h1 := hd1 j; omega)
      (by have h2 := he1 j; omega)
  by_cases hL : (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
            h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
              Nat.Coprime (w + h i)
                (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) ∧ Nat.lcm (d i) (e i) = 1
  · have hR : (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
            h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ Nat.lcm (d i) (e i) = 1 ∧
        (∃ p j, Nat.Prime p ∧ j ≠ i ∧ p ∣ Nat.lcm (d j) (e j) ∧
            (h j = h i ∨
              p ∈ (Int.natAbs ((h i : ℤ) - (h j : ℤ))).primeFactors)) :=
      (compat_not_good_lcm_one_iff_tied_general_aux hm).mp hL
    rw [if_pos hL, if_pos hR]
  · have hRneg : ¬ ((∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
            h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ Nat.lcm (d i) (e i) = 1 ∧
        (∃ p j, Nat.Prime p ∧ j ≠ i ∧ p ∣ Nat.lcm (d j) (e j) ∧
            (h j = h i ∨
              p ∈ (Int.natAbs ((h i : ℤ) - (h j : ℤ))).primeFactors))) :=
      fun hR => hL ((compat_not_good_lcm_one_iff_tied_general_aux hm).mpr hR)
    rw [if_neg hL, if_neg hRneg]

theorem solution {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (i : Fin k) :
    (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
      ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
            h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
              Nat.Coprime (w + h i)
                (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) ∧ Nat.lcm (d i) (e i) = 1 then
          lam d * lam e / Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
         else 0)) =
      (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
      ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
            h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ Nat.lcm (d i) (e i) = 1 ∧
          (∃ p j, Nat.Prime p ∧ j ≠ i ∧ p ∣ Nat.lcm (d j) (e j) ∧
            (h j = h i ∨
              p ∈ (Int.natAbs ((h i : ℤ) - (h j : ℤ))).primeFactors)) then
          lam d * lam e / Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
         else 0)) :=
  defectOffPart_eq_tied_sum_general_aux h R lam i
