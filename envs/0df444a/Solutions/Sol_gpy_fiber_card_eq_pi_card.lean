-- Prove2me | solution 1 for gpy_fiber_card_eq_pi_card
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-30T20:26:42.325446+00:00
-- url     : https://prove2.me/submissions/248dfd12-bfc2-4800-b1a1-32b41739abb3

import Mathlib

open scoped BigOperators
open Classical

set_option autoImplicit false

def tupleSupport (k : ℕ) (R : ℕ) : Finset (Fin k → ℕ) :=
  (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)

def goodPair {k : ℕ} (h d e : Fin k → ℕ) (i : Fin k) : Prop :=
  ∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
    Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))

noncomputable def localGoodChoiceFinset {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (p : ℕ) (hd he : Prop) [Decidable hd] [Decidable he] :
    Finset (Option (Fin k) × Option (Fin k)) :=
  Finset.univ.filter (fun ab =>
    (ab.1.isSome ↔ hd) ∧ (ab.2.isSome ↔ he) ∧
    (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
      (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
    (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p]))

noncomputable def coordOf {k : ℕ} (d : Fin k → ℕ) (p : ℕ) : Option (Fin k) :=
  if hex : ∃ j, p ∣ d j then some (Classical.choose hex) else none

noncomputable def piChoiceFun {k : ℕ} (s : Finset ℕ)
    (f : ∀ p, p ∈ s → Option (Fin k) × Option (Fin k)) :
    ℕ → Option (Fin k) × Option (Fin k) :=
  fun p => if hp : p ∈ s then f p hp else (none, none)

noncomputable def backwardD {k : ℕ} (s : Finset ℕ)
    (Ff : ℕ → Option (Fin k) × Option (Fin k)) (j : Fin k) : ℕ :=
  ∏ p ∈ s, (if (Ff p).1 = some j then p else 1)

noncomputable def backwardE {k : ℕ} (s : Finset ℕ)
    (Ff : ℕ → Option (Fin k) × Option (Fin k)) (j : Fin k) : ℕ :=
  ∏ p ∈ s, (if (Ff p).2 = some j then p else 1)

noncomputable def crtResidue {k : ℕ} (h d e : Fin k → ℕ) (p : ℕ) : ℕ :=
  if hex : ∃ j, p ∣ Nat.lcm (d j) (e j)
  then p - h (Classical.choose hex) % p else 0

theorem mem_tupleSupport_aux {k : ℕ} {R : ℕ} {d : Fin k → ℕ} :
    d ∈ tupleSupport k R ↔
      (∀ i, 1 ≤ d i) ∧ (∀ i, d i ≤ R) ∧ ∏ i, d i ≤ R := by
  rw [tupleSupport, Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => (Finset.mem_Icc.mp (h1 i)).1,
      fun i => (Finset.mem_Icc.mp (h1 i)).2, h2⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun i => Finset.mem_Icc.mpr ⟨h1 i, h2 i⟩, h3⟩

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

theorem coprime_prime_prod_aux {P : Finset ℕ} {p : ℕ} (hp : Nat.Prime p)
    (hP : ∀ q ∈ P, Nat.Prime q) (hne : ∀ q ∈ P, q ≠ p) :
    Nat.Coprime p (∏ q ∈ P, q) := by
  induction P using Finset.induction with
  | empty =>
    rw [Finset.prod_empty]
    exact Nat.coprime_one_right p
  | insert a P ha ih =>
    have hP' : ∀ q ∈ P, Nat.Prime q := fun q hq => hP q (Finset.mem_insert_of_mem hq)
    have hne' : ∀ q ∈ P, q ≠ p := fun q hq => hne q (Finset.mem_insert_of_mem hq)
    have hpa : Nat.Coprime p a :=
      (Nat.coprime_primes hp (hP a (Finset.mem_insert_self a P))).mpr
        ((hne a (Finset.mem_insert_self a P)).symm)
    rw [Finset.prod_insert ha]
    exact hpa.mul_right (ih hP' hne')

theorem exists_modEq_prime_finset_aux {P : Finset ℕ} (a : ℕ → ℕ)
    (hP : ∀ q ∈ P, Nat.Prime q) :
    ∃ w, ∀ q ∈ P, w ≡ a q [MOD q] := by
  induction P using Finset.induction with
  | empty =>
    exact ⟨0, fun q hq => absurd hq (Finset.notMem_empty q)⟩
  | insert p P hp ih =>
    have hP' : ∀ q ∈ P, Nat.Prime q := fun q hq => hP q (Finset.mem_insert_of_mem hq)
    obtain ⟨w, hw⟩ := ih hP'
    have hpprime : Nat.Prime p := hP p (Finset.mem_insert_self p P)
    have hcop : Nat.Coprime (∏ q ∈ P, q) p := by
      apply Nat.Coprime.symm
      apply coprime_prime_prod_aux hpprime hP'
      intro q hq hqp
      subst hqp
      exact hp hq
    obtain ⟨w', hw'⟩ := Nat.chineseRemainder hcop w (a p)
    refine ⟨w', ?_⟩
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hqP
    · exact hw'.2
    · have hqdvd : q ∣ ∏ q' ∈ P, q' := Finset.dvd_prod_of_mem _ hqP
      exact (Nat.ModEq.of_dvd hqdvd hw'.1).trans (hw q hqP)

theorem crtResidue_add_aux {k : ℕ} {h d e : Fin k → ℕ} {p : ℕ} {j : Fin k}
    (hp : Nat.Prime p) (hj : p ∣ Nat.lcm (d j) (e j))
    (hcompat : ∀ j', p ∣ Nat.lcm (d j') (e j') → h j ≡ h j' [MOD p]) :
    crtResidue h d e p + h j ≡ 0 [MOD p] := by
  unfold crtResidue
  have hex : ∃ j', p ∣ Nat.lcm (d j') (e j') := ⟨j, hj⟩
  rw [dif_pos hex]
  have hj₀dvd : p ∣ Nat.lcm (d (Classical.choose hex)) (e (Classical.choose hex)) :=
    Classical.choose_spec hex
  have hmod : h j ≡ h (Classical.choose hex) [MOD p] := hcompat _ hj₀dvd
  have step1 : (p - h (Classical.choose hex) % p) + h j
      ≡ (p - h (Classical.choose hex) % p) + h (Classical.choose hex) [MOD p] :=
    Nat.ModEq.add_left _ hmod
  have step2 : (p - h (Classical.choose hex) % p) + h (Classical.choose hex)
      ≡ 0 [MOD p] := by
    have hr : h (Classical.choose hex) % p < p := Nat.mod_lt _ hp.pos
    have e : (p - h (Classical.choose hex) % p) + h (Classical.choose hex)
        ≡ (p - h (Classical.choose hex) % p) + (h (Classical.choose hex) % p) [MOD p] :=
      (Nat.ModEq.add_left _ (Nat.mod_modEq _ _)).symm
    have e2 : (p - h (Classical.choose hex) % p) + (h (Classical.choose hex) % p) = p :=
      Nat.sub_add_cancel (le_of_lt hr)
    rw [e2] at e
    exact e.trans ((Nat.modEq_zero_iff_dvd).mpr (dvd_refl p))
  exact step1.trans step2

theorem squarefree_of_mem_prod_aux {k : ℕ} {d : Fin k → ℕ} {j : Fin k}
    (hsq : Squarefree (∏ i, d i)) : Squarefree (d j) := by
  apply Nat.squarefree_of_factorization_le_one
  · intro h0
    exact hsq.ne_zero (Finset.prod_eq_zero (Finset.mem_univ j) h0)
  · intro q
    have hall : ∀ i ∈ (Finset.univ : Finset (Fin k)), d i ≠ 0 := by
      intro i _ hi
      exact hsq.ne_zero (Finset.prod_eq_zero (Finset.mem_univ i) hi)
    have hle : (d j).factorization q ≤ (∏ i, d i).factorization q := by
      rw [Nat.factorization_prod_apply hall]
      exact Finset.single_le_sum (f := fun x => (d x).factorization q)
        (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
    exact le_trans hle (Squarefree.natFactorization_le_one q hsq)

theorem squarefree_lcm_aux {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b) :
    Squarefree (Nat.lcm a b) := by
  apply Nat.squarefree_of_factorization_le_one (Nat.lcm_ne_zero ha.ne_zero hb.ne_zero)
  intro p
  rw [Nat.factorization_lcm ha.ne_zero hb.ne_zero, Finsupp.sup_apply]
  exact sup_le (Squarefree.natFactorization_le_one p ha)
    (Squarefree.natFactorization_le_one p hb)

theorem goodPair_iff_local_aux {k : ℕ} {h d e : Fin k → ℕ} {i : Fin k}
    (hsqd : Squarefree (∏ j, d j)) (hsqe : Squarefree (∏ j, e j)) :
    goodPair h d e i ↔
      ∀ p, Nat.Prime p →
        p ∣ Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) →
        (∀ j, p ∣ Nat.lcm (d j) (e j) → ∀ j', p ∣ Nat.lcm (d j') (e j') →
          h j ≡ h j' [MOD p]) ∧
        (∀ j, p ∣ Nat.lcm (d j) (e j) → ¬ h i ≡ h j [MOD p]) := by
  have hprod_d_ne : (∏ j, d j) ≠ 0 := hsqd.ne_zero
  have hprod_e_ne : (∏ j, e j) ≠ 0 := hsqe.ne_zero
  have hd_ne : ∀ j, d j ≠ 0 :=
    fun j hj => hprod_d_ne (Finset.prod_eq_zero (Finset.mem_univ j) hj)
  have he_ne : ∀ j, e j ≠ 0 :=
    fun j hj => hprod_e_ne (Finset.prod_eq_zero (Finset.mem_univ j) hj)
  have hlc_ne : ∀ j, Nat.lcm (d j) (e j) ≠ 0 :=
    fun j => Nat.lcm_ne_zero (hd_ne j) (he_ne j)
  have hL_ne : Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) ≠ 0 :=
    Finset.lcm_ne_zero_iff.mpr (fun j _ => hlc_ne j)
  have hlc_sq : ∀ j, Squarefree (Nat.lcm (d j) (e j)) := fun j =>
    squarefree_lcm_aux (squarefree_of_mem_prod_aux hsqd) (squarefree_of_mem_prod_aux hsqe)
  constructor
  · intro hgood p hp hpL
    unfold goodPair at hgood
    obtain ⟨w, hw, hcop⟩ := hgood
    constructor
    · intro j hj j' hj'
      have h1 : p ∣ w + h j := dvd_trans hj (hw j)
      have h2 : p ∣ w + h j' := dvd_trans hj' (hw j')
      have e1 : w + h j ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr h1
      have e2 : w + h j' ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr h2
      have e3 : w + h j ≡ w + h j' [MOD p] := e1.trans e2.symm
      exact Nat.ModEq.add_left_cancel' _ e3
    · intro j hj hcon
      have h1 : p ∣ w + h j := dvd_trans hj (hw j)
      have e1 : w + h i ≡ w + h j [MOD p] := Nat.ModEq.add_left _ hcon
      have h2 : p ∣ w + h i :=
        Nat.modEq_zero_iff_dvd.mp (e1.trans (Nat.modEq_zero_iff_dvd.mpr h1))
      have hcop' : Nat.Coprime (w + h i) p := hcop.coprime_dvd_right hpL
      exact ((Nat.Prime.coprime_iff_not_dvd hp).mp hcop'.symm) h2
  · intro hlocal
    have hPprime : ∀ q ∈ (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))).primeFactors,
        Nat.Prime q := fun q hq => Nat.prime_of_mem_primeFactors hq
    obtain ⟨w, hw⟩ := exists_modEq_prime_finset_aux (crtResidue h d e) hPprime
    have hwdiv : ∀ j, Nat.lcm (d j) (e j) ∣ w + h j := by
      intro j
      by_cases h0 : w + h j = 0
      · rw [h0]
        exact dvd_zero _
      · apply (Nat.factorization_le_iff_dvd (hlc_ne j) h0).mp
        refine Finsupp.le_def.mpr ?_
        intro q
        by_cases hqprime : Nat.Prime q
        · by_cases hqdvd : q ∣ Nat.lcm (d j) (e j)
          · have hle1 := Squarefree.natFactorization_le_one q (hlc_sq j)
            have hpos : 1 ≤ (Nat.lcm (d j) (e j)).factorization q :=
              (Nat.Prime.pow_dvd_iff_le_factorization hqprime (hlc_ne j)).mp
                (by rwa [pow_one])
            have hqL : q ∣ Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) :=
              dvd_trans hqdvd (Finset.dvd_lcm (Finset.mem_univ j))
            have hqP : q ∈ (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))).primeFactors :=
              Nat.mem_primeFactors.mpr ⟨hqprime, hqL, hL_ne⟩
            have hwq : w ≡ crtResidue h d e q [MOD q] := hw q hqP
            have hlocq := hlocal q hqprime hqL
            have hres : crtResidue h d e q + h j ≡ 0 [MOD q] :=
              crtResidue_add_aux hqprime hqdvd
                (fun j' hj' => (hlocq.1 j' hj' j hqdvd).symm)
            have hqw : q ∣ w + h j :=
              Nat.modEq_zero_iff_dvd.mp ((Nat.ModEq.add_right _ hwq).trans hres)
            have hpos2 : 1 ≤ (w + h j).factorization q :=
              (Nat.Prime.pow_dvd_iff_le_factorization hqprime h0).mp
                (by rwa [pow_one])
            omega
          · rw [Nat.factorization_eq_zero_of_not_dvd hqdvd]
            exact Nat.zero_le _
        · rw [Nat.factorization_eq_zero_of_not_prime _ hqprime]
          exact Nat.zero_le _
    refine ⟨w, hwdiv, ?_⟩
    by_contra hne
    obtain ⟨p, hpprime, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    have h1 : p ∣ w + h i := dvd_trans hpdvd (Nat.gcd_dvd_left _ _)
    have h2 : p ∣ Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) :=
      dvd_trans hpdvd (Nat.gcd_dvd_right _ _)
    obtain ⟨j, -, hj⟩ := prime_dvd_finset_lcm_aux hpprime h2
    have hloc := hlocal p hpprime h2
    apply hloc.2 j hj
    have hwj : p ∣ w + h j := dvd_trans hj (hwdiv j)
    have e1 : w + h i ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr h1
    have e2 : w + h j ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr hwj
    have e3 : w + h i ≡ w + h j [MOD p] := e1.trans e2.symm
    exact Nat.ModEq.add_left_cancel' _ e3

theorem pairwise_coprime_of_squarefree_prod_aux {k : ℕ} {d : Fin k → ℕ}
    (_hd1 : ∀ i, 1 ≤ d i) (hsq : Squarefree (∏ i, d i))
    {i j : Fin k} (hij : i ≠ j) :
    Nat.Coprime (d i) (d j) := by
  have hjerase : d j ∣ ∏ i' ∈ Finset.univ.erase i, d i' :=
    Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)
  have hprod : ∏ i', d i' = d i * ∏ i' ∈ Finset.univ.erase i, d i' :=
    (Finset.mul_prod_erase Finset.univ d (Finset.mem_univ i)).symm
  have hmul : d i * d j ∣ ∏ i', d i' := by
    rw [hprod]
    exact mul_dvd_mul_left (d i) hjerase
  have hg1 : Nat.gcd (d i) (d j) ∣ d i := Nat.gcd_dvd_left _ _
  have hg2 : Nat.gcd (d i) (d j) ∣ d j := Nat.gcd_dvd_right _ _
  have hgg : Nat.gcd (d i) (d j) * Nat.gcd (d i) (d j) ∣ ∏ i', d i' :=
    dvd_trans (mul_dvd_mul hg1 hg2) hmul
  have hu : IsUnit (Nat.gcd (d i) (d j)) := hsq _ hgg
  exact Nat.isUnit_iff.mp hu

theorem prod_dvd_of_pairwise_coprime_aux :
    ∀ {k : ℕ} {d : Fin k → ℕ} {L : ℕ},
      (∀ i j, i ≠ j → Nat.Coprime (d i) (d j)) →
      (∀ i, d i ∣ L) → ∏ i, d i ∣ L := by
  intro k
  induction k with
  | zero =>
    intro d L _ _
    simp
  | succ k ih =>
    intro d L hcop hdvd
    rw [Fin.prod_univ_succ]
    have hcop_tail : ∀ i j, i ≠ j → Nat.Coprime (Fin.tail d i) (Fin.tail d j) :=
      fun i j hij => hcop i.succ j.succ (fun h => hij (Fin.succ_inj.mp h))
    have hdvd_tail : ∀ i, Fin.tail d i ∣ L := fun i => hdvd i.succ
    have htail : ∏ i, Fin.tail d i ∣ L := ih hcop_tail hdvd_tail
    have hcop0 : Nat.Coprime (d 0) (∏ i, Fin.tail d i) := by
      rw [Nat.coprime_prod_right_iff]
      intro i _
      exact hcop 0 i.succ (Fin.succ_ne_zero i).symm
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop0 (hdvd 0) htail

theorem combined_lcm_eq_aux {k : ℕ} {d e : Fin k → ℕ}
    (hd1 : ∀ i, 1 ≤ d i) (he1 : ∀ i, 1 ≤ e i)
    (hsqd : Squarefree (∏ i, d i)) (hsqe : Squarefree (∏ i, e i)) :
    Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
      = Nat.lcm (∏ i, d i) (∏ i, e i) := by
  apply dvd_antisymm
  · apply Finset.lcm_dvd
    intro j _
    apply Nat.lcm_dvd
    · exact dvd_trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))
        (Nat.dvd_lcm_left _ _)
    · exact dvd_trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))
        (Nat.dvd_lcm_right _ _)
  · apply Nat.lcm_dvd
    · apply prod_dvd_of_pairwise_coprime_aux
        (fun i j hij => pairwise_coprime_of_squarefree_prod_aux hd1 hsqd hij)
      intro j
      exact dvd_trans (Nat.dvd_lcm_left (d j) (e j))
        (Finset.dvd_lcm (Finset.mem_univ j))
    · apply prod_dvd_of_pairwise_coprime_aux
        (fun i j hij => pairwise_coprime_of_squarefree_prod_aux he1 hsqe hij)
      intro j
      exact dvd_trans (Nat.dvd_lcm_right (d j) (e j))
        (Finset.dvd_lcm (Finset.mem_univ j))

theorem goodPair_iff_local_of_products_aux {k : ℕ} {h d e : Fin k → ℕ} {i : Fin k}
    {D E : ℕ} (hD : ∏ j, d j = D) (hE : ∏ j, e j = E)
    (hsqD : Squarefree D) (hsqE : Squarefree E) :
    goodPair h d e i ↔
      ∀ p, Nat.Prime p → p ∣ Nat.lcm D E →
        (∀ j, p ∣ Nat.lcm (d j) (e j) → ∀ j', p ∣ Nat.lcm (d j') (e j') →
          h j ≡ h j' [MOD p]) ∧
        (∀ j, p ∣ Nat.lcm (d j) (e j) → ¬ h i ≡ h j [MOD p]) := by
  have hsqd : Squarefree (∏ j, d j) := by
    rw [hD]
    exact hsqD
  have hsqe : Squarefree (∏ j, e j) := by
    rw [hE]
    exact hsqE
  have hd1 : ∀ j, 1 ≤ d j := by
    intro j
    by_contra hc
    have hj0 : d j = 0 := by omega
    have h0 : ∏ j', d j' = 0 := Finset.prod_eq_zero (Finset.mem_univ j) hj0
    rw [hD] at h0
    exact hsqD.ne_zero h0
  have he1 : ∀ j, 1 ≤ e j := by
    intro j
    by_contra hc
    have hj0 : e j = 0 := by omega
    have h0 : ∏ j', e j' = 0 := Finset.prod_eq_zero (Finset.mem_univ j) hj0
    rw [hE] at h0
    exact hsqE.ne_zero h0
  have hcomb : Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) = Nat.lcm D E := by
    rw [← hD, ← hE]
    exact combined_lcm_eq_aux hd1 he1 hsqd hsqe
  rw [goodPair_iff_local_aux hsqd hsqe, hcomb]

theorem mem_localGoodChoiceFinset_aux {k : ℕ} {h : Fin k → ℕ} {i : Fin k} {p : ℕ}
    {hd he : Prop} [Decidable hd] [Decidable he]
    {ab : Option (Fin k) × Option (Fin k)} :
    ab ∈ localGoodChoiceFinset h i p hd he ↔
      (ab.1.isSome ↔ hd) ∧ (ab.2.isSome ↔ he) ∧
      (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
        (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
      (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p]) := by
  simp only [localGoodChoiceFinset, Finset.mem_filter, Finset.mem_univ, true_and]

theorem prime_dvd_finset_prod_aux {ι : Type*} {s : Finset ι} {f : ι → ℕ} {p : ℕ}
    (hp : Nat.Prime p) (h : p ∣ ∏ i ∈ s, f i) : ∃ j ∈ s, p ∣ f j := by
  induction s using Finset.induction with
  | empty =>
    rw [Finset.prod_empty] at h
    exact absurd h hp.not_dvd_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha] at h
    rcases hp.dvd_mul.mp h with h1 | h2
    · exact ⟨a, Finset.mem_insert_self a s, h1⟩
    · obtain ⟨j, hj, hjf⟩ := ih h2
      exact ⟨j, Finset.mem_insert_of_mem hj, hjf⟩

theorem exists_unique_coord_of_squarefree_prod_aux {k : ℕ} {d : Fin k → ℕ} {p : ℕ}
    (hd1 : ∀ j, 1 ≤ d j) (hsq : Squarefree (∏ j, d j)) (hp : Nat.Prime p)
    (hpd : p ∣ ∏ j, d j) : ∃! j, p ∣ d j := by
  obtain ⟨j₀, -, hj₀⟩ := prime_dvd_finset_prod_aux hp hpd
  refine ⟨j₀, hj₀, ?_⟩
  intro y hy
  by_contra hne
  have hcop := pairwise_coprime_of_squarefree_prod_aux hd1 hsq hne
  have hdiv : p ∣ Nat.gcd (d y) (d j₀) := Nat.dvd_gcd hy hj₀
  have hgcd : Nat.gcd (d y) (d j₀) = 1 := hcop
  rw [hgcd] at hdiv
  exact hp.not_dvd_one hdiv

theorem coordOf_eq_some_aux {k : ℕ} {d : Fin k → ℕ} {p : ℕ} {j : Fin k}
    (h : coordOf d p = some j) : p ∣ d j := by
  unfold coordOf at h
  by_cases hex : ∃ j, p ∣ d j
  · rw [dif_pos hex] at h
    have hc : Classical.choose hex = j := Option.some.inj h
    rw [← hc]
    exact Classical.choose_spec hex
  · rw [dif_neg hex] at h
    simp at h

theorem coordOf_some_of_dvd_aux {k : ℕ} {d : Fin k → ℕ} {p : ℕ}
    (hd1 : ∀ j, 1 ≤ d j) (hsq : Squarefree (∏ j, d j)) (hp : Nat.Prime p)
    {j : Fin k} (hj : p ∣ d j) : coordOf d p = some j := by
  have hpd : p ∣ ∏ j, d j :=
    dvd_trans hj (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))
  obtain ⟨j₀, hj₀, huniq⟩ := exists_unique_coord_of_squarefree_prod_aux hd1 hsq hp hpd
  have hjj : j = j₀ := huniq j hj
  have hex : ∃ j', p ∣ d j' := ⟨j, hj⟩
  have hc : Classical.choose hex = j := by
    have h1 := Classical.choose_spec hex
    have h2 := huniq _ h1
    rw [← hjj] at h2
    exact h2
  unfold coordOf
  rw [dif_pos hex, hc]

theorem coordOf_none_of_not_dvd_aux {k : ℕ} {d : Fin k → ℕ} {p : ℕ}
    (h : ¬ ∃ j, p ∣ d j) : coordOf d p = none := by
  unfold coordOf
  rw [dif_neg h]

theorem coordOf_isSome_aux {k : ℕ} {d : Fin k → ℕ} {p : ℕ} :
    (coordOf d p).isSome ↔ ∃ j, p ∣ d j := by
  unfold coordOf
  by_cases hex : ∃ j, p ∣ d j
  · rw [dif_pos hex]
    simp [hex]
  · rw [dif_neg hex]
    simp [hex]

theorem mem_primeFactors_lcm_aux {D E p : ℕ} (hD : D ≠ 0) (hE : E ≠ 0) :
    p ∈ (Nat.lcm D E).primeFactors ↔ Nat.Prime p ∧ (p ∣ D ∨ p ∣ E) := by
  rw [Nat.mem_primeFactors]
  constructor
  · rintro ⟨hp, hpdvd, -⟩
    refine ⟨hp, ?_⟩
    rcases prime_dvd_lcm_aux hp hpdvd with h | h
    · exact Or.inl h
    · exact Or.inr h
  · rintro ⟨hp, h | h⟩
    · exact ⟨hp, dvd_trans h (Nat.dvd_lcm_left D E), Nat.lcm_ne_zero hD hE⟩
    · exact ⟨hp, dvd_trans h (Nat.dvd_lcm_right D E), Nat.lcm_ne_zero hD hE⟩

theorem piChoiceFun_apply_aux {k : ℕ} {s : Finset ℕ}
    {f : ∀ p, p ∈ s → Option (Fin k) × Option (Fin k)} {p : ℕ} (hp : p ∈ s) :
    piChoiceFun s f p = f p hp := by
  unfold piChoiceFun
  rw [dif_pos hp]

theorem solution {k : ℕ} {h : Fin k → ℕ} {R : ℕ} {i : Fin k}
    {D E : ℕ} (hsqD : Squarefree D) (hsqE : Squarefree E)
    (hDR : D ≤ R) (hER : E ≤ R) :
    ((((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
        (fun d => ∏ i, d i ≤ R) ×ˢ
      (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
        (fun d => ∏ i, d i ≤ R)).filter
      (fun p => ∏ j, p.1 j = D ∧ ∏ j, p.2 j = E ∧
        (∃ w, (∀ j, Nat.lcm (p.1 j) (p.2 j) ∣ w + h j) ∧
          Nat.Coprime (w + h i)
            (Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)))) ∧
        Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = Nat.lcm D E))).card
      = ((Nat.lcm D E).primeFactors.pi
          (fun p => (Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter
            (fun ab => (ab.1.isSome ↔ p ∣ D) ∧ (ab.2.isSome ↔ p ∣ E) ∧
              (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
                (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
              (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])))).card := by
  classical
  have hD0 : D ≠ 0 := hsqD.ne_zero
  have hE0 : E ≠ 0 := hsqE.ne_zero
  have hL0 : Nat.lcm D E ≠ 0 := Nat.lcm_ne_zero hD0 hE0
  have hprime : ∀ p ∈ (Nat.lcm D E).primeFactors, Nat.Prime p := by
    intro p hp
    exact (Nat.mem_primeFactors.mp hp).1
  have memF : ∀ de : (Fin k → ℕ) × (Fin k → ℕ),
      de ∈ ((tupleSupport k R ×ˢ tupleSupport k R).filter
        (fun p => ∏ j, p.1 j = D ∧ ∏ j, p.2 j = E ∧ goodPair h p.1 p.2 i ∧
          Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = Nat.lcm D E)) →
      de.1 ∈ tupleSupport k R ∧ de.2 ∈ tupleSupport k R ∧
      ∏ j, de.1 j = D ∧ ∏ j, de.2 j = E ∧ goodPair h de.1 de.2 i ∧
      Finset.lcm Finset.univ (fun j => Nat.lcm (de.1 j) (de.2 j)) = Nat.lcm D E := by
    intro de hde
    rw [Finset.mem_filter, Finset.mem_product] at hde
    obtain ⟨⟨h1, h2⟩, hp1, hp2, hg, hl⟩ := hde
    exact ⟨h1, h2, hp1, hp2, hg, hl⟩
  have fwd_char1 : ∀ de : (Fin k → ℕ) × (Fin k → ℕ),
      ∀ hde : de ∈ ((tupleSupport k R ×ˢ tupleSupport k R).filter
        (fun p => ∏ j, p.1 j = D ∧ ∏ j, p.2 j = E ∧ goodPair h p.1 p.2 i ∧
          Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = Nat.lcm D E)),
      ∀ p : ℕ, ∀ hp : p ∈ (Nat.lcm D E).primeFactors, ∀ j : Fin k,
        coordOf de.1 p = some j ↔ p ∣ de.1 j := by
    intro de hde p hp j
    obtain ⟨hs1, -, hp1, -, -, -⟩ := memF de hde
    have hsup1 := (mem_tupleSupport_aux.mp hs1).1
    have hsq1 : Squarefree (∏ j, de.1 j) := by rw [hp1]; exact hsqD
    constructor
    · intro hc
      exact coordOf_eq_some_aux hc
    · intro hj
      exact coordOf_some_of_dvd_aux hsup1 hsq1 (hprime p hp) hj
  have fwd_char2 : ∀ de : (Fin k → ℕ) × (Fin k → ℕ),
      ∀ hde : de ∈ ((tupleSupport k R ×ˢ tupleSupport k R).filter
        (fun p => ∏ j, p.1 j = D ∧ ∏ j, p.2 j = E ∧ goodPair h p.1 p.2 i ∧
          Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = Nat.lcm D E)),
      ∀ p : ℕ, ∀ hp : p ∈ (Nat.lcm D E).primeFactors, ∀ j : Fin k,
        coordOf de.2 p = some j ↔ p ∣ de.2 j := by
    intro de hde p hp j
    obtain ⟨-, hs2, -, hp2, -, -⟩ := memF de hde
    have hsup2 := (mem_tupleSupport_aux.mp hs2).1
    have hsq2 : Squarefree (∏ j, de.2 j) := by rw [hp2]; exact hsqE
    constructor
    · intro hc
      exact coordOf_eq_some_aux hc
    · intro hj
      exact coordOf_some_of_dvd_aux hsup2 hsq2 (hprime p hp) hj
  have fwd_isSome1 : ∀ de : (Fin k → ℕ) × (Fin k → ℕ),
      ∀ hde : de ∈ ((tupleSupport k R ×ˢ tupleSupport k R).filter
        (fun p => ∏ j, p.1 j = D ∧ ∏ j, p.2 j = E ∧ goodPair h p.1 p.2 i ∧
          Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = Nat.lcm D E)),
      ∀ p : ℕ, ∀ hp : p ∈ (Nat.lcm D E).primeFactors,
        (coordOf de.1 p).isSome ↔ p ∣ D := by
    intro de hde p hp
    obtain ⟨-, -, hp1, -, -, -⟩ := memF de hde
    rw [coordOf_isSome_aux]
    constructor
    · rintro ⟨j, hj⟩
      have hprod : p ∣ ∏ j, de.1 j :=
        dvd_trans hj (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))
      rw [hp1] at hprod
      exact hprod
    · intro hpd
      have hprod : p ∣ ∏ j, de.1 j := by rw [hp1]; exact hpd
      obtain ⟨j, -, hj⟩ := prime_dvd_finset_prod_aux (hprime p hp) hprod
      exact ⟨j, hj⟩
  have fwd_isSome2 : ∀ de : (Fin k → ℕ) × (Fin k → ℕ),
      ∀ hde : de ∈ ((tupleSupport k R ×ˢ tupleSupport k R).filter
        (fun p => ∏ j, p.1 j = D ∧ ∏ j, p.2 j = E ∧ goodPair h p.1 p.2 i ∧
          Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = Nat.lcm D E)),
      ∀ p : ℕ, ∀ hp : p ∈ (Nat.lcm D E).primeFactors,
        (coordOf de.2 p).isSome ↔ p ∣ E := by
    intro de hde p hp
    obtain ⟨-, -, -, hp2, -, -⟩ := memF de hde
    rw [coordOf_isSome_aux]
    constructor
    · rintro ⟨j, hj⟩
      have hprod : p ∣ ∏ j, de.2 j :=
        dvd_trans hj (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))
      rw [hp2] at hprod
      exact hprod
    · intro hpd
      have hprod : p ∣ ∏ j, de.2 j := by rw [hp2]; exact hpd
      obtain ⟨j, -, hj⟩ := prime_dvd_finset_prod_aux (hprime p hp) hprod
      exact ⟨j, hj⟩
  apply Finset.card_bij (fun de _ p _ => (coordOf de.1 p, coordOf de.2 p))
  · intro de hde
    show (fun p _ => (coordOf de.1 p, coordOf de.2 p)) ∈
      (Nat.lcm D E).primeFactors.pi
        (fun p => localGoodChoiceFinset h i p (p ∣ D) (p ∣ E))
    rw [Finset.mem_pi]
    intro p hp
    show (coordOf de.1 p, coordOf de.2 p) ∈
      localGoodChoiceFinset h i p (p ∣ D) (p ∣ E)
    rw [mem_localGoodChoiceFinset_aux]
    obtain ⟨-, -, hp1, hp2, hg, -⟩ := memF de hde
    have hpL : p ∣ Nat.lcm D E := (Nat.mem_primeFactors.mp hp).2.1
    have hloc := (goodPair_iff_local_of_products_aux hp1 hp2 hsqD hsqE).mp hg p (hprime p hp) hpL
    refine ⟨fwd_isSome1 de hde p hp, fwd_isSome2 de hde p hp, ?_, ?_⟩
    · intro j j' hj hj'
      have hlj : p ∣ Nat.lcm (de.1 j) (de.2 j) := by
        rcases hj with hj | hj
        · exact dvd_trans ((fwd_char1 de hde p hp j).mp hj) (Nat.dvd_lcm_left _ _)
        · exact dvd_trans ((fwd_char2 de hde p hp j).mp hj) (Nat.dvd_lcm_right _ _)
      have hlj' : p ∣ Nat.lcm (de.1 j') (de.2 j') := by
        rcases hj' with hj' | hj'
        · exact dvd_trans ((fwd_char1 de hde p hp j').mp hj') (Nat.dvd_lcm_left _ _)
        · exact dvd_trans ((fwd_char2 de hde p hp j').mp hj') (Nat.dvd_lcm_right _ _)
      exact hloc.1 j hlj j' hlj'
    · intro j hj
      have hlj : p ∣ Nat.lcm (de.1 j) (de.2 j) := by
        rcases hj with hj | hj
        · exact dvd_trans ((fwd_char1 de hde p hp j).mp hj) (Nat.dvd_lcm_left _ _)
        · exact dvd_trans ((fwd_char2 de hde p hp j).mp hj) (Nat.dvd_lcm_right _ _)
      exact hloc.2 j hlj
  · intro de₁ h₁ de₂ h₂ heq
    have hpt : ∀ p (hp : p ∈ (Nat.lcm D E).primeFactors),
        coordOf de₁.1 p = coordOf de₂.1 p ∧
        coordOf de₁.2 p = coordOf de₂.2 p := by
      intro p hp
      have hfun := congrFun (congrFun heq p) hp
      exact ⟨congrArg Prod.fst hfun, congrArg Prod.snd hfun⟩
    have hpf1 : ∀ j : Fin k, (de₁.1 j).primeFactors =
        (Nat.lcm D E).primeFactors.filter (fun p => coordOf de₁.1 p = some j) := by
      intro j
      obtain ⟨hs1, -, hp1, -, -, -⟩ := memF de₁ h₁
      apply Finset.ext
      intro p
      rw [Finset.mem_filter]
      constructor
      · intro hpm
        have hpp : Nat.Prime p := (Nat.mem_primeFactors.mp hpm).1
        have hpdvd : p ∣ de₁.1 j := (Nat.mem_primeFactors.mp hpm).2.1
        have hdj0 : de₁.1 j ≠ 0 := by
          have h1 := (mem_tupleSupport_aux.mp hs1).1 j
          omega
        have hps : p ∈ (Nat.lcm D E).primeFactors := by
          rw [Nat.mem_primeFactors]
          refine ⟨hpp, ?_, hL0⟩
          have hpd : p ∣ D := by
            have h1 : p ∣ ∏ j, de₁.1 j :=
              dvd_trans hpdvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))
            rw [hp1] at h1
            exact h1
          exact dvd_trans hpd (Nat.dvd_lcm_left D E)
        exact ⟨hps, (fwd_char1 de₁ h₁ p hps j).mpr hpdvd⟩
      · rintro ⟨hps, hc⟩
        have hpdvd : p ∣ de₁.1 j := (fwd_char1 de₁ h₁ p hps j).mp hc
        have hdj0 : de₁.1 j ≠ 0 := by
          have h1 := (mem_tupleSupport_aux.mp hs1).1 j
          omega
        rw [Nat.mem_primeFactors]
        exact ⟨hprime p hps, hpdvd, hdj0⟩
    have hpf2 : ∀ j : Fin k, (de₂.1 j).primeFactors =
        (Nat.lcm D E).primeFactors.filter (fun p => coordOf de₂.1 p = some j) := by
      intro j
      obtain ⟨hs2, -, hp2, -, -, -⟩ := memF de₂ h₂
      apply Finset.ext
      intro p
      rw [Finset.mem_filter]
      constructor
      · intro hpm
        have hpp : Nat.Prime p := (Nat.mem_primeFactors.mp hpm).1
        have hpdvd : p ∣ de₂.1 j := (Nat.mem_primeFactors.mp hpm).2.1
        have hdj0 : de₂.1 j ≠ 0 := by
          have h1 := (mem_tupleSupport_aux.mp hs2).1 j
          omega
        have hps : p ∈ (Nat.lcm D E).primeFactors := by
          rw [Nat.mem_primeFactors]
          refine ⟨hpp, ?_, hL0⟩
          have hpd : p ∣ D := by
            have h1 : p ∣ ∏ j, de₂.1 j :=
              dvd_trans hpdvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))
            rw [hp2] at h1
            exact h1
          exact dvd_trans hpd (Nat.dvd_lcm_left D E)
        exact ⟨hps, (fwd_char1 de₂ h₂ p hps j).mpr hpdvd⟩
      · rintro ⟨hps, hc⟩
        have hpdvd : p ∣ de₂.1 j := (fwd_char1 de₂ h₂ p hps j).mp hc
        have hdj0 : de₂.1 j ≠ 0 := by
          have h1 := (mem_tupleSupport_aux.mp hs2).1 j
          omega
        rw [Nat.mem_primeFactors]
        exact ⟨hprime p hps, hpdvd, hdj0⟩
    have hcoord1 : ∀ j : Fin k, de₁.1 j = de₂.1 j := by
      intro j
      obtain ⟨-, -, hp1, -, -, -⟩ := memF de₁ h₁
      obtain ⟨-, -, hp2, -, -, -⟩ := memF de₂ h₂
      have hsq1 : Squarefree (de₁.1 j) :=
        squarefree_of_mem_prod_aux (by rw [hp1]; exact hsqD)
      have hsq2 : Squarefree (de₂.1 j) :=
        squarefree_of_mem_prod_aux (by rw [hp2]; exact hsqD)
      calc de₁.1 j = ∏ p ∈ (de₁.1 j).primeFactors, p :=
            (Nat.prod_primeFactors_of_squarefree hsq1).symm
        _ = ∏ p ∈ (Nat.lcm D E).primeFactors.filter
              (fun p => coordOf de₁.1 p = some j), p := by rw [hpf1 j]
        _ = ∏ p ∈ (Nat.lcm D E).primeFactors.filter
              (fun p => coordOf de₂.1 p = some j), p := by
            apply Finset.prod_congr _ (fun p _ => rfl)
            apply Finset.filter_congr
            intro p hp
            rw [(hpt p hp).1]
        _ = ∏ p ∈ (de₂.1 j).primeFactors, p := by rw [hpf2 j]
        _ = de₂.1 j := Nat.prod_primeFactors_of_squarefree hsq2
    have hcoord2 : ∀ j : Fin k, de₁.2 j = de₂.2 j := by
      intro j
      obtain ⟨-, -, -, hp1, -, -⟩ := memF de₁ h₁
      obtain ⟨-, -, -, hp2, -, -⟩ := memF de₂ h₂
      have hsq1 : Squarefree (de₁.2 j) :=
        squarefree_of_mem_prod_aux (by rw [hp1]; exact hsqE)
      have hsq2 : Squarefree (de₂.2 j) :=
        squarefree_of_mem_prod_aux (by rw [hp2]; exact hsqE)
      have hpf1' : (de₁.2 j).primeFactors =
          (Nat.lcm D E).primeFactors.filter (fun p => coordOf de₁.2 p = some j) := by
        apply Finset.ext
        intro p
        rw [Finset.mem_filter]
        constructor
        · intro hpm
          have hpp : Nat.Prime p := (Nat.mem_primeFactors.mp hpm).1
          have hpdvd : p ∣ de₁.2 j := (Nat.mem_primeFactors.mp hpm).2.1
          have hdj0 : de₁.2 j ≠ 0 := by
            have h1 := (mem_tupleSupport_aux.mp (memF de₁ h₁).2.1).1 j
            omega
          have hps : p ∈ (Nat.lcm D E).primeFactors := by
            rw [Nat.mem_primeFactors]
            refine ⟨hpp, ?_, hL0⟩
            have hpd : p ∣ E := by
              have h1 : p ∣ ∏ j, de₁.2 j :=
                dvd_trans hpdvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))
              rw [hp1] at h1
              exact h1
            exact dvd_trans hpd (Nat.dvd_lcm_right D E)
          exact ⟨hps, (fwd_char2 de₁ h₁ p hps j).mpr hpdvd⟩
        · rintro ⟨hps, hc⟩
          have hpdvd : p ∣ de₁.2 j := (fwd_char2 de₁ h₁ p hps j).mp hc
          have hdj0 : de₁.2 j ≠ 0 := by
            have h1 := (mem_tupleSupport_aux.mp (memF de₁ h₁).2.1).1 j
            omega
          rw [Nat.mem_primeFactors]
          exact ⟨hprime p hps, hpdvd, hdj0⟩
      have hpf2' : (de₂.2 j).primeFactors =
          (Nat.lcm D E).primeFactors.filter (fun p => coordOf de₂.2 p = some j) := by
        apply Finset.ext
        intro p
        rw [Finset.mem_filter]
        constructor
        · intro hpm
          have hpp : Nat.Prime p := (Nat.mem_primeFactors.mp hpm).1
          have hpdvd : p ∣ de₂.2 j := (Nat.mem_primeFactors.mp hpm).2.1
          have hdj0 : de₂.2 j ≠ 0 := by
            have h1 := (mem_tupleSupport_aux.mp (memF de₂ h₂).2.1).1 j
            omega
          have hps : p ∈ (Nat.lcm D E).primeFactors := by
            rw [Nat.mem_primeFactors]
            refine ⟨hpp, ?_, hL0⟩
            have hpd : p ∣ E := by
              have h1 : p ∣ ∏ j, de₂.2 j :=
                dvd_trans hpdvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))
              rw [hp2] at h1
              exact h1
            exact dvd_trans hpd (Nat.dvd_lcm_right D E)
          exact ⟨hps, (fwd_char2 de₂ h₂ p hps j).mpr hpdvd⟩
        · rintro ⟨hps, hc⟩
          have hpdvd : p ∣ de₂.2 j := (fwd_char2 de₂ h₂ p hps j).mp hc
          have hdj0 : de₂.2 j ≠ 0 := by
            have h1 := (mem_tupleSupport_aux.mp (memF de₂ h₂).2.1).1 j
            omega
          rw [Nat.mem_primeFactors]
          exact ⟨hprime p hps, hpdvd, hdj0⟩
      calc de₁.2 j = ∏ p ∈ (de₁.2 j).primeFactors, p :=
            (Nat.prod_primeFactors_of_squarefree hsq1).symm
        _ = ∏ p ∈ (Nat.lcm D E).primeFactors.filter
              (fun p => coordOf de₁.2 p = some j), p := by rw [hpf1']
        _ = ∏ p ∈ (Nat.lcm D E).primeFactors.filter
              (fun p => coordOf de₂.2 p = some j), p := by
            apply Finset.prod_congr _ (fun p _ => rfl)
            apply Finset.filter_congr
            intro p hp
            rw [(hpt p hp).2]
        _ = ∏ p ∈ (de₂.2 j).primeFactors, p := by rw [hpf2']
        _ = de₂.2 j := Nat.prod_primeFactors_of_squarefree hsq2
    exact Prod.ext (funext fun j => hcoord1 j) (funext fun j => hcoord2 j)
  · intro f hf
    set Ff := piChoiceFun (Nat.lcm D E).primeFactors f with hFf_def
    have hFf : ∀ p (hp : p ∈ (Nat.lcm D E).primeFactors), Ff p = f p hp := by
      intro p hp
      rw [hFf_def]
      exact piChoiceFun_apply_aux hp
    set dd := backwardD (Nat.lcm D E).primeFactors Ff with hdd_def
    set ee := backwardE (Nat.lcm D E).primeFactors Ff with hee_def
    have hFmem : ∀ p (hp : p ∈ (Nat.lcm D E).primeFactors),
        (((Ff p).1.isSome = true ↔ p ∣ D) ∧ ((Ff p).2.isSome = true ↔ p ∣ E) ∧
        (∀ j j', ((Ff p).1 = some j ∨ (Ff p).2 = some j) →
          ((Ff p).1 = some j' ∨ (Ff p).2 = some j') → h j ≡ h j' [MOD p]) ∧
        (∀ j, ((Ff p).1 = some j ∨ (Ff p).2 = some j) →
          ¬ h i ≡ h j [MOD p])) := by
      intro p hp
      rw [hFf p hp]
      have hfm : f p hp ∈ localGoodChoiceFinset h i p (p ∣ D) (p ∣ E) := by
        have hmem := hf
        rw [Finset.mem_pi] at hmem
        exact hmem p hp
      rwa [mem_localGoodChoiceFinset_aux] at hfm
    have hdvd : ∀ p ∈ (Nat.lcm D E).primeFactors, ∀ j, (Ff p).1 = some j → p ∣ dd j := by
      intro p hp j hj
      have hfac : (if (Ff p).1 = some j then p else 1) = p := if_pos hj
      have hdvd0 : (if (Ff p).1 = some j then p else 1) ∣ dd j := by
        rw [hdd_def]
        show (if (Ff p).1 = some j then p else 1) ∣
          ∏ p' ∈ (Nat.lcm D E).primeFactors, (if (Ff p').1 = some j then p' else 1)
        exact Finset.dvd_prod_of_mem _ hp
      rwa [hfac] at hdvd0
    have hedvd : ∀ p ∈ (Nat.lcm D E).primeFactors, ∀ j, (Ff p).2 = some j → p ∣ ee j := by
      intro p hp j hj
      have hfac : (if (Ff p).2 = some j then p else 1) = p := if_pos hj
      have hdvd0 : (if (Ff p).2 = some j then p else 1) ∣ ee j := by
        rw [hee_def]
        show (if (Ff p).2 = some j then p else 1) ∣
          ∏ p' ∈ (Nat.lcm D E).primeFactors, (if (Ff p').2 = some j then p' else 1)
        exact Finset.dvd_prod_of_mem _ hp
      rwa [hfac] at hdvd0
    have hdvd_rev : ∀ p ∈ (Nat.lcm D E).primeFactors, ∀ j, p ∣ dd j → (Ff p).1 = some j := by
      intro p hp j hdvd
      have hpp : Nat.Prime p := hprime p hp
      have hdvd' : p ∣ ∏ p' ∈ (Nat.lcm D E).primeFactors,
          (if (Ff p').1 = some j then p' else 1) := by
        rw [hdd_def] at hdvd
        exact hdvd
      obtain ⟨p', hp', hpf⟩ := prime_dvd_finset_prod_aux hpp hdvd'
      by_cases hc : (Ff p').1 = some j
      · rw [if_pos hc] at hpf
        have hp'prime : Nat.Prime p' := hprime p' hp'
        rcases (Nat.dvd_prime hp'prime).mp hpf with h1 | h1
        · exact absurd h1 hpp.ne_one
        · rw [← h1] at hc
          exact hc
      · rw [if_neg hc] at hpf
        exact (hpp.not_dvd_one hpf).elim
    have hedvd_rev : ∀ p ∈ (Nat.lcm D E).primeFactors, ∀ j, p ∣ ee j → (Ff p).2 = some j := by
      intro p hp j hedvd
      have hpp : Nat.Prime p := hprime p hp
      have hedvd' : p ∣ ∏ p' ∈ (Nat.lcm D E).primeFactors,
          (if (Ff p').2 = some j then p' else 1) := by
        rw [hee_def] at hedvd
        exact hedvd
      obtain ⟨p', hp', hpf⟩ := prime_dvd_finset_prod_aux hpp hedvd'
      by_cases hc : (Ff p').2 = some j
      · rw [if_pos hc] at hpf
        have hp'prime : Nat.Prime p' := hprime p' hp'
        rcases (Nat.dvd_prime hp'prime).mp hpf with h1 | h1
        · exact absurd h1 hpp.ne_one
        · rw [← h1] at hc
          exact hc
      · rw [if_neg hc] at hpf
        exact (hpp.not_dvd_one hpf).elim
    have hfilterD : (Nat.lcm D E).primeFactors.filter (fun p => p ∣ D) = D.primeFactors := by
      apply Finset.ext
      intro p
      rw [Finset.mem_filter]
      constructor
      · rintro ⟨hps, hpd⟩
        rw [Nat.mem_primeFactors]
        exact ⟨hprime p hps, hpd, hD0⟩
      · intro hpm
        have hpp : Nat.Prime p := (Nat.mem_primeFactors.mp hpm).1
        have hpd : p ∣ D := (Nat.mem_primeFactors.mp hpm).2.1
        refine ⟨?_, hpd⟩
        rw [Nat.mem_primeFactors]
        exact ⟨hpp, dvd_trans hpd (Nat.dvd_lcm_left D E), hL0⟩
    have hfilterE : (Nat.lcm D E).primeFactors.filter (fun p => p ∣ E) = E.primeFactors := by
      apply Finset.ext
      intro p
      rw [Finset.mem_filter]
      constructor
      · rintro ⟨hps, hpd⟩
        rw [Nat.mem_primeFactors]
        exact ⟨hprime p hps, hpd, hE0⟩
      · intro hpm
        have hpp : Nat.Prime p := (Nat.mem_primeFactors.mp hpm).1
        have hpd : p ∣ E := (Nat.mem_primeFactors.mp hpm).2.1
        refine ⟨?_, hpd⟩
        rw [Nat.mem_primeFactors]
        exact ⟨hpp, dvd_trans hpd (Nat.dvd_lcm_right D E), hL0⟩
    have hprod_dd : ∏ j, dd j = D := by
      calc ∏ j, dd j
          = ∏ j, ∏ p ∈ (Nat.lcm D E).primeFactors,
              (if (Ff p).1 = some j then p else 1) := by
            apply Finset.prod_congr rfl
            intro j _
            rfl
        _ = ∏ p ∈ (Nat.lcm D E).primeFactors, ∏ j,
              (if (Ff p).1 = some j then p else 1) := Finset.prod_comm
        _ = ∏ p ∈ (Nat.lcm D E).primeFactors, (if (Ff p).1.isSome then p else 1) := by
            apply Finset.prod_congr rfl
            intro p hp
            cases hFp : (Ff p).1 with
            | none =>
              have h1 : ∀ j : Fin k,
                  (if (none : Option (Fin k)) = some j then p else 1) = 1 := by
                intro j
                exact if_neg (fun h => Option.some_ne_none j h.symm)
              rw [Finset.prod_congr rfl (fun j _ => h1 j), Finset.prod_const_one]
              rfl
            | some j₀ =>
              have h1 : ∀ b ∈ (Finset.univ : Finset (Fin k)), b ≠ j₀ →
                  (if (some j₀ : Option (Fin k)) = some b then p else 1) = 1 := by
                intro b _ hb
                exact if_neg (fun hcon => hb (Option.some.inj hcon).symm)
              have h2 : j₀ ∉ (Finset.univ : Finset (Fin k)) →
                  (if (some j₀ : Option (Fin k)) = some j₀ then p else 1) = 1 :=
                fun hcon => absurd (Finset.mem_univ j₀) hcon
              rw [Finset.prod_eq_single j₀ h1 h2, if_pos rfl]
              rfl
        _ = ∏ p ∈ (Nat.lcm D E).primeFactors.filter (fun p => (Ff p).1.isSome), p := by
            rw [Finset.prod_filter]
        _ = ∏ p ∈ (Nat.lcm D E).primeFactors.filter (fun p => p ∣ D), p := by
            apply Finset.prod_congr _ (fun p _ => rfl)
            apply Finset.filter_congr
            intro p hp
            exact (hFmem p hp).1
        _ = ∏ p ∈ D.primeFactors, p := by rw [hfilterD]
        _ = D := Nat.prod_primeFactors_of_squarefree hsqD
    have hprod_ee : ∏ j, ee j = E := by
      calc ∏ j, ee j
          = ∏ j, ∏ p ∈ (Nat.lcm D E).primeFactors,
              (if (Ff p).2 = some j then p else 1) := by
            apply Finset.prod_congr rfl
            intro j _
            rfl
        _ = ∏ p ∈ (Nat.lcm D E).primeFactors, ∏ j,
              (if (Ff p).2 = some j then p else 1) := Finset.prod_comm
        _ = ∏ p ∈ (Nat.lcm D E).primeFactors, (if (Ff p).2.isSome then p else 1) := by
            apply Finset.prod_congr rfl
            intro p hp
            cases hFp : (Ff p).2 with
            | none =>
              have h1 : ∀ j : Fin k,
                  (if (none : Option (Fin k)) = some j then p else 1) = 1 := by
                intro j
                exact if_neg (fun h => Option.some_ne_none j h.symm)
              rw [Finset.prod_congr rfl (fun j _ => h1 j), Finset.prod_const_one]
              rfl
            | some j₀ =>
              have h1 : ∀ b ∈ (Finset.univ : Finset (Fin k)), b ≠ j₀ →
                  (if (some j₀ : Option (Fin k)) = some b then p else 1) = 1 := by
                intro b _ hb
                exact if_neg (fun hcon => hb (Option.some.inj hcon).symm)
              have h2 : j₀ ∉ (Finset.univ : Finset (Fin k)) →
                  (if (some j₀ : Option (Fin k)) = some j₀ then p else 1) = 1 :=
                fun hcon => absurd (Finset.mem_univ j₀) hcon
              rw [Finset.prod_eq_single j₀ h1 h2, if_pos rfl]
              rfl
        _ = ∏ p ∈ (Nat.lcm D E).primeFactors.filter (fun p => (Ff p).2.isSome), p := by
            rw [Finset.prod_filter]
        _ = ∏ p ∈ (Nat.lcm D E).primeFactors.filter (fun p => p ∣ E), p := by
            apply Finset.prod_congr _ (fun p _ => rfl)
            apply Finset.filter_congr
            intro p hp
            exact (hFmem p hp).2.1
        _ = ∏ p ∈ E.primeFactors, p := by rw [hfilterE]
        _ = E := Nat.prod_primeFactors_of_squarefree hsqE
    have h1d : ∀ j, 1 ≤ dd j := by
      intro j
      rw [hdd_def]
      show 1 ≤ ∏ p ∈ (Nat.lcm D E).primeFactors, (if (Ff p).1 = some j then p else 1)
      apply Finset.one_le_prod'
      intro p' hp'
      split_ifs with hc
      · exact (hprime p' hp').one_lt.le
      · exact le_refl 1
    have h1e : ∀ j, 1 ≤ ee j := by
      intro j
      rw [hee_def]
      show 1 ≤ ∏ p ∈ (Nat.lcm D E).primeFactors, (if (Ff p).2 = some j then p else 1)
      apply Finset.one_le_prod'
      intro p' hp'
      split_ifs with hc
      · exact (hprime p' hp').one_lt.le
      · exact le_refl 1
    have hdle : ∀ j, dd j ≤ R := by
      intro j
      calc dd j ≤ ∏ j', dd j' :=
            Finset.single_le_prod' (fun j' _ => h1d j') (Finset.mem_univ j)
        _ = D := hprod_dd
        _ ≤ R := hDR
    have hele : ∀ j, ee j ≤ R := by
      intro j
      calc ee j ≤ ∏ j', ee j' :=
            Finset.single_le_prod' (fun j' _ => h1e j') (Finset.mem_univ j)
        _ = E := hprod_ee
        _ ≤ R := hER
    have hprodle_dd : ∏ j, dd j ≤ R := by rw [hprod_dd]; exact hDR
    have hprodle_ee : ∏ j, ee j ≤ R := by rw [hprod_ee]; exact hER
    have hdmem : dd ∈ tupleSupport k R := mem_tupleSupport_aux.mpr ⟨h1d, hdle, hprodle_dd⟩
    have hemem : ee ∈ tupleSupport k R := mem_tupleSupport_aux.mpr ⟨h1e, hele, hprodle_ee⟩
    have hcomb : Finset.lcm Finset.univ (fun j => Nat.lcm (dd j) (ee j)) = Nat.lcm D E := by
      have hsqd : Squarefree (∏ j, dd j) := by rw [hprod_dd]; exact hsqD
      have hsqe : Squarefree (∏ j, ee j) := by rw [hprod_ee]; exact hsqE
      calc Finset.lcm Finset.univ (fun j => Nat.lcm (dd j) (ee j))
          = Nat.lcm (∏ j, dd j) (∏ j, ee j) := combined_lcm_eq_aux h1d h1e hsqd hsqe
        _ = Nat.lcm D E := by rw [hprod_dd, hprod_ee]
    have hgood : goodPair h dd ee i := by
      apply (goodPair_iff_local_of_products_aux hprod_dd hprod_ee hsqD hsqE).mpr
      intro p hp hpL
      have hps : p ∈ (Nat.lcm D E).primeFactors := by
        rw [Nat.mem_primeFactors]
        exact ⟨hp, hpL, hL0⟩
      obtain ⟨-, -, hcompat, hnoncong⟩ := hFmem p hps
      constructor
      · intro j hlj j' hlj'
        apply hcompat j j'
        · rcases prime_dvd_lcm_aux hp hlj with hd | he
          · exact Or.inl (hdvd_rev p hps j hd)
          · exact Or.inr (hedvd_rev p hps j he)
        · rcases prime_dvd_lcm_aux hp hlj' with hd | he
          · exact Or.inl (hdvd_rev p hps j' hd)
          · exact Or.inr (hedvd_rev p hps j' he)
      · intro j hlj
        apply hnoncong j
        rcases prime_dvd_lcm_aux hp hlj with hd | he
        · exact Or.inl (hdvd_rev p hps j hd)
        · exact Or.inr (hedvd_rev p hps j he)
    have hmem : (dd, ee) ∈ ((tupleSupport k R ×ˢ tupleSupport k R).filter
        (fun p => ∏ j, p.1 j = D ∧ ∏ j, p.2 j = E ∧ goodPair h p.1 p.2 i ∧
          Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = Nat.lcm D E)) := by
      rw [Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hdmem, hemem⟩, hprod_dd, hprod_ee, hgood, hcomb⟩
    have hfwdeq : (fun p _ => (coordOf dd p, coordOf ee p)) = f := by
      funext p hp
      show (coordOf dd p, coordOf ee p) = f p hp
      rw [← hFf p hp]
      refine Prod.ext ?_ ?_
      · show coordOf dd p = (Ff p).1
        cases hFc : (Ff p).1 with
        | none =>
          apply coordOf_none_of_not_dvd_aux
          rintro ⟨j, hj⟩
          have hcon := hdvd_rev p hp j hj
          rw [hFc] at hcon
          simp at hcon
        | some j₀ =>
          exact coordOf_some_of_dvd_aux h1d
            (by rw [hprod_dd]; exact hsqD) (hprime p hp) (hdvd p hp j₀ hFc)
      · show coordOf ee p = (Ff p).2
        cases hFc : (Ff p).2 with
        | none =>
          apply coordOf_none_of_not_dvd_aux
          rintro ⟨j, hj⟩
          have hcon := hedvd_rev p hp j hj
          rw [hFc] at hcon
          simp at hcon
        | some j₀ =>
          exact coordOf_some_of_dvd_aux h1e
            (by rw [hprod_ee]; exact hsqE) (hprime p hp) (hedvd p hp j₀ hFc)
    exact ⟨(dd, ee), hmem, hfwdeq⟩

