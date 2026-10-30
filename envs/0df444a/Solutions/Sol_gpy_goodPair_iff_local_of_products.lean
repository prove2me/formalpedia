-- Prove2me | solution 1 for gpy_goodPair_iff_local_of_products
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-30T02:57:43.947992+00:00
-- url     : https://prove2.me/submissions/69595c08-f53a-44bd-8f5f-a3ffa1b37cc9

/- Submission file for `gpy_goodPair_iff_local_of_products` (publish2 good-count batch).
Self-contained: imports Mathlib only. Includes the good-pair
factorization and the combined-lcm identity as supporting lemmas
plus their helpers.
   Top-level `theorem solution` in the problem's exact binder/statement
   form. No sorry tactic, no axioms beyond the standard ones, no platform
   imports. -/
import Mathlib

open scoped BigOperators
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

noncomputable def crtResidue_aux {k : ℕ} (h d e : Fin k → ℕ) (p : ℕ) : ℕ :=
  if hex : ∃ j, p ∣ Nat.lcm (d j) (e j)
  then p - h (Classical.choose hex) % p else 0

theorem crtResidue_add_aux {k : ℕ} {h d e : Fin k → ℕ} {p : ℕ} {j : Fin k}
    (hp : Nat.Prime p) (hj : p ∣ Nat.lcm (d j) (e j))
    (hcompat : ∀ j', p ∣ Nat.lcm (d j') (e j') → h j ≡ h j' [MOD p]) :
    crtResidue_aux h d e p + h j ≡ 0 [MOD p] := by
  unfold crtResidue_aux
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
    (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
      Nat.Coprime (w + h i)
        (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) ↔
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
    obtain ⟨w, hw⟩ := exists_modEq_prime_finset_aux (crtResidue_aux h d e) hPprime
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
            have hwq : w ≡ crtResidue_aux h d e q [MOD q] := hw q hqP
            have hlocq := hlocal q hqprime hqL
            have hres : crtResidue_aux h d e q + h j ≡ 0 [MOD q] :=
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

theorem solution {k : ℕ} {h d e : Fin k → ℕ} {i : Fin k}
    {D E : ℕ} (hD : ∏ j, d j = D) (hE : ∏ j, e j = E)
    (hsqD : Squarefree D) (hsqE : Squarefree E) :
    (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
      Nat.Coprime (w + h i)
        (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) ↔
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
