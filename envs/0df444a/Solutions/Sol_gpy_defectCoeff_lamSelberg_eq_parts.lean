-- Prove2me | solution 1 for gpy_defectCoeff_lamSelberg_eq_parts
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-31T05:38:03.527025+00:00
-- url     : https://prove2.me/submissions/7a980832-3654-4f0e-aebd-d740276ba4a1

/- Submission file for `gpy` publish3 defect-control problem `gpy_defectCoeff_lamSelberg_eq_parts`.
   Self-contained: imports Mathlib only. Top-level `theorem solution`
   in the problem's exact binder/statement form (statement mechanically
   extracted from the restated theorem, textually identical modulo the
   theorem name). No sorry, no axioms beyond the standard ones, no
   platform imports, no smallness claim. -/
import Mathlib

open scoped BigOperators
open scoped Function
open Classical

set_option autoImplicit false

theorem goodPair_coord_eq_one_aux {k : ℕ} {h d e : Fin k → ℕ} {i : Fin k}
    (hg : (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))) : d i = 1 ∧ e i = 1 := by
  obtain ⟨w, hw, hcop⟩ := hg
  have hdvd1 : Nat.lcm (d i) (e i) ∣ w + h i := hw i
  have hdvdL : Nat.lcm (d i) (e i)
      ∣ Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) :=
    Finset.dvd_lcm (Finset.mem_univ i)
  have hgcd : Nat.lcm (d i) (e i)
      ∣ Nat.gcd (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) :=
    Nat.dvd_gcd hdvd1 hdvdL
  rw [hcop.gcd_eq_one] at hgcd
  have hlcm1 : Nat.lcm (d i) (e i) = 1 := Nat.dvd_one.mp hgcd
  constructor
  · exact Nat.dvd_one.mp (hlcm1 ▸ Nat.dvd_lcm_left (d i) (e i))
  · exact Nat.dvd_one.mp (hlcm1 ▸ Nat.dvd_lcm_right (d i) (e i))
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
theorem defect_prime_sq_aux {k : ℕ} {h d e : Fin k → ℕ} {i : Fin k}
    (hsqd : Squarefree (∏ j, d j)) (hsqe : Squarefree (∏ j, e j))
    (hcompat : (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))])) (hnotgood : ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))) :
    ∃ p, Nat.Prime p ∧
      p ∣ Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) ∧
      (p ∣ Nat.lcm (d i) (e i) ∨
        ∃ j, j ≠ i ∧ p ∣ Nat.lcm (d j) (e j) ∧ h i ≡ h j [MOD p]) := by
  have hnotlocal : ¬ ∀ p, Nat.Prime p →
      p ∣ Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) →
      (∀ j, p ∣ Nat.lcm (d j) (e j) → ∀ j', p ∣ Nat.lcm (d j') (e j') →
        h j ≡ h j' [MOD p]) ∧
      (∀ j, p ∣ Nat.lcm (d j) (e j) → ¬ h i ≡ h j [MOD p]) := by
    intro hloc
    exact hnotgood ((goodPair_iff_local_aux hsqd hsqe).mpr hloc)
  obtain ⟨p, hp_not⟩ := not_forall.mp hnotlocal
  obtain ⟨hp, hp_not2⟩ := Classical.not_imp.mp hp_not
  obtain ⟨hpL, hneg⟩ := Classical.not_imp.mp hp_not2
  by_cases hcomp_p : ∀ j, p ∣ Nat.lcm (d j) (e j) → ∀ j',
      p ∣ Nat.lcm (d j') (e j') → h j ≡ h j' [MOD p]
  · have hnoncong_neg : ¬ ∀ j, p ∣ Nat.lcm (d j) (e j) →
        ¬ h i ≡ h j [MOD p] :=
      fun hB => hneg ⟨hcomp_p, hB⟩
    obtain ⟨j, hj_not⟩ := not_forall.mp hnoncong_neg
    obtain ⟨hj, hcong_not⟩ := Classical.not_imp.mp hj_not
    have hcong : h i ≡ h j [MOD p] := not_not.mp hcong_not
    refine ⟨p, hp, hpL, ?_⟩
    by_cases hji : j = i
    · left
      rw [hji] at hj
      exact hj
    · right
      exact ⟨j, hji, hj, hcong⟩
  · obtain ⟨j, hj_not⟩ := not_forall.mp hcomp_p
    obtain ⟨hj, hj_not2⟩ := Classical.not_imp.mp hj_not
    obtain ⟨j', hj'_not⟩ := not_forall.mp hj_not2
    obtain ⟨hj', hne⟩ := Classical.not_imp.mp hj'_not
    have hglob : h j ≡ h j' [MOD Nat.gcd (Nat.lcm (d j) (e j))
        (Nat.lcm (d j') (e j'))] :=
      hcompat j (Finset.mem_univ j) j' (Finset.mem_univ j')
    have hpgcd : p ∣ Nat.gcd (Nat.lcm (d j) (e j))
        (Nat.lcm (d j') (e j')) := Nat.dvd_gcd hj hj'
    exact absurd (Nat.ModEq.of_dvd hpgcd hglob) hne
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
    ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) :=
  fun hg => goodPair_noncong_aux hp hg hj hcong
theorem compat_not_good_lcm_one_iff_tied_aux {k : ℕ} {h d e : Fin k → ℕ}
    {i : Fin k} (hsqd : Squarefree (∏ j, d j))
    (hsqe : Squarefree (∏ j, e j)) :
    ((∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) ∧ Nat.lcm (d i) (e i) = 1) ↔
    ((∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ Nat.lcm (d i) (e i) = 1 ∧
      ∃ p j, Nat.Prime p ∧ j ≠ i ∧ p ∣ Nat.lcm (d j) (e j) ∧
        (h j = h i ∨
          p ∈ (Int.natAbs ((h i : ℤ) - (h j : ℤ))).primeFactors)) := by
  constructor
  · rintro ⟨hcompat, hnotgood, hlcm⟩
    obtain ⟨p, hp, -, hdisj⟩ := defect_prime_sq_aux hsqd hsqe hcompat hnotgood
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

theorem solution {k : ℕ} (h : Fin k → ℕ)
    (R : ℕ) (deg : ℕ) (i : Fin k) :
    (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
      ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
            h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧
              ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
                Nat.Coprime (w + h i)
                  (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
         then (if ∏ i, d i ≤ R then
              (ArithmeticFunction.moebius (∏ i, d i) : ℝ)
                * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg
              else 0) *
            (if ∏ i, e i ≤ R then
              (ArithmeticFunction.moebius (∏ i, e i) : ℝ)
                * (1 - Real.log ((∏ i, e i : ℕ) : ℝ) / Real.log R) ^ deg
              else 0) /
           Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
         else 0)) =
      (∑ d ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R)).filter (fun d : Fin k → ℕ => Squarefree (∏ j, d j)),
       ∑ e ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R)).filter (fun e : Fin k → ℕ => Squarefree (∏ j, e j)),
         (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
            h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧
              Nat.lcm (d i) (e i) ≠ 1
          then (if ∏ i, d i ≤ R then
              (ArithmeticFunction.moebius (∏ i, d i) : ℝ)
                * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg
              else 0) *
            (if ∏ i, e i ≤ R then
              (ArithmeticFunction.moebius (∏ i, e i) : ℝ)
                * (1 - Real.log ((∏ i, e i : ℕ) : ℝ) / Real.log R) ^ deg
              else 0) /
           Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
          else 0))
      + (∑ d ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R)).filter (fun d : Fin k → ℕ => Squarefree (∏ j, d j)),
       ∑ e ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R)).filter (fun e : Fin k → ℕ => Squarefree (∏ j, e j)),
         (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
            h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧
              Nat.lcm (d i) (e i) = 1 ∧
           (∃ p j, Nat.Prime p ∧ j ≠ i ∧ p ∣ Nat.lcm (d j) (e j) ∧
             (h j = h i ∨
               p ∈ (Int.natAbs ((h i : ℤ) - (h j : ℤ))).primeFactors)) then
           (if ∏ i, d i ≤ R then
              (ArithmeticFunction.moebius (∏ i, d i) : ℝ)
                * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg
              else 0) *
            (if ∏ i, e i ≤ R then
              (ArithmeticFunction.moebius (∏ i, e i) : ℝ)
                * (1 - Real.log ((∏ i, e i : ℕ) : ℝ) / Real.log R) ^ deg
              else 0) /
             Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
          else 0)) := by
  have h1 : (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
      ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
        (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
         then (if ∏ i, d i ≤ R then (ArithmeticFunction.moebius (∏ i, d i) : ℝ) * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg else 0) * (if ∏ i, e i ≤ R then (ArithmeticFunction.moebius (∏ i, e i) : ℝ) * (1 - Real.log ((∏ i, e i : ℕ) : ℝ) / Real.log R) ^ deg else 0) /
           Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
         else 0)) =
      ∑ d ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)).filter (fun d : Fin k → ℕ => Squarefree (∏ j, d j)),
      ∑ e ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)).filter (fun e : Fin k → ℕ => Squarefree (∏ j, e j)),
        (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
         then (if ∏ i, d i ≤ R then (ArithmeticFunction.moebius (∏ i, d i) : ℝ) * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg else 0) * (if ∏ i, e i ≤ R then (ArithmeticFunction.moebius (∏ i, e i) : ℝ) * (1 - Real.log ((∏ i, e i : ℕ) : ℝ) / Real.log R) ^ deg else 0) /
           Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
         else 0) := by
    have hzero : ∀ {d : Fin k → ℕ}, ¬ Squarefree (∏ i, d i) →
        (if ∏ i, d i ≤ R then (ArithmeticFunction.moebius (∏ i, d i) : ℝ)
          * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg else 0) = 0 := by
      intro d hd
      by_cases hle : ∏ i, d i ≤ R
      · rw [if_pos hle]
        have hmu : (ArithmeticFunction.moebius (∏ i, d i) : ℝ) = 0 := by
          exact_mod_cast ArithmeticFunction.moebius_eq_zero_of_not_squarefree hd
        rw [hmu, zero_mul]
      · rw [if_neg hle]
    have hsplit_d : (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
          ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
            (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) then
              (if ∏ i, d i ≤ R then (ArithmeticFunction.moebius (∏ i, d i) : ℝ) * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg else 0) * (if ∏ i, e i ≤ R then (ArithmeticFunction.moebius (∏ i, e i) : ℝ) * (1 - Real.log ((∏ i, e i : ℕ) : ℝ) / Real.log R) ^ deg else 0) /
                Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
             else 0))
        = (∑ d ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)).filter (fun d : Fin k → ℕ => Squarefree (∏ j, d j)),
            ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
              (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) then
                (if ∏ i, d i ≤ R then (ArithmeticFunction.moebius (∏ i, d i) : ℝ) * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg else 0) * (if ∏ i, e i ≤ R then (ArithmeticFunction.moebius (∏ i, e i) : ℝ) * (1 - Real.log ((∏ i, e i : ℕ) : ℝ) / Real.log R) ^ deg else 0) /
                  Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
               else 0))
          + (∑ d ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)).filter
              (fun d : Fin k → ℕ => ¬ Squarefree (∏ j, d j)),
              ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
                (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) then
                  (if ∏ i, d i ≤ R then (ArithmeticFunction.moebius (∏ i, d i) : ℝ) * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg else 0) * (if ∏ i, e i ≤ R then (ArithmeticFunction.moebius (∏ i, e i) : ℝ) * (1 - Real.log ((∏ i, e i : ℕ) : ℝ) / Real.log R) ^ deg else 0) /
                    Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
                 else 0)) :=
      (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    have hzero_d : (∑ d ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)).filter
          (fun d : Fin k → ℕ => ¬ Squarefree (∏ j, d j)),
          ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
            (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) then
              (if ∏ i, d i ≤ R then (ArithmeticFunction.moebius (∏ i, d i) : ℝ) * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg else 0) * (if ∏ i, e i ≤ R then (ArithmeticFunction.moebius (∏ i, e i) : ℝ) * (1 - Real.log ((∏ i, e i : ℕ) : ℝ) / Real.log R) ^ deg else 0) /
                Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
             else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      rw [Finset.mem_filter] at hd
      apply Finset.sum_eq_zero
      intro e _
      by_cases hc : (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
      · rw [if_pos hc, hzero hd.2, zero_mul, zero_div]
      · rw [if_neg hc]
    rw [hsplit_d, hzero_d, add_zero]
    apply Finset.sum_congr rfl
    intro d _
    have hsplit_e : (∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
          (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) then
            (if ∏ i, d i ≤ R then (ArithmeticFunction.moebius (∏ i, d i) : ℝ) * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg else 0) * (if ∏ i, e i ≤ R then (ArithmeticFunction.moebius (∏ i, e i) : ℝ) * (1 - Real.log ((∏ i, e i : ℕ) : ℝ) / Real.log R) ^ deg else 0) /
              Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
           else 0))
        = (∑ e ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)).filter (fun e : Fin k → ℕ => Squarefree (∏ j, e j)),
            (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) then
              (if ∏ i, d i ≤ R then (ArithmeticFunction.moebius (∏ i, d i) : ℝ) * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg else 0) * (if ∏ i, e i ≤ R then (ArithmeticFunction.moebius (∏ i, e i) : ℝ) * (1 - Real.log ((∏ i, e i : ℕ) : ℝ) / Real.log R) ^ deg else 0) /
                Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
             else 0))
          + (∑ e ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)).filter
              (fun e : Fin k → ℕ => ¬ Squarefree (∏ j, e j)),
              (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) then
                (if ∏ i, d i ≤ R then (ArithmeticFunction.moebius (∏ i, d i) : ℝ) * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg else 0) * (if ∏ i, e i ≤ R then (ArithmeticFunction.moebius (∏ i, e i) : ℝ) * (1 - Real.log ((∏ i, e i : ℕ) : ℝ) / Real.log R) ^ deg else 0) /
                  Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
               else 0)) :=
      (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    have hzero_e : (∑ e ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)).filter
          (fun e : Fin k → ℕ => ¬ Squarefree (∏ j, e j)),
          (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) then
            (if ∏ i, d i ≤ R then (ArithmeticFunction.moebius (∏ i, d i) : ℝ) * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg else 0) * (if ∏ i, e i ≤ R then (ArithmeticFunction.moebius (∏ i, e i) : ℝ) * (1 - Real.log ((∏ i, e i : ℕ) : ℝ) / Real.log R) ^ deg else 0) /
              Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
           else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro e he
      rw [Finset.mem_filter] at he
      by_cases hc : (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
      · rw [if_pos hc, hzero he.2, mul_zero, zero_div]
      · rw [if_neg hc]
    rw [hsplit_e, hzero_e, add_zero]
  have h2 : (∑ d ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)).filter (fun d : Fin k → ℕ => Squarefree (∏ j, d j)),
      ∑ e ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)).filter (fun e : Fin k → ℕ => Squarefree (∏ j, e j)),
        (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
         then (if ∏ i, d i ≤ R then (ArithmeticFunction.moebius (∏ i, d i) : ℝ) * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg else 0) * (if ∏ i, e i ≤ R then (ArithmeticFunction.moebius (∏ i, e i) : ℝ) * (1 - Real.log ((∏ i, e i : ℕ) : ℝ) / Real.log R) ^ deg else 0) /
           Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
         else 0)) =
      (∑ d ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)).filter (fun d : Fin k → ℕ => Squarefree (∏ j, d j)),
      ∑ e ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)).filter (fun e : Fin k → ℕ => Squarefree (∏ j, e j)),
        (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) ∧ Nat.lcm (d i) (e i) ≠ 1
         then (if ∏ i, d i ≤ R then (ArithmeticFunction.moebius (∏ i, d i) : ℝ) * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg else 0) * (if ∏ i, e i ≤ R then (ArithmeticFunction.moebius (∏ i, e i) : ℝ) * (1 - Real.log ((∏ i, e i : ℕ) : ℝ) / Real.log R) ^ deg else 0) /
           Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
         else 0))
      + (∑ d ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)).filter (fun d : Fin k → ℕ => Squarefree (∏ j, d j)),
      ∑ e ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)).filter (fun e : Fin k → ℕ => Squarefree (∏ j, e j)),
        (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) ∧ Nat.lcm (d i) (e i) = 1
         then (if ∏ i, d i ≤ R then (ArithmeticFunction.moebius (∏ i, d i) : ℝ) * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg else 0) * (if ∏ i, e i ≤ R then (ArithmeticFunction.moebius (∏ i, e i) : ℝ) * (1 - Real.log ((∏ i, e i : ℕ) : ℝ) / Real.log R) ^ deg else 0) /
           Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
         else 0)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hc : (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
    · by_cases hl : Nat.lcm (d i) (e i) = 1
      · have hneg2 : ¬ ((∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) ∧ Nat.lcm (d i) (e i) ≠ 1) :=
          fun hcon => hcon.2.2 hl
        have hpos3 : (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) ∧ Nat.lcm (d i) (e i) = 1 :=
          ⟨hc.1, hc.2, hl⟩
        rw [if_pos hc, if_neg hneg2, if_pos hpos3]
        simp
      · have hpos2 : (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) ∧ Nat.lcm (d i) (e i) ≠ 1 :=
          ⟨hc.1, hc.2, hl⟩
        have hneg3 : ¬ ((∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) ∧ Nat.lcm (d i) (e i) = 1) :=
          fun hcon => hl hcon.2.2
        rw [if_pos hc, if_pos hpos2, if_neg hneg3]
        simp
    · have hneg2 : ¬ ((∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) ∧ Nat.lcm (d i) (e i) ≠ 1) :=
        fun hcon => hc ⟨hcon.1, hcon.2.1⟩
      have hneg3 : ¬ ((∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) ∧ Nat.lcm (d i) (e i) = 1) :=
        fun hcon => hc ⟨hcon.1, hcon.2.1⟩
      rw [if_neg hc, if_neg hneg2, if_neg hneg3]
      simp
  have h3 : (∑ d ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)).filter (fun d : Fin k → ℕ => Squarefree (∏ j, d j)),
      ∑ e ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)).filter (fun e : Fin k → ℕ => Squarefree (∏ j, e j)),
        (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) ∧ Nat.lcm (d i) (e i) ≠ 1
         then (if ∏ i, d i ≤ R then (ArithmeticFunction.moebius (∏ i, d i) : ℝ) * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg else 0) * (if ∏ i, e i ≤ R then (ArithmeticFunction.moebius (∏ i, e i) : ℝ) * (1 - Real.log ((∏ i, e i : ℕ) : ℝ) / Real.log R) ^ deg else 0) /
           Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
         else 0)) =
      ∑ d ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)).filter (fun d : Fin k → ℕ => Squarefree (∏ j, d j)),
      ∑ e ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)).filter (fun e : Fin k → ℕ => Squarefree (∏ j, e j)),
        (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ Nat.lcm (d i) (e i) ≠ 1
         then (if ∏ i, d i ≤ R then (ArithmeticFunction.moebius (∏ i, d i) : ℝ) * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg else 0) * (if ∏ i, e i ≤ R then (ArithmeticFunction.moebius (∏ i, e i) : ℝ) * (1 - Real.log ((∏ i, e i : ℕ) : ℝ) / Real.log R) ^ deg else 0) /
           Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
         else 0) := by
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro e _
    by_cases hc : (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))])
    · by_cases hl : Nat.lcm (d i) (e i) ≠ 1
      · have hnotgood : ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) := by
          intro hg
          obtain ⟨hd1, he1⟩ := goodPair_coord_eq_one_aux hg
          apply hl
          rw [hd1, he1]
          simp
        have hposL : (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) ∧ Nat.lcm (d i) (e i) ≠ 1 :=
          ⟨hc, hnotgood, hl⟩
        have hposR : (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ Nat.lcm (d i) (e i) ≠ 1 := ⟨hc, hl⟩
        rw [if_pos hposL, if_pos hposR]
      · have hnegL : ¬ ((∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) ∧ Nat.lcm (d i) (e i) ≠ 1) :=
          fun hcon => hl hcon.2.2
        have hnegR : ¬ ((∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ Nat.lcm (d i) (e i) ≠ 1) :=
          fun hcon => hl hcon.2
        rw [if_neg hnegL, if_neg hnegR]
    · have hnegL : ¬ ((∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) ∧ Nat.lcm (d i) (e i) ≠ 1) :=
        fun hcon => hc hcon.1
      have hnegR : ¬ ((∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ Nat.lcm (d i) (e i) ≠ 1) :=
        fun hcon => hc hcon.1
      rw [if_neg hnegL, if_neg hnegR]
  have h4 : (∑ d ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)).filter (fun d : Fin k → ℕ => Squarefree (∏ j, d j)),
      ∑ e ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)).filter (fun e : Fin k → ℕ => Squarefree (∏ j, e j)),
        (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) ∧ Nat.lcm (d i) (e i) = 1
         then (if ∏ i, d i ≤ R then (ArithmeticFunction.moebius (∏ i, d i) : ℝ) * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg else 0) * (if ∏ i, e i ≤ R then (ArithmeticFunction.moebius (∏ i, e i) : ℝ) * (1 - Real.log ((∏ i, e i : ℕ) : ℝ) / Real.log R) ^ deg else 0) /
           Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
         else 0)) =
      ∑ d ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)).filter (fun d : Fin k → ℕ => Squarefree (∏ j, d j)),
      ∑ e ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)).filter (fun e : Fin k → ℕ => Squarefree (∏ j, e j)),
        (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ Nat.lcm (d i) (e i) = 1 ∧
          (∃ p j, Nat.Prime p ∧ j ≠ i ∧ p ∣ Nat.lcm (d j) (e j) ∧
            (h j = h i ∨
              p ∈ (Int.natAbs ((h i : ℤ) - (h j : ℤ))).primeFactors)) then
          (if ∏ i, d i ≤ R then (ArithmeticFunction.moebius (∏ i, d i) : ℝ) * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg else 0) * (if ∏ i, e i ≤ R then (ArithmeticFunction.moebius (∏ i, e i) : ℝ) * (1 - Real.log ((∏ i, e i : ℕ) : ℝ) / Real.log R) ^ deg else 0) / Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))
         else 0) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mem_filter] at hd
    apply Finset.sum_congr rfl
    intro e he
    rw [Finset.mem_filter] at he
    by_cases hL : (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) ∧ Nat.lcm (d i) (e i) = 1
    · have hR : (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ Nat.lcm (d i) (e i) = 1 ∧
          (∃ p j, Nat.Prime p ∧ j ≠ i ∧ p ∣ Nat.lcm (d j) (e j) ∧
            (h j = h i ∨
              p ∈ (Int.natAbs ((h i : ℤ) - (h j : ℤ))).primeFactors)) :=
        (compat_not_good_lcm_one_iff_tied_aux hd.2 he.2).mp hL
      rw [if_pos hL, if_pos hR]
    · have hRneg : ¬ ((∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ Nat.lcm (d i) (e i) = 1 ∧
          (∃ p j, Nat.Prime p ∧ j ≠ i ∧ p ∣ Nat.lcm (d j) (e j) ∧
            (h j = h i ∨
              p ∈ (Int.natAbs ((h i : ℤ) - (h j : ℤ))).primeFactors))) :=
        fun hR => hL ((compat_not_good_lcm_one_iff_tied_aux hd.2 he.2).mpr hR)
      rw [if_neg hL, if_neg hRneg]
  rw [h1, h2, h3, h4]
