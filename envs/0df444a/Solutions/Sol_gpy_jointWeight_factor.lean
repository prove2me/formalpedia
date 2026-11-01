-- Prove2me | solution 1 for gpy_jointWeight_factor
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T03:13:53.382972+00:00
-- url     : https://prove2.me/submissions/4f7439d4-4314-4896-967e-07dfdb1d6c3d

import Mathlib

open scoped BigOperators
open Classical

set_option autoImplicit false

noncomputable def localGoodChoiceFinset {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (p : ℕ) (hd he : Prop) [Decidable hd] [Decidable he] :
    Finset (Option (Fin k) × Option (Fin k)) :=
  Finset.univ.filter (fun ab =>
    (ab.1.isSome ↔ hd) ∧ (ab.2.isSome ↔ he) ∧
    (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
      (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
    (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p]))

noncomputable def jointWeight {k : ℕ} (h : Fin k → ℕ) (i : Fin k)
    (D E : ℕ) : ℝ :=
  (∏ p ∈ (Nat.lcm D E).primeFactors,
    ((localGoodChoiceFinset h i p (p ∣ D) (p ∣ E)).card : ℝ))
    / ((Nat.totient (Nat.lcm D E) : ℕ) : ℝ)

theorem sq_not_dvd_both_aux {n d : ℕ} (hsq : Squarefree n) (hd : d ∣ n)
    {p : ℕ} (hp : p.Prime) : ¬ (p ∣ d ∧ p ∣ n / d) := by
  rintro ⟨h1, h2⟩
  have hpp : p * p ∣ n := by
    have hnm : n = (n / d) * d := (Nat.div_mul_cancel hd).symm
    rw [hnm]
    exact mul_dvd_mul h2 h1
  have hunit : IsUnit p := hsq p hpp
  rw [Nat.isUnit_iff] at hunit
  subst hunit
  exact Nat.not_prime_one hp

theorem coprime_div_of_squarefree_aux {n d : ℕ} (hsq : Squarefree n)
    (hd : d ∣ n) : Nat.Coprime (n / d) d := by
  show Nat.gcd (n / d) d = 1
  by_contra hne
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
  have h1 : p ∣ n / d := dvd_trans hpdvd (Nat.gcd_dvd_left _ _)
  have h2 : p ∣ d := dvd_trans hpdvd (Nat.gcd_dvd_right _ _)
  exact sq_not_dvd_both_aux hsq hd hp ⟨h2, h1⟩

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

theorem primeFactors_lcm_split_aux {D E : ℕ} (hD0 : D ≠ 0) (hE0 : E ≠ 0) :
    (Nat.lcm D E).primeFactors
      = (Nat.gcd D E).primeFactors ∪ (D / Nat.gcd D E).primeFactors
        ∪ (E / Nat.gcd D E).primeFactors := by
  have hdvdD : Nat.gcd D E ∣ D := Nat.gcd_dvd_left D E
  have hdvdE : Nat.gcd D E ∣ E := Nat.gcd_dvd_right D E
  have hD1dvd : D / Nat.gcd D E ∣ D :=
    ⟨Nat.gcd D E, (Nat.div_mul_cancel hdvdD).symm⟩
  have hE1dvd : E / Nat.gcd D E ∣ E :=
    ⟨Nat.gcd D E, (Nat.div_mul_cancel hdvdE).symm⟩
  have hgdpos : 0 < Nat.gcd D E :=
    Nat.pos_of_dvd_of_pos hdvdD (Nat.pos_of_ne_zero hD0)
  have hgdne : Nat.gcd D E ≠ 0 := Nat.ne_of_gt hgdpos
  have hD1ne : D / Nat.gcd D E ≠ 0 := by
    intro h
    have h2 := Nat.div_mul_cancel hdvdD
    rw [h, Nat.zero_mul] at h2
    exact hD0 h2.symm
  have hE1ne : E / Nat.gcd D E ≠ 0 := by
    intro h
    have h2 := Nat.div_mul_cancel hdvdE
    rw [h, Nat.zero_mul] at h2
    exact hE0 h2.symm
  ext p
  rw [mem_primeFactors_lcm_aux hD0 hE0]
  simp only [Finset.mem_union, Nat.mem_primeFactors]
  constructor
  · rintro ⟨hpp, hpD | hpE⟩
    · have h : p ∣ Nat.gcd D E ∨ p ∣ D / Nat.gcd D E := by
        have hDD : D = Nat.gcd D E * (D / Nat.gcd D E) :=
          (Nat.mul_div_cancel' hdvdD).symm
        rw [hDD] at hpD
        exact hpp.dvd_mul.mp hpD
      rcases h with h1 | h1
      · exact Or.inl (Or.inl ⟨hpp, h1, hgdne⟩)
      · exact Or.inl (Or.inr ⟨hpp, h1, hD1ne⟩)
    · have h : p ∣ Nat.gcd D E ∨ p ∣ E / Nat.gcd D E := by
        have hEE : E = Nat.gcd D E * (E / Nat.gcd D E) :=
          (Nat.mul_div_cancel' hdvdE).symm
        rw [hEE] at hpE
        exact hpp.dvd_mul.mp hpE
      rcases h with h1 | h1
      · exact Or.inl (Or.inl ⟨hpp, h1, hgdne⟩)
      · exact Or.inr ⟨hpp, h1, hE1ne⟩
  · intro hmem
    rcases hmem with hAB | hC
    · rcases hAB with hA | hB
      · exact ⟨hA.1, Or.inl (dvd_trans hA.2.1 hdvdD)⟩
      · exact ⟨hB.1, Or.inl (dvd_trans hB.2.1 hD1dvd)⟩
    · exact ⟨hC.1, Or.inr (dvd_trans hC.2.1 hE1dvd)⟩

theorem primeFactors_gcd_disjoint_left_aux {D E : ℕ} (hsqD : Squarefree D) :
    Disjoint (Nat.gcd D E).primeFactors (D / Nat.gcd D E).primeFactors := by
  rw [Finset.disjoint_left]
  intro p hp1 hp2
  rw [Nat.mem_primeFactors] at hp1 hp2
  exact sq_not_dvd_both_aux hsqD (Nat.gcd_dvd_left D E) hp1.1 ⟨hp1.2.1, hp2.2.1⟩

theorem primeFactors_gcd_disjoint_right_aux {D E : ℕ} (hsqD : Squarefree D)
    (hsqE : Squarefree E) :
    Disjoint ((Nat.gcd D E).primeFactors ∪ (D / Nat.gcd D E).primeFactors)
      (E / Nat.gcd D E).primeFactors := by
  rw [Finset.disjoint_left]
  intro p hpU hpE
  simp only [Finset.mem_union, Nat.mem_primeFactors] at hpU
  rw [Nat.mem_primeFactors] at hpE
  rcases hpU with hp1 | hp1
  · exact sq_not_dvd_both_aux hsqE (Nat.gcd_dvd_right D E) hp1.1 ⟨hp1.2.1, hpE.2.1⟩
  · have hpD : p ∣ D :=
      dvd_trans hp1.2.1 ⟨Nat.gcd D E, (Nat.div_mul_cancel (Nat.gcd_dvd_left D E)).symm⟩
    have hpE' : p ∣ E :=
      dvd_trans hpE.2.1 ⟨Nat.gcd D E, (Nat.div_mul_cancel (Nat.gcd_dvd_right D E)).symm⟩
    have hpg : p ∣ Nat.gcd D E := Nat.dvd_gcd hpD hpE'
    exact sq_not_dvd_both_aux hsqD (Nat.gcd_dvd_left D E) hp1.1 ⟨hpg, hp1.2.1⟩

theorem jointWeight_factor_aux {k : ℕ} {h : Fin k → ℕ} {i : Fin k} {D E : ℕ}
    (hsqD : Squarefree D) (hsqE : Squarefree E) :
    jointWeight h i D E
      = ((∏ p ∈ (Nat.gcd D E).primeFactors,
            ((localGoodChoiceFinset h i p (p ∣ D) (p ∣ E)).card : ℝ))
            / ((Nat.totient (Nat.gcd D E) : ℕ) : ℝ))
        * ((∏ p ∈ (D / Nat.gcd D E).primeFactors,
            ((localGoodChoiceFinset h i p (p ∣ D) (p ∣ E)).card : ℝ))
            / ((Nat.totient (D / Nat.gcd D E) : ℕ) : ℝ))
        * ((∏ p ∈ (E / Nat.gcd D E).primeFactors,
            ((localGoodChoiceFinset h i p (p ∣ D) (p ∣ E)).card : ℝ))
            / ((Nat.totient (E / Nat.gcd D E) : ℕ) : ℝ)) := by
  classical
  have hD0 : D ≠ 0 := hsqD.ne_zero
  have hE0 : E ≠ 0 := hsqE.ne_zero
  have hdD : Nat.gcd D E ∣ D := Nat.gcd_dvd_left D E
  have hdE : Nat.gcd D E ∣ E := Nat.gcd_dvd_right D E
  have hgdpos : 0 < Nat.gcd D E :=
    Nat.pos_of_dvd_of_pos hdD (Nat.pos_of_ne_zero hD0)
  have hDD : D = Nat.gcd D E * (D / Nat.gcd D E) := (Nat.mul_div_cancel' hdD).symm
  have hEE : E = Nat.gcd D E * (E / Nat.gcd D E) := (Nat.mul_div_cancel' hdE).symm
  have hlcm : Nat.lcm D E
      = Nat.gcd D E * ((D / Nat.gcd D E) * (E / Nat.gcd D E)) := by
    apply Nat.eq_of_mul_eq_mul_left hgdpos
    calc Nat.gcd D E * Nat.lcm D E = D * E := Nat.gcd_mul_lcm D E
      _ = (Nat.gcd D E * (D / Nat.gcd D E)) * (Nat.gcd D E * (E / Nat.gcd D E)) := by
          rw [← hDD, ← hEE]
      _ = Nat.gcd D E * (Nat.gcd D E * ((D / Nat.gcd D E) * (E / Nat.gcd D E))) := by
          ring
  have hφ : ((Nat.totient (Nat.lcm D E) : ℕ) : ℝ)
      = ((Nat.totient (Nat.gcd D E) : ℕ) : ℝ)
        * ((Nat.totient (D / Nat.gcd D E) : ℕ) : ℝ)
        * ((Nat.totient (E / Nat.gcd D E) : ℕ) : ℝ) := by
    rw [hlcm]
    have hc1 : Nat.Coprime (Nat.gcd D E)
        ((D / Nat.gcd D E) * (E / Nat.gcd D E)) := by
      apply Nat.Coprime.mul_right
      · exact (coprime_div_of_squarefree_aux hsqD hdD).symm
      · exact (coprime_div_of_squarefree_aux hsqE hdE).symm
    have hc2 : Nat.Coprime (D / Nat.gcd D E) (E / Nat.gcd D E) :=
      Nat.coprime_div_gcd_div_gcd hgdpos
    rw [Nat.totient_mul hc1, Nat.totient_mul hc2]
    push_cast
    ring
  have hprod : (∏ p ∈ (Nat.lcm D E).primeFactors,
        ((localGoodChoiceFinset h i p (p ∣ D) (p ∣ E)).card : ℝ))
      = (∏ p ∈ (Nat.gcd D E).primeFactors,
            ((localGoodChoiceFinset h i p (p ∣ D) (p ∣ E)).card : ℝ))
        * (∏ p ∈ (D / Nat.gcd D E).primeFactors,
            ((localGoodChoiceFinset h i p (p ∣ D) (p ∣ E)).card : ℝ))
        * (∏ p ∈ (E / Nat.gcd D E).primeFactors,
            ((localGoodChoiceFinset h i p (p ∣ D) (p ∣ E)).card : ℝ)) := by
    rw [primeFactors_lcm_split_aux hD0 hE0,
      Finset.prod_union (primeFactors_gcd_disjoint_right_aux hsqD hsqE),
      Finset.prod_union (primeFactors_gcd_disjoint_left_aux hsqD)]
  unfold jointWeight
  rw [hprod, hφ]
  ring

theorem solution {k : ℕ} {h : Fin k → ℕ} {i : Fin k} {D E : ℕ}
    (hsqD : Squarefree D) (hsqE : Squarefree E) :
    ((∏ p ∈ (Nat.lcm D E).primeFactors, ((((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
        (ab.1.isSome ↔ p ∣ D) ∧ (ab.2.isSome ↔ p ∣ E) ∧
        (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
          (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
        (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])))).card : ℝ))
          / ((Nat.totient (Nat.lcm D E) : ℕ) : ℝ))
      = ((∏ p ∈ (Nat.gcd D E).primeFactors, ((((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
        (ab.1.isSome ↔ p ∣ D) ∧ (ab.2.isSome ↔ p ∣ E) ∧
        (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
          (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
        (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])))).card : ℝ))
          / ((Nat.totient (Nat.gcd D E) : ℕ) : ℝ))
        * ((∏ p ∈ (D / Nat.gcd D E).primeFactors, ((((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
        (ab.1.isSome ↔ p ∣ D) ∧ (ab.2.isSome ↔ p ∣ E) ∧
        (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
          (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
        (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])))).card : ℝ))
          / ((Nat.totient (D / Nat.gcd D E) : ℕ) : ℝ))
        * ((∏ p ∈ (E / Nat.gcd D E).primeFactors, ((((Finset.univ : Finset (Option (Fin k) × Option (Fin k))).filter (fun ab =>
        (ab.1.isSome ↔ p ∣ D) ∧ (ab.2.isSome ↔ p ∣ E) ∧
        (∀ j j', (ab.1 = some j ∨ ab.2 = some j) →
          (ab.1 = some j' ∨ ab.2 = some j') → h j ≡ h j' [MOD p]) ∧
        (∀ j, (ab.1 = some j ∨ ab.2 = some j) → ¬ h i ≡ h j [MOD p])))).card : ℝ))
          / ((Nat.totient (E / Nat.gcd D E) : ℕ) : ℝ)) :=
  jointWeight_factor_aux hsqD hsqE
