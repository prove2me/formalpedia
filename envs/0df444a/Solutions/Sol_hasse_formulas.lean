-- Prove2me | solution 1 for hasse_formulas
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T16:51:11.447697+00:00
-- url     : https://prove2.me/submissions/246f2845-c784-4024-9f4b-98438d040972

import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_HasseDerivatives
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_hasseDerivOp_X_sub_C_pow




theorem solution (F : Type*) [Field F] (k r : ℕ) (hk : k ≤ r) :
  (∀ a : F,
      hasseDerivOp F k ((Polynomial.X - Polynomial.C a)^r) =
        Polynomial.C (Nat.choose r k : F) * (Polynomial.X - Polynomial.C a)^(r - k))
  ∧
  (∀ f g : Polynomial F,
      g^(r - k) ∣ hasseDerivOp F k (f * g^r) ∧
      Polynomial.degree ((hasseDerivOp F k (f * g^r)) / (g^(r - k))) ≤
        (match (Polynomial.degree f + (k : WithBot ℕ) * Polynomial.degree g) with
         | ⊥ => ⊥
         | some n => ((n - k : ℕ) : WithBot ℕ))) :=
by
  constructor
  · intro a
    simpa using
      (hasseDerivOp_X_sub_C_pow (F := F) (k := k) (r := r) (hk := hk) (a := a))
  · intro f g
    constructor
    · simpa using
        (hasseDerivOp_mul_pow_dvd (F := F) (k := k) (r := r) f g)
    · by_cases hf : f = 0
      · subst hf
        simp [hasseDerivOp]
      · by_cases hg : g = 0
        · subst hg
          by_cases hr0 : r = 0
          · subst hr0
            have hk0 : k = 0 := Nat.le_antisymm hk (Nat.zero_le _)
            subst hk0
            have :
                Polynomial.degree f ≤
                  (match Polynomial.degree f with
                   | ⊥ => (⊥ : WithBot ℕ)
                   | some n => ((n - 0 : ℕ) : WithBot ℕ)) := by
              cases hdeg : Polynomial.degree f with
              | bot =>
                  simp
              | coe a =>
                  simp only [Nat.sub_zero]
                  exact le_rfl
            simpa [hasseDerivOp] using this
          · simp [hasseDerivOp, hr0]
        · -- Main case: `f ≠ 0` and `g ≠ 0`.
          set num : Polynomial F := hasseDerivOp F k (f * g ^ r) with hnum
          set den : Polynomial F := g ^ (r - k) with hden
          have hdiv : den ∣ num := by
            have hdiv' : g ^ (r - k) ∣ hasseDerivOp F k (f * g ^ r) :=
              hasseDerivOp_mul_pow_dvd (F := F) (k := k) (r := r) f g
            simpa [hnum, hden] using hdiv'
          have hden_ne : den ≠ 0 := by
            have hg0 : g ≠ 0 := hg
            simpa [hden] using pow_ne_zero (r - k) hg0
          set q : Polynomial F := num / den with hq_def
          have h_deg_q :
              Polynomial.degree q ≤
                (match
                    Polynomial.degree f
                      + (k : WithBot ℕ) * Polynomial.degree g with
                 | ⊥ => (⊥ : WithBot ℕ)
                 | some n => ((n - k : ℕ) : WithBot ℕ)) := by
            by_cases hq0 : q = 0
            · simp [hq0]
            · have hq_ne : q ≠ 0 := hq0
              have hnum_nat_le1 :
                  num.natDegree ≤ (f * g ^ r).natDegree - k := by
                simpa [hnum, hasseDerivOp] using
                  (Polynomial.natDegree_hasseDeriv_le (p := f * g ^ r) (n := k))
              have hmul_nat_le :
                  (f * g ^ r).natDegree ≤
                    f.natDegree + (g ^ r).natDegree :=
                Polynomial.natDegree_mul_le (p := f) (q := g ^ r)
              have hpow_nat_le :
                  (g ^ r).natDegree ≤ r * g.natDegree :=
                Polynomial.natDegree_pow_le (p := g) (n := r)
              have hfg_nat_le :
                  (f * g ^ r).natDegree ≤
                    f.natDegree + r * g.natDegree :=
                le_trans hmul_nat_le (Nat.add_le_add_left hpow_nat_le _)
              have hnum_nat_le :
                  num.natDegree ≤ f.natDegree + r * g.natDegree - k :=
                le_trans hnum_nat_le1 (Nat.sub_le_sub_right hfg_nat_le _)
              have hmul_eq : den * q = num := by
                simpa [hq_def] using
                  (EuclideanDomain.mul_div_cancel'
                    (R := Polynomial F) (a := num) (b := den) hden_ne hdiv)
              have hnum_nat_eq :
                  num.natDegree = den.natDegree + q.natDegree := by
                have := congrArg Polynomial.natDegree hmul_eq.symm
                simpa [Polynomial.natDegree_mul (p := den) (q := q) hden_ne hq_ne] using this
              have hden_nat : den.natDegree = (r - k) * g.natDegree := by
                simp [hden]
              have hsub_le :
                  num.natDegree - (r - k) * g.natDegree ≤
                    f.natDegree + r * g.natDegree - k
                      - (r - k) * g.natDegree :=
                Nat.sub_le_sub_right hnum_nat_le _
              have hq_eq :
                  num.natDegree - (r - k) * g.natDegree =
                    q.natDegree := by
                have : num.natDegree =
                    (r - k) * g.natDegree + q.natDegree := by
                  simpa [hden_nat, Nat.add_comm] using hnum_nat_eq
                simp [this]
              have hr : k + (r - k) = r := Nat.add_sub_of_le hk
              have hr_mul :
                  r * g.natDegree =
                    k * g.natDegree + (r - k) * g.natDegree := by
                calc
                  r * g.natDegree
                      = (k + (r - k)) * g.natDegree := by simp [hr]
                  _ = k * g.natDegree + (r - k) * g.natDegree := by
                        simp [Nat.add_mul]
              have hRHS_eq :
                  f.natDegree + r * g.natDegree - k
                      - (r - k) * g.natDegree =
                    f.natDegree + k * g.natDegree - k := by
                have h1 :
                    f.natDegree + r * g.natDegree - k
                        - (r - k) * g.natDegree =
                      f.natDegree + r * g.natDegree
                        - (k + (r - k) * g.natDegree) := by
                  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
                      (tsub_add_eq_tsub_tsub
                        (a := f.natDegree + r * g.natDegree)
                        (b := k)
                        (c := (r - k) * g.natDegree)).symm
                have h2 :
                    f.natDegree + r * g.natDegree
                        - (k + (r - k) * g.natDegree) =
                      f.natDegree + k * g.natDegree - k := by
                  calc
                    f.natDegree + r * g.natDegree
                        - (k + (r - k) * g.natDegree)
                        = f.natDegree
                            + (k * g.natDegree + (r - k) * g.natDegree)
                            - (k + (r - k) * g.natDegree) := by
                            simp [hr_mul]
                    _ = f.natDegree + k * g.natDegree
                          + (r - k) * g.natDegree
                          - (k + (r - k) * g.natDegree) := by
                          simp [Nat.add_assoc]
                    _ = f.natDegree + k * g.natDegree - k := by
                      simpa [Nat.add_comm, Nat.add_left_comm,
                        Nat.add_assoc] using
                        (add_tsub_add_eq_tsub_right
                          (a := f.natDegree + k * g.natDegree)
                          (c := (r - k) * g.natDegree)
                          (b := k))
                exact h1.trans h2
              have hq_nat_le :
                  q.natDegree ≤ f.natDegree + k * g.natDegree - k := by
                have := hsub_le
                simpa [hq_eq, hRHS_eq] using this
              have hdeg_q' :
                  Polynomial.degree q ≤
                    ((f.natDegree + k * g.natDegree - k : ℕ) :
                      WithBot ℕ) :=
                (Polynomial.natDegree_le_iff_degree_le).1 hq_nat_le
              have hf_deg :
                  Polynomial.degree f =
                    (Polynomial.natDegree f : WithBot ℕ) :=
                Polynomial.degree_eq_natDegree hf
              have hg_deg :
                  Polynomial.degree g =
                    (Polynomial.natDegree g : WithBot ℕ) :=
                Polynomial.degree_eq_natDegree hg
              rw [hf_deg, hg_deg]
              exact hdeg_q'
          simpa [hnum, hden, hq_def] using h_deg_q
