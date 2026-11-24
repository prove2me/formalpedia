-- Prove2me | solution 1 for stepanov_system_has_solution
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T17:21:20.646798+00:00
-- url     : https://prove2.me/submissions/cb3024fd-45b0-44c6-b86b-f49b9a9571cb

import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_HasseDerivatives
import Definitions.Def_Sensitivity214439_Phase0_RiemannHypothesisCurves_StepanovSystem
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
import Theorems.Thm_auxiliary_derivatives
import Theorems.Thm_stepanovHasseQuotMap_mul
import Theorems.Thm_stepanov_system_dimension_inequality_nat

section


lemma stepanov_sigma_degree_bound_fin
    (F : Type*) [Field F]
    (d k m J : ℕ) (a : F)
    (rjk sjk : Fin J → Polynomial F)
    (hdeg_r : ∀ j : Fin J, (rjk j).natDegree ≤ d + k * (m - 1))
    (hdeg_s : ∀ j : Fin J, (sjk j).natDegree ≤ d + k * (m - 1)) :
    (∑ j : Fin J, (rjk j + Polynomial.C a * sjk j) * Polynomial.X ^ (j : ℕ)).natDegree
      ≤ J - 1 + d + k * (m - 1) :=
by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  have hmul :=
    Polynomial.natDegree_mul_le
      (p := rjk j + Polynomial.C a * sjk j) (q := Polynomial.X ^ (j : ℕ))
  have h_sum : (rjk j + Polynomial.C a * sjk j).natDegree ≤ d + k * (m - 1) := by
    have :=
      (Polynomial.natDegree_add_le (rjk j) (Polynomial.C a * sjk j)).trans
        (max_le_max (hdeg_r j) (Polynomial.natDegree_C_mul_le a _))
    simpa [hdeg_s j] using this
  calc
    ((rjk j + Polynomial.C a * sjk j) * Polynomial.X ^ (j : ℕ)).natDegree
        ≤ (rjk j + Polynomial.C a * sjk j).natDegree + (j : ℕ) := by
          simpa [Polynomial.natDegree_X_pow] using hmul
    _ ≤ d + k * (m - 1) + (j : ℕ) :=
      Nat.add_le_add_right h_sum _
    _ ≤ J - 1 + d + k * (m - 1) := by
      have := add_le_add_left (Nat.le_pred_of_lt j.isLt) (d + k * (m - 1))
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this









lemma exists_nonzero_solution_of_finrank_lt
    (F : Type*) [Field F]
    (V W : Type*) [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    [FiniteDimensional F V] [FiniteDimensional F W]
    (L : V →ₗ[F] W)
    (h : Module.finrank F W < Module.finrank F V) :
    ∃ v : V, v ≠ 0 ∧ L v = 0 :=
by
  obtain ⟨v, hv_mem, hv_ne⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot
      (p := LinearMap.ker L)
      (by
        intro hker
        have hk0 : Module.finrank F (LinearMap.ker L) = 0 := by
          simp [hker]
        exact
          (ne_of_lt
            (lt_of_le_of_lt (Submodule.finrank_le (s := LinearMap.range L)) h))
            (by
              simpa [hk0] using
                LinearMap.finrank_range_add_finrank_ker (f := L)))
  refine ⟨v, hv_ne, ?_⟩
  simpa using hv_mem

lemma natDegree_le_of_mem_degreeLT_succ
    (F : Type*) [Semiring F] (d : ℕ) (p : Polynomial.degreeLT F (d + 1)) :
    (p : Polynomial F).natDegree ≤ d :=
by
  have h := p.2
  simp only [Polynomial.mem_degreeLT] at h
  refine Nat.lt_succ_iff.mp ?_
  by_cases hp : (p : Polynomial F) = 0
  · simp [hp]
  · rw [Polynomial.degree_eq_natDegree hp] at h
    exact WithBot.coe_lt_coe.mp h

lemma stepanov_dimension_inequality_ceil
    (F : Type*) [Field F]
    (ℓ d m q B : ℕ)
    (hℓ_pos : 0 < ℓ) (hm_ge_two : 2 ≤ m)
    (hq6m : q > 6 * m) (hl : ℓ ≤ q / 3)
    (hd : d = Nat.ceil (((q : ℚ) - m) / 2) - 1)
    (hB : B ≤ ∑ k ∈ Finset.range ℓ,
      (Nat.ceil ((ℓ : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) / (q : ℚ)) + d + k * (m - 1))) :
  let J := Nat.ceil ((ℓ : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) / (q : ℚ))
  Module.finrank F (Fin B → F) <
    Module.finrank F (Fin (2 * J) → Polynomial.degreeLT F (d + 1)) :=
by
  intro J
  have hceil_nat : 1 ≤ Nat.ceil (((q : ℚ) - m) / 2) := by
    refine Nat.one_le_ceil_iff.mpr ?_
    have hm_lt_q : m < q :=
      lt_of_le_of_lt
        (by
          simpa [Nat.one_mul] using
            Nat.mul_le_mul_right m (show (1 : ℕ) ≤ 6 by decide))
        (by simpa using hq6m)
    have : (0 : ℚ) < (q : ℚ) - m :=
      sub_pos.mpr (by exact_mod_cast hm_lt_q)
    simpa using div_pos this (show (0 : ℚ) < (2 : ℚ) by norm_num)
  have hA_gt_B :
      2 * J * Nat.ceil (((q : ℚ) - m) / 2) > B :=
    stepanov_system_dimension_inequality_nat q m ℓ hm_ge_two hq6m hl hℓ_pos B
      (by simpa [hd] using hB)
  simpa [ Module.finrank_pi_fintype,
          Module.finrank_fintype_fun_eq_card,
          LinearEquiv.finrank_eq (Polynomial.degreeLTEquiv F (d + 1)),
          hd, Nat.sub_add_cancel hceil_nat ] using hA_gt_B









lemma stepanovHasseQuotMap_eq_div
    (F : Type*) [Field F] {f : Polynomial F} (hf : f ≠ 0)
    (r k : ℕ) (p : Polynomial F) :
    stepanovHasseQuotMap (F := F) (f := f) hf r k p =
      hasseDerivOp F k (p * f ^ r) / f ^ (r - k) :=
by
  refine mul_right_cancel₀ (pow_ne_zero (r - k) hf) ?_
  refine (stepanovHasseQuotMap_mul (F := F) (f := f) hf r k p).trans ?_
  simpa [mul_comm] using
    (EuclideanDomain.mul_div_cancel'
      (a := hasseDerivOp F k (p * f ^ r))
      (b := f ^ (r - k))
      (pow_ne_zero (r - k) hf)
      (hasseDerivOp_mul_pow_dvd F k r p f)).symm

lemma stepanovHasseQuotMap_eq_div_left
    (F : Type*) [Field F] {f : Polynomial F} (hf : f ≠ 0)
    (r k : ℕ) (p : Polynomial F) :
    stepanovHasseQuotMap (F := F) (f := f) hf r k p =
      hasseDerivOp F k (f ^ r * p) / f ^ (r - k) :=
by simpa [mul_comm] using stepanovHasseQuotMap_eq_div (F := F) hf r k p

lemma stepanovHasseQuotMap_natDegree_le
    (F : Type*) [Field F] {f : Polynomial F} (hf : f ≠ 0)
    (m d r k : ℕ) (hfdeg : f.natDegree = m) (hk : k ≤ r)
    (p : Polynomial F) (hp : p.natDegree ≤ d) :
    (stepanovHasseQuotMap (F := F) (f := f) hf r k p).natDegree
      ≤ d + k * (m - 1) :=
by
  obtain ⟨rjk, _, hr_eq, -, hdeg_rjk, -⟩ :=
    auxiliary_derivatives (F := F) f m d r 0 hfdeg p 0 hp (by simp) k hk
  have h_eq :
      stepanovHasseQuotMap (F := F) (f := f) hf r k p = rjk := by
    refine mul_right_cancel₀ (pow_ne_zero (r - k) hf) ?_
    have hmul :=
      stepanovHasseQuotMap_mul (F := F) (f := f) hf r k p
    have hr_eq' : hasseDerivOp F k (p * f ^ r) = rjk * f ^ (r - k) := by
      simpa [mul_comm] using hr_eq
    simpa [hmul] using hr_eq'
  simpa [h_eq] using hdeg_rjk

lemma finrank_stepanov_constraint_space
    (F : Type*) [Field F] (ℓ J d m : ℕ) :
    Module.finrank F (∀ k : Fin ℓ, Polynomial.degreeLT F (J + d + k * (m - 1))) =
      ∑ k ∈ Finset.range ℓ, (J + d + k * (m - 1)) :=
by
  calc
    Module.finrank F (∀ k : Fin ℓ, Polynomial.degreeLT F (J + d + k * (m - 1)))
        = ∑ k : Fin ℓ, (J + d + k * (m - 1)) := by
          simp [Module.finrank_pi_fintype,
            Module.finrank_fintype_fun_eq_card,
            LinearEquiv.finrank_eq (Polynomial.degreeLTEquiv F _)]
    _ = ∑ k ∈ Finset.range ℓ, (J + d + k * (m - 1)) := by
          simpa using
            (Fin.sum_univ_eq_sum_range (n := ℓ) (fun k => J + d + k * (m - 1)))





end



theorem solution
  (F : Type*) [Field F] [Fintype F]
  (f : Polynomial F) (q m ℓ : ℕ) (a : F)
  (_hq : q = Fintype.card F) (hfdeg : f.natDegree = m)
  (hm_ge_two : 2 ≤ m) (_hm_pos : 0 < m) (hℓ_pos : 0 < ℓ)
  (hq6m : q > 6 * m) (hl : ℓ ≤ q / 3)
  (hJ_pos :
      1 ≤ Nat.ceil (((ℓ : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) / (q : ℚ)))) :
  let d : ℕ := Nat.ceil (((q : ℚ) - m) / 2) - 1
  let J : ℕ := Nat.ceil ((ℓ : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) / (q : ℚ))
  ∃ rj sj : ℕ → Polynomial F,
    (∃ j < J, rj j ≠ 0 ∨ sj j ≠ 0) ∧
    (∀ j < J, (rj j).natDegree ≤ d ∧ (sj j).natDegree ≤ d) ∧
    (∀ x : F, f.eval x ≠ 0 → (f.eval x) ^ ((q - 1) / 2) = a →
      ∀ k < ℓ,
        Finset.sum (Finset.range J)
          (fun j =>
            (((hasseDerivOp F k (f ^ ℓ * rj j)) / f ^ (ℓ - k)).eval x +
              a *
                ((hasseDerivOp F k (f ^ (ℓ + ((q - 1) / 2)) * sj j)) /
                    f ^ (ℓ + ((q - 1) / 2) - k)).eval x) *
              x ^ j) = 0) :=
by
  set d : ℕ := Nat.ceil (((q : ℚ) - m) / 2) - 1 with hd
  set J : ℕ := Nat.ceil ((ℓ : ℚ) / 2 + (ℓ : ℚ) ^ 2 * (m : ℚ) / (q : ℚ)) with hJdef
  simp [d, J]
  have hf : f ≠ 0 := by
    rintro hf0
    have hm0 : m = 0 := by simpa [hf0] using hfdeg.symm
    have : (2 : ℕ) ≤ 0 := by simp [hm0] at hm_ge_two
    exact (by decide : ¬ (2 ≤ 0)) this
  let c : ℕ := (q - 1) / 2
  let V := Fin (2 * J) → Polynomial.degreeLT F (d + 1)
  let W := ∀ k : Fin ℓ, Polynomial.degreeLT F (J + d + k * (m - 1))
  let finLeft : Fin J → Fin (2 * J) := fun j =>
    ⟨j, lt_of_lt_of_le j.isLt (Nat.le_mul_of_pos_left _ (by decide : 0 < 2))⟩
  let finRight : Fin J → Fin (2 * J) := fun j =>
    ⟨J + j, by simp [two_mul, add_comm]⟩
  let piProj : Fin (2 * J) → V →ₗ[F] Polynomial.degreeLT F (d + 1) := fun i =>
    { toFun := fun v => v i
      map_add' := by intro v w; rfl
      map_smul' := by intro a v; rfl }
  let rjMap : Fin J → V →ₗ[F] Polynomial F := fun j =>
    (Polynomial.degreeLT F (d + 1)).subtype.comp (piProj (finLeft j))
  let sjMap : Fin J → V →ₗ[F] Polynomial F := fun j =>
    (Polynomial.degreeLT F (d + 1)).subtype.comp (piProj (finRight j))
  let rjkMap : Fin ℓ → Fin J → V →ₗ[F] Polynomial F := fun k j =>
    (stepanovHasseQuotMap (F := F) (f := f) hf ℓ k.1).comp (rjMap j)
  let sjkMap : Fin ℓ → Fin J → V →ₗ[F] Polynomial F := fun k j =>
    (stepanovHasseQuotMap (F := F) (f := f) hf (ℓ + c) k.1).comp (sjMap j)
  let sigmaMap : Fin ℓ → V →ₗ[F] Polynomial F := fun k =>
    Finset.sum (Finset.univ : Finset (Fin J))
      (fun j =>
        (polyMulRightLinear (F := F) (Polynomial.X ^ (j : ℕ))).comp
          (rjkMap k j + a • sjkMap k j))
  have h_sigma_deg :
      ∀ k : Fin ℓ, ∀ v : V,
        (sigmaMap k v).natDegree ≤ J - 1 + d + k * (m - 1) := by
    intro k v
    let rjkFin : Fin J → Polynomial F := fun j => rjkMap k j v
    let sjkFin : Fin J → Polynomial F := fun j => sjkMap k j v
    have hdeg_r : ∀ j : Fin J, (rjkFin j).natDegree ≤ d + k * (m - 1) := by
      intro j
      have hk_le : k.1 ≤ ℓ := Nat.le_of_lt k.isLt
      simp only [rjkFin, rjkMap, rjMap]
      exact
        stepanovHasseQuotMap_natDegree_le (F := F) hf m d ℓ k.1 hfdeg hk_le
          _ (natDegree_le_of_mem_degreeLT_succ F d (piProj (finLeft j) v))
    have hdeg_s : ∀ j : Fin J, (sjkFin j).natDegree ≤ d + k * (m - 1) := by
      intro j
      have hk_le : k.1 ≤ ℓ + c := le_trans (Nat.le_of_lt k.isLt) (Nat.le_add_right _ _)
      simp only [sjkFin, sjkMap, sjMap]
      exact
        stepanovHasseQuotMap_natDegree_le (F := F) hf m d (ℓ + c) k.1 hfdeg hk_le
          _ (natDegree_le_of_mem_degreeLT_succ F d (piProj (finRight j) v))
    have hdeg_sum :=
      stepanov_sigma_degree_bound_fin (F := F) (d := d) (k := k) (m := m) (J := J)
        (a := a) rjkFin sjkFin hdeg_r hdeg_s
    have hsum :
        sigmaMap k v =
          ∑ j : Fin J, (rjkFin j + Polynomial.C a * sjkFin j) * Polynomial.X ^ (j : ℕ) := by
      simp [sigmaMap, rjkFin, sjkFin, polyMulRightLinear,
        LinearMap.add_apply, LinearMap.smul_apply, Polynomial.smul_eq_C_mul]
    simpa [hsum] using hdeg_sum
  let sigmaMapLT :
      (k : Fin ℓ) → V →ₗ[F] Polynomial.degreeLT F (J + d + k * (m - 1)) :=
    fun k =>
      LinearMap.codRestrict (Polynomial.degreeLT F (J + d + k * (m - 1))) (sigmaMap k) (by
        intro v
        by_cases hzero : sigmaMap k v = 0
        · simp [hzero]
        · have hdeg_nat : (sigmaMap k v).natDegree < J + d + k * (m - 1) := by
            have hlt : J - 1 + d + k * (m - 1) < J + d + k * (m - 1) := by
              omega
            exact lt_of_le_of_lt (h_sigma_deg k v) hlt
          have hdeg : (sigmaMap k v).degree < (J + d + k * (m - 1) : ℕ) :=
            (Polynomial.natDegree_lt_iff_degree_lt hzero).1 hdeg_nat
          simpa [Polynomial.mem_degreeLT] using hdeg)
  let L : V →ₗ[F] W := LinearMap.pi (fun k => sigmaMapLT k)
  set B : ℕ := ∑ k ∈ Finset.range ℓ, (J + d + k * (m - 1)) with hBdef
  have hW_finrank : Module.finrank F W = B := by
    simpa [W, hBdef] using finrank_stepanov_constraint_space F ℓ J d m
  have h_dim :
      Module.finrank F (Fin B → F) <
        Module.finrank F V := by
    have hB_le : B ≤ ∑ k ∈ Finset.range ℓ, (J + d + k * (m - 1)) := by
      simp [B]
    have h := stepanov_dimension_inequality_ceil
      (F := F) (ℓ := ℓ) (d := d) (m := m) (q := q) (B := B)
      hℓ_pos hm_ge_two hq6m hl hd
      (by
        simpa [J, hJdef, add_comm, add_left_comm, add_assoc] using hB_le)
    simpa [J, hJdef, V] using h
  have hB_lt : B < Module.finrank F V := by
    have hFin : Module.finrank F (Fin B → F) = B := by simp
    simpa [hFin] using h_dim
  have hW_lt : Module.finrank F W < Module.finrank F V := by
    simpa [hW_finrank] using hB_lt
  obtain ⟨v, hv_ne, hv_zero⟩ :=
    exists_nonzero_solution_of_finrank_lt (L := L) (h := by simpa [V] using hW_lt)
  let rj : ℕ → Polynomial F := fun j =>
    if hj : j < J then (rjMap ⟨j, hj⟩ v) else 0
  let sj : ℕ → Polynomial F := fun j =>
    if hj : j < J then (sjMap ⟨j, hj⟩ v) else 0
  have h_nonzero : ∃ j < J, rj j ≠ 0 ∨ sj j ≠ 0 := by
    by_contra h
    push_neg at h
    have hv_zero' : v = 0 := by
      funext i
      have hi : (i : ℕ) < J ∨ J ≤ (i : ℕ) := lt_or_ge (i : ℕ) J
      cases hi with
      | inl hlt =>
          have : rj i = 0 := (h i hlt).1
          change v i = 0
          simpa [rj, hlt, rjMap, piProj, finLeft] using this
      | inr hge =>
          have hj : (i : ℕ) - J < J := by
            have hlt : (i : ℕ) < 2 * J := i.isLt
            omega
          have : sj ((i : ℕ) - J) = 0 := (h ((i : ℕ) - J) hj).2
          have hidx : finRight ⟨(i : ℕ) - J, hj⟩ = i := by
            ext
            simp [finRight, Nat.add_sub_of_le hge]
          change v i = 0
          simpa [sj, hj, sjMap, piProj, hidx] using this
    exact hv_ne hv_zero'
  have hdeg :
      ∀ j < J, (rj j).natDegree ≤ d ∧ (sj j).natDegree ≤ d := by
    intro j hj
    have hr : (rj j).natDegree ≤ d := by
      simp [rj, hj, rjMap, piProj, finLeft,
        natDegree_le_of_mem_degreeLT_succ]
    have hs : (sj j).natDegree ≤ d := by
      simp [sj, hj, sjMap, piProj, finRight,
        natDegree_le_of_mem_degreeLT_succ]
    exact ⟨hr, hs⟩
  have hvan :
      ∀ x : F, f.eval x ≠ 0 → (f.eval x) ^ c = a →
        ∀ k < ℓ,
          Finset.sum (Finset.range J)
            (fun j =>
              (((hasseDerivOp F k (f ^ ℓ * rj j)) / f ^ (ℓ - k)).eval x +
                  a *
                    ((hasseDerivOp F k (f ^ (ℓ + c) * sj j)) /
                        f ^ (ℓ + c - k)).eval x) *
                x ^ j) = 0 := by
    intro x _hx _hxa k hk
    have hLk : sigmaMapLT ⟨k, hk⟩ v = 0 := by
      exact congrArg (fun f => f ⟨k, hk⟩) hv_zero
    have hpoly_zero : sigmaMap ⟨k, hk⟩ v = 0 := by
      have := congrArg Subtype.val hLk
      simpa [sigmaMapLT] using this
    have hsum_eval :
        (sigmaMap ⟨k, hk⟩ v).eval x =
          Finset.sum (Finset.range J)
            (fun j =>
              (((hasseDerivOp F k (f ^ ℓ * rj j)) / f ^ (ℓ - k)).eval x +
                  a *
                    ((hasseDerivOp F k (f ^ (ℓ + c) * sj j)) /
                        f ^ (ℓ + c - k)).eval x) *
                x ^ j) := by
      classical
      let p : Fin J → Polynomial F := fun j =>
        hasseDerivOp F k (f ^ ℓ * (rjMap j v)) / f ^ (ℓ - k) +
          Polynomial.C a *
            (hasseDerivOp F k (f ^ (ℓ + c) * (sjMap j v)) / f ^ (ℓ + c - k))
      have hsum_poly :
          sigmaMap ⟨k, hk⟩ v =
            ∑ j : Fin J,
              p j * Polynomial.X ^ (j : ℕ) := by
        simp [p, sigmaMap, rjkMap, sjkMap, stepanovHasseQuotMap_eq_div_left,
          polyMulRightLinear, LinearMap.comp_apply, LinearMap.add_apply,
          LinearMap.smul_apply, Polynomial.smul_eq_C_mul]
      have hsum_eval_fin :
          (sigmaMap ⟨k, hk⟩ v).eval x =
            ∑ j : Fin J,
              (p j).eval x * x ^ (j : ℕ) := by
        have :=
          (Polynomial.eval_finset_sum (s := (Finset.univ : Finset (Fin J)))
            (g := fun j : Fin J => p j * Polynomial.X ^ (j : ℕ)) (x := x))
        simpa [hsum_poly] using this
      have hsum_eval_fin' :
          (sigmaMap ⟨k, hk⟩ v).eval x =
            ∑ j : Fin J,
              ((hasseDerivOp F k (f ^ ℓ * (rjMap j v)) / f ^ (ℓ - k)).eval x +
                a *
                  (hasseDerivOp F k (f ^ (ℓ + c) * (sjMap j v)) /
                    f ^ (ℓ + c - k)).eval x) *
                x ^ (j : ℕ) := by
        simpa [p, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
          mul_add, mul_assoc] using hsum_eval_fin
      let G : Fin J → F := fun j =>
        ((hasseDerivOp F k (f ^ ℓ * (rjMap j v)) / f ^ (ℓ - k)).eval x +
            a *
              (hasseDerivOp F k (f ^ (ℓ + c) * (sjMap j v)) /
                f ^ (ℓ + c - k)).eval x) *
          x ^ (j : ℕ)
      have hsum_eval_finG :
          (sigmaMap ⟨k, hk⟩ v).eval x = ∑ j : Fin J, G j := by
        simpa [G] using hsum_eval_fin'
      let GNat : ℕ → F := fun j =>
        if hj : j < J then G ⟨j, hj⟩ else 0
      have hsum_eval_finGNat :
          (sigmaMap ⟨k, hk⟩ v).eval x = ∑ j : Fin J, GNat j := by
        refine hsum_eval_finG.trans ?_
        refine Finset.sum_congr rfl ?_
        intro j hj
        simp [GNat, j.isLt]
      have hsum_range := (Fin.sum_univ_eq_sum_range (n := J) (f := GNat))
      refine (hsum_eval_finGNat.trans hsum_range).trans ?_
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hj' : j < J := by
        simpa using (Finset.mem_range.mp hj)
      simp [GNat, G, rj, sj, hj']
    have : (sigmaMap ⟨k, hk⟩ v).eval x = 0 := by
      simp [hpoly_zero]
    simpa [hsum_eval] using this
  refine ⟨rj, sj, h_nonzero, hdeg, hvan⟩
