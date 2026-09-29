-- Prove2me | solution 1 for mme_CW_2376_target_table_factorial_dominates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T23:34:59.740267+00:00
-- url     : https://prove2.me/submissions/cfdd7671-1f05-44a4-8643-1a96c3a147c3

import Definitions.Def_mme_CW_2376_marginal_joint_tables
import Theorems.Thm_mme_CW_2376_target_factorial_profile_dominates
import Theorems.Thm_mme_CW_2376_target_joint_table_marginal

open MME BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

private theorem sum_ite_eq_sum_subtype
    {beta iota M : Type*} [Fintype beta] [DecidableEq iota]
    [AddCommMonoid M] (q : beta → iota) (i : iota) (f : beta → M) :
    (∑ b : beta, if q b = i then f b else 0) =
      ∑ b : {b : beta // q b = i}, f b.1 := by
  classical
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype
    ((Finset.univ : Finset beta).filter (fun b => q b = i))
    (fun b => by simp) f

private theorem sum_by_fibers
    {beta iota M : Type*} [Fintype beta] [Fintype iota]
    [DecidableEq iota] [AddCommMonoid M]
    (q : beta → iota) (f : beta → M) :
    (∑ b : beta, f b) =
      ∑ i : iota, ∑ b : {b : beta // q b = i}, f b.1 := by
  classical
  calc
    (∑ b : beta, f b) =
        ∑ x : Sigma fun i : iota => {b : beta // q b = i},
          f x.2.1 := by
      exact (Equiv.sum_comp (Equiv.sigmaFiberEquiv q) f).symm
    _ = ∑ i : iota, ∑ b : {b : beta // q b = i}, f b.1 :=
      Fintype.sum_sigma _

/-- The optimized target factorial denominator is no larger than that of
any supported joint table with the same three five-grade marginals. -/
theorem solution
    (m : ℕ) (hm : 0 < m) (k : CW2376JointMultiplicityTable)
    (hkMarginal : ∀ l : Fin 3, ∀ r : Fin 5,
      (∑ sigma : {sigma : CW2376SupportedJointType //
          sigma.1 l = r}, k sigma.1) =
        cw2376MarginalMultiplicity m r) :
    (∏ sigma : CW2376SupportedJointType,
        (cw2376TargetJointTable m sigma).factorial) ≤
      ∏ sigma : CW2376SupportedJointType, (k sigma).factorial := by
  classical
  let kExt : (Fin 3 → Fin 5) → ℕ := fun sigma =>
    if h : sigma ∈ cw2376TargetJointTypes then k ⟨sigma, h⟩ else 0
  have hrowK (l : Fin 3) (r : Fin 5) :
      (∑ sigma ∈ cw2376TargetJointTypes,
        if sigma l = r then kExt sigma else 0) =
        cw2376MarginalMultiplicity m r := by
    rw [Finset.sum_subtype cw2376TargetJointTypes
      (fun sigma => Iff.rfl)]
    calc
      (∑ sigma : CW2376SupportedJointType,
          if sigma.1 l = r then kExt sigma.1 else 0) =
          ∑ sigma : CW2376SupportedJointType,
            if sigma.1 l = r then k sigma else 0 := by
        apply Finset.sum_congr rfl
        intro sigma hsigma
        by_cases hgrade : sigma.1 l = r
        · simp [hgrade, kExt, sigma.2]
        · simp [hgrade]
      _ = ∑ sigma : {sigma : CW2376SupportedJointType //
            sigma.1 l = r}, k sigma.1 :=
        sum_ite_eq_sum_subtype
          (fun sigma : CW2376SupportedJointType => sigma.1 l) r k
      _ = cw2376MarginalMultiplicity m r := hkMarginal l r
  have hrowTarget (l : Fin 3) (r : Fin 5) :
      (∑ sigma ∈ cw2376TargetJointTypes,
        if sigma l = r then cw2376ProfileMultiplicity m sigma else 0) =
        cw2376MarginalMultiplicity m r := by
    rw [Finset.sum_subtype cw2376TargetJointTypes
      (fun sigma => Iff.rfl)]
    change (∑ sigma : CW2376SupportedJointType,
      if sigma.1 l = r then cw2376TargetJointTable m sigma else 0) = _
    rw [sum_ite_eq_sum_subtype
      (fun sigma : CW2376SupportedJointType => sigma.1 l) r
      (cw2376TargetJointTable m)]
    exact mme_CW_2376_target_joint_table_marginal m l r
  have ha (l : Fin 3) (r : Fin 5) :
      (∑ sigma ∈ cw2376TargetJointTypes,
        if sigma l = r then kExt sigma else 0) =
      ∑ sigma ∈ cw2376TargetJointTypes,
        if sigma l = r then cw2376ProfileMultiplicity m sigma else 0 :=
    (hrowK l r).trans (hrowTarget l r).symm
  have hsumK :
      (∑ sigma ∈ cw2376TargetJointTypes, kExt sigma) =
        ∑ sigma : CW2376SupportedJointType, k sigma := by
    rw [Finset.sum_subtype cw2376TargetJointTypes
      (fun sigma => Iff.rfl)]
    apply Finset.sum_congr rfl
    intro sigma hsigma
    simp only [kExt, dif_pos sigma.2]
  have hsumTarget :
      (∑ sigma ∈ cw2376TargetJointTypes,
          cw2376ProfileMultiplicity m sigma) =
        ∑ sigma : CW2376SupportedJointType,
          cw2376TargetJointTable m sigma := by
    rw [Finset.sum_subtype cw2376TargetJointTypes
      (fun sigma => Iff.rfl)]
    rfl
  have htotalSupported :
      (∑ sigma : CW2376SupportedJointType, k sigma) =
        ∑ sigma : CW2376SupportedJointType,
          cw2376TargetJointTable m sigma := by
    calc
      (∑ sigma : CW2376SupportedJointType, k sigma) =
          ∑ r : Fin 5,
            ∑ sigma : {sigma : CW2376SupportedJointType //
              sigma.1 0 = r}, k sigma.1 :=
        sum_by_fibers
          (fun sigma : CW2376SupportedJointType => sigma.1 0) k
      _ = ∑ r : Fin 5, cw2376MarginalMultiplicity m r := by
        apply Finset.sum_congr rfl
        intro r hr
        exact hkMarginal 0 r
      _ = ∑ r : Fin 5,
            ∑ sigma : {sigma : CW2376SupportedJointType //
              sigma.1 0 = r}, cw2376TargetJointTable m sigma.1 := by
        apply Finset.sum_congr rfl
        intro r hr
        exact (mme_CW_2376_target_joint_table_marginal m 0 r).symm
      _ = ∑ sigma : CW2376SupportedJointType,
          cw2376TargetJointTable m sigma :=
        (sum_by_fibers
          (fun sigma : CW2376SupportedJointType => sigma.1 0)
          (cw2376TargetJointTable m)).symm
  have htotal :
      (∑ sigma ∈ cw2376TargetJointTypes, kExt sigma) =
        ∑ sigma ∈ cw2376TargetJointTypes,
          cw2376ProfileMultiplicity m sigma := by
    rw [hsumK, hsumTarget]
    exact htotalSupported
  have hdom := mme_CW_2376_target_factorial_profile_dominates
    m hm kExt ha htotal
  have hK : ∀ sigma : CW2376SupportedJointType, kExt sigma.1 = k sigma := by
    intro sigma
    simp only [kExt, dif_pos sigma.2]
  rw [Finset.prod_subtype cw2376TargetJointTypes
    (fun sigma => Iff.rfl)] at hdom
  rw [Finset.prod_subtype cw2376TargetJointTypes
    (fun sigma => Iff.rfl)] at hdom
  simp only [hK] at hdom
  exact hdom
