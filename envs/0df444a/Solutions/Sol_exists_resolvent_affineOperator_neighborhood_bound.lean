-- Prove2me | solution 1 for exists_resolvent_affineOperator_neighborhood_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:28:32.090509+00:00
-- url     : https://prove2.me/submissions/f0150e8f-b5d6-49eb-95a2-0059e1cecd6f

import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelWinding
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Definitions.Def_Operator_Crouzeix_ResolventContourHomotopy
import Theorems.Thm_SmoothJordanDomain_canonicalOrientation_carrier
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_boundaryParam
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_carrier
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_mem_numericalRange
attribute [local simp] SmoothJordanDomain.canonicalOrientation_carrier
attribute [local simp] SmoothJordanDomain.reverseOrientation_boundaryParam
attribute [local simp] SmoothJordanDomain.reverseOrientation_carrier
attribute [local simp] crouzeixPolynomialScalarCompanionBoundaryValue_zero
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero
attribute [local simp] crouzeixPolynomialScalarCompanionRegularized_zero
attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex Filter MeasureTheory Metric Set spectrum
open scoped InnerProductSpace Interval Pointwise Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (B D : E →L[ℂ] E) (Omega : SmoothJordanDomain) (s : ℂ)
    (hres : ∀ t : ℝ,
      Omega.boundaryParam t ∈ resolventSet ℂ (B + s • D)) :
    ∃ epsilon C : ℝ, 0 < epsilon ∧ 0 ≤ C ∧
      ∀ w ∈ ball s epsilon, ∀ t : ℝ,
        Omega.boundaryParam t ∈ resolventSet ℂ (B + w • D) ∧
          ‖resolvent (B + w • D) (Omega.boundaryParam t)‖ ≤ C := by
  let base : ℂ × ℝ → (E →L[ℂ] E) := fun p =>
    Omega.boundaryParam p.2 • (1 : E →L[ℂ] E) - (B + p.1 • D)
  let N : Set (ℂ × ℝ) := {p | IsUnit (base p)}
  have hbasecont : Continuous base := by
    dsimp only [base]
    exact
      ((Omega.boundaryParam_contDiff.continuous.comp continuous_snd).smul
        continuous_const).sub
        (continuous_const.add (continuous_fst.smul continuous_const))
  have hNopen : IsOpen N := by
    exact Units.isOpen.preimage hbasecont
  have hprodSubset : ({s} : Set ℂ) ×ˢ Icc (0 : ℝ) (2 * Real.pi) ⊆ N := by
    rintro ⟨w, t⟩ ⟨hw, _⟩
    simp only [mem_singleton_iff] at hw
    subst w
    exact (mem_resolventSet_iff.mp (hres t))
  obtain ⟨U, V, hUopen, _hVopen, hsU, hIV, hUV⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_Icc hNopen hprodSubset
  obtain ⟨delta, hdelta, hballU⟩ :=
    (Metric.isOpen_iff.mp hUopen) s (hsU (mem_singleton s))
  let epsilon : ℝ := delta / 2
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon]
    linarith
  let K : Set (ℂ × ℝ) :=
    closedBall s epsilon ×ˢ Icc (0 : ℝ) (2 * Real.pi)
  have hKcompact : IsCompact K :=
    IsCompact.prod (isCompact_closedBall s epsilon) isCompact_Icc
  have hKsubset : K ⊆ N := by
    rintro ⟨w, t⟩ ⟨hw, ht⟩
    apply hUV
    constructor
    · apply hballU
      change w ∈ closedBall s epsilon at hw
      change w ∈ ball s delta
      rw [mem_closedBall] at hw
      rw [mem_ball]
      dsimp only [epsilon] at hw
      linarith
    · exact hIV ht
  let Rfun : ℂ × ℝ → (E →L[ℂ] E) := fun p =>
    resolvent (B + p.1 • D) (Omega.boundaryParam p.2)
  have hRcont : ContinuousOn Rfun K := by
    intro p hp
    have hpN : p ∈ N := hKsubset hp
    have hunit : IsUnit (base p) := hpN
    have hinv := (NormedRing.inverse_continuousAt hunit.unit).comp_of_eq
      hbasecont.continuousAt rfl
    exact hinv.continuousWithinAt
  have himage : IsCompact (Rfun '' K) :=
    hKcompact.image_of_continuousOn hRcont
  obtain ⟨C, hCbound⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : E →L[ℂ] E)).mp
      himage.isBounded
  have hzeroIcc : (0 : ℝ) ∈ Icc (0 : ℝ) (2 * Real.pi) :=
    ⟨le_rfl, Real.two_pi_pos.le⟩
  have hsK : (s, (0 : ℝ)) ∈ K := by
    exact ⟨mem_closedBall_self hepsilon.le, hzeroIcc⟩
  have hCnonneg : 0 ≤ C := by
    have hmem := hCbound ⟨(s, 0), hsK, rfl⟩
    rw [mem_closedBall, dist_zero_right] at hmem
    exact (norm_nonneg _).trans hmem
  refine ⟨epsilon, C, hepsilon, hCnonneg, ?_⟩
  intro w hw t
  obtain ⟨u, hu, htu⟩ :=
    Omega.boundaryParam_periodic.exists_mem_Ico₀ Real.two_pi_pos t
  have huIcc : u ∈ Icc (0 : ℝ) (2 * Real.pi) := ⟨hu.1, hu.2.le⟩
  have hwclosed : w ∈ closedBall s epsilon :=
    ball_subset_closedBall hw
  have hwuK : (w, u) ∈ K := ⟨hwclosed, huIcc⟩
  have hwuN : (w, u) ∈ N := hKsubset hwuK
  constructor
  · rw [htu]
    exact mem_resolventSet_iff.mpr hwuN
  · have hmem := hCbound ⟨(w, u), hwuK, rfl⟩
    rw [mem_closedBall, dist_zero_right] at hmem
    rw [htu]
    exact hmem
