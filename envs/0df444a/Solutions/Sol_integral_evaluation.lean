-- Prove2me | solution 1 for integral_evaluation
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-07-29T18:23:41.392064+00:00
-- url     : https://prove2.me/submissions/6dc23fb8-38e8-4330-80f7-1ffe4ad17e97

import Mathlib.Algebra.Group.Support
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.Chebyshev
import Batteries.Tactic.Lemma
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Notation.Support
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Bound
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Definitions.Def_EulerMaclaurin_defs
import Definitions.Def_Fourier_defs
import Definitions.Def_MediumPNT_defs
import Definitions.Def_MellinCalculus_defs
import Definitions.Def_Rectangle_defs
import Definitions.Def_ResidueCalcOnRectangles_defs
import Definitions.Def_ZetaBounds_defs

set_option lang.lemmaCmd true

open Set Function Filter Complex Real

open ArithmeticFunction (vonMangoldt)
open scoped Chebyshev

local notation (name := mellintransform2) "𝓜" => mellin

local notation "Λ" => vonMangoldt

local notation "ζ" => riemannZeta

local notation "ζ'" => deriv ζ

open Chebyshev

open ComplexConjugate

open MeasureTheory

-- TODO: add to mathlib
attribute [fun_prop] Continuous.const_cpow

--open scoped ArithmeticFunction in

-- TODO : Move elsewhere (should be in Mathlib!) NOT NEEDED

theorem ae_volume_of_contains_compl_singleton_zero
  (s : Set ℝ)
  (h : (univ : Set ℝ) \ {0} ⊆ s) :
  s ∈ (MeasureTheory.ae volume) := by
  -- The key insight is that {0} has measure zero in ℝ
  have h_zero_null : volume ({0} : Set ℝ) = 0 := by
    exact volume_singleton

  -- Since s contains univ \ {0} = ℝ \ {0}, its complement is contained in {0}
  have h_compl_subset : sᶜ ⊆ {0} := by
    intro x hx
    -- If x is not in s, then x is not in ℝ \ {0} (since ℝ \ {0} is a subset of s)
    -- This means x = 0
    by_contra h_not_zero
    have : x ∈ univ \ {0} := ⟨trivial, h_not_zero⟩
    exact hx (h this)

  -- Therefore, volume(sᶜ) ≤ volume({0}) = 0
  have h_compl_measure : volume sᶜ ≤ volume ({0} : Set ℝ) :=
    measure_mono h_compl_subset

  -- So volume(sᶜ) = 0
  have h_compl_zero : volume sᶜ = 0 := by
    rw [h_zero_null] at h_compl_measure
    exact le_antisymm h_compl_measure (by positivity)

  -- A set is in ae.sets iff its complement has measure zero
  rwa [mem_ae_iff]

theorem solution (x : ℝ) (T : ℝ) (T_large : 3 < T) :
    ∫ (t : ℝ) in Iic (-T), (‖x + t * I‖ ^ 2)⁻¹ ≤ T⁻¹ := by
  have T00 : ∀ (x t : ℝ), t^2 ≤ ‖x + t * I‖^2 := by
    intro x t
    rw [Complex.norm_add_mul_I x t]
    ring_nf
    rw [Real.sq_sqrt _]
    · simp only [le_add_iff_nonneg_right]; positivity
    · positivity

  have T0 : ∀ (x t : ℝ), t ≠ 0 → (‖x + t * I‖^2)⁻¹ ≤ (t^2)⁻¹ := by
    intro x t hyp
    have U0 : 0 < t^2 := by positivity
    have U1 : 0 < ‖x + t * I‖^2 := by
      rw [Complex.norm_add_mul_I x t,
        Real.sq_sqrt _]

      · positivity
      · positivity
    rw [inv_le_inv₀ U1 U0]
    exact (T00 x t)

  have T1 : (fun (t : ℝ) ↦ (‖x + t * I‖^2)⁻¹) ≤ᶠ[ae (volume.restrict (Iic (-T)))] (fun (t : ℝ) ↦ (t^2)⁻¹) := by
    unfold Filter.EventuallyLE
    unfold Filter.Eventually
    simp_all only [ne_eq, measurableSet_Iic, ae_restrict_eq]
    refine mem_inf_of_left ?_
    · refine Filter.mem_sets.mp ?_
      · have U :  {x_1 : ℝ | x_1 ≠ 0} ⊆ {x_1 : ℝ | (‖x + x_1 * I‖ ^ 2)⁻¹ ≤ (x_1 ^ 2)⁻¹}  := by
          rw [Set.setOf_subset_setOf]
          intro t hyp_t
          exact T0 x t hyp_t
        have U1 : {x_1 : ℝ | x_1 ≠ 0} = (univ \ {0}) := by
          apply Set.ext
          intro x
          simp_all only [ne_eq, setOf_subset_setOf, not_false_eq_true, implies_true,
            mem_setOf_eq, mem_diff, mem_univ, mem_singleton_iff, true_and]

        rw [U1] at U
        exact ae_volume_of_contains_compl_singleton_zero _ U

  have T3 : Integrable (fun (t : ℝ) ↦ (t^2)⁻¹) (volume.restrict (Iic (-T))) := by
    have D3 := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
      (by linarith : 0 < T) |>.comp_neg
    simp only [rpow_neg_ofNat, Int.reduceNeg, zpow_neg, neg_Ioi] at D3
    have D4 :=
      (integrableOn_Iic_iff_integrableOn_Iio'
        (by
          refine EReal.coe_ennreal_ne_coe_ennreal_iff.mp ?_
          simp_all only [ne_eq, measurableSet_Iic, ae_restrict_eq, measure_singleton,
            EReal.coe_ennreal_zero, EReal.coe_ennreal_top, EReal.zero_ne_top, not_false_eq_true])).mpr D3
    simp_all only [ne_eq, measurableSet_Iic, ae_restrict_eq]
    unfold IntegrableOn at D4
    have eq_fun : (fun (x : ℝ) ↦ ((-x)^2)⁻¹) = fun x ↦ (x^2)⁻¹ := by
      funext x
      simp_all only [even_two, Even.neg_pow]
    simp_all only [even_two, Even.neg_pow]
    norm_cast at D4
    simp_all only [even_two, Even.neg_pow]

  calc
    _ ≤ ∫ (t : ℝ) in Iic (-T), (t^2)⁻¹  := by
      apply MeasureTheory.integral_mono_of_nonneg _ T3 T1
      filter_upwards [] with x
      simp
    _ = _ := by
      rw [← integral_comp_neg_Ioi]
      conv => lhs; arg 2; ext x; rw [show ((-x) ^ 2)⁻¹ = x ^ (-2 : ℝ) by simp [zpow_ofNat]]
      rw[integral_Ioi_rpow_of_lt (by norm_num) (by linarith)]
      ring_nf
      rw [rpow_neg_one]

open Filter Topology

-- `x * rexp (-c * (log x) ^ B)) = Real.exp (Real.log x - c * (Real.log x) ^ B))`
-- so if `B < 1`, the exponent goes to infinity
