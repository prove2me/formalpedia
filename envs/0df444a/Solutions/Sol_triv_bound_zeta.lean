-- Prove2me | solution 1 for triv_bound_zeta
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-07-29T18:37:32.68336+00:00
-- url     : https://prove2.me/submissions/75796915-2b49-4641-b34d-ea5508df8ae6

import Batteries.Tactic.Lemma
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Definitions.Def_EulerMaclaurin_defs
import Definitions.Def_Fourier_defs
import Definitions.Def_Rectangle_defs
import Definitions.Def_ResidueCalcOnRectangles_defs
import Definitions.Def_ZetaBounds_defs
import Theorems.Thm_dlog_riemannZeta_bdd_on_vertical_lines_generalized
import Theorems.Thm_riemannZetaLogDerivResidue

set_option lang.lemmaCmd true

open Complex Topology Filter Interval Set Asymptotics

local notation (name := riemannzeta) "ζ" => riemannZeta
local notation (name := derivriemannzeta) "ζ'" => deriv riemannZeta

-- Main theorem: if functions agree on a punctured set, their derivatives agree there too

/- New two theorems to be proven -/

-- Alternative cleaner proof using more direct approach

/- The set should be open so that f'(p) = O(1) for all p ∈ U -/

/-- We use `ζ` to denote the Rieman zeta function and `ζ₀` to denote the alternative Rieman zeta
function. -/
local notation (name := riemannzeta0) "ζ₀" => riemannZeta0

-- move near `Real.differentiableAt_rpow_const_of_ne`

-- MOVE TO MATHLIB near `differentiableAt_riemannZeta`

-- **Another AlphaProof collaboration (thanks to Thomas Hubert!)**

-- **End collaboration 6/20/25**

/-% ** Bad delimiters on purpose **
Annoying: we have reciprocals of $log |t|$ in the bounds, and we've assumed that $|t|>3$; but we
want to make things uniform in $t$. Let's change to things like $log (|t|+3)$ instead of $log |t|$.
\begin{lemma}[LogLeLog]\label{LogLeLog}\lean{LogLeLog}\leanok
There is a constant $C>0$ so that for all $t>3$,
$$
1/\log t \le C / \log (t + 3).
$$
\end{lemma}
%-/
/-%
\begin{proof}
Write
$$
\log (t + 3) = \log t + \log (1 + 3/t) = \log t + O(1/t).
$$
Then we can bound $1/\log t$ by $C / \log (t + 3)$ for some constant $C>0$.
\end{proof}
%-/

-- **Begin collaboration with the Alpha Proof team! 5/29/25**

-- **End collaboration**

open ArithmeticFunction (vonMangoldt)
local notation "Λ" => vonMangoldt
--TODO generalize to any LSeries with nonnegative coefficients

theorem solution :  ∃C ≥ 0, ∀(σ₀ t : ℝ), 1 < σ₀ →
    ‖- ζ' (σ₀ + t * I) / ζ (σ₀ + t * I)‖ ≤ (σ₀ - 1)⁻¹ + C := by
  let ⟨U, ⟨U_in_nhds, zeta_residue_on_U⟩⟩ := riemannZetaLogDerivResidue
  let ⟨open_in_U, ⟨open_in_U_subs_U, open_in_U_is_open, one_in_open_U⟩⟩ :=
    mem_nhds_iff.mp U_in_nhds
  let ⟨ε₀, ⟨ε_pos, metric_ball_around_1_is_in_U'⟩⟩ :=
    EMetric.isOpen_iff.mp open_in_U_is_open (1 : ℂ) one_in_open_U

  let ε := if ε₀ = ⊤ then ENNReal.ofReal 1 else ε₀
  have O1 : ε ≠ ⊤ := by
    unfold ε
    by_cases h : ε₀ = ⊤ <;> simp [*]

  have metric_ball_around_1_is_in_U :
    Metric.eball (1 : ℂ) ε ⊆ U := by
      unfold ε
      by_cases h : ε₀ = ⊤
      · simp only [↓reduceIte, ENNReal.ofReal_one, h]
        have T : Metric.eball (1 : ℂ) 1 ⊆ Metric.eball 1 ε₀ := by
          simp [*]
        exact subset_trans (subset_trans T metric_ball_around_1_is_in_U') open_in_U_subs_U

      · simp only [h, ↓reduceIte]
        exact subset_trans metric_ball_around_1_is_in_U' open_in_U_subs_U

  have O2 : ε ≠ 0 := by
    unfold ε
    by_cases h : ε₀ = ⊤
    · simp [*]
    · simp only [↓reduceIte, ne_eq, h]
      exact pos_iff_ne_zero.mp ε_pos

  let metric_ball_around_1 := Metric.eball (1 : ℂ) ε
  let ε_div_two := ε / 2
  let boundary := ENNReal.toReal (1 + ε_div_two)

  let ⟨bound, ⟨bound_pos, bound_prop⟩⟩ :=
      BddAbove.exists_ge zeta_residue_on_U 0

  have boundary_geq_one : 1 < boundary := by
      unfold boundary
      have Z : (1 : ENNReal).toReal = 1 := by rfl
      rw [←Z]
      have U : ε_div_two ≠ ⊤ := by
        refine ENNReal.div_ne_top O1 ?_
        simp
      simp only [ENNReal.toReal_one, ne_eq, ENNReal.one_ne_top, not_false_eq_true,
        ENNReal.toReal_add _ U, lt_add_iff_pos_right, gt_iff_lt]
      refine ENNReal.toReal_pos ?_ ?_
      · unfold ε_div_two
        simp [*]
      · exact U

  let const : ℝ := bound
  let final_const : ℝ := (boundary - 1)⁻¹ + const
  have final_const_pos : final_const ≥ 0 := by bound
  have const_le_final_const : const ≤ final_const := by bound

  /- final const is actually the constant that we will use -/

  refine ⟨final_const, final_const_pos, fun σ₀ t σ₀_gt ↦ ?_⟩
  have U4 : ENNReal.ofReal 1 ≠ ⊤ := by exact ENNReal.ofReal_ne_top
  have Z0 : ε_div_two.toReal < ε.toReal := by
    exact ENNReal.toReal_strict_mono O1 <| ENNReal.half_lt_self O2 O1

  -- Pick a neighborhood, if in neighborhood then we are good
  -- If outside of the neighborhood then use that ζ' / ζ is monotonic
  -- and take the bound to be the edge but this will require some more work

  by_cases! h : σ₀ ≤ boundary
  · have σ₀_in_ball : (↑σ₀ : ℂ) ∈ metric_ball_around_1 := by
      unfold metric_ball_around_1
      unfold Metric.eball
      simp only [mem_setOf_eq]
      rw [edist_dist, dist_eq_norm]
      norm_cast
      have U : 0 ≤ σ₀ - 1 := by linarith
      simp only [Real.norm_of_nonneg U, gt_iff_lt]
      simp only [ENNReal.ofReal_lt_iff_lt_toReal U O1]
      calc
        _ ≤ boundary - 1 := by linarith
        _ = ENNReal.toReal (1 + ε_div_two) - 1 := rfl
        _ = ENNReal.toReal (1 + ε_div_two) - ENNReal.toReal (ENNReal.ofReal 1) := by simp
        _ ≤ ENNReal.toReal (1 + ε_div_two - ENNReal.ofReal 1) := ENNReal.le_toReal_sub U4
        _ = ENNReal.toReal (ε_div_two) := by
          simp only [ENNReal.ofReal_one, ENNReal.addLECancellable_iff_ne, ne_eq,
            ENNReal.one_ne_top, not_false_eq_true, AddLECancellable.add_tsub_cancel_left]
        _ < ε.toReal := Z0

    have σ₀_in_U : (↑σ₀ : ℂ) ∈ (U \ {1}) := by
      refine mem_diff_singleton.mpr ?_
      constructor
      · exact metric_ball_around_1_is_in_U σ₀_in_ball
      · by_contra a
        have U : σ₀ = 1 := by exact ofReal_eq_one.mp a
        rw [U] at σ₀_gt
        linarith

    have bdd := Set.forall_mem_image.mp bound_prop (σ₀_in_U)
    simp only [Function.comp_apply, Pi.sub_apply, Pi.neg_apply, Pi.div_apply] at bdd

    calc
      _ ≤ ‖ζ' σ₀ / ζ σ₀‖ := by
        exact dlog_riemannZeta_bdd_on_vertical_lines_generalized σ₀ σ₀ t (σ₀_gt) (by simp)
      _ = ‖- ζ' σ₀ / ζ σ₀‖ := by simp only [Complex.norm_div, norm_neg]
      _ = ‖(- ζ' σ₀ / ζ σ₀ - (σ₀ - 1)⁻¹) + (σ₀ - 1)⁻¹‖ := by
        simp only [Complex.norm_div, norm_neg, ofReal_inv, ofReal_sub, ofReal_one, sub_add_cancel]
      _ ≤ ‖(- ζ' σ₀ / ζ σ₀ - (σ₀ - 1)⁻¹)‖ + ‖(σ₀ - 1)⁻¹‖ := by
        have Z := norm_add_le (- ζ' σ₀ / ζ σ₀ - (σ₀ - 1)⁻¹) ((σ₀ - 1)⁻¹)
        norm_cast at Z
      _ ≤ const + ‖(σ₀ - 1)⁻¹‖ := by
        have U := add_le_add_left bdd ‖(σ₀ - 1)⁻¹‖
        ring_nf at U
        ring_nf
        norm_cast at U
        norm_cast
      _ ≤ const + (σ₀ - 1)⁻¹ := by
        simp [norm_inv]
        have pos : 0 ≤ σ₀ - 1 := by
          linarith
        simp [abs_of_nonneg pos]
      _ = (σ₀ - 1)⁻¹ + const := by
        rw [add_comm]
      _ ≤ (σ₀ - 1)⁻¹ + final_const := by
        simp [const_le_final_const]

  · have boundary_in_ball : (↑boundary : ℂ) ∈ metric_ball_around_1 := by
      unfold metric_ball_around_1
      unfold Metric.eball
      simp only [mem_setOf_eq]
      rw [edist_dist, dist_eq_norm]
      norm_cast
      have U : 0 ≤ boundary - 1 := by linarith
      simp only [Real.norm_of_nonneg U, gt_iff_lt]
      simp only [ENNReal.ofReal_lt_iff_lt_toReal U O1]
      calc
        _ = ENNReal.toReal (1 + ε_div_two) - 1 := rfl
        _ = ENNReal.toReal (1 + ε_div_two) - ENNReal.toReal (ENNReal.ofReal 1) := by simp
        _ ≤ ENNReal.toReal (1 + ε_div_two - ENNReal.ofReal 1) := ENNReal.le_toReal_sub U4
        _ = ENNReal.toReal (ε_div_two) := by
          simp only [ENNReal.ofReal_one, ENNReal.addLECancellable_iff_ne, ne_eq,
            ENNReal.one_ne_top, not_false_eq_true, AddLECancellable.add_tsub_cancel_left]
        _ < ε.toReal := Z0

    have boundary_in_U : (↑boundary : ℂ) ∈ U \ {1} := by
      refine mem_diff_singleton.mpr ?_
      constructor
      · exact metric_ball_around_1_is_in_U boundary_in_ball
      · by_contra a
        norm_cast at a
        norm_cast at boundary_geq_one
        simp [←a] at boundary_geq_one

    have bdd := Set.forall_mem_image.mp bound_prop (boundary_in_U)
    simp only [Function.comp_apply, Pi.sub_apply, Pi.neg_apply, Pi.div_apply] at bdd

    calc
      _ ≤ ‖ζ' boundary / ζ boundary‖ := by
        exact dlog_riemannZeta_bdd_on_vertical_lines_generalized boundary σ₀ t
          (boundary_geq_one) (by linarith)
      _ = ‖- ζ' boundary / ζ boundary‖ := by simp only [Complex.norm_div, norm_neg]
      _ = ‖(- ζ' boundary / ζ boundary - (boundary - 1)⁻¹) + (boundary - 1)⁻¹‖ := by
        simp only [Complex.norm_div, norm_neg, ofReal_inv, ofReal_sub, ofReal_one, sub_add_cancel]
      _ ≤ ‖(- ζ' boundary / ζ boundary - (boundary - 1)⁻¹)‖ + ‖(boundary - 1)⁻¹‖ := by
        have Z := norm_add_le (- ζ' boundary / ζ boundary - (boundary - 1)⁻¹) ((boundary - 1)⁻¹)
        norm_cast at Z
      _ ≤ const + ‖(boundary - 1)⁻¹‖ := by
        have U9 := add_le_add_left bdd ‖(boundary - 1)⁻¹‖
        ring_nf at U9
        ring_nf
        norm_cast at U9
        norm_cast
      _ ≤ const + (boundary - 1)⁻¹ := by
        simp [norm_inv]
        have pos : 0 ≤ boundary - 1 := by
          linarith
        simp [abs_of_nonneg pos]
      _ = (boundary - 1)⁻¹ + const := by
        rw [add_comm]
      _ = final_const := by rfl
      _ ≤ _ := by bound
