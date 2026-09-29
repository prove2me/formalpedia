-- Prove2me | solution 1 for hasDerivAt_Zeta0Integral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-07-29T17:40:30.33749+00:00
-- url     : https://prove2.me/submissions/7e62e7c8-1e5f-49be-af0f-0c5a55640043

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
import Theorems.Thm_ZetaSum_aux1_3
import Theorems.Thm_integrableOn_of_Zeta0_fun
import Theorems.Thm_integrableOn_of_Zeta0_fun_log
import Theorems.Thm_integrable_log_over_pow

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

private noncomputable def Z0F (z : ℂ) (x : ℝ) : ℂ := (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-z - 1)
private noncomputable def Z0F' (z : ℂ) (x : ℝ) : ℂ :=
  (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-z - 1) * (-Real.log x)
private noncomputable def Z0bound (s : ℂ) (x : ℝ) : ℝ := ‖x ^ (-s.re / 2 - 1)‖ * ‖Real.log x‖

open MeasureTheory in
theorem solution {N : ℕ} (Npos : 0 < N) {s : ℂ} (hs : s ∈ {s | 0 < s.re}) :
  HasDerivAt (fun z ↦ ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-z - 1))
    (∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (- s - 1) * (- Real.log x)) s := by
  simp only [mem_setOf_eq] at hs
  have ε_pos : 0 < s.re / 2 := half_pos hs
  have hneg : ∀ z : ℂ, -(z + 1) = -z - 1 := fun z => neg_add' z 1
  have hF_meas : ∀ᶠ (z : ℂ) in 𝓝 s,
      AEStronglyMeasurable (Z0F z) (volume.restrict (Ioi (N : ℝ))) := by
    have : {z : ℂ | 0 < z.re} ∈ 𝓝 s := by
      rw [mem_nhds_iff]
      refine ⟨{z | 0 < z.re}, fun ⦃a⦄ a ↦ a, isOpen_lt continuous_const Complex.continuous_re, hs⟩
    filter_upwards [this] with z hz
    have h := (integrableOn_of_Zeta0_fun Npos hz).aestronglyMeasurable
    simp only [hneg] at h
    exact h
  have hF_int : Integrable (Z0F s) (volume.restrict (Ioi (N : ℝ))) := by
    have h := integrableOn_of_Zeta0_fun Npos hs
    simp only [hneg] at h
    exact h
  have hF'_meas : AEStronglyMeasurable (Z0F' s) (volume.restrict (Ioi (N : ℝ))) := by
    have h := (integrableOn_of_Zeta0_fun_log Npos hs).aestronglyMeasurable
    simp only [hneg] at h
    exact h
  have IoiSubIoi1 : (Ioi (N : ℝ)) ⊆ {x | 1 < x} :=
      fun x hx ↦ lt_of_le_of_lt (by simp only [Nat.one_le_cast]; omega) <| mem_Ioi.mp hx
  have measSetIoi1 : MeasurableSet {x : ℝ | 1 < x} := (isOpen_lt' 1).measurableSet
  have h_bound1 : ∀ᵐ (x : ℝ) ∂volume.restrict {x | 1 < x},
      ∀ z ∈ Metric.ball s (s.re / 2), ‖Z0F' z x‖ ≤ Z0bound s x := by
    filter_upwards [self_mem_ae_restrict measSetIoi1] with x hx
    intro z hz
    have hx1 : 1 < x := hx
    have hx0 : 0 < x := by linarith
    simp only [Metric.mem_ball, Complex.dist_eq] at hz
    have hzre : -z.re - 1 ≤ -s.re / 2 - 1 := by
      have := abs_le.mp <| le_trans (Complex.abs_re_le_norm (z - s)) hz.le
      simp only [Complex.sub_re] at this
      linarith [this.1, this.2]
    have hA : ‖((⌊x⌋ : ℂ) + 1 / 2 - x)‖ ≤ 1 := by
      have h := ZetaSum_aux1_3 x
      have hcast : ((⌊x⌋ : ℂ) + 1 / 2 - x) = (((⌊x⌋ + 1 / 2 - x : ℝ)) : ℂ) := by push_cast; ring
      rw [hcast, Complex.norm_real]
      exact le_trans h (by norm_num)
    have hB : ‖(x : ℂ) ^ (-z - 1)‖ ≤ x ^ (-s.re / 2 - 1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
      exact Real.rpow_le_rpow_of_exponent_le hx1.le hzre
    have hbnd : Z0bound s x = x ^ (-s.re / 2 - 1) * ‖Real.log x‖ := by
      unfold Z0bound
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)]
    rw [hbnd]
    simp only [Z0F', norm_mul, norm_neg, Complex.norm_real]
    calc _ ≤ 1 * x ^ (-s.re / 2 - 1) * ‖Real.log x‖ := by gcongr
      _ = _ := by ring
  have h_bound : ∀ᵐ x ∂(volume.restrict (Ioi (N : ℝ))),
      ∀ z ∈ Metric.ball s (s.re / 2), ‖Z0F' z x‖ ≤ Z0bound s x :=
    ae_restrict_of_ae_restrict_of_subset IoiSubIoi1 h_bound1
  have bound_integrable : Integrable (Z0bound s) (volume.restrict (Ioi (N : ℝ))) := by
    have h := integrable_log_over_pow (r := -s.re / 2) (by linarith) Npos
    exact h
  have h_diff : ∀ᵐ x ∂(volume.restrict (Ioi (N : ℝ))),
      ∀ z ∈ Metric.ball s (s.re / 2), HasDerivAt (fun w ↦ Z0F w x) (Z0F' z x) z := by
    apply ae_restrict_of_ae_restrict_of_subset IoiSubIoi1
    filter_upwards [self_mem_ae_restrict measSetIoi1] with x hx
    intro z _
    have hx1 : 1 < x := hx
    have hx0 : 0 < x := by linarith
    have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0.ne'
    have h1 : HasDerivAt (fun w : ℂ ↦ -w - 1) (-1) z := ((hasDerivAt_id' z).neg).sub_const 1
    have h2 : HasDerivAt (fun w : ℂ ↦ (x : ℂ) ^ w)
        ((x : ℂ) ^ (-z - 1) * (Real.log x : ℂ)) (-z - 1) := by
      have := (hasDerivAt_id' (-z - 1)).const_cpow (c := (x : ℂ)) (Or.inl hxC)
      refine this.congr_deriv ?_
      rw [Complex.ofReal_log hx0.le, mul_one]
    have h3 := (h2.comp z h1).const_mul ((⌊x⌋ : ℂ) + 1 / 2 - x)
    refine h3.congr_deriv ?_
    simp only [Z0F']
    ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := Z0F) (F' := Z0F') (x₀ := s)
    (bound := Z0bound s) (μ := volume.restrict (Ioi (N : ℝ)))
    (Metric.ball_mem_nhds s ε_pos) hF_meas hF_int hF'_meas h_bound bound_integrable h_diff).2

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
