-- Prove2me | Theorems.Thm_FormalCapacity_Measure_ThreeLabelDensities_integral_canonicalScore_eq_components
-- name    : FormalCapacity.Measure.ThreeLabelDensities.integral_canonicalScore_eq_components
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-07T23:46:13.240832+00:00
-- url     : https://prove2.me/theorems/5b36cf22-928b-4900-b043-ff03f691f127
-- title:
--   Integral decomposition of the canonical three-label score
-- statement:
--   Let $(X,\mu)$ be an arbitrary measure space and let $f_1,f_2,f_3,\beta_{123},\beta_{12},\beta_{13},\beta_{23}:X\to\mathbb R$ be three-label density data. Let $q_{12},q_{23}:X\to\mathbb R$ be arbitrary weights. Define pointwise
--
--   $$
--   \begin{aligned}
--   \gamma_{123}&=\min(f_1,\min(f_2,f_3)),\\
--   \gamma_{12}&=\max(\min(f_1,f_2)-f_3,0),\\
--   \gamma_{23}&=\max(\min(f_2,f_3)-f_1,0),\\
--   C_q&=\gamma_{123}+q_{12}\gamma_{12}+q_{23}\gamma_{23}.
--   \end{aligned}
--   $$
--
--   Assume each of $\gamma_{123}$, $q_{12}\gamma_{12}$, and $q_{23}\gamma_{23}$ is real-integrable with respect to $\mu$. Then
--
--   $$
--   \begin{aligned}
--   \int C_q\,d\mu={}&\int\gamma_{123}\,d\mu\\
--   &+\int q_{12}\gamma_{12}\,d\mu\\
--   &+\int q_{23}\gamma_{23}\,d\mu.
--   \end{aligned}
--   $$
--
--   This identity provides the component-wise form of the canonical score used in density-level temporal inequalities. It is an integrable-sum identity, not a coupling-existence or stability theorem. The four block-intensity functions are part of the data but do not enter the formula. No capacity inequalities, nonnegativity, weight bounds, density ordering, probability normalization, or finiteness of the ambient measure is required.
-- source:
--   Interval-Möbius capacity and temporal block flow, unpublished project note (2026), score definition (3.2) and the component expansion used in (4.2); the manuscript does not separately number this integral-linearity lemma. CAPACITY_FLOW_THEOREM.md SHA-256 700d20415a4a673e5b27b1e6d508a89204afb85dfe54daddf8d4d84b1492d15f. Exact formal source: formal_capacity/FormalCapacity/Measure/ThreeLabel.lean, FormalCapacity.Measure.ThreeLabelDensities.integral_canonicalScore_eq_components, lines 236–260, including its source docstring. Source-file SHA-256 be25fa12896fcf4b5371133ccd12aef7584a76154ca7363db31d8866b6730642. Range is compiler-derived. Local source archive; no public repository URL, commit, externally established authorship, or novelty claim is asserted. Target environment: Lean 4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_capacityMeasureThreeLabel

set_option autoImplicit false

/-!
# Measure-theoretic three-label stability

This file lifts the scalar theorem `FormalCapacity.Finite.threeLabel_stability`
to densities over an arbitrary measure space.  Pair deficits are defined
pointwise, proved nonnegative almost everywhere from the block-capacity
constraints, and then integrated.  Nothing here assumes a stochastic process
or a Brownian law.
-/

open MeasureTheory

open FormalCapacity.Measure



open FormalCapacity.Measure.ThreeLabelDensities

variable {α : Type*}































variable [MeasurableSpace α]

theorem FormalCapacity.Measure.ThreeLabelDensities.integral_canonicalScore_eq_components
    (d : ThreeLabelDensities α) (q12 q23 : α → ℝ) (μ : Measure α)
    (h123 : Integrable d.canonical123 μ)
    (h12 : Integrable (fun x ↦ q12 x * d.canonical12 x) μ)
    (h23 : Integrable (fun x ↦ q23 x * d.canonical23 x) μ) :
    (∫ x, d.canonicalScore q12 q23 x ∂μ) =
      (∫ x, d.canonical123 x ∂μ) +
        (∫ x, q12 x * d.canonical12 x ∂μ) +
        (∫ x, q23 x * d.canonical23 x ∂μ) := by
  sorry
