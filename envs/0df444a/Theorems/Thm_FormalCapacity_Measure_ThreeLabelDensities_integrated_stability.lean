-- Prove2me | Theorems.Thm_FormalCapacity_Measure_ThreeLabelDensities_integrated_stability
-- name    : FormalCapacity.Measure.ThreeLabelDensities.integrated_stability
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-07T23:46:51.581313+00:00
-- url     : https://prove2.me/theorems/98c55b2f-a170-432a-9c7d-068e4c2379cb
-- title:
--   Integrated asymmetric three-label stability
-- statement:
--   Let $(X,\mu)$ be an arbitrary measure space, let $f_1,f_2,f_3,\beta_{123},\beta_{12},\beta_{13},\beta_{23}:X\to\mathbb R$ be three-label density data, and let $q_{12},q_{23}:X\to\mathbb R$ be weight functions. Define, pointwise,
--
--   $$
--   \begin{aligned}
--   \gamma_{123}&=\min(f_1,\min(f_2,f_3)),\\
--   \gamma_{12}&=\max(\min(f_1,f_2)-f_3,0),\\
--   \gamma_{23}&=\max(\min(f_2,f_3)-f_1,0),\\
--   A_q&=\beta_{123}+q_{12}\beta_{12}+q_{23}\beta_{23},\\
--   C_q&=\gamma_{123}+q_{12}\gamma_{12}+q_{23}\gamma_{23}.
--   \end{aligned}
--   $$
--
--   For $ij\in\{12,13,23\}$ set
--
--   $$
--   d_{ij}=\min(f_i,f_j)-\beta_{123}-\beta_{ij}.
--   $$
--
--   Assume that, almost everywhere, all four block intensities are nonnegative and
--
--   $$
--   \begin{aligned}
--   \beta_{123}+\beta_{12}+\beta_{13}&\le f_1,\\
--   \beta_{123}+\beta_{12}+\beta_{23}&\le f_2,\\
--   \beta_{123}+\beta_{13}+\beta_{23}&\le f_3.
--   \end{aligned}
--   $$
--
--   Assume also, almost everywhere,
--
--   $$
--   \begin{aligned}
--   0\le q_{12}\le1,&\qquad 0\le q_{23}\le1,\\
--   q_{12}+q_{23}&\ge1,\\
--   f_2&\ge\min(f_1,f_3).
--   \end{aligned}
--   $$
--
--   Require each of $C_q,A_q,d_{12},d_{13},d_{23}$ to be real-integrable with respect to $\mu$. Write $C=\int C_q\,d\mu$, $A=\int A_q\,d\mu$, and $D_{ij}=\int d_{ij}\,d\mu$. Then both bounds hold:
--
--   $$
--   \begin{aligned}
--   C-D_{12}-D_{23}&\le A,\\
--   A&\le C+D_{13}.
--   \end{aligned}
--   $$
--
--   Thus integrated downward score loss is controlled by the two adjacent-pair deficits, while integrated upward score gain is controlled by the outer-pair deficit. No probability normalization, finite-measure assumption, stochastic process, or realized equality partition is part of the statement. Integrability is required only for the five displayed combinations; separate integrability or measurability assumptions on every input function are not imposed. Zero measures, tied densities, and boundary weights are included.
-- source:
--   Interval-Möbius capacity and temporal block flow, unpublished project note (2026), Lemma 3.1 and equation (3.3), passed from pointwise densities to real integrals with explicit integrability assumptions; definitions (2.2)–(2.4) and (3.1)–(3.2). CAPACITY_FLOW_THEOREM.md SHA-256 700d20415a4a673e5b27b1e6d508a89204afb85dfe54daddf8d4d84b1492d15f. Exact formal source: formal_capacity/FormalCapacity/Measure/ThreeLabel.lean, FormalCapacity.Measure.ThreeLabelDensities.integrated_stability, lines 183–234, including its source docstring; its pointwise helper is at 121–131. Source-file SHA-256 be25fa12896fcf4b5371133ccd12aef7584a76154ca7363db31d8866b6730642. Ranges are compiler-derived. Local source archive; no public repository URL, commit, externally established authorship, or novelty claim is asserted. Target environment: Lean 4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

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

theorem FormalCapacity.Measure.ThreeLabelDensities.integrated_stability (d : ThreeLabelDensities α) (q12 q23 : α → ℝ)
    (μ : Measure α) (hint : d.IntegrableFor q12 q23 μ)
    (hv : ∀ᵐ x ∂μ, d.ValidAt x)
    (hq : ∀ᵐ x ∂μ, d.AdmissibleAt q12 q23 x) :
    (∫ x, d.canonicalScore q12 q23 x ∂μ) - (∫ x, d.deficit12 x ∂μ) -
          (∫ x, d.deficit23 x ∂μ) ≤ ∫ x, d.actualScore q12 q23 x ∂μ ∧
      (∫ x, d.actualScore q12 q23 x ∂μ) ≤
        (∫ x, d.canonicalScore q12 q23 x ∂μ) +
          (∫ x, d.deficit13 x ∂μ) := by
  sorry
