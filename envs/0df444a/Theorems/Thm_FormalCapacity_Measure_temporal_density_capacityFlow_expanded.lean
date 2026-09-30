-- Prove2me | Theorems.Thm_FormalCapacity_Measure_temporal_density_capacityFlow_expanded
-- name    : FormalCapacity.Measure.temporal_density_capacityFlow_expanded
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-07T23:47:45.95608+00:00
-- url     : https://prove2.me/theorems/6dddabda-abb5-4e8e-805c-6fb4a51c93a0
-- title:
--   Expanded temporal density-capacity inequality under score coarsening
-- statement:
--   Let $(X_E,\mu_E)$ and $(X_L,\mu_L)$ be arbitrary measure spaces, and let $R:X_E\to X_L$ be any function. At each stage $r\in\{E,L\}$, take seven real-valued functions $f_1^r,f_2^r,f_3^r,\beta_{123}^r,\beta_{12}^r,\beta_{13}^r,\beta_{23}^r$ on $X_r$. For arbitrary weights $q_{12},q_{23}:X_L\to\mathbb R$, put $w_{ij}^E=q_{ij}\circ R$ and $w_{ij}^L=q_{ij}$. Define the following functions pointwise at each stage:
--
--   $$
--   \begin{aligned}
--   \gamma_{123}^r&=\min(f_1^r,\min(f_2^r,f_3^r)),\\
--   \gamma_{12}^r&=\max(\min(f_1^r,f_2^r)-f_3^r,0),\\
--   \gamma_{23}^r&=\max(\min(f_2^r,f_3^r)-f_1^r,0),\\
--   A_r&=\beta_{123}^r+w_{12}^r\beta_{12}^r+w_{23}^r\beta_{23}^r,\\
--   C_r&=\gamma_{123}^r+w_{12}^r\gamma_{12}^r+w_{23}^r\gamma_{23}^r.
--   \end{aligned}
--   $$
--
--   For $ij\in\{12,13,23\}$, let
--
--   $$
--   d_{ij}^r=\min(f_i^r,f_j^r)-\beta_{123}^r-\beta_{ij}^r.
--   $$
--
--   For each stage separately, assume almost everywhere that the four block intensities are nonnegative and satisfy
--
--   $$
--   \begin{aligned}
--   \beta_{123}^r+\beta_{12}^r+\beta_{13}^r&\le f_1^r,\\
--   \beta_{123}^r+\beta_{12}^r+\beta_{23}^r&\le f_2^r,\\
--   \beta_{123}^r+\beta_{13}^r+\beta_{23}^r&\le f_3^r.
--   \end{aligned}
--   $$
--
--   Assume also, almost everywhere at each stage,
--
--   $$
--   \begin{aligned}
--   0\le w_{12}^r\le1,&\qquad 0\le w_{23}^r\le1,\\
--   w_{12}^r+w_{23}^r&\ge1,\\
--   f_2^r&\ge\min(f_1^r,f_3^r).
--   \end{aligned}
--   $$
--
--   Require $C_r,A_r,d_{12}^r,d_{13}^r,d_{23}^r$ and, separately, each of $\gamma_{123}^r,w_{12}^r\gamma_{12}^r,w_{23}^r\gamma_{23}^r$ to be real-integrable with respect to $\mu_r$. The temporal input is the assumed integrated score-coarsening inequality
--
--   $$
--   \int A_E\,d\mu_E\le\int A_L\,d\mu_L.
--   $$
--
--   Write $D_{ij}^r=\int d_{ij}^r\,d\mu_r$ and
--
--   $$
--   \begin{aligned}
--   T_r&=\int\gamma_{123}^r\,d\mu_r,\\
--   P_{12,r}&=\int w_{12}^r\gamma_{12}^r\,d\mu_r,\\
--   P_{23,r}&=\int w_{23}^r\gamma_{23}^r\,d\mu_r.
--   \end{aligned}
--   $$
--
--   Then the expanded canonical-flow gap obeys
--
--   $$
--   \begin{aligned}
--   &(T_E-T_L)\\
--   &\quad +(P_{12,E}-P_{12,L})\\
--   &\quad +(P_{23,E}-P_{23,L})\\
--   &\le D_{12}^E+D_{23}^E+D_{13}^L.
--   \end{aligned}
--   $$
--
--   This transfers early adjacent-pair loss and late outer-pair gain bounds to a comparison of canonical density scores. It does not prove the assumed score-coarsening inequality or construct a coupling realizing the density data. The labels early and late do not encode time parameters or a Brownian process. No measurability of $R$, pushforward relation between the measures, probability normalization, or finite-measure assumption is required: the displayed pulled-back integrability and almost-everywhere hypotheses are supplied directly.
-- source:
--   Interval-Möbius capacity and temporal block flow, unpublished project note (2026), density-level form of equation (4.2), using Lemma 3.1 / (3.3) and taking the integrated score inequality (4.1) as a hypothesis. This is not a formalization of the manuscript's pathwise derivation of (4.1), nor of a Brownian specialization. CAPACITY_FLOW_THEOREM.md SHA-256 700d20415a4a673e5b27b1e6d508a89204afb85dfe54daddf8d4d84b1492d15f. Exact formal source: formal_capacity/FormalCapacity/Measure/Temporal.lean, FormalCapacity.Measure.temporal_density_capacityFlow_expanded, lines 121–145, including its source docstring; proof helpers temporal_density_capacityFlow (55–82) and densityCanonicalFlowGap_eq_expanded (102–119). Source-file SHA-256 a3635f1e16db99dcb1c6f75e9f898023ec59225c99e22894e21a77556bf1089b. Ranges are compiler-derived. Local source archive; no public repository URL, commit, externally established authorship, or novelty claim is asserted. Target environment: Lean 4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Definitions.Def_capacityMeasureThreeLabel
import Definitions.Def_capacityTemporalFlow

set_option autoImplicit false

/-!
# The temporal capacity-flow inequality

This file proves the abstract form of equation (4.2).  The first theorem uses
finite block measures and an arbitrary measurable restriction map.  The second
specializes it to the density hypotheses discharged by the integrated
three-label stability theorem.  The final corollary expands the canonical
score into the triple and two weighted pair terms printed in (4.2).
-/

open MeasureTheory

open FormalCapacity.Measure



variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

theorem FormalCapacity.Measure.temporal_density_capacityFlow_expanded
    (early : ThreeLabelDensities α) (late : ThreeLabelDensities β)
    (μEarly : Measure α) (μLate : Measure β) (R : α → β)
    (q12 q23 : β → ℝ)
    (hintEarly : early.IntegrableFor (q12 ∘ R) (q23 ∘ R) μEarly)
    (hintLate : late.IntegrableFor q12 q23 μLate)
    (hcomponentsEarly : CanonicalComponentsIntegrable early (q12 ∘ R) (q23 ∘ R) μEarly)
    (hcomponentsLate : CanonicalComponentsIntegrable late q12 q23 μLate)
    (hvalidEarly : ∀ᵐ x ∂μEarly, early.ValidAt x)
    (hvalidLate : ∀ᵐ y ∂μLate, late.ValidAt y)
    (hadmissibleEarly : ∀ᵐ x ∂μEarly,
      early.AdmissibleAt (q12 ∘ R) (q23 ∘ R) x)
    (hadmissibleLate : ∀ᵐ y ∂μLate, late.AdmissibleAt q12 q23 y)
    (hcoarsen :
      (∫ x, early.actualScore (q12 ∘ R) (q23 ∘ R) x ∂μEarly) ≤
        ∫ y, late.actualScore q12 q23 y ∂μLate) :
    densityCanonicalFlowGapExpanded early late μEarly μLate R q12 q23 ≤
      (∫ x, early.deficit12 x ∂μEarly) +
        (∫ x, early.deficit23 x ∂μEarly) +
        (∫ y, late.deficit13 y ∂μLate) := by
  sorry
