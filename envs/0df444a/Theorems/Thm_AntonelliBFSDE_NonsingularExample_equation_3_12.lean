-- Prove2me | Theorems.Thm_AntonelliBFSDE_NonsingularExample_equation_3_12
-- name    : AntonelliBFSDE.NonsingularExample.equation_3_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T20:00:52.934974+00:00
-- url     : https://prove2.me/theorems/56a12265-c78f-41b3-aecc-df8d2bb7d3fa
-- title:
--   Equation (3.12) — corrected conditional-expectation identity
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space with a complete, right-continuous filtration $(\mathcal F_t)_{0\le t\le T}$. Let $J_0$ be $\mathcal F_0$-measurable, integrable and strictly positive almost surely. Let $Y$ be $\mathcal F_T$-measurable, bounded and strictly positive almost surely. A solution $(U,V)$ belongs to $L^1(dt\otimes dP)^2$ and satisfies $U_t=J_0+\int_0^t V_s\,ds$ and $V_t=\mathbb E[\int_t^T U_s\,ds+Y\mid\mathcal F_t]$ in that space. Set $U_T=J_0+\int_0^T V_s\,ds$, $M_t=\mathbb E[U_T\mid\mathcal F_t]$, and $Y_t^{\mathrm c}=\mathbb E[Y\mid\mathcal F_t]$. For any $T>0$, and for jointly measurable conditional-expectation versions $M,Y^{\mathrm c}$, the weighted tail $R_t$ is integrable for each $t\le T$ and has a jointly measurable conditional-expectation version. In $L^1(dt\otimes dP)$,
--
--   $$
--   V_t=(T-t)M_t-\mathbb E[R_t\mid\mathcal F_t]+Y_t^{\mathrm c}.
--   $$
--
--   This is the Volterra identity from which the closed form of $V$ is stated.
--
--   **Formalization Note** The paper prints $-\mathbb E[R_t+Y\mid\mathcal F_t]$ in (3.12); we state $-\mathbb E[R_t\mid\mathcal F_t]+\mathbb E[Y\mid\mathcal F_t]$, matching the preceding display and the subsequent formula. Process equality means zero $L^1(dt\otimes dP)$ norm of the residual.
-- source:
--   Antonelli, Backward-forward stochastic differential equations, Ann. Appl. Probab. 3(3) (1993), p. 792, Example 2, (3.12) and display immediately preceding it

import Mathlib
import Definitions.Def_AntonelliBFSDE_NonsingularExample_Example2

open MeasureTheory
open scoped NNReal ENNReal

namespace AntonelliBFSDE.NonsingularExample

/-- Example 2, (3.12), with the sign of the Y term corrected. -/
theorem equation_3_12 {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (J₀ Y : Ω → ℝ) (U V M Yc : ℝ≥0 → Ω → ℝ)
    (husual : AntonelliBFSDE.BackwardForward.UsualHypotheses 𝓕 P) (hT : 0 < T)
    (hJmeas : Measurable[𝓕 0] J₀) (hJint : Integrable J₀ P)
    (hJpos : ∀ᵐ ω ∂P, 0 < J₀ ω)
    (hYmeas : Measurable[𝓕 T] Y) (hYpos : ∀ᵐ ω ∂P, 0 < Y ω)
    (hYbounded : ∃ C : ℝ, ∀ᵐ ω ∂P, |Y ω| ≤ C)
    (hsol : AntonelliBFSDE.SingularExample.IsDtSystemSolution 𝓕 P T J₀ (fun _ v => v) (fun u _ => u) Y U V)
    (hM : AntonelliBFSDE.Backward.IsCondExpVersion 𝓕 P T (fun _ => UT T J₀ V) M)
    (hYc : AntonelliBFSDE.Backward.IsCondExpVersion 𝓕 P T (fun _ => Y) Yc) :
    (∀ t : ℝ≥0, t ≤ T → Integrable (weightedTail T V t) P) ∧
    ∃ W : ℝ≥0 → Ω → ℝ,
      AntonelliBFSDE.Backward.IsCondExpVersion 𝓕 P T (weightedTail T V) W ∧
      AntonelliBFSDE.SingularExample.L1NormDt P T (fun t ω => V t ω -
        (((T : ℝ) - (t : ℝ)) * M t ω - W t ω + Yc t ω)) = 0 := by sorry

end AntonelliBFSDE.NonsingularExample
