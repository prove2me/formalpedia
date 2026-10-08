-- Prove2me | Theorems.Thm_AntonelliBFSDE_NonsingularExample_mean_terminal_identity
-- name    : AntonelliBFSDE.NonsingularExample.mean_terminal_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T20:01:00.746661+00:00
-- url     : https://prove2.me/theorems/0e9273dd-38fb-4b45-a32d-facf4991ade4
-- title:
--   Example 2 — expectation equation for U_T
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space with a complete, right-continuous filtration $(\mathcal F_t)_{0\le t\le T}$. Let $J_0$ be $\mathcal F_0$-measurable, integrable and strictly positive almost surely. Let $Y$ be $\mathcal F_T$-measurable, bounded and strictly positive almost surely. A solution $(U,V)$ belongs to $L^1(dt\otimes dP)^2$ and satisfies $U_t=J_0+\int_0^t V_s\,ds$ and $V_t=\mathbb E[\int_t^T U_s\,ds+Y\mid\mathcal F_t]$ in that space. Set $U_T=J_0+\int_0^T V_s\,ds$, $M_t=\mathbb E[U_T\mid\mathcal F_t]$, and $Y_t^{\mathrm c}=\mathbb E[Y\mid\mathcal F_t]$. For any $T>0$, the terminal value $U_T$ and $Y$ are integrable and their expectations satisfy
--
--   $$
--   \mathbb E[U_T]\cos T=\mathbb E[J_0]+\mathbb E[Y]\sin T.
--   $$
--
--   This undivided form remains meaningful at $T=\pi/2$ and gives the contradiction used in Example 2.
--
--   **Formalization Note** The paper first obtains $\mathbb E[U_T]=\mathbb E[J_0]+\mathbb E[U_T](1-\cos T)+\mathbb E[Y]\sin T$, then divides by $\cos T$. We state the equivalent undivided identity, avoiding division by zero at the goal horizon.
-- source:
--   Antonelli, Backward-forward stochastic differential equations, Ann. Appl. Probab. 3(3) (1993), p. 792, Example 2, displays after (3.13)

import Mathlib
import Definitions.Def_AntonelliBFSDE_NonsingularExample_Example2

open MeasureTheory
open scoped NNReal ENNReal

namespace AntonelliBFSDE.NonsingularExample

/-- Example 2, p. 792: the expectation identity before dividing by cos T. -/
theorem mean_terminal_identity {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (J₀ Y : Ω → ℝ) (U V : ℝ≥0 → Ω → ℝ)
    (husual : AntonelliBFSDE.BackwardForward.UsualHypotheses 𝓕 P) (hT : 0 < T)
    (hJmeas : Measurable[𝓕 0] J₀) (hJint : Integrable J₀ P)
    (hJpos : ∀ᵐ ω ∂P, 0 < J₀ ω)
    (hYmeas : Measurable[𝓕 T] Y) (hYpos : ∀ᵐ ω ∂P, 0 < Y ω)
    (hYbounded : ∃ C : ℝ, ∀ᵐ ω ∂P, |Y ω| ≤ C)
    (hsol : AntonelliBFSDE.SingularExample.IsDtSystemSolution 𝓕 P T J₀ (fun _ v => v) (fun u _ => u) Y U V) :
    Integrable (UT T J₀ V) P ∧ Integrable Y P ∧
    (∫ ω, UT T J₀ V ω ∂P) * Real.cos (T : ℝ) =
      (∫ ω, J₀ ω ∂P) + (∫ ω, Y ω ∂P) * Real.sin (T : ℝ) := by sorry

end AntonelliBFSDE.NonsingularExample
