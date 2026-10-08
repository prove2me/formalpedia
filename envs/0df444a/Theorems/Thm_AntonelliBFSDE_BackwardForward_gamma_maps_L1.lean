-- Prove2me | Theorems.Thm_AntonelliBFSDE_BackwardForward_gamma_maps_L1
-- name    : AntonelliBFSDE.BackwardForward.gamma_maps_L1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:09:08.69885+00:00
-- url     : https://prove2.me/theorems/a2a33782-3e3c-49df-9503-b5cc9180fe22
-- title:
--   §3, pp. 785–787 — Γ maps L¹(μ) ⊗ L¹(μ) into L¹(μ) ⊗ L¹(μ)
-- statement:
--   Assume the usual hypotheses, the standing hypotheses 1–3 of §3 on $f, g$ (with constant $k$), $Y \in L^1(P)$ $\mathcal F_T$-measurable, $J$ progressively measurable with $E(\int_0^T |J_t|\,dD_t) < \infty$, and that $D = \max(|A|,|C|)$ dominates $|dA|$ and $|dC|$. Let $U, V \in L^1(\mu)$, $\mu$ the Doléans measure of $D$. Then:
--
--   1. $\|F(U,V)\|_{L^1(\mu)} < \infty$, where $F(U,V)_t = J_t + \int_0^t f_s(U_s,V_s)\,dA_s$;
--   2. for every $t \le T$, $\xi_t = \int_t^T g_s(U_s,V_s)\,dC_s + Y$ is integrable, so $G(U,V)_t = E(\xi_t \mid \mathcal F_t)$ is defined;
--   3. every càdlàg version $W$ of $G(U,V)$ satisfies $\|W\|_{L^1(\mu)} < \infty$.
--
--   In the paper's words,
--   $$\|\Gamma(U,V)\|_{L^1 \otimes L^1} < +\infty \qquad \forall (U,V) \in L^1(\mu) \otimes L^1(\mu).$$
--   This is what makes $\Gamma$ an operator on $L^1(\mu) \otimes L^1(\mu)$, the space on which Theorem 3.1 applies the Banach fixed point theorem.
--
--   **Formalization Note** The paper's computation (p. 786) uses that $|A|$ and $|C|$ are absolutely continuous with respect to $D$ with densities at most $1$; that claim is false for $D = \max(|A|,|C|)$ in general and is assumed here as `Dominated`. Clause 2 makes explicit the integrability that the conditional expectation needs.
-- source:
--   Antonelli, Backward-forward stochastic differential equations, Ann. Appl. Probab. 3(3) (1993), pp. 785–787, §3, from 'Under the previous hypotheses, Γ: L¹(μ) ⊗ L¹(μ) → L¹(μ) ⊗ L¹(μ)' (p. 785) to 'In conclusion ‖Γ(U, V)‖ < +∞' (p. 787)

import Mathlib
import Definitions.Def_AntonelliBFSDE_BackwardForward_Setting
import Definitions.Def_AntonelliBFSDE_BackwardForward_System

open MeasureTheory
open scoped NNReal ENNReal

namespace AntonelliBFSDE.BackwardForward

theorem gamma_maps_L1 {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (β : ℝ) (hT : 0 < T)
    (husual : UsualHypotheses 𝓕 P) (IA IC : BVIntegrator 𝓕 T β) (hdom : Dominated IA IC)
    (k : ℝ) (f g : ℝ≥0 → Ω → ℝ → ℝ → ℝ) (Y : Ω → ℝ) (J : ℝ≥0 → Ω → ℝ)
    (hyp : StandingHyp 𝓕 P IA IC k f g Y J)
    (U V : ℝ≥0 → Ω → ℝ) (hU : MemL1D P IA IC U) (hV : MemL1D P IA IC V) :
    L1NormD P IA IC (Fop IA J f U V) < ⊤ ∧
    (∀ t ≤ T, Integrable (xiG IC g Y U V t) P) ∧
    ∀ W : ℝ≥0 → Ω → ℝ, IsGVersion 𝓕 P IC g Y U V W → L1NormD P IA IC W < ⊤ := by sorry

end AntonelliBFSDE.BackwardForward
