-- Prove2me | Theorems.Thm_AntonelliBFSDE_BackwardForward_theorem_3_1
-- name    : AntonelliBFSDE.BackwardForward.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:09:13.30174+00:00
-- url     : https://prove2.me/theorems/1733d2d0-030b-4235-8f63-1e80b6e0d907
-- title:
--   Theorem 3.1 — if k‖D‖_{H^∞} < 1, the backward-forward system (3.1)–(3.2) has a unique adapted solution in L¹(μ) ⊗ L¹(μ)
-- statement:
--   Let $(\Omega,\mathcal F,(\mathcal F_t)_{0 \le t \le T},P)$ satisfy the usual hypotheses, let $A$ and $C$ be adapted bounded-variation processes with $A_0 = C_0 = 0$ and $|A|_T, |C|_T \le \beta$, and let $D_t = \max(|A|_t,|C|_t)$ with Doléans measure $\mu$. Assume that $|dA| \le dD$ and $|dC| \le dD$ on $[0,T]$, and that $f, g$, $k$, $Y$, $J$ satisfy the standing hypotheses of §3:
--
--   1. $f, g : [0,T]\times\Omega\times\mathbb R^2 \to \mathbb R$ are jointly measurable and $k$-Lipschitz in $(x,y)$, $k > 0$, uniformly in $(s,\omega)$;
--   2. $f(\cdot,\cdot,x,y)$ is progressively measurable and $g_s(\cdot,x,y)$ is $\mathcal F_s$-measurable;
--   3. $E(\int_0^T |f_s(0,0)|\,dD_s) < \infty$, $E(\int_0^T |g_s(0,0)|\,dD_s) < \infty$;
--
--   $Y$ is $\mathcal F_T$-measurable and integrable, and $J$ is progressively measurable with $E(\int_0^T |J_t|\,dD_t) < \infty$. Consider the system
--   $$U_t = J_t + \int_0^t f_s(U_s,V_s)\,dA_s, \qquad V_t = E\Big(\int_t^T g_s(U_s,V_s)\,dC_s + Y \;\Big|\; \mathcal F_t\Big). \tag{3.1–3.2}$$
--   If
--   $$k\,\|D\|_{\mathbf H^\infty} < 1, \qquad \|D\|_{\mathbf H^\infty} = \operatorname{ess\,sup} D_T,$$
--   then:
--
--   1. **existence**: there is a progressively measurable pair $(U,V)$ that satisfies (3.1)–(3.2) in the $L^1(\mu)\otimes L^1(\mu)$ sense (both equations hold $\mu$-a.e., with a càdlàg version of the conditional expectation);
--   2. **uniqueness**: any two progressively measurable solutions agree in $L^1(\mu)\otimes L^1(\mu)$, i.e. $\|U - U'\|_{L^1(\mu)} + \|V - V'\|_{L^1(\mu)} = 0$.
--
--   The theorem shows that coupling a forward and a backward equation is well posed under a smallness condition on the product of the Lipschitz constant and the size of the integrators; the paper's examples (§3) show that without such a condition a solution may fail to exist.
--
--   **Formalization Note** This states the conclusion of Theorem 3.1 ("Consequently there exists a unique adapted solution"); the contraction property is the milestone `contraction`. The paper asserts on p. 786 that $|A| \ll D$ and $|C| \ll D$ with densities at most $1$; this is false for $D = \max(|A|,|C|)$ in general, so domination is an explicit hypothesis (it holds in the paper's Example 1, $A = C$). "Adapted" solutions are read as progressively measurable, and $f$ is required to be progressively measurable in $(s,\omega)$ for each $(x,y)$ (the paper: $\mathcal F_s$-measurable), so that $\int_0^t f\,dA$ is adapted, as the proof uses. The paper's $k_1$ bound on $J$ is stated as finiteness; $|A|_T, |C|_T < \beta$ is stated as $\le \beta$; the càdlàg clause of §1 on $J$ is not imposed (it is not used).
-- source:
--   Antonelli, Backward-forward stochastic differential equations, Ann. Appl. Probab. 3(3) (1993), p. 787, Theorem 3.1 (with the system (3.1)–(3.2) and hypotheses 1–3 of p. 785)

import Mathlib
import Definitions.Def_AntonelliBFSDE_BackwardForward_Setting
import Definitions.Def_AntonelliBFSDE_BackwardForward_System

open MeasureTheory
open scoped NNReal ENNReal

namespace AntonelliBFSDE.BackwardForward

theorem theorem_3_1 {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (β : ℝ) (hT : 0 < T)
    (husual : UsualHypotheses 𝓕 P) (IA IC : BVIntegrator 𝓕 T β) (hdom : Dominated IA IC)
    (k : ℝ) (f g : ℝ≥0 → Ω → ℝ → ℝ → ℝ) (Y : Ω → ℝ) (J : ℝ≥0 → Ω → ℝ)
    (hyp : StandingHyp 𝓕 P IA IC k f g Y J)
    (hk : ENNReal.ofReal k * HInfNorm P IA IC < 1) :
    (∃ U V : ℝ≥0 → Ω → ℝ, IsProgressive 𝓕 U ∧ IsProgressive 𝓕 V ∧
      IsSystemSolution 𝓕 P IA IC f g Y J U V) ∧
    ∀ U V U' V' : ℝ≥0 → Ω → ℝ,
      IsProgressive 𝓕 U → IsProgressive 𝓕 V → IsProgressive 𝓕 U' → IsProgressive 𝓕 V' →
      IsSystemSolution 𝓕 P IA IC f g Y J U V → IsSystemSolution 𝓕 P IA IC f g Y J U' V' →
      L1NormD P IA IC (U - U') + L1NormD P IA IC (V - V') = 0 := by sorry

end AntonelliBFSDE.BackwardForward
