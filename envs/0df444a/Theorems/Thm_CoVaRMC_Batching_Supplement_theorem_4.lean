-- Prove2me | Theorems.Thm_CoVaRMC_Batching_Supplement_theorem_4
-- name    : CoVaRMC.Batching.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T02:14:03.357462+00:00
-- url     : https://prove2.me/theorems/ca46af9e-8ae5-4e85-a672-a8b3a7e66c0c
-- title:
--   Theorem 4, p. 16 — IS representation Pr{Y ≤ y | X = x} = E[I{Y₁ ≤ y}q₁ + I{Y₂ ≤ y}q₂] / E[q₁ + q₂] for the delta-gamma pair
-- statement:
--   Let $(X,Y)$ be the delta-gamma pair (17)–(18) in $d\ge1$ i.i.d. standard normal factors, and suppose that $(X,Y)$ has a joint density, as in the paper's standing model. Fix $x\in\mathbb R$ and suppose
--
--   1. $\gamma_{1d}>0$;
--   2. $\mathrm E\big[|g^*-x|^{-1/2}\big]<\infty$, where $g^*=g^*(Z_1,\dots,Z_{d-1})$;
--   3. $\mathrm E[q_1+q_2]>0$.
--
--   Then for every $y\in\mathbb R$ the conditional probability $\Pr\{Y\le y\mid X=x\}=\lim_{\varepsilon\to0}\Pr\{Y\le y,|X-x|\le\varepsilon\}/\Pr\{|X-x|\le\varepsilon\}$ exists and
--   $$\Pr\{Y\le y\mid X=x\}=\frac{\mathrm E\big[I\{Y_1\le y\}q_1+I\{Y_2\le y\}q_2\big]}{\mathrm E[q_1+q_2]},$$
--   where $\mathrm E[\cdot]$ is the expectation with respect to $(Z_1,\dots,Z_{d-1})^\top$ and $Y_\ell,q_\ell$ are the root values and weights of Lemma 5.
--
--   The theorem turns a conditional probability given the probability-zero event $\{X=x\}$ into a ratio of two ordinary expectations over the first $d-1$ factors. This is what makes the IS-inspired estimator of §4.2.2 possible.
--
--   **Formalization Note** $\Pr\{Y\le y\mid X=x\}$ is the limit as $\varepsilon\to0^+$ of `condRatio`, the middle expression of (3) on p. 14, computed under $Z\sim N(0,I_d)$; the conclusion asserts that this limit exists. The moment condition is a lower Lebesgue integral in $[0,\infty]$, in which $|g^*-x|^{-1/2}=\infty$ where $g^*=x$, as in the paper. The joint density is stated as absolute continuity of the law of $(X,Y)$ with respect to Lebesgue measure on $\mathbb R^2$. The expectations are Bochner integrals over $W\sim N(0,I_{d-1})$; condition 2 makes $q_1+q_2$ integrable.
--
--   Differences from the source:
--   - reading: Theorem 4 stated for the delta-gamma pair; §2 (pp. 4–5) assumes throughout that X and Y are continuous with a joint density → hypothesis that the law of (X, Y) is absolutely continuous on ℝ²; reason: the paper's standing model applies to §4; without it the identity is false at atoms of the conditional law (Y = X, i.e. c2 = c1, δ2 = δ1, γ2 = γ1, and y = x: the limit in (3) is 1/2, the right side is 1)
--   - encoding: the page divides by E[q1 + q2] → hypothesis E[q1 + q2] > 0; reason: a nondegeneracy condition that only excludes the case where the right side is the undefined 0/0 (x ≤ g* almost surely)
--   - encoding: Pr{Y ≤ y | X = x} → the limit as ε → 0⁺ of Pr{Y ≤ y, |X − x| ≤ ε} / Pr{|X − x| ≤ ε}, asserted to exist; reason: the paper's own definition, Equation (3) as displayed on p. 14
-- source:
--   Huang, Lin, Hong, Monte-Carlo Estimation of CoVaR, arXiv:2210.06148v1, p. 16, Theorem 4; definition (3) as displayed on p. 14; standing model pp. 4–5; proof Appendix B, pp. 33–35

import Mathlib
import Definitions.Def_CoVaRMC_Batching_Setting
import Definitions.Def_CoVaRMC_Batching_Supplement_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace CoVaRMC.Batching.Supplement

/-- Theorem 4, p. 16: if `γ_{1d} > 0`, `E[|g* - x|^{-1/2}] < ∞`, the pair `(X, Y)` has a joint density
and `E[q₁ + q₂] > 0`, then for every `y` the limit `Pr{Y ≤ y | X = x}` of (3) exists and equals
`E[I{Y₁ ≤ y} q₁ + I{Y₂ ≤ y} q₂] / E[q₁ + q₂]`, expectations over `(Z_1, …, Z_{d-1})`. -/
theorem theorem_4 {d' : ℕ} (M : DeltaGamma d') (hγ : 0 < M.γ1d) (x : ℝ)
    (hdens : lawXY M ≪ volume)
    (hfin : ∫⁻ w, (ENNReal.ofReal |M.gStar w - x|) ^ (-(1 / 2 : ℝ)) ∂(stdW d') < ⊤)
    (hpos : 0 < EQ M x) :
    ∀ y : ℝ, Tendsto (fun ε => condRatio M y x ε) (𝓝[>] 0) (𝓝 (EQy M y x / EQ M x)) := by sorry

end CoVaRMC.Batching.Supplement
