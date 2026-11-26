-- Prove2me | Theorems.Thm_ChandrasekaranNullCone_gaussian_sin_sin_D20
-- name    : ChandrasekaranNullCone.gaussian_sin_sin_D20
-- status  : Proved
-- author  : @Alien60
-- created : 2026-11-26T15:32:47.851795+00:00
-- url     : https://prove2.me/theorems/c06a6287-eaf9-5228-979e-722332455389
-- title:
--   Vacuum expectation of the bounded boost observable, eq. (D.20)
-- statement:
--   Let $(X,Y)$ be a real random vector on a probability space $(\Omega,\mathbb P)$ with a centred jointly Gaussian law: $\mathbb E[X]=\mathbb E[Y]=0$. Here $X$ and $Y$ model the two smeared graviton insertions $\hat\sigma_{f_L}$ and $\hat\sigma_{f_R}$ in the freely falling vacuum. Write
--   $$G_{LL}=\mathbb E[X^2],\qquad G_{RR}=\mathbb E[Y^2],\qquad G_{LR}=\mathbb E[XY].$$
--   Then for all real sources $j_L,j_R$, the bounded observable $\hat O=\sin(j_L\hat\sigma_{f_L})\sin(j_R\hat\sigma_{f_R})$ of (5.33) has
--   $$\mathbb E\big[\sin(j_LX)\sin(j_RY)\big]=\exp\!\Big[-\tfrac12\big(j_L^2G_{LL}+j_R^2G_{RR}\big)\Big]\sinh\big(j_Lj_RG_{LR}\big).$$
--
--   **Role in the source.** This is the vacuum value of the bounded observable used to evaluate the boost bound (5.32). A relative boost preserves $G_{LL}$ and $G_{RR}$ but deforms $G_{LR}$ by (5.29). By (D.20), the expectation of $\hat O$ therefore changes for suitable $j_L,j_R$.
--
--   **Formalization note.** The source evaluates (5.33) with the generating function (D.17) at fixed $j_L,j_R$. It notes that the two insertions commute because their supports are disjoint, so the commutator term drops out. What remains is a centred Gaussian generating function with logarithm $-\frac12\sum_{a,c}j_aj_cG_{ac}$. Their joint vacuum distribution is therefore that of a classical centred Gaussian pair, with $G_{ac}=\frac12\langle\{\hat\sigma_{f_a},\hat\sigma_{f_c}\}\rangle$ equal to the second moments. In Lean, joint Gaussianity is `HasGaussianLaw (fun ω => (X ω, Y ω)) P`, which implies `P` is a probability measure. Centring and the second moments are stated as integral hypotheses.
-- source:
--   Chandrasekaran 2026, An algebraic quantization of gravity from the null cone, https://arxiv.org/abs/2611.34924v1, Appendix D.2, p. 71, eq. (D.20), evaluating the observable of eq. (5.33) (p. 41) with the Gaussian generating function (D.17).

import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
open MeasureTheory ProbabilityTheory

namespace ChandrasekaranNullCone

/-- Chandrasekaran (arXiv:2611.34924), eq. (D.20) for the observable of (5.33): for a centred
jointly Gaussian pair `(X, Y)` (the two commuting smeared graviton insertions in the vacuum) with
second moments `G_LL = E[X²]`, `G_RR = E[Y²]`, `G_LR = E[XY]`,
`E[sin(j_L X) sin(j_R Y)] = exp[-(j_L² G_LL + j_R² G_RR)/2] sinh(j_L j_R G_LR)`. -/
theorem gaussian_sin_sin_D20 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X Y : Ω → ℝ)
    (hXY : HasGaussianLaw (fun ω => (X ω, Y ω)) P)
    (hX : ∫ ω, X ω ∂P = 0) (hY : ∫ ω, Y ω ∂P = 0)
    (G_LL G_RR G_LR : ℝ) (hLL : ∫ ω, X ω ^ 2 ∂P = G_LL) (hRR : ∫ ω, Y ω ^ 2 ∂P = G_RR)
    (hLR : ∫ ω, X ω * Y ω ∂P = G_LR) (j_L j_R : ℝ) :
    ∫ ω, Real.sin (j_L * X ω) * Real.sin (j_R * Y ω) ∂P
      = Real.exp (-(j_L ^ 2 * G_LL + j_R ^ 2 * G_RR) / 2) * Real.sinh (j_L * j_R * G_LR) := by sorry

end ChandrasekaranNullCone
