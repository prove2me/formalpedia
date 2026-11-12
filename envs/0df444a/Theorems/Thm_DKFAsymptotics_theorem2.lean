-- Prove2me | Theorems.Thm_DKFAsymptotics_theorem2
-- name    : DKFAsymptotics.theorem2
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-15T20:54:16.146982+00:00
-- url     : https://prove2.me/theorems/139ecfb7-19bf-4fa0-ab9e-e05a4cccc3bc
-- title:
--   Theorem 2 — Discriminative Kalman Filter asymptotics
-- statement:
--   Let the state dimension be positive and finite. Let $A$ be real and let $\Gamma,S$ be symmetric positive-definite matrices with $S=ASA^\top+\Gamma$. Set $p(z)=\eta_d(z;0,S)$ and $(\tau s)(z)=\int\eta_d(z;Ay,\Gamma)s(y)\,dy$.
--
--   Let $s_n,u_n$ be probability densities and let $s'_n,u'_n$ be Gaussian probability densities with positive-definite covariances, for each positive integer $n$. Assume the normalized density $p_n=(u_n\tau s_n/p)/\|u_n\tau s_n/p\|_1$ is well defined for every $n$. Let $P$ be an arbitrary probability measure and $b\in\mathbb R^d$. Assume
--
--   $$s_n\Rightarrow P,\quad \|s_n-s'_n\|_1\to0,\quad u_n\Rightarrow\delta_b,\quad \|u_n-u'_n\|_1\to0,\quad p_n\Rightarrow\delta_b.$$
--
--   All densities and $L^1$ distances use Lebesgue measure. Weak convergence means convergence against every bounded continuous real test function. The approximate update is the specific expression $p'_n=(u'_n\tau s'_n/p)/\|u'_n\tau s'_n/p\|_1$; its validity is not assumed at every index.
--
--   Then $s'_n\Rightarrow P$.
--
--   Then $u'_n\Rightarrow\delta_b$.
--
--   Then, for all sufficiently large $n$, the approximate update has a measurable weight and a finite, strictly positive normalizer, and $p'_n$ is a Gaussian probability density with positive-definite covariance.
--
--   Then $p'_n\Rightarrow\delta_b$. The conclusion concerns the same normalized update as C3, including its eventual validity established in that milestone.
--
--   Then $\|p_n-p'_n\|_1\to0$. Equivalently, the total variation distance between the exact and DKF filtering densities tends to zero.
--
--   ## Intended proof following Appendix B
--
--   The proof targets remain open. The intended argument follows the appendix in this order.
--
--   1. **C1 and C2:** bound differences of bounded-continuous test-function integrals by the function's supremum norm times the input $L^1$ error. Apply A1–A2 and A3–A4 respectively.
--   2. **Lemma 1:** convolve the Gaussian transition with the previous Gaussian, combine the full quadratic form and complete the square. For the asymptotic part, use convergence of Gaussian means and covariances, the positive-definite noise covariance, and the appendix's bounded eigenvalue-perturbation argument. Prove that the updated covariance tends to zero and its mean tends to $b$.
--   3. **C3 and C4:** apply Lemma 1 using C1 and C2. Gaussian identities and density updates must be transported across almost-everywhere equality of representatives.
--   4. **C5:** retain the five-term decomposition in equation (B.2). A5 and C4 control the four outer reweighting and normalization terms. Product-measure weak convergence gives the common positive limit $\alpha=\int\eta_d(b;Ay,\Gamma)\,dP(y)$ for the two middle normalizers. The bound $\|\tau h\|_\infty\le\eta_d(0;0,\Gamma)\|h\|_1$, together with A2 and A4, controls the middle term.
--
--   One intermediate identity requires care without strengthening the assumptions. The difference $D_n=G_n^{-1}-S^{-1}$ in (B.3) can be singular. Use the equivalent identity $T_n=(I+U_nD_n)^{-1}U_n$ and $T_nU_n^{-1}=(I+U_nD_n)^{-1}$, which give the same limits without assuming an inverse of $D_n$. At finite indices, combine the full precision quadratic form before identifying a Gaussian: the quotient by the stationary prior need not itself be a Gaussian density.
-- source:
--   M. C. Burkhart, D. M. Brandman, B. Franco, L. R. Hochberg and M. T. Harrison, The Discriminative Kalman Filter for Bayesian Filtering with Nonlinear and Nongaussian Observation Models, Neural Computation 32(5), 969–1017 (2020), doi:10.1162/neco_a_01275; https://burkh4rt.github.io/pubs/Burkhart-et-al-2020-Neural-Comput.pdf; Appendix B, Theorem 2, p. 1003; proof pp. 1005–1007.

import Definitions.Def_DKFAsymptotics_Assumptions

noncomputable section
open MeasureTheory Filter Matrix
open scoped Topology ENNReal

namespace DKFAsymptotics

theorem theorem2 {d : ℕ} [NeZero d] (M : Model d) (D : Problem M)
    (h : Assumptions M D) :
    Weakly D.s' D.P ∧
    Weakly D.u' (Measure.dirac D.b) ∧
    (∀ᶠ n in atTop, UpdateDefined M (D.s' n) (D.u' n) ∧
      IsGaussianPDF (D.p' M n)) ∧
    Weakly (D.p' M) (Measure.dirac D.b) ∧
    Tendsto (fun n => l1Distance (D.p M n) (D.p' M n)) atTop (𝓝 0) := by sorry

end DKFAsymptotics
