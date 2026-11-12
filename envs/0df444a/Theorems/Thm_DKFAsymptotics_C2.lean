-- Prove2me | Theorems.Thm_DKFAsymptotics_C2
-- name    : DKFAsymptotics.C2
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-15T20:52:41.514419+00:00
-- url     : https://prove2.me/theorems/7421b6c2-dc61-44ab-8810-b84d71c7458b
-- title:
--   Theorem 2, C2 — Concentration of the discriminative Gaussian approximation
-- statement:
--   Let the state dimension be positive and finite. Let $A$ be real and let $\Gamma,S$ be symmetric positive-definite matrices with $S=ASA^\top+\Gamma$. Set $p(z)=\eta_d(z;0,S)$ and $(\tau s)(z)=\int\eta_d(z;Ay,\Gamma)s(y)\,dy$.
--
--   Let $s_n,u_n$ be probability densities and let $s'_n,u'_n$ be Gaussian probability densities with positive-definite covariances, for each positive integer $n$. Assume the normalized density $p_n=(u_n\tau s_n/p)/\|u_n\tau s_n/p\|_1$ is well defined for every $n$. Let $P$ be an arbitrary probability measure and $b\in\mathbb R^d$. Assume
--
--   $$s_n\Rightarrow P,\quad \|s_n-s'_n\|_1\to0,\quad u_n\Rightarrow\delta_b,\quad \|u_n-u'_n\|_1\to0,\quad p_n\Rightarrow\delta_b.$$
--
--   All densities and $L^1$ distances use Lebesgue measure. Weak convergence means convergence against every bounded continuous real test function. The approximate update is the specific expression $p'_n=(u'_n\tau s'_n/p)/\|u'_n\tau s'_n/p\|_1$; its validity is not assumed at every index.
--
--   Then $u'_n\Rightarrow\delta_b$.
-- source:
--   M. C. Burkhart, D. M. Brandman, B. Franco, L. R. Hochberg and M. T. Harrison, The Discriminative Kalman Filter for Bayesian Filtering with Nonlinear and Nongaussian Observation Models, Neural Computation 32(5), 969–1017 (2020), doi:10.1162/neco_a_01275; https://burkh4rt.github.io/pubs/Burkhart-et-al-2020-Neural-Comput.pdf; Appendix B, Theorem 2, conclusion C2, p. 1003; proof pp. 1005–1007 and Lemma 1, pp. 1007–1010.

import Definitions.Def_DKFAsymptotics_Assumptions

noncomputable section
open MeasureTheory Filter Matrix
open scoped Topology ENNReal

namespace DKFAsymptotics

theorem C2 {d : ℕ} [NeZero d] (M : Model d) (D : Problem M)
    (h : Assumptions M D) :
    Weakly D.u' (Measure.dirac D.b) := by sorry

end DKFAsymptotics
