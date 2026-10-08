-- Prove2me | Theorems.Thm_Coulhon_nash_of_heatKernel_le
-- name    : Coulhon.nash_of_heatKernel_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-04T11:31:41.797766+00:00
-- url     : https://prove2.me/theorems/d6b56299-e34c-47c9-a445-e6734f167845
-- title:
--   Coulhon, Proposition II.2 (as Erschler–Zheng apply it) — p_R ≤ C·e^(4t/φ(R))·t^(−1/β) gives the Nash inequality for the near part J^R_1
-- statement:
--   For real numbers $C > 0$ and $\beta > 0$ there is a constant $C' > 0$, chosen before everything else and so depending only on $C$ and $\beta$, with the following property. Let $X$ be a countable set, $J$ a symmetric transition kernel on $X$ (`IsTransition J`, `IsSymmetric J`), $\rho$ a metric on $X$ (`IsMetric ρ`), $\phi : \mathbb R \to \mathbb R$ a function and $R$ a real number with $\phi(R) > 0$. Let $J^R_1$ be the near part of $J$ (`nearPart J ρ R`), with $J^R_1(x,y) = J(x,y)$ if $\rho(x,y) \le R$ and $0$ otherwise, and let $p_R$ be its heat kernel (`heatKernel (nearPart J ρ R)`): the transition function of the jump process with jump kernel $J^R_1$, in which each jump longer than $R$ is replaced by staying put. If, for every real $t > 0$ and all $x, y \in X$,
--   $$p_R(t,x,y) \le C\,e^{4t/\phi(R)}\,t^{-1/\beta},$$
--   then $J^R_1$ satisfies the Nash inequality with constants $C'$, $\delta = 4/\phi(R)$ and $\beta$ (`SatisfiesNash (nearPart J ρ R) C' (4 / φ R) β`): for every finitely supported $f : X \to \mathbb R$,
--   $$\|f\|_2^{2(1+\beta)} \le C'\Bigl(\mathcal E_{J^R_1}(f) + \tfrac{4}{\phi(R)}\|f\|_2^2\Bigr)\|f\|_1^{2\beta},$$
--   where $\|f\|_2^2 = \sum_x f(x)^2$, $\|f\|_1 = \sum_x|f(x)|$ and $\mathcal E_{J^R_1}(f) = \frac12\sum_{x,y}(f(x)-f(y))^2J^R_1(x,y)$ are taken for the counting measure. The function $\phi$ enters only through the number $\phi(R)$, and $C'$ depends neither on $R$ nor on $\phi$.
--
--   T. Coulhon, *Ultracontractivity and Nash type inequalities*, J. Funct. Anal. 141 (1996) 510–539, [doi:10.1006/jfan.1996.0140](https://doi.org/10.1006/jfan.1996.0140), states on p. 514: “**II.2. Proposition.** Let $T_t$ be a symmetric contractive semigroup on $L^2$, with infinitesimal generator $-A$, that satisfies $\|T_t\|^2_{1\to2} \leqslant m(t)$, $\forall t > 0$. Then $\tilde\theta(\|f\|_2^2) \leqslant (Af,f)$, $\forall f \in \mathscr D(A)$, $\|f\|_1 \leqslant 1$, where $\tilde\theta(x) = \sup_{t>0}(x/2t)\log(x/(m(t)))$.”
--
--   A. Erschler and T. Zheng, *Growth of periodic Grigorchuk groups*, Invent. Math. 219 (2020) 1069–1155, [doi:10.1007/s00222-019-00922-0](https://doi.org/10.1007/s00222-019-00922-0), with the page numbers of [arXiv:1802.09077v2](https://arxiv.org/abs/1802.09077v2), write in the proof of Proposition 7.20 (p. 51): “It follows that $\sup_{x,y}p_R(t,x,y) \leqslant e^{\frac{4t}{\phi(R)}}\sup_{x,y}p(t,x,y) \leqslant Ce^{\frac{4t}{\phi(R)}}t^{-1/\beta}$. By [17], this bound turns into Nash inequality $\|f\|_2^{2(1+\beta)} \leqslant C\left(\mathcal E_{J_1^R}(f,f) + \frac{4}{\phi(R)}\|f\|_2^2\right)\|f\|_1^{2\beta}$”. Here [17] is Coulhon’s paper, cited without a result number. Proposition II.2 is the result there that turns a bound on $\|T_t\|^2_{1\to2}$ into a Nash-type inequality with no assumption on the decay of $m$ (pp. 513–514); Proposition II.4 and Theorem II.5 (p. 516) assume a regularity condition (D) on $m$.
--
--   The formal proof does not cite Proposition II.2. It runs Coulhon’s comparison of $\|f\|_2^2$ with $\langle P_sf, f\rangle$ directly, using moments of the kernel in place of the spectral theorem. Let $\delta = 4/\phi(R)$ and let $U$ be `uniformize (nearPart J ρ R)`. For $f$ supported in a finite set, put $m_n = \sum_{x,y}f(x)U^n(x,y)f(y)$ and $Q_s = \sum_{x,y}f(x)\,p_R(s,x,y)\,f(y)$. Then $\mathcal E_{J^R_1}(f) = m_0 - m_1$ and $Q_s = \sum_n e^{-s}\frac{s^n}{n!}m_n$. The proof has three steps.
--
--   - The moments satisfy $m_0 - m_n \le n(m_0 - m_1)$, which stands in for the spectral inequality $1 - \lambda^n \le n(1 - \lambda)$ on $[-1,1]$. It is proved from the Gram identities $\|U^af - U^bf\|_2^2 = m_{2a} - 2m_{a+b} + m_{2b}$ and the $\ell^2$ contraction of $U$. Averaging over the Poisson weights gives $\|f\|_2^2 - Q_s \le s\,\mathcal E_{J^R_1}(f)$.
--   - The hypothesis gives $Q_s \le Ce^{\delta s}s^{-1/\beta}\|f\|_1^2$, and $Q_s \le \|f\|_2^2$. Together, for every $s > 0$,
--   $$\|f\|_2^2 \le s\bigl(\mathcal E_{J^R_1}(f) + \delta\|f\|_2^2\bigr) + C\,s^{-1/\beta}\|f\|_1^2 .$$
--   - The choice $s = (2C\|f\|_1^2/\|f\|_2^2)^\beta$ makes the last term $\frac12\|f\|_2^2$.
--
--   This gives the Nash inequality with $C' = 2(2C)^\beta$. The factor $e^{4t/\phi(R)}$ in the hypothesis becomes the term $\frac{4}{\phi(R)}\|f\|_2^2$.
-- source:
--   T. Coulhon, Ultracontractivity and Nash type inequalities, J. Funct. Anal. 141 (1996) 510–539, https://doi.org/10.1006/jfan.1996.0140, Proposition II.2, as applied in A. Erschler and T. Zheng, Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 51 (proof of Proposition 7.20)

import Mathlib
import Definitions.Def_DurrettProbability_MarkovChain
import Definitions.Def_MarkovChain_HeatKernels

universe u

open DurrettProbability MarkovChain

namespace Coulhon

theorem nash_of_heatKernel_le (C β : ℝ) (hC : 0 < C) (hβ : 0 < β) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ (X : Type u) [Countable X] [DecidableEq X] (J ρ : X → X → ℝ)
      (φ : ℝ → ℝ) (R : ℝ),
      IsTransition J → IsSymmetric J → IsMetric ρ → 0 < φ R →
      (∀ t : ℝ, 0 < t → ∀ x y,
        heatKernel (nearPart J ρ R) t x y ≤ C * Real.exp (4 * t / φ R) * t ^ (-1 / β)) →
      SatisfiesNash (nearPart J ρ R) C' (4 / φ R) β := by
  sorry

end Coulhon
