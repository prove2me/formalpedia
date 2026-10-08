-- Prove2me | Theorems.Thm_ErschlerZhengPrinted_exists_dirichletEigenvalue_lt_half_mul_sq_boundarySize_div
-- name    : ErschlerZhengPrinted.exists_dirichletEigenvalue_lt_half_mul_sq_boundarySize_div
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-04T11:32:07.378356+00:00
-- url     : https://prove2.me/theorems/eddbd8cd-3782-4ead-927c-11415aad4e4a
-- title:
--   Erschler–Zheng, p. 24, (5.1) as printed — a reversible chain on three states with λ₁(Ω) < ½·(|∂Ω|/π(Ω))²
-- statement:
--   There are a transition kernel $P$ on the three-element set `Fin 3` (`IsTransition P`), a weight $\pi$ with $\pi(x) > 0$ for every $x$ such that $P$ is reversible with respect to $\pi$ (`IsReversible P π`: $\pi(x)P(x,y) = \pi(y)P(y,x)$), and a non-empty set $\Omega \subseteq$ `Fin 3`, such that
--   $$\lambda_1(\Omega) < \frac12\left(\frac{|\partial_P\Omega|}{\pi(\Omega)}\right)^2.$$
--   Here $\lambda_1(\Omega)$ (`dirichletEigenvalue P π Ω`) is the infimum of $\mathcal E_P(f) = \frac12\sum_{x,y}(f(x)-f(y))^2P(x,y)\pi(x)$ over the real functions $f$ that vanish outside $\Omega$ and have $\sum_x f(x)^2\pi(x) = 1$; $|\partial_P\Omega| = \sum_{x\in\Omega}\sum_{y\notin\Omega}\pi(x)P(x,y)$ (`boundarySize P π Ω`) is the flow out of $\Omega$; and $\pi(\Omega) = \sum_{x\in\Omega}\pi(x)$.
--
--   So Cheeger’s inequality (5.1) of A. Erschler and T. Zheng, *Growth of periodic Grigorchuk groups*, Invent. Math. 219 (2020) 1069–1155, [doi:10.1007/s00222-019-00922-0](https://doi.org/10.1007/s00222-019-00922-0), fails when it is read as printed, as a claim about each set $\Omega$ on its own. On p. 24 of [arXiv:1802.09077v2](https://arxiv.org/abs/1802.09077v2) they write: “By Cheeger’s inequality (see [37, Theorem 3.1]) (5.1) $\lambda_1(\Omega) \geqslant \frac12\left(\frac{|\partial_P\Omega|}{\pi(\Omega)}\right)^2$, where $|\partial_P\Omega| = \sum_{x\in\Omega,y\in\Omega^c}\pi(x)P(x,y)$ is the size of the boundary of $\Omega$ with respect to $(P,\pi)$.”
--
--   One example: the states $0, 1, 2$, with $0$ absorbing and $1$ and $2$ exchanged, that is $P(0,0) = P(1,2) = P(2,1) = 1$ and every other entry $0$; the weight $\pi \equiv 1$; and $\Omega = \{0, 1\}$. The kernel is symmetric, hence reversible with respect to $\pi \equiv 1$. The only flow out of $\Omega$ is $P(1,2) = 1$, so $|\partial_P\Omega|/\pi(\Omega) = 1/2$ and the right-hand side is $1/8$. The indicator function of $\{0\}$ vanishes outside $\Omega$, has $\sum_x f(x)^2\pi(x) = 1$, and has $\mathcal E_P(f) = 0$ because no transition joins $0$ to another state. So $\lambda_1(\Omega) \le 0 < 1/8$.
--
--   Cheeger’s inequality as G. F. Lawler and A. D. Sokal prove it (*Bounds on the $L^2$ spectrum for Markov chains and Markov processes: a generalization of Cheeger’s inequality*, Trans. Amer. Math. Soc. 309 (1988) 557–580, [doi:10.1090/S0002-9947-1988-0930082-9](https://doi.org/10.1090/S0002-9947-1988-0930082-9), Theorem 3.1, p. 565) bounds $\lambda_0$ below by $h^2/2M$ with “(3.3) $h \equiv \inf_{\substack{A\in\mathscr S\\ \pi(A)>0}} h(A)$” (p. 564), an infimum of boundary ratios over subsets. With the ratio bounded below for every non-empty $U \subseteq \Omega$, the inequality holds: that is `LawlerSokal.half_mul_sq_le_dirichletEigenvalue_of_mul_le_boundarySize`. It is also the form Erschler and Zheng apply in the proofs of Lemma 5.2 (p. 25) and Proposition 7.19 (p. 48), where the ratio is bounded below for every set of bounded size.
-- source:
--   A. Erschler and T. Zheng, Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 24, (5.1) as printed

import Mathlib
import Definitions.Def_DurrettProbability_MarkovChain
import Definitions.Def_MarkovChain_HeatKernels

open DurrettProbability MarkovChain

namespace ErschlerZhengPrinted

theorem exists_dirichletEigenvalue_lt_half_mul_sq_boundarySize_div :
    ∃ (P : Fin 3 → Fin 3 → ℝ) (π : Fin 3 → ℝ) (Ω : Finset (Fin 3)),
      IsTransition P ∧ (∀ x, 0 < π x) ∧ IsReversible P π ∧ Ω.Nonempty ∧
        dirichletEigenvalue P π Ω < 1 / 2 * (boundarySize P π Ω / ∑ x ∈ Ω, π x) ^ 2 := by
  sorry

end ErschlerZhengPrinted
