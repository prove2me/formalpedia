-- Prove2me | Theorems.Thm_Arxiv2108_02600_dirichlet_problem_unique_solution
-- name    : Arxiv2108_02600.dirichlet_problem_unique_solution
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T10:11:49.25532+00:00
-- url     : https://prove2.me/theorems/e064e096-5512-41c6-a305-8ed83ad10899
-- title:
--   Remark 2.3: the problem (DP) has a unique solution
-- statement:
--   Let $f\in B^{(0)}_{c,M}$ with $c>0$ and $M>0$, so that $\Gamma$ lies above the $x_1$-axis, and let $g\in[BC(\Gamma)\cap H^{1/2}_{\rm loc}(\Gamma)]^2$. Then the Dirichlet problem (DP) has exactly one solution. That is, there is a unique $u\in[C^2(\Omega)\cap C(\overline\Omega)\cap H^1_{\rm loc}(\Omega)]^2$ such that
--
--   1. $\mu\Delta u+(\lambda+\mu)\nabla\nabla\cdot u+\omega^2u=0$ in $\Omega$;
--   2. $u=g$ on $\Gamma$;
--   3. $u$ satisfies the upward propagating radiation condition (2.3);
--   4. $\sup_{x\in\Omega}|x_2|^\beta|u(x)|<\infty$ for some $\beta\in\mathbb R$.
--
--   This is Remark 2.3, which combines Theorem 2.1 (uniqueness, [TA01, Thm 4.6]) with Theorem 2.2 ([TA02, Cor. 5.12]) and the potential (2.9).
--
--   **Formalization Note** The hypothesis $c>0$ is the paper's standing assumption that $\Gamma$ lies above the $x_1$-axis (Section 2). It is needed: the growth condition uses $|x_2|^\beta$, and the paper's existence argument gives it only with $\beta=-1/2$, which requires $x_2$ to stay away from $0$ on $\Omega$. Uniqueness is asserted on $\Omega$, since values outside $\overline\Omega$ do not enter (DP). $H^{1/2}_{\rm loc}(\Gamma)$ is expressed through the parametrization $x(s)=(s,f(s))$.
-- source:
--   J. Li, X. Liu, B. Zhang and H. Zhang, The Nyström method for elastic wave scattering by unbounded rough surfaces, arXiv:2108.02600v1 (2021), claim c024; Section 2, Remark 2.3 with Theorems 2.1-2.2 and the argument after (2.9), PDF pp. 6-7

import Mathlib
import Definitions.Def_Arxiv2108_02600_Basic

open MeasureTheory Filter Topology

namespace Arxiv2108_02600

theorem dirichlet_problem_unique_solution (P : Lame) (c M : ℝ) (hc : 0 < c) (hM : 0 < M) (f : ℝ → ℝ)
    (hf : InB 0 c M f) (g : Pt → Fin 2 → ℂ) (hg : IsDPData f g) :
    ∃ u : Pt → Fin 2 → ℂ, IsDPSolution P f g u ∧
      ∀ v : Pt → Fin 2 → ℂ, IsDPSolution P f g v → ∀ x ∈ domainAbove f, v x = u x := by sorry

end Arxiv2108_02600
