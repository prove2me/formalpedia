-- Prove2me | Theorems.Thm_ForecastComp_IELF_theorem_7
-- name    : ForecastComp.IELF.theorem_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:34:34.798994+00:00
-- url     : https://prove2.me/theorems/12d11084-9f05-4f7e-aa76-b31e16451f18
-- title:
--   Theorem 7, p. 14 — I-ELF is limit accurate for independent events
-- statement:
--   Let $n\ge2$ and let $R$ be any scoring rule with values in $[0,1]$ on reports in $[0,1]$. Then $M_{\text{I-ELF}^R}$ is limit accurate with respect to $R$ and the set of joint laws under which the event outcomes $X_1,\dots,X_m$ are independent: for every $\underline\Delta>0$ and every $\pi\in[0,1)$ there is $\underline m\in\mathbb N$ such that for all $m\ge\underline m$, all $\theta\in[0,1]^m$, all $y_1,\dots,y_n\in[0,1]^m$ and every forecaster $i$ with $R(y_i,\theta)-R(y_j,\theta)>\underline\Delta$ for all $j\ne i$,
--   $$\Pr_{X\sim\theta}\big(M_{\text{I-ELF}^R}(y_1,\dots,y_n,X)=i\big)>\pi.$$
--
--   The threshold $\underline m$ depends only on $n$, $\underline\Delta$ and $\pi$ (and $R$), never on $\theta$ or the reports.
--
--   **Formalization Note** Independent outcome laws are parametrized by their marginals $\theta\in[0,1]^m$. Strict properness of $R$ and the requirement $R<1$ for $m\ge2$ are not assumed: the result holds for every $[0,1]$-valued $R$ (a disclosed strengthening of the statement; the paper's $R$ satisfies it).
-- source:
--   Witkowski et al., arXiv:2101.01816v2, p. 14, Theorem 7 (proof pp. 35–36, Appendix M); Definition 7, p. 13

import Mathlib
import Definitions.Def_ForecastComp_IELF_Model

namespace ForecastComp.IELF

/-- Theorem 7, p. 14 (proof pp. 35–36): I-ELF is limit accurate for every scoring rule `R` with
values in `[0,1]` and all joint laws under which the event outcomes are independent. -/
theorem theorem_7 {n : ℕ} (hn : 2 ≤ n) (R : ℝ → Bool → ℝ) (hbdd : IsUnitBounded R) :
    IsLimitAccurateIndep R (fun m θ y i => ielfSelProbIndep (m := m) (n := n) R θ y i) := by sorry

end ForecastComp.IELF
