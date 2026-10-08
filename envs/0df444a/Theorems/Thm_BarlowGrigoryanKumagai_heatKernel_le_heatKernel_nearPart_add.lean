-- Prove2me | Theorems.Thm_BarlowGrigoryanKumagai_heatKernel_le_heatKernel_nearPart_add
-- name    : BarlowGrigoryanKumagai.heatKernel_le_heatKernel_nearPart_add
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-04T11:31:47.097065+00:00
-- url     : https://prove2.me/theorems/71888118-3a57-42d1-86ea-675ddb26647c
-- title:
--   Barlow–Grigor’yan–Kumagai, Lemma 3.1(c) (Meyer’s construction, as Erschler–Zheng apply it in (7.14)) — p(t,x,y) ≤ p_R(t,x,y) + t·‖J^R_2‖_∞
-- statement:
--   Let $X$ be a countable set, $J$ a symmetric transition kernel on $X$ (`IsTransition J`, `IsSymmetric J`), $\rho$ a metric on $X$ (`IsMetric ρ`), $R$ a real number and $t > 0$. Then for all $x, y \in X$,
--   $$p(t,x,y) \le p_R(t,x,y) + t\,\|J^R_2\|_\infty.$$
--   Here:
--
--   - $p(t,x,y) = \sum_{n\ge0}e^{-t}\frac{t^n}{n!}J^n(x,y)$ (`heatKernel J t x y`) is the transition function of the continuous-time walk with jump kernel $J$;
--   - $p_R$ (`heatKernel (nearPart J ρ R)`) is the heat kernel of the near part $J^R_1(u,v) = J(u,v)\mathbf 1_{\{\rho(u,v)\le R\}}$: the transition function of the jump process with jump kernel $J^R_1$, in which each jump longer than $R$ becomes a stay at the current point;
--   - $\|J^R_2\|_\infty$ (`supNorm (farPart J ρ R)`) is the supremum of $J(u,v)$ over all pairs $(u,v)$ of $X$ with $\rho(u,v) > R$, and $0$ if there are none.
--
--   The error term is $t$ times the largest single far jump weight, not the largest total far mass $\sup_u\sum_v J^R_2(u,v)$. Any real $R$ is allowed. The inequality is stated in $[0,\infty]$, each heat kernel entering through `ENNReal.ofReal`; all its terms are finite and non-negative, so it is the real inequality displayed.
--
--   M. T. Barlow, A. Grigor’yan and T. Kumagai, *Heat kernel upper bounds for jump processes and the first exit time*, J. Reine Angew. Math. 626 (2009) 135–157, [doi:10.1515/CRELLE.2009.005](https://doi.org/10.1515/CRELLE.2009.005), write in §3.1 (quoted from p. 16 of the authors’ preprint of September 2007): “We use the following construction of Meyer [16] for jump processes. Let $n(x,y) = n'(x,y) + n''(x,y)$, and suppose there exists $C_1$ such that $N(x) = \int n''(x,y)\mu(dy) \le C_1$ for all $x$. Let $(Y_t, t \ge 0)$ be a process corresponding to the jump kernel $n'$. Then we can construct a process $X$ corresponding to the jump kernel $n$ by the following procedure.” … “Let $\mathcal F^Y_t = \sigma(Y_s, s \in [0,t])$, and write $p^Y_t(x,y)$ for the transition density of $Y$. **Lemma 3.1** Let $n = n' + n''$, $X$ and $Y$ be as above. … (c) If $\|n''\|_\infty < \infty$ then $p_t(x,y) \le p^Y_t(x,y) + t\|n''\|_\infty$ for $\mu$-a.a. $y \in M$. (3.4)” The authors’ corrections to the journal version place part (b), display (3.3), on p. 152, and add a missing factor $e^{-H_s}$ to the integrand of (3.3) and of a formula in its proof (p. 153); they list no change to (3.4).
--
--   A. Erschler and T. Zheng, *Growth of periodic Grigorchuk groups*, Invent. Math. 219 (2020) 1069–1155, [doi:10.1007/s00222-019-00922-0](https://doi.org/10.1007/s00222-019-00922-0), with the page numbers of [arXiv:1802.09077v2](https://arxiv.org/abs/1802.09077v2), write in the proof of Proposition 7.20 (p. 51): “Let $p_R(t,x,y)$ be transition density of the jumping process with jump kernel $J_1^R$. Then as a consequence of the Meyer’s construction, see [4, Lemma 3.1], we have (7.14) $p(t,x,y) \leqslant p_R(t,x,y) + t\left\|J_2^R\right\|_\infty$.”
--
--   This statement is Lemma 3.1(c) with $\mu$ the counting measure on $X$, $n = J$, $n' = J^R_1$ and $n'' = J^R_2$, where “$\mu$-a.a. $y$” means every $y$. Since $0 \le J^R_2 \le J$ entrywise and the rows of $J$ sum to $1$, the constant $C_1 = 1$ bounds $N(x) = \sum_y J^R_2(x,y)$, and $\|n''\|_\infty \le 1$. The transition functions of $X$ and $Y$ are read as the two heat kernels, as in the definitions bundle’s note on `heatKernel`: the series in $J$ for $X$, in which a diagonal entry $J(x,x)$ is a jump to the same point, and the series in $U$ = `uniformize (nearPart J ρ R)` for $Y$, whose off-diagonal entries are those of $J^R_1$.
--
--   The proof of (c) (p. 17 of the preprint) bounds $N(x)r_s(x,z)$ by $\|n''\|_\infty\int p_s(y,z)\mu(dy) = \|n''\|_\infty$, an integral of $p_s$ over its first variable. The proof here argues with the kernels instead of the processes: $J \le U + J^R_2$ entrywise; peeling one step at a time gives $J^n(x,y) \le U^n(x,y) + n\|J^R_2\|_\infty$, where the columns of $U$ sum to $1$ because $J$ and $\rho$ are symmetric; and averaging over the Poisson weights, whose mean is $t$, gives the statement.
-- source:
--   M. T. Barlow, A. Grigor'yan and T. Kumagai, Heat kernel upper bounds for jump processes and the first exit time, J. Reine Angew. Math. 626 (2009) 135–157, https://doi.org/10.1515/CRELLE.2009.005, Lemma 3.1, as applied in A. Erschler and T. Zheng, Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 51, (7.14)

import Mathlib
import Definitions.Def_DurrettProbability_MarkovChain
import Definitions.Def_MarkovChain_HeatKernels

open DurrettProbability MarkovChain

namespace BarlowGrigoryanKumagai

theorem heatKernel_le_heatKernel_nearPart_add {X : Type*} [Countable X] [DecidableEq X]
    (J ρ : X → X → ℝ) (hJ : IsTransition J) (hJs : IsSymmetric J) (hρ : IsMetric ρ) (R t : ℝ)
    (ht : 0 < t) (x y : X) :
    ENNReal.ofReal (heatKernel J t x y) ≤
      ENNReal.ofReal (heatKernel (nearPart J ρ R) t x y) +
        ENNReal.ofReal t * supNorm (farPart J ρ R) := by
  sorry

end BarlowGrigoryanKumagai
