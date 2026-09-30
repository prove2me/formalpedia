-- Prove2me | Theorems.Thm_AccelPPM_FPR_lemma4_1_dual_feasible
-- name    : AccelPPM.FPR.lemma4_1_dual_feasible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T11:53:17.804509+00:00
-- url     : https://prove2.me/theorems/b20b64b6-5c4c-41df-9158-035e697e1963
-- title:
--   Lemma 4.1 — Kim's coefficients (25) with $a_i=\frac{2(i-1)i}{N^2}$, $b_N=\frac2N$, $c=\frac1{N^2}$ are feasible for (D)
-- statement:
--   Let $N\ge1$. Take Kim's step coefficients
--   $$
--   h_{i,k}=\begin{cases}-\dfrac{2k}{i(i+1)}, & k=1,\dots,i-1,\\[2mm] \dfrac{2i}{i+1}, & k=i,\end{cases}\qquad i=1,\dots,N-1,
--   $$
--   and the dual variables
--   $$
--   a_i=\frac{2(i-1)i}{N^2}\ (i=2,\dots,N),\qquad b_N=\frac2N,\qquad c=\frac1{N^2}.
--   $$
--   Then $(a_2,\dots,a_N,b_N,c)$ is a feasible point of the dual problem (D) for $h$: all dual variables are nonnegative and
--   $$
--   \sum_{i=2}^{N}a_iA_{i-1,i}(h)+b_NB_N(h)+cC-u_Nu_N^\top\succeq0 .
--   $$
--   Consequently $(h;a,b_N,c)$ is a feasible point of the joint problem (HD) $=\min_h\mathcal B_D(h)$, and $\mathcal B_D(h)\le1/N^2$.
--
--   This dual certificate is the source of the accelerated $O(1/N^2)$ rate of the fixed-point residual.
--
--   **Formalization Note** A feasible point of (HD) is a pair ($h$, dual variables) feasible for (D), so the single statement `IsDualFeasible N kimCoeff a b c` covers both halves of "a feasible point of (D) and (HD)". $a_i$ is the function `fun i => 2 * ((i:ℝ) - 1) * i / N^2`, with $i$ cast to $\mathbb R$ before subtracting; only $i=2,\dots,N$ is read.
-- source:
--   Kim, Accelerated proximal point method for maximally monotone operators, arXiv:1905.05149v4, p. 8, Lemma 4.1 (Eqs. (25), (26))

import Mathlib
import Definitions.Def_AccelPPM_FPR_kimCoeff
import Definitions.Def_AccelPPM_FPR_boundBD

namespace AccelPPM.FPR

/-- **Lemma 4.1** (Kim, arXiv:1905.05149v4, p. 8). For every `N ≥ 1`, the step coefficients
`h = (25)` (`kimCoeff`) together with the dual variables (26),
`a_i = 2(i − 1)i/N²` (`i = 2, …, N`), `b_N = 2/N`, `c = 1/N²`,
form a feasible point of the dual problem (D), hence (with `h`) of (HD). -/
theorem lemma4_1_dual_feasible (N : ℕ) (hN : 1 ≤ N) :
    IsDualFeasible N kimCoeff (fun i => 2 * ((i : ℝ) - 1) * (i : ℝ) / (N : ℝ) ^ 2)
      (2 / (N : ℝ)) (1 / (N : ℝ) ^ 2) := by sorry

end AccelPPM.FPR
