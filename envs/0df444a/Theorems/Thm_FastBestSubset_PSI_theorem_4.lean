-- Prove2me | Theorems.Thm_FastBestSubset_PSI_theorem_4
-- name    : FastBestSubset.PSI.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:07:51.080223+00:00
-- url     : https://prove2.me/theorems/7794061d-7bdb-4771-84c6-4f1c98bd30ed
-- title:
--   Theorem 4 — CD-PSI(k) terminates in finitely many iterations and its output is a PSI(k) minimum
-- statement:
--   Consider Problem (2), $\min_\beta F(\beta)=\tfrac12\|y-X\beta\|^2+\lambda_1\|\beta\|_1+\lambda_2\|\beta\|_2^2+\lambda_0\|\beta\|_0$, where the columns of $X\in\mathbb R^{n\times p}$ have unit $L_2$ norm, $p\ge1$, $\lambda_0>0$, $\lambda_1,\lambda_2\ge0$ and $\lambda_1=0$ or $\lambda_2=0$. For the (L0) and (L0L1) problems ($\lambda_2=0$), suppose Assumption 1 holds, and Assumption 2 holds for the initial point $\beta^0$ when $p>n$.
--
--   Let $k\ge1$ and $C\ge1$ be integers, and let $(\hat\beta^\ell)_{\ell\ge0}$, $(\beta^{\ell+1})_{\ell\ge0}$ be a run of Algorithm 2 (CD-PSI($k$)) started at $\beta^0$. Here $\beta^{\ell+1}$ is the output of Algorithm 1 (CDSS with parameter $C$) initialized at $\hat\beta^\ell$, and $\hat\beta^{\ell+1}$ is an improving feasible point of Problem (14) at $\beta^{\ell+1}$ whenever one exists. Then Algorithm 2 terminates after finitely many iterations, and its output is a PSI($k$) minimum. That is, there is an $L$ such that:
--
--   1. Problem (14) is improving at $\beta^1,\dots,\beta^L$ (the algorithm does not stop before iteration $L$);
--   2. Problem (14) is not improving at $\beta^{L+1}$ (the algorithm stops at iteration $L$);
--   3. $\beta^{L+1}$ is a PSI($k$) minimum: it is stationary and, for every $S_1\subseteq\operatorname{Supp}(\beta^{L+1})$ and $S_2\subseteq\operatorname{Supp}(\beta^{L+1})^c$ with $|S_1|,|S_2|\le k$,
--   $$F(\beta^{L+1})\le\min_{\beta_{S_2}}F\big(\beta^{L+1}-U_{S_1}\beta^{L+1}+U_{S_2}\beta\big).$$
--
--   This is the guarantee behind the local combinatorial search of Hazimeh and Mazumder: alternating coordinate descent with swap moves of size at most $k$ stops, and it stops at a point that no such swap can improve.
--
--   **Formalization Note** The scope sentence "For the (L0) and (L0L1) problems, suppose that Assumptions 1 and 2 hold" is encoded as in Theorem 2: the theorem covers (L0), (L0L1) and (L0L2), and Assumptions 1–2 are required only when $\lambda_2=0$. Assumption 2 is imposed on $\beta^0$ only; for the later calls of Algorithm 1 it is a consequence of the descent, not a hypothesis. The output of Algorithm 1 is the limit of its iterates. No bound on the number of iterations is claimed, as on the page.
-- source:
--   Hazimeh, Mazumder, Fast Best Subset Selection: Coordinate Descent and Local Combinatorial Optimization Algorithms, arXiv:1803.01454v3, Theorem 4, p. 13 (proof §A.8, p. 44)

import Mathlib
import Definitions.Def_FastBestSubset_CDSS_Setting
import Definitions.Def_FastBestSubset_PSI_CDPSI

namespace FastBestSubset.PSI

/-- Theorem 4 (p. 13): on the (L0), (L0L1) and (L0L2) problems (with Assumptions 1–2 for (L0) and
(L0L1)), every run of Algorithm 2 (CD-PSI(k)) terminates after finitely many iterations: there is
an iteration `L` such that iterations `0, …, L − 1` found an improving point of Problem (14) and
iteration `L` did not, and the output `βᴸ⁺¹` is a PSI(k) minimum. -/
theorem theorem_4 {n p : ℕ} [NeZero p] (D : FastBestSubset.CDSS.Data n p) (hX : ∀ j, ∑ r, D.X r j ^ 2 = 1)
    (hlam0 : 0 < D.lam0) (hlam1 : 0 ≤ D.lam1) (hlam2 : 0 ≤ D.lam2)
    (hscope : D.lam1 = 0 ∨ D.lam2 = 0)
    (C : ℕ) (hC : 0 < C) (β0 : Fin p → ℝ)
    (hA : D.lam2 = 0 → (FastBestSubset.CDSS.Assumption1 D ∧ (n < p → FastBestSubset.CDSS.Assumption2 D β0)))
    (k : ℕ) (hk : 0 < k) (βhat β : ℕ → Fin p → ℝ) (hrun : IsCDPSIRun D k C β0 βhat β) :
    ∃ L : ℕ, (∀ m < L, Improving14 D k (β (m + 1))) ∧ ¬ Improving14 D k (β (L + 1)) ∧
      IsPSI D k (β (L + 1)) := by sorry

end FastBestSubset.PSI
