-- Prove2me | Theorems.Thm_FastBestSubset_PSI_support_once
-- name    : FastBestSubset.PSI.support_once
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:08:06.552161+00:00
-- url     : https://prove2.me/theorems/ce08ba95-28a8-4af0-ae30-f8940d0e02c9
-- title:
--   Proof of Theorem 4 (§A.8) — along CD-PSI(k) the objective strictly decreases and no support appears twice
-- statement:
--   Make the hypotheses of Theorem 2: unit-norm columns, $p\ge1$, $\lambda_0>0$, $\lambda_1,\lambda_2\ge0$ with $\lambda_1=0$ or $\lambda_2=0$, a positive integer $C$, and, when $\lambda_2=0$, Assumption 1 and (if $p>n$) Assumption 2 on $\beta^0$. Let $k\ge1$ and let $(\hat\beta^\ell)$, $(\beta^{\ell+1})$ be a run of Algorithm 2 (CD-PSI($k$)) started at $\beta^0$.
--
--   Suppose the algorithm has not terminated in iterations $0,\dots,L-1$, i.e. Problem (14) was improving at $\beta^1,\dots,\beta^L$. Then the outputs $\beta^1,\dots,\beta^{L+1}$ of Algorithm 1 satisfy
--   $$F(\beta^{L+1})<F(\beta^{L})<\cdots<F(\beta^{1}),$$
--   and their supports are pairwise distinct: $\operatorname{Supp}(\beta^i)\neq\operatorname{Supp}(\beta^j)$ for $1\le i<j\le L+1$.
--
--   Hence a support appears at most once during the course of Algorithm 2. Since there are only finitely many supports, this is what forces termination in Theorem 4.
--
--   **Formalization Note** The page states the claim for the outputs produced "before it terminates". Here the output $\beta^{L+1}$ of iteration $L$ is included; the same argument covers it, since $F(\beta^{L+1})\le F(\hat\beta^L)<F(\beta^L)$. Distinct supports are expressed as injectivity of $i\mapsto\operatorname{Supp}(\beta^i)$ on $\{1,\dots,L+1\}$.
-- source:
--   Hazimeh, Mazumder, Fast Best Subset Selection: Coordinate Descent and Local Combinatorial Optimization Algorithms, arXiv:1803.01454v3, §A.8, proof of Theorem 4, p. 44

import Mathlib
import Definitions.Def_FastBestSubset_CDSS_Setting
import Definitions.Def_FastBestSubset_PSI_CDPSI

namespace FastBestSubset.PSI

/-- Proof of Theorem 4 (§A.8, p. 44): along a run of Algorithm 2 that has not terminated in
iterations `0, …, L − 1`, the outputs `β¹, …, βᴸ⁺¹` of Algorithm 1 have strictly decreasing
objective, and their supports are pairwise distinct. -/
theorem support_once {n p : ℕ} [NeZero p] (D : FastBestSubset.CDSS.Data n p) (hX : ∀ j, ∑ r, D.X r j ^ 2 = 1)
    (hlam0 : 0 < D.lam0) (hlam1 : 0 ≤ D.lam1) (hlam2 : 0 ≤ D.lam2)
    (hscope : D.lam1 = 0 ∨ D.lam2 = 0)
    (C : ℕ) (hC : 0 < C) (β0 : Fin p → ℝ)
    (hA : D.lam2 = 0 → (FastBestSubset.CDSS.Assumption1 D ∧ (n < p → FastBestSubset.CDSS.Assumption2 D β0)))
    (k : ℕ) (hk : 0 < k) (βhat β : ℕ → Fin p → ℝ) (hrun : IsCDPSIRun D k C β0 βhat β)
    (L : ℕ) (hL : ∀ m < L, Improving14 D k (β (m + 1))) :
    (∀ m < L, FastBestSubset.CDSS.F D (β (m + 2)) < FastBestSubset.CDSS.F D (β (m + 1))) ∧
      Set.InjOn (fun i => FastBestSubset.CDSS.supp (β i)) (Set.Icc 1 (L + 1)) := by sorry

end FastBestSubset.PSI
