-- Prove2me | Theorems.Thm_FastBestSubset_CDSS_lemma_10
-- name    : FastBestSubset.CDSS.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:03:20.846796+00:00
-- url     : https://prove2.me/theorems/effef45c-0866-4989-b6ad-1de312e4255f
-- title:
--   Lemma 10 — the support of every limit point of {βᵏ} occurs infinitely often
-- statement:
--   Let $X$ have unit-norm columns, $\lambda_0>0$, $\lambda_1,\lambda_2\ge0$ with $\lambda_1=0$ or $\lambda_2=0$, and when $\lambda_2=0$ assume Assumption 1 and, if $p>n$, Assumption 2. Let $\{\beta^k\}$ be the iterates of Algorithm 1 with a positive integer $C$. If $B$ is a limit point of $\{\beta^k\}$ with $\mathrm{Supp}(B)=S$, then
--   $$\mathrm{Supp}(\beta^k)=S\quad\text{for infinitely many }k .$$
--
--   The lemma ties every limit point to a support visited infinitely often, so that Lemma 9 applies to it.
--
--   **Formalization Note** "Limit point" is `MapClusterPt B atTop`: every neighbourhood of $B$ contains $\beta^k$ for infinitely many $k$.
-- source:
--   Hazimeh, Mazumder, Fast Best Subset Selection: Coordinate Descent and Local Combinatorial Optimization Algorithms, arXiv:1803.01454v3, Lemma 10, p. 40 (proof p. 40)

import Mathlib
import Definitions.Def_FastBestSubset_CDSS_Setting

open Filter Topology

namespace FastBestSubset.CDSS

/-- Lemma 10 (p. 40): if `B` is a limit point of `{βᵏ}` with `Supp(B) = S`, then
`Supp(βᵏ) = S` for infinitely many `k`. -/
theorem lemma_10 {n p : ℕ} [NeZero p] (D : Data n p) (hX : ∀ j, ∑ r, D.X r j ^ 2 = 1)
    (hlam0 : 0 < D.lam0) (hlam1 : 0 ≤ D.lam1) (hlam2 : 0 ≤ D.lam2)
    (hscope : D.lam1 = 0 ∨ D.lam2 = 0)
    (C : ℕ) (hC : 0 < C) (β0 : Fin p → ℝ)
    (hA : D.lam2 = 0 → (Assumption1 D ∧ (n < p → Assumption2 D β0)))
    (B : Fin p → ℝ) (hB : MapClusterPt B atTop (iter D C β0)) :
    ∃ᶠ k in atTop, supp (iter D C β0 k) = supp B := by sorry

end FastBestSubset.CDSS
