-- Prove2me | Theorems.Thm_FastBestSubset_CDSS_lemma_8
-- name    : FastBestSubset.CDSS.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:03:22.476544+00:00
-- url     : https://prove2.me/theorems/50f977c3-3259-4168-867f-906febb305fc
-- title:
--   Lemma 8 — the sequence {βᵏ} of Algorithm 1 is bounded
-- statement:
--   Let $X$ have unit-norm columns, $\lambda_0>0$, $\lambda_1,\lambda_2\ge0$ with $\lambda_1=0$ or $\lambda_2=0$ (the problems (L0), (L0L1), (L0L2)), and when $\lambda_2=0$ assume Assumption 1 and, if $p>n$, Assumption 2. Let $\{\beta^k\}$ be the iterates of Algorithm 1 with a positive integer $C$. Then
--   $$\{\beta^k : k\ge0\}\ \text{ is a bounded subset of }\mathbb R^p .$$
--
--   Boundedness supplies the convergent subsequences used to identify the limit points of the algorithm.
--
--   **Formalization Note** Boundedness is stated for the product (sup) metric on `Fin p → ℝ`, which is equivalent to Euclidean boundedness.
-- source:
--   Hazimeh, Mazumder, Fast Best Subset Selection: Coordinate Descent and Local Combinatorial Optimization Algorithms, arXiv:1803.01454v3, Lemma 8, p. 37 (proof pp. 37–38)

import Mathlib
import Definitions.Def_FastBestSubset_CDSS_Setting

open Filter Topology

namespace FastBestSubset.CDSS

/-- Lemma 8 (p. 37): the sequence `{βᵏ}` of Algorithm 1 is bounded, for the (L0), (L0L1) and
(L0L2) problems, with Assumptions 1–2 in force for (L0) and (L0L1). -/
theorem lemma_8 {n p : ℕ} [NeZero p] (D : Data n p) (hX : ∀ j, ∑ r, D.X r j ^ 2 = 1)
    (hlam0 : 0 < D.lam0) (hlam1 : 0 ≤ D.lam1) (hlam2 : 0 ≤ D.lam2)
    (hscope : D.lam1 = 0 ∨ D.lam2 = 0)
    (C : ℕ) (hC : 0 < C) (β0 : Fin p → ℝ)
    (hA : D.lam2 = 0 → (Assumption1 D ∧ (n < p → Assumption2 D β0))) :
    Bornology.IsBounded (Set.range (iter D C β0)) := by sorry

end FastBestSubset.CDSS
