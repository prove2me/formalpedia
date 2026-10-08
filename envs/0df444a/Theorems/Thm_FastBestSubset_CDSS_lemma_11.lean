-- Prove2me | Theorems.Thm_FastBestSubset_CDSS_lemma_11
-- name    : FastBestSubset.CDSS.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:03:20.904253+00:00
-- url     : https://prove2.me/theorems/8ef33695-86ce-4c00-96f3-a876b337af57
-- title:
--   Lemma 11 — two limit points whose supports differ by one coordinate j
-- statement:
--   Let $X$ have unit-norm columns, $\lambda_0>0$, $\lambda_1,\lambda_2\ge0$ with $\lambda_1=0$ or $\lambda_2=0$, and when $\lambda_2=0$ assume Assumption 1 and, if $p>n$, Assumption 2. Let $\{\beta^k\}$ be the iterates of Algorithm 1 with a positive integer $C$, and let $B^{(1)},B^{(2)}$ be two limit points with supports $S_1$ and $S_2=S_1\cup\{j\}$, where $j\notin S_1$. Put $\theta=\sqrt{2\lambda_0/(1+2\lambda_2)}$.
--
--   1. If $\langle X_i,X_j\rangle\neq0$ for some $i\in S_1$, then $|B^{(2)}_j|>\theta$.
--   2. If $\langle X_i,X_j\rangle=0$ for all $i\in S_1$, then $|B^{(2)}_j|=\theta$, and moreover for every $\beta\in\mathbb R^p$ with $\mathrm{Supp}(\beta)=S_2$,
--   $$\big|T(\tilde\beta_j,\lambda_0,\lambda_1,\lambda_2)\big|=\theta .$$
--
--   The two cases are complementary, so exactly one applies. The lemma is the device that rules out a coordinate being dropped from the support infinitely often in the proof of Theorem 2.
-- source:
--   Hazimeh, Mazumder, Fast Best Subset Selection: Coordinate Descent and Local Combinatorial Optimization Algorithms, arXiv:1803.01454v3, Lemma 11, p. 40 (proof pp. 40–42)

import Mathlib
import Definitions.Def_FastBestSubset_CDSS_Setting

open Filter Topology

namespace FastBestSubset.CDSS

/-- Lemma 11 (p. 40): let `B⁽¹⁾, B⁽²⁾` be limit points of `{βᵏ}` with supports `S₁` and
`S₂ = S₁ ∪ {j}`, `j ∉ S₁`. (1) If `⟨X_i, X_j⟩ ≠ 0` for some `i ∈ S₁`, then
`|B⁽²⁾_j| > √(2λ₀/(1+2λ₂))`. (2) If `⟨X_i, X_j⟩ = 0` for all `i ∈ S₁`, then
`|B⁽²⁾_j| = √(2λ₀/(1+2λ₂))`, and `|T(β̃_j, λ₀, λ₁, λ₂)| = √(2λ₀/(1+2λ₂))` for every `β` with
`Supp(β) = S₂`. -/
theorem lemma_11 {n p : ℕ} [NeZero p] (D : Data n p) (hX : ∀ j, ∑ r, D.X r j ^ 2 = 1)
    (hlam0 : 0 < D.lam0) (hlam1 : 0 ≤ D.lam1) (hlam2 : 0 ≤ D.lam2)
    (hscope : D.lam1 = 0 ∨ D.lam2 = 0)
    (C : ℕ) (hC : 0 < C) (β0 : Fin p → ℝ)
    (hA : D.lam2 = 0 → (Assumption1 D ∧ (n < p → Assumption2 D β0)))
    (B1 B2 : Fin p → ℝ)
    (hB1 : MapClusterPt B1 atTop (iter D C β0)) (hB2 : MapClusterPt B2 atTop (iter D C β0))
    (j : Fin p) (hj : j ∉ supp B1) (hS2 : supp B2 = insert j (supp B1)) :
    ((∃ i ∈ supp B1, ∑ r, D.X r i * D.X r j ≠ 0) →
        Real.sqrt (2 * D.lam0 / (1 + 2 * D.lam2)) < |B2 j|) ∧
    ((∀ i ∈ supp B1, ∑ r, D.X r i * D.X r j = 0) →
        |B2 j| = Real.sqrt (2 * D.lam0 / (1 + 2 * D.lam2)) ∧
        ∀ β : Fin p → ℝ, supp β = supp B2 →
          |T (btilde D β j) D.lam0 D.lam1 D.lam2| = Real.sqrt (2 * D.lam0 / (1 + 2 * D.lam2))) := by sorry

end FastBestSubset.CDSS
