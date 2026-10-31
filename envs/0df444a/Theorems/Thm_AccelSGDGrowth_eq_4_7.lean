-- Prove2me | Theorems.Thm_AccelSGDGrowth_eq_4_7
-- name    : AccelSGDGrowth.eq_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:31:31.873039+00:00
-- url     : https://prove2.me/theorems/70ca4001-baa0-4cf1-ba3b-2b873345a90d
-- title:
--   (4.7) — closed form of $\nabla\phi_k^\star$; (4.6a) is uniquely solvable for $k\ge2$ (corrected: at $k=1$ it forces $z_1=0$)
-- statement:
--   Let $m>0$, $k\ge1$, positive weights $a_1,\dots,a_k$ and points $x_1,\dots,x_k\in\mathbb R^d$; write $A_k=\sum_{i\le k}a_i$ and $m_k=A_km$.
--
--   1. For every $z$, the point
--   $$
--   u=\frac{z+m\sum_{i=1}^k a_ix_i}{A_km}=\frac{z+m\sum_{i=1}^{k-1}a_ix_i}{m_k}+\frac{a_k}{A_k}x_k
--   $$
--   is the unique maximizer of $v\mapsto z^\top v-\phi_k(v)$, $\phi_k^\star(z)=z^\top u-\phi_k(u)$, and $\nabla\phi_k^\star(z)=u$ (4.7).
--   2. For $k\ge2$, given $y_k$, $z_k$ and $x_1,\dots,x_{k-1}$, the implicit equation (4.6a)
--   $$
--   x_k=\frac{A_{k-1}}{A_k}y_k+\frac{a_k}{A_k}\nabla\phi_k^\star(z_k)
--   $$
--   (where $\phi_k$ contains the unknown $x_k$) has exactly one solution $x_k$.
--   3. For $k=1$, (4.6a) holds if and only if $z_1=0$, whatever $x_1$ and $y_1$ are.
--
--   Clause 2 makes DAM+ well defined from the second step on; clause 3 shows that the first step does not determine $x_1$ but forces $z_1=0$.
--
--   Differences from the source:
--   - correction: 'Since a_k/A_k < 1, (4.6a) is always solvable for x_k' → unique solvability for k ≥ 2; at k = 1, (4.6a) holds iff z_1 = 0; reason: a_1/A_1 = 1, so at k = 1 (4.6a) reads x_1 = x_1 + z_1/(a_1 m): for any z_1 ≠ 0 it has no solution x_1
--   - generalization: the closed form (4.7) of ∇φ⋆_k obtained from Lemma 2.3(a) (∇f⋆(z) = argmax) → the gradient identity together with attainment, uniqueness of the maximizer and the value φ⋆_k(z) = zᵀu − φ_k(u); reason: the extra conjuncts are the argmax characterization the page invokes; the gradient identity (4.7) is one of the conjuncts
-- source:
--   Chen, Na, Kolar, Convergence Analysis of Accelerated Stochastic Gradient Descent under the Growth Condition, arXiv:2006.06782v4 (preprint basis), https://arxiv.org/abs/2006.06782v4, (4.7) and the following sentence, p.16

import Definitions.Def_AccelSGDGrowth_cumWeight
import Definitions.Def_AccelSGDGrowth_phiStar

namespace AccelSGDGrowth

/-- Chen, Na, Kolar, arXiv:2006.06782v4, (4.7), p.16, and the sentence after it.
Let `m > 0`, `k ≥ 1`, positive weights `a_1, …, a_k` and points `x_1, …, x_k`; write
`A_k = Σ_{i≤k} a_i` and `m_k = A_k m`.

1. For every `z`, the supremum defining `φ⋆_k(z)` is attained exactly at
   `u = (z + m Σ_{i=1}^k a_i x_i)/(A_k m)`: `u` maximizes `v ↦ zᵀv − φ_k(v)`, it is the only maximizer,
   `φ⋆_k(z) = zᵀu − φ_k(u)`, `∇φ⋆_k(z) = u`, and
   `u = (z + m Σ_{i=1}^{k−1} a_i x_i)/m_k + (a_k/A_k) x_k` (4.7).
2. For `k ≥ 2`, given `y_k`, `z_k` and `x_1, …, x_{k−1}`, the implicit equation (4.6a)
   `x_k = (A_{k−1}/A_k) y_k + (a_k/A_k) ∇φ⋆_k(z_k)` (where `φ⋆_k` contains `x_k`) has exactly one
   solution `x_k` ("Since a_k/A_k < 1, (4.6a) is always solvable for x_k").
3. For `k = 1`, (4.6a) holds if and only if `z_1 = 0`, whatever `x_1` and `y_1` are.

**Formalization Note.** In clause 2, the candidate `v` for `x_k` is substituted into the conjugate
through `Function.update x k v`. Clause 3 records that the page's "a_k/A_k < 1" fails at `k = 1`
(`a_1/A_1 = 1`): there (4.6a) is a condition on `z_1`, not an equation for `x_1`. -/
theorem eq_4_7 {d : ℕ} {m : ℝ} (hm : 0 < m) (a : ℕ → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin d))
    (k : ℕ) (hk : 1 ≤ k) (ha : ∀ i ∈ Finset.Icc 1 k, 0 < a i) :
    (∀ z u : EuclideanSpace ℝ (Fin d),
      u = (1 / (cumWeight a k * m)) • (z + m • ∑ i ∈ Finset.Icc 1 k, a i • x i) →
      (∀ v : EuclideanSpace ℝ (Fin d),
        inner ℝ z v - phi m a x k v ≤ inner ℝ z u - phi m a x k u) ∧
      (∀ v : EuclideanSpace ℝ (Fin d),
        inner ℝ z v - phi m a x k v = inner ℝ z u - phi m a x k u → v = u) ∧
      phiStar m a x k z = inner ℝ z u - phi m a x k u ∧
      gradient (phiStar m a x k) z = u ∧
      u = (1 / (cumWeight a k * m)) • (z + m • ∑ i ∈ Finset.Icc 1 (k - 1), a i • x i) +
        (a k / cumWeight a k) • x k) ∧
    (2 ≤ k → ∀ y z : EuclideanSpace ℝ (Fin d), ∃! v : EuclideanSpace ℝ (Fin d),
      v = (cumWeight a (k - 1) / cumWeight a k) • y +
        (a k / cumWeight a k) • gradient (phiStar m a (Function.update x k v) k) z) ∧
    (k = 1 → ∀ y z : EuclideanSpace ℝ (Fin d),
      (x 1 = (cumWeight a 0 / cumWeight a 1) • y +
        (a 1 / cumWeight a 1) • gradient (phiStar m a x 1) z ↔ z = 0)) := by sorry

end AccelSGDGrowth
