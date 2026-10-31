-- Prove2me | Theorems.Thm_AccelSGDGrowth_eq_4_14
-- name    : AccelSGDGrowth.eq_4_14
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:32:28.411187+00:00
-- url     : https://prove2.me/theorems/8076d53f-5634-4a54-aa26-c04977fc1cec
-- title:
--   (4.13)–(4.14) — the conjugate step $\phi_k^\star(z_{k+1})-\phi_{k-1}^\star(z_k)-(z_{k+1}-z_k)^\top\nabla\phi_k^\star(z_k)\le\frac{a_k^2}{2m_k}\|g_k\|^2$
-- statement:
--   Let $m>0$, positive weights $(a_k)$, real step sizes $(\eta_k)$, and a run $x,y,z,g$ of DAM+ (4.6); write $m_k=A_km$. For every $k\ge1$:
--
--   1. (4.13) if $k\ge2$, then $\phi_{k-1}^\star(w)\ge\phi_k^\star(w)$ for all $w$;
--   2. (4.14)
--   $$
--   \phi_k^\star(z_{k+1})-\phi_{k-1}^\star(z_k)-(z_{k+1}-z_k)^\top\nabla\phi_k^\star(z_k)\le\frac{a_k^2}{2m_k}\|g_k\|^2 .
--   $$
--
--   This bounds the dual-averaging part of the one-step progress of the potential.
--
--   Differences from the source:
--   - encoding: (4.13) φ⋆_{k−1}(z) ≥ φ⋆_k(z) for all k ≥ 1 → for k ≥ 2; reason: at k = 1, φ⋆_0(z) = +∞ for z ≠ 0, so the source's inequality is trivially true there and is not representable with a real-valued conjugate
--   - reading: the chain (4.14) of two inequalities and three equalities → its first expression ≤ its last expression; reason: the outer inequality is what the proof of Theorem 4.1 uses; the intermediate Bregman-divergence expressions are steps of its proof
-- source:
--   Chen, Na, Kolar, Convergence Analysis of Accelerated Stochastic Gradient Descent under the Growth Condition, arXiv:2006.06782v4 (preprint basis), https://arxiv.org/abs/2006.06782v4, (4.13) and (4.14), p.18

import Definitions.Def_AccelSGDGrowth_IsDAMPlusRun

namespace AccelSGDGrowth

/-- Chen, Na, Kolar, arXiv:2006.06782v4, (4.13) and (4.14), p.18. Along a DAM+ run (4.6) with
`m > 0` and positive weights, for every `k ≥ 1`, with `m_k = A_k m`:
* (4.13) for `k ≥ 2`, `φ⋆_{k−1}(w) ≥ φ⋆_k(w)` for all `w`;
* (4.14) `φ⋆_k(z_{k+1}) − φ⋆_{k−1}(z_k) − (z_{k+1} − z_k)ᵀ∇φ⋆_k(z_k) ≤ (a_k²/(2m_k))‖g_k‖²`.

**Formalization Note.** (4.13) is stated for `k ≥ 2`: at `k = 1` the paper's `φ⋆_0(w)` is `+∞` for
`w ≠ 0`, which the real-valued `phiStar` cannot represent (it returns `0`), so the `k = 1` case is
the trivial `+∞ ≥ φ⋆_1(w)` and is omitted. (4.14) holds at `k = 1` with `φ⋆_0(z_1) = φ⋆_0(0) = 0`.
The item is the outer inequality of the chain (4.14) (first expression ≤ last). -/
theorem eq_4_14 {d : ℕ} {m : ℝ} (hm : 0 < m) (a η : ℕ → ℝ) (ha : ∀ k : ℕ, 1 ≤ k → 0 < a k)
    (x y z g : ℕ → EuclideanSpace ℝ (Fin d)) (hrun : IsDAMPlusRun m a η x y z g)
    (k : ℕ) (hk : 1 ≤ k) :
    (2 ≤ k → ∀ w : EuclideanSpace ℝ (Fin d), phiStar m a x k w ≤ phiStar m a x (k - 1) w) ∧
    phiStar m a x k (z (k + 1)) - phiStar m a x (k - 1) (z k) -
        inner ℝ (z (k + 1) - z k) (gradient (phiStar m a x k) (z k)) ≤
      a k ^ 2 / (2 * (cumWeight a k * m)) * ‖g k‖ ^ 2 := by sorry

end AccelSGDGrowth
