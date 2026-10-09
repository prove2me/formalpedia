-- Prove2me | Theorems.Thm_DIGing_Push_lemma_17
-- name    : DIGing.Push.lemma_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:57:54.21595+00:00
-- url     : https://prove2.me/theorems/8dc753c6-eb40-4b0a-ba2f-30cc212f8267
-- title:
--   Lemma 17, p. 24 — last arrow x̌ → q, the bound (58)
-- statement:
--   Let Assumptions 4, 5 and 7 hold, let $x^*$ minimize $f=\frac1n\sum_if_i$, and let $(\mathbf u,\mathbf x,\mathbf y)$ be a run of Push-DIGing with step size $\alpha>0$. Suppose that $\beta>0$, $\eta>0$ and
--   $$\sqrt{1-\frac{\alpha\bar\mu\beta}{\beta+1}}\le\lambda<1,\qquad \alpha\le\frac1{(1+\eta)\bar L}.$$
--   Let $\mathbf q(k)=\mathbf x(k)-\mathbf 1(x^*)^\top$. Then for every $K=0,1,\dots$
--   $$\|\mathbf q\|_F^{\lambda,K}\le(1+\sqrt n)\Big(1+\frac{\sqrt n}{\lambda}\sqrt{\frac{L(1+\eta)}{\bar\mu\eta}+\frac{\hat\mu}{\bar\mu}\beta}\Big)\|\check{\mathbf x}\|_F^{\lambda,K}+2\sqrt n\,\|\bar{\mathbf x}(0)-x^*\|.$$
--
--   This is the fourth gain of the small gain cycle of Theorem 18; it closes the cycle back to the optimality error $\mathbf q$.
--
--   **Formalization Note** As on the page, Assumption 6 is not assumed. Assumption 7 includes the disclosed self-weight, which makes $C(k)$ column stochastic so that $\sum_iv_i(k)=n$. $\bar{\mathbf x}(0)$ is the row average of $\mathbf x(0)$ (equal to $\bar{\mathbf u}(0)$ since $\mathbf u(0)=\mathbf x(0)$).
-- source:
--   arXiv:1607.03218v3, Lemma 17 and (58), p. 24

import Mathlib
import Definitions.Def_DIGing_Undir_Common
import Definitions.Def_DIGing_Push_Setting

namespace DIGing.Push

theorem lemma_17 {n p : ℕ} (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ) (Lc mu : Fin n → ℝ)
    (h4 : DIGing.Undir.Assumption4 f Lc) (h5 : DIGing.Undir.Assumption5 f mu)
    (xstar : EuclideanSpace ℝ (Fin p)) (hopt : ∀ z, DIGing.Undir.objective f xstar ≤ DIGing.Undir.objective f z)
    (A : ℕ → Finset (Fin n × Fin n)) (C : ℕ → Matrix (Fin n) (Fin n) ℝ) (h7 : Assumption7 A C)
    (α : ℝ) (hα : 0 < α) (u x y : ℕ → DIGing.Undir.Stack n p) (hrun : IsPushDIGingRun f C α u x y)
    (β η lam : ℝ) (hβ : 0 < β) (hη : 0 < η)
    (hlam : Real.sqrt (1 - α * DIGing.Undir.mubar mu * β / (β + 1)) ≤ lam) (hlam1 : lam < 1)
    (hαL : α ≤ 1 / ((1 + η) * DIGing.Undir.Lbar Lc)) :
    ∀ K : ℕ, DIGing.Undir.ergK lam K (fun k => DIGing.Undir.frob (x k - DIGing.Undir.ones xstar)) ≤
      (1 + Real.sqrt n) * (1 + Real.sqrt n / lam *
          Real.sqrt (DIGing.Undir.Lmax Lc * (1 + η) / (DIGing.Undir.mubar mu * η) + DIGing.Undir.muhat mu / DIGing.Undir.mubar mu * β)) *
          DIGing.Undir.ergK lam K (fun k => DIGing.Undir.frob (DIGing.Undir.cons (x k))) +
        2 * Real.sqrt n * ‖DIGing.Undir.avg (x 0) - xstar‖ := by sorry

end DIGing.Push
