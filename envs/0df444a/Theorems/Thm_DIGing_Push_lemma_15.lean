-- Prove2me | Theorems.Thm_DIGing_Push_lemma_15
-- name    : DIGing.Push.lemma_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:58:01.485931+00:00
-- url     : https://prove2.me/theorems/dfcd4fcb-a699-456e-a8da-31c695b3745c
-- title:
--   Lemma 15, p. 24 — second arrow z → ȟ, the bound (53)
-- statement:
--   Let $n\ge2$, let Assumptions 6 and 7 hold, and let $B\ge B_\ominus$ with $\delta<1$ be as in Lemma 13. Let $\|V^{-1}\|^1_{\max}$ be the least upper bound of $\{1/v_i(k)\}$, and let $Q_1$ be as in (50). Let $\lambda>0$ satisfy $\delta<\lambda^B<1$. Let $(\mathbf u,\mathbf x,\mathbf y)$ be a run of Push-DIGing with any step size, $\mathbf h(k)=V(k)^{-1}\mathbf y(k)$, $\check{\mathbf h}(k)=(I-\frac1n\mathbf 1\mathbf 1^\top)\mathbf h(k)$, and $\mathbf z$ the gradient increments. Then for all $K=0,1,\dots$
--   $$\|\check{\mathbf h}\|_F^{\lambda,K}\le\frac{Q_1\|V^{-1}\|^1_{\max}\,\lambda(1-\lambda^B)}{(\lambda^B-\delta)(1-\lambda)}\,\|\mathbf z\|_F^{\lambda,K}+\frac{\lambda^B}{\lambda^B-\delta}\sum_{t=1}^{B}\lambda^{1-t}\|\check{\mathbf h}(t-1)\|_F.$$
--
--   This is the second gain of the small gain cycle of Theorem 18.
--
--   **Formalization Note** $\lambda^{1-t}\|\check{\mathbf h}(t-1)\|_F$ is written $\|\check{\mathbf h}(t-1)\|_F/\lambda^{t-1}$. The condition $\lambda>0$ is added: it is the standing range $\lambda\in(0,1)$ of the ergodic norm (p. 9), and for even $B$ the page's hypothesis $\delta<\lambda^B<1$ would also admit negative $\lambda$. $n\ge2$ and the self-weight of Assumption 7 are the disclosed additions of Lemma 13.
-- source:
--   arXiv:1607.03218v3, Lemma 15 and (53), p. 24

import Mathlib
import Definitions.Def_DIGing_Undir_Common
import Definitions.Def_DIGing_Push_Setting

namespace DIGing.Push

theorem lemma_15 {n p : ℕ} (hn : 2 ≤ n) (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (A : ℕ → Finset (Fin n × Fin n)) (Bt : ℕ) (h6 : Assumption6 A Bt)
    (C : ℕ → Matrix (Fin n) (Fin n) ℝ) (h7 : Assumption7 A C)
    (B : ℕ) (hB : 2 * Bt - 1 ≤ B) (hδ : deltaPush n (2 * Bt - 1) B < 1)
    (Vmax : ℝ) (hV : IsLUB {r | ∃ k i, r = (vSeq C k i)⁻¹} Vmax)
    (lam : ℝ) (h0 : 0 < lam) (hlam : deltaPush n (2 * Bt - 1) B < lam ^ B)
    (hlam1 : lam ^ B < 1)
    (α : ℝ) (u x y : ℕ → DIGing.Undir.Stack n p) (hrun : IsPushDIGingRun f C α u x y) :
    ∀ K : ℕ, DIGing.Undir.ergK lam K (fun k => DIGing.Undir.frob (DIGing.Undir.cons (hSeq C y k))) ≤
      Q1 n (2 * Bt - 1) * Vmax * lam * (1 - lam ^ B) /
          ((lam ^ B - deltaPush n (2 * Bt - 1) B) * (1 - lam)) *
          DIGing.Undir.ergK lam K (fun k => DIGing.Undir.frob (DIGing.Undir.zSeq f x k)) +
        lam ^ B / (lam ^ B - deltaPush n (2 * Bt - 1) B) *
          ∑ t ∈ Finset.Icc 1 B, DIGing.Undir.frob (DIGing.Undir.cons (hSeq C y (t - 1))) / lam ^ (t - 1) := by sorry

end DIGing.Push
