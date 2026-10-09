-- Prove2me | Theorems.Thm_DIGing_Push_lemma_16
-- name    : DIGing.Push.lemma_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T10:58:06.464084+00:00
-- url     : https://prove2.me/theorems/cc98d049-30c4-43a7-a9a0-9aa4c525b486
-- title:
--   Lemma 16, p. 24 — third arrow ȟ → x̌, the bound (56)
-- statement:
--   Let $n\ge2$, let Assumptions 6 and 7 hold, and let $B\ge B_\ominus$ with $\delta<1$ be as in Lemma 13; let $Q_1$ be as in (50). Let $\lambda>0$ satisfy $\delta<\lambda^B<1$. Let $(\mathbf u,\mathbf x,\mathbf y)$ be a run of Push-DIGing with step size $\alpha>0$, $\mathbf h(k)=V(k)^{-1}\mathbf y(k)$, and write $\check{\mathbf x}$, $\check{\mathbf h}$ for the consensus violations. Then for all $K=0,1,\dots$
--   $$\|\check{\mathbf x}\|_F^{\lambda,K}\le\frac{\alpha}{\lambda^B-\delta}\Big(\delta+Q_1\frac{1-\lambda^{B-1}}{1-\lambda}\Big)\|\check{\mathbf h}\|_F^{\lambda,K}+\frac{\lambda^B}{\lambda^B-\delta}\sum_{t=1}^{B}\lambda^{1-t}\|\check{\mathbf x}(t-1)\|_F.$$
--
--   This is the third gain of the small gain cycle of Theorem 18.
--
--   **Formalization Note** $\lambda^{1-t}\|\check{\mathbf x}(t-1)\|_F$ is written $\|\check{\mathbf x}(t-1)\|_F/\lambda^{t-1}$; $\lambda^{B-1}$ is a natural power with $B\ge1$. The condition $\lambda>0$ is added as in Lemma 15. $n\ge2$ and the self-weight of Assumption 7 are the disclosed additions of Lemma 13.
-- source:
--   arXiv:1607.03218v3, Lemma 16 and (56), p. 24

import Mathlib
import Definitions.Def_DIGing_Undir_Common
import Definitions.Def_DIGing_Push_Setting

namespace DIGing.Push

theorem lemma_16 {n p : ℕ} (hn : 2 ≤ n) (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ)
    (A : ℕ → Finset (Fin n × Fin n)) (Bt : ℕ) (h6 : Assumption6 A Bt)
    (C : ℕ → Matrix (Fin n) (Fin n) ℝ) (h7 : Assumption7 A C)
    (B : ℕ) (hB : 2 * Bt - 1 ≤ B) (hδ : deltaPush n (2 * Bt - 1) B < 1)
    (lam : ℝ) (h0 : 0 < lam) (hlam : deltaPush n (2 * Bt - 1) B < lam ^ B)
    (hlam1 : lam ^ B < 1)
    (α : ℝ) (hα : 0 < α) (u x y : ℕ → DIGing.Undir.Stack n p) (hrun : IsPushDIGingRun f C α u x y) :
    ∀ K : ℕ, DIGing.Undir.ergK lam K (fun k => DIGing.Undir.frob (DIGing.Undir.cons (x k))) ≤
      α / (lam ^ B - deltaPush n (2 * Bt - 1) B) *
          (deltaPush n (2 * Bt - 1) B + Q1 n (2 * Bt - 1) * (1 - lam ^ (B - 1)) / (1 - lam)) *
          DIGing.Undir.ergK lam K (fun k => DIGing.Undir.frob (DIGing.Undir.cons (hSeq C y k))) +
        lam ^ B / (lam ^ B - deltaPush n (2 * Bt - 1) B) *
          ∑ t ∈ Finset.Icc 1 B, DIGing.Undir.frob (DIGing.Undir.cons (x (t - 1))) / lam ^ (t - 1) := by sorry

end DIGing.Push
