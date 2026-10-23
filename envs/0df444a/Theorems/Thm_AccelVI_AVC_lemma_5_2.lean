-- Prove2me | Theorems.Thm_AccelVI_AVC_lemma_5_2
-- name    : AccelVI.AVC.lemma_5_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:03:03.257534+00:00
-- url     : https://prove2.me/theorems/1e7ae55b-cabd-4fcd-abd8-ebc8d956bdb1
-- title:
--   Lemma 5.2, p. 8 — x_s = x^π + B_π^{s−1}(x_1 − x^π) for all s ≥ 1
-- statement:
--   Let $(\mathbb S,\mathbb A,P,r,\lambda)$ be a finite MDP with $\lambda\in(0,1)$ and let $\pi$ be a policy, with reward vector $r_\pi$, transition matrix $L_\pi$ and value function $v^\pi$. Let $(v_s)_{s\ge0}$ be the iterates of Accelerated Value Computation with the step sizes (4.1), $\alpha=1/(1+\lambda)$ and $\gamma=(1-\sqrt{1-\lambda^2})/\lambda$, started from arbitrary $v_0,v_1\in\mathbb R^n$. Put $x^\pi=(v^\pi,v^\pi)\in\mathbb R^{2n}$ and $x_s=(v_s,v_{s-1})\in\mathbb R^{2n}$, and let $B_\pi$ be the matrix (5.1). Then
--   $$x_s=x^\pi+B_\pi^{\,s-1}\,(x_1-x^\pi)\qquad\text{for every } s\ge1.$$
--
--   The lemma turns the analysis of A-VC into that of the powers of a single $2n\times 2n$ matrix. It holds for every policy; reversibility is not needed.
--
--   **Formalization Note.** $x_s$ is the function on $\mathbb S\sqcup\mathbb S$ equal to $v_s$ on the first copy and $v_{s-1}$ on the second; the hypothesis $s\ge1$ keeps $v_{s-1}$ meaningful. $v^\pi$ is the discounted reward series $\sum_t\lambda^tL_\pi^tr_\pi$ (the published `PolicyValue`). The paper's proof ends with "$(x_0-x^\pi)$", a slip; the statement, with $x_1$, is the one posed.
-- source:
--   Goyal & Grand-Clément, A First-Order Approach to Accelerated Value Iteration, arXiv:1905.09963v7, p. 8, Lemma 5.2

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_AccelVI_AVC_Setting

namespace AccelVI.AVC

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]

/-- Lemma 5.2, p. 8: with `x^π = (v^π, v^π)` and `x_s = (v_s, v_{s−1})`, the A-VC iterates with
step sizes (4.1) satisfy `x_s = x^π + B_π^{s−1}(x_1 − x^π)` for every `s ≥ 1`. -/
theorem lemma_5_2 (M : MDP S A) (hM : M.Valid) (pol : S → A → ℝ) (hpol : FoundationsML.ReinforcementLearning.IsPolicy pol)
    (v0 v1 : S → ℝ) (s : ℕ) (hs : 1 ≤ s) :
    xvec (avc M pol (alphaAVC M.lam) (gammaAVC M.lam) v0 v1) s =
      xPi M pol + ((Bpol M pol) ^ (s - 1)).mulVec
        (xvec (avc M pol (alphaAVC M.lam) (gammaAVC M.lam) v0 v1) 1 - xPi M pol) := by sorry

end AccelVI.AVC
