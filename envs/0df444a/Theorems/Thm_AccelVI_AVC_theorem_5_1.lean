-- Prove2me | Theorems.Thm_AccelVI_AVC_theorem_5_1
-- name    : AccelVI.AVC.theorem_5_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:03:21.219737+00:00
-- url     : https://prove2.me/theorems/a77f29f9-2b60-42fe-a171-bb4edfb5eddc
-- title:
--   Theorem 5.1, p. 8 — for a reversible policy chain, A-VC converges to v^π with v_s = v^π + o((1 − √(1/κ) + η)^s) for every η > 0
-- statement:
--   Let $(\mathbb S,\mathbb A,P,r,\lambda)$ be a finite MDP with discount $\lambda\in(0,1)$ and let $\pi$ be a policy whose transition matrix $L_\pi$, $L_{\pi,ij}=\sum_a\pi_{ia}P_{iaj}$, defines an irreducible, reversible Markov chain (Definition 2.1). Let $v^\pi$ be the value function of $\pi$, and let $(v_s)_{s\ge0}$ be the iterates of Accelerated Value Computation
--   $$h_s=v_s+\gamma(v_s-v_{s-1}),\qquad v_{s+1}=h_s-\alpha\big(h_s-T_\pi(h_s)\big)\quad(s\ge1),$$
--   with arbitrary $v_0,v_1\in\mathbb R^n$, $T_\pi(v)=r_\pi+\lambda L_\pi v$, and the step sizes (4.1): $\alpha=1/(1+\lambda)$, $\gamma=(1-\sqrt{1-\lambda^2})/\lambda$. Put $\kappa=(1+\lambda)/(1-\lambda)$. Then:
--
--   1. $(v_s)_{s\ge0}$ converges to $v^\pi$;
--   2. for every $\eta>0$,
--   $$v_s=v^\pi+o\Big(\big(1-\sqrt{1/\kappa}+\eta\big)^s\Big)\qquad(s\to\infty);$$
--   3. $0<1-\sqrt{1/\kappa}<\lambda$.
--
--   Plain value computation $v_{s+1}=T_\pi(v_s)$ converges at rate $\lambda$; since $1-\sqrt{1/\kappa}=1-\sqrt{(1-\lambda)/(1+\lambda)}$, the accelerated rate is of order $1-\sqrt{1-\lambda}$, which is the source of the $1/\sqrt{1-\lambda}$ iteration count in the paper.
--
--   **Formalization Note.** The error is measured in the sup norm $\|\cdot\|_\infty$ on $\mathbb R^n$; $o(\cdot)$ is the little-o of Mathlib along $s\to\infty$. $v^\pi$ is the discounted reward series $\sum_t\lambda^tL_\pi^tr_\pi$ (the published `PolicyValue`). Reversibility means irreducibility together with a stationary probability vector $\nu$ in detailed balance. The printed statement places $\eta$ under the square root, $o\big((1-\sqrt{1/\kappa+\eta})^s\big)$, which is false: on a one-state chain the error is of exact order $s\,(1-\sqrt{1/\kappa})^s$, and this is not $o\big((1-\sqrt{1/\kappa+\eta})^s\big)$ because $1-\sqrt{1/\kappa+\eta}<1-\sqrt{1/\kappa}$; the posed statement uses the rate $(1-\sqrt{1/\kappa}+\eta)^s$ that the paper's proof concludes on p. 9. The initial-state distribution $p_0$ plays no role and is omitted.
-- source:
--   Goyal & Grand-Clément, A First-Order Approach to Accelerated Value Iteration, arXiv:1905.09963v7, p. 8, Theorem 5.1; proof p. 9 (rate as in its conclusion)

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_AccelVI_AVC_Setting

namespace AccelVI.AVC

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]

/-- Theorem 5.1, p. 8 (rate as concluded in its proof, p. 9): for a policy whose chain is
irreducible and reversible, the A-VC iterates with step sizes (4.1) converge to `v^π`, satisfy
`v_s = v^π + o((1 − √(1/κ) + η)^s)` for every `η > 0`, and `0 < 1 − √(1/κ) < λ`. -/
theorem theorem_5_1 (M : MDP S A) (hM : M.Valid) (pol : S → A → ℝ) (hpol : FoundationsML.ReinforcementLearning.IsPolicy pol)
    (hrev : IsReversible (LPol M pol)) (v0 v1 : S → ℝ) :
    Filter.Tendsto (avc M pol (alphaAVC M.lam) (gammaAVC M.lam) v0 v1) Filter.atTop
        (nhds (valuePol M pol)) ∧
    (∀ η : ℝ, 0 < η →
      (fun s => avc M pol (alphaAVC M.lam) (gammaAVC M.lam) v0 v1 s - valuePol M pol)
        =o[Filter.atTop] (fun s => (theta M.lam + η) ^ s)) ∧
    0 < theta M.lam ∧ theta M.lam < M.lam := by sorry

end AccelVI.AVC
