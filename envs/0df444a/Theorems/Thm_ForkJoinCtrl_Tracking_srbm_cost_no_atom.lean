-- Prove2me | Theorems.Thm_ForkJoinCtrl_Tracking_srbm_cost_no_atom
-- name    : ForkJoinCtrl.Tracking.srbm_cost_no_atom
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-31T12:23:15.0415+00:00
-- url     : https://prove2.me/theorems/99019919-f98e-4c3f-9187-972523fec84d
-- title:
--   Continuity-point condition used in Theorem 2 (App. B.2) — $\mathbf P(z(\tilde Q(t),\tilde W(t))=\varepsilon)=0$ for the SRBM limit
-- statement:
--   Let $Z$ be a semimartingale reflected Brownian motion with data $(\mathbb R^{a_1}_+,\Theta,\Sigma,R,0)$ as in Proposition 2 of the paper, with positive definite covariance matrix $\Sigma$. Let $(\tilde Q_k(t),\tilde W_i(t))$ be the limit vector read off $Z$ at time $t$ (with $\tilde Q_k\equiv0$ for light-traffic dedicated servers), and let $z$ be the optimal value of the LP (18). Then for every $\varepsilon>0$ and $t\ge0$ the level $\varepsilon$ is not an atom of the law of the limiting cost:
--   $$\mathbf P\Big(z\big(\tilde Q_k(t),k\in\mathcal K;\ \tilde W_i(t),i\in\mathcal I\big)=\varepsilon\Big)=0 .$$
--
--   **Role in the paper.** In the proof of Theorem 2 (Appendix B.2), the weak convergence $(32)$ $\sum_j h_j\hat N^r_j\Rightarrow z(\tilde Q,\tilde W)$ is turned into the limit of the probabilities $\mathbf P(\sum_j h_j\hat N^r_j(t)>\varepsilon)$ for **every** $\varepsilon>0$. This step is valid exactly when $\varepsilon$ is a continuity point of the law of $z(\tilde Q(t),\tilde W(t))$, which the paper uses implicitly. For $t=0$ the claim is immediate, since $Z(0)=0$ and $z(0)=0<\varepsilon$. For $t>0$ it follows from absolute continuity of the law of the reflected Brownian motion at a fixed time (non-degenerate $\Sigma$), together with the fact that $z$ is a nonnegative, convex, positively homogeneous piecewise-linear function, so its level set $\{z=\varepsilon\}$ is Lebesgue-null.
--
--   The probability is a (possibly outer) measure in $[0,\infty]$; the statement asserts it is $0$.
-- source:
--   Özkan, Control of Fork-Join Processing Networks with Multiple Job Types and Parallel Shared Resources, arXiv:2002.01496v1, Appendix B.2 (p. 20), proof of Theorem 2: the final step "Theorem 2 follows from (32)" requires ε to be a continuity point of the law of z(Q̃(t), W̃(t)); SRBM data from §3.2 (p. 10), Proposition 2, and Σ positive definite as asserted on p. 10.

import Mathlib
import Definitions.Def_ForkJoinCtrl_Tracking_LP
import Definitions.Def_ForkJoinCtrl_Tracking_SRBM

open MeasureTheory

namespace ForkJoinCtrl.Tracking

theorem srbm_cost_no_atom {N : Network} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (M : Model N Ω P) (hSigma : M.Sigma.PosDef)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') (Z : Ω' → ℝ → Fin M.a1 → ℝ)
    (hZ : IsSRBM P' M.Theta M.Sigma Z) (ε : ℝ) (hε : 0 < ε) (t : ℝ) (ht : 0 ≤ t) :
    P' {ω' | z N (M.limitVec Z ω' t) = ε} = 0 := by sorry

end ForkJoinCtrl.Tracking
