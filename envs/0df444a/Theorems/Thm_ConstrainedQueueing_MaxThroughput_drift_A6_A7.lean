-- Prove2me | Theorems.Thm_ConstrainedQueueing_MaxThroughput_drift_A6_A7
-- name    : ConstrainedQueueing.MaxThroughput.drift_A6_A7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:49:04.664239+00:00
-- url     : https://prove2.me/theorems/647e3415-6f05-422e-b941-fbfef69c64ef
-- title:
--   Proof of Lemma 3.2, (A.6)–(A.7), p. 1945 — quadratic drift under π₀ is < −ε for V(x) ≥ b and finite everywhere
-- statement:
--   Consider a constrained queueing network satisfying C.1 and C.2, with $\emptyset\in S$, every single server forming an activation set, and service probabilities $0<m_i\le 1$. Let $g$ be an activation rule of policy $\pi_0$, and let the arrivals have an admissible law (finite second moments) whose rate vector $a$ lies in $C'$. Let
--   $$V(x)=\sum_{l=1}^{L}\sum_{j=1}^{J}x_{lj}^2$$
--   (the sum over the queues $(l,j)$, $l\notin V_j$), and let $\epsilon>0$.
--
--   **Claim (A.6)–(A.7).** There is a number $b>0$ such that, for the queue-length chain $X$ under $g$,
--   $$E[V(X(t+1))-V(X(t))\mid X(t)=x]<-\epsilon\quad\text{if } V(x)\ge b,\qquad(A.6)$$
--   and $E[V(X(t+1))\mid X(t)=x]<\infty$ for every state $x$ (A.7).
--
--   The paper's witness is $b=JL\bigl(L(\epsilon+b_1+N^2)/(2(1-\sum_i\lambda_i)\min_i m_i)\bigr)^2$, with $b_1$ the constant of (A.10) and $\lambda_i$ the coefficients of the decomposition (A.15). Together with Theorem 3.1 this yields Lemma 3.2.
--
--   **Formalization Note.** The conditional expectation is the series $\sum_y P_{g,\alpha}(x,y)V(y)$; (A.7) is stated as its summability. The page writes "if $a\in C$"; it means $C'$, as the proof uses the strict inequalities of $C'$. The hypothesis that every singleton $\{i\}$ is an activation set is used at (A.24) without being stated; without it the claim fails (a server that can never be activated cannot drain its queue).
-- source:
--   Tassiulas and Ephremides, Stability properties of constrained queueing systems and scheduling policies for maximum throughput in multihop radio networks, IEEE Trans. Automat. Control 37(12) (1992), p. 1945, proof of Lemma 3.2, (A.6)–(A.7); b on p. 1947

import Mathlib
import Definitions.Def_ConstrainedQueueing_MaxThroughput_MarkovChain
import Definitions.Def_ConstrainedQueueing_MaxThroughput_Model

namespace ConstrainedQueueing.MaxThroughput

/-- (A.6)–(A.7), proof of Lemma 3.2 (p. 1945): for `V(x) = ∑_{(l,j)} x_{lj}^2`, under a `π₀` rule and
an admissible arrival law with mean in `C′`, the one-step drift is finite everywhere and is
`< -ε` wherever `V(x) ≥ b`, for some `b > 0`. -/
theorem drift_A6_A7 {L N J : ℕ} (net : Network L N J) (hC1 : C1 net)
    (hempty : (∅ : Finset (Fin N)) ∈ net.S) (hsingle : ∀ i : Fin N, ({i} : Finset (Fin N)) ∈ net.S)
    (hm : ∀ i, 0 < net.m i ∧ net.m i ≤ 1) (hC2 : C2 net)
    (g : (QIdx net → ℕ) → MultiAct N J) (hg : IsPi0Rule net g)
    (α : ArrivalLaw net) (hα : Admissible α) (ha : meanRate α ∈ Cprime net)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ b : ℝ, 0 < b ∧
      (∀ x : QIdx net → ℕ,
        Summable (fun y => (transProb net g α x y).toReal * ∑ p, ((y p : ℝ)) ^ 2)) ∧
      ∀ x : QIdx net → ℕ, b ≤ ∑ p, ((x p : ℝ)) ^ 2 →
        (∑' y, (transProb net g α x y).toReal * ∑ p, ((y p : ℝ)) ^ 2)
          - ∑ p, ((x p : ℝ)) ^ 2 < -ε := by sorry

end ConstrainedQueueing.MaxThroughput
