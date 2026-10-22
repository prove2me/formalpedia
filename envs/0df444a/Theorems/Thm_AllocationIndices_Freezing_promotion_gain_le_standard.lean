-- Prove2me | Theorems.Thm_AllocationIndices_Freezing_promotion_gain_le_standard
-- name    : AllocationIndices.Freezing.promotion_gain_le_standard
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:38:26.531409+00:00
-- url     : https://prove2.me/theorems/e2e857c9-1ebc-488e-8e59-985951a29dc4
-- title:
--   Lemma 4.7 — promoting rewards gains no more than for a standard bandit with parameter $\nu(B)$
-- statement:
--   Let $B$ be a bandit process on a countable state space $S$ with transition kernel $P$, bounded reward $r$ and discount factor $0 < a < 1$, started in state $x$, and let $\tau \in \{0, 1, 2, \dots\}$ be a fixed (non-random) time. Under the null promotion rule all rewards of $B$ are taken from time $\tau$ on: the reward of process time $i$ accrues at time $\tau + i$. A promotion rule $p$ with respect to $\tau$ takes the reward of process time $i$ at time $\tau + i + p_i$ instead, where $-\tau \le p_0 \le p_1 \le \cdots \le 0$ and $p_i$ depends only on the history of $B$ up to process time $i$; equivalently, rewards accrue as under the freezing rule $f_i = \tau + p_i$, which is a freezing rule with $0 \le f_i \le \tau$. Write $R(B, x) = E\sum_{t \ge 0} a^t r(x(t))$ and $W(B, x) = \sum_{t \ge 0} a^t$ for the total discounted reward and time without freezing, and $R_f$, $W_f$ as for freezing rules. Then
--   $$R_f(B, x) - a^\tau R(B, x) \;\le\; \nu(B, x)\,\big[W_f(B, x) - a^\tau W(B, x)\big],$$
--   the form (4.13) of the lemma: the increase in the expected total reward caused by applying the promotion rule $p$ instead of the null promotion rule is at most the corresponding increase for a standard bandit process with parameter $\nu(B, x)$, i.e. one that pays $\nu(B, x)$ per unit time.
--
--   In the proof of the index theorem by freezing and promotion rules this controls the rewards of the bandits other than the one of greatest index, which an arbitrary policy may take before the first stage of the index policy has ended.
--
--   **Formalization Note** Time is discrete and $\nu$ is the discrete-time index (2.6). The promotion rule is encoded by the freezing rule $f_i = \tau + p_i$, as in the book's proof: a `FreezingRule` with every $f_i \le \tau$ (nonnegativity of $f_i$ is the book's $-\tau \le p_i$, monotonicity is $p_i \le p_{i+1}$, and $f_i \le \tau$ is $p_i \le 0$). $R(B, x)$ and $W(B, x)$ are the published `stoppedReward` and `stoppedTime` at the stopping time $\tau \equiv \infty$. The book indexes the promoted rewards from $p_1$; here process times start at $0$.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §4.5.2 p. 95, Lemma 4.7 and Eq. (4.13)

import Definitions.Def_AllocationIndices_Freezing_Model

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace AllocationIndices.Freezing

theorem promotion_gain_le_standard {S : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ}
    (hr : BoundedReward r) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (τ : ℕ) (f : FreezingRule S)
    (hf : ∀ i ω, f.freeze i ω ≤ (τ : ℕ∞)) (x : S) :
    freezingReward P r a f x - a ^ τ * stoppedReward P r a (fun _ ↦ ⊤) x ≤
      gittinsIndex P r a x *
        (freezingTime P a f x - a ^ τ * stoppedTime P a (fun _ ↦ ⊤) x) := by sorry

end AllocationIndices.Freezing
