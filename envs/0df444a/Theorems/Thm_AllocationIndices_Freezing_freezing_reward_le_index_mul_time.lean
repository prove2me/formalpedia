-- Prove2me | Theorems.Thm_AllocationIndices_Freezing_freezing_reward_le_index_mul_time
-- name    : AllocationIndices.Freezing.freezing_reward_le_index_mul_time
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:38:26.285987+00:00
-- url     : https://prove2.me/theorems/fe5172ac-3f75-4ffe-8c14-fb685000b7be
-- title:
--   Eq. (4.8) — postponing rewards by a freezing rule: $R_f(B) \le W_f(B)\,\nu(B)$
-- statement:
--   Let $B$ be a bandit process on a countable state space $S$ with transition kernel $P$ and bounded reward $r$, and let $0 < a < 1$ be the discount factor. Let $f$ be a freezing rule for $B$: a nondecreasing sequence $f_0 \le f_1 \le \cdots$ of times in $\{0, 1, 2, \dots\} \cup \{\infty\}$, where $f_i$ depends only on the history $x(0), \dots, x(i)$ of $B$ and the reward $r(x(i))$ of process time $i$ is postponed to time $i + f_i$. Then, for every initial state $x$,
--   $$R_f(B, x) = E\sum_{i=0}^{\infty} a^{i + f_i}\, r(x(i)) \;\le\; W_f(B, x)\,\nu(B, x), \qquad W_f(B, x) = E\sum_{i=0}^{\infty} a^{i + f_i},$$
--   where $\nu(B, x)$ is the Gittins index of $B$ in state $x$ and $a^\infty = 0$.
--
--   In words: inserting periods of freeze control, at times that may depend on the past of $B$, cannot raise the reward rate earned by $B$ above its index. This is the inequality by which the book compares the rewards of the first stage of an index policy with the same rewards taken later by an arbitrary policy, in its proof of the index theorem by freezing and promotion rules.
--
--   **Formalization Note** Time is discrete, so the book's $W_{f}(B) = E\sum_i a^{f_i}\int_{t_i}^{t_{i+1}} a^t\,dt$ becomes $E\sum_i a^{i + f_i}$ (one unit of process time per decision time), and $\nu$ is the discrete-time index (2.6). The book's "past-measurable nondecreasing sequence of non-negative $f'_0, f'_1, \dots$" is a `FreezingRule`: deterministic functions of the trajectory of $B$ (the book's definition of a freezing rule on p. 93); randomized sequences are not covered by this statement. The countable state space and bounded reward are the standing assumptions of §2.4.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §4.5 p. 91, Eq. (4.8)

import Definitions.Def_AllocationIndices_Freezing_Model

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace AllocationIndices.Freezing

theorem freezing_reward_le_index_mul_time {S : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ}
    (hr : BoundedReward r) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (f : FreezingRule S) (x : S) :
    freezingReward P r a f x ≤ freezingTime P a f x * gittinsIndex P r a x := by sorry

end AllocationIndices.Freezing
