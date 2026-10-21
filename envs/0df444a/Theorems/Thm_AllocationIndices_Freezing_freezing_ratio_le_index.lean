-- Prove2me | Theorems.Thm_AllocationIndices_Freezing_freezing_ratio_le_index
-- name    : AllocationIndices.Freezing.freezing_ratio_le_index
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:38:33.398884+00:00
-- url     : https://prove2.me/theorems/eddf195d-39c5-4122-a3d2-1bad049b1bed
-- title:
--   Lemma 4.5 — a freezing rule cannot beat the Gittins index: $\nu_f(B) \le \nu(B)$
-- statement:
--   Let $B$ be a bandit process on a countable state space $S$ with transition kernel $P$ and bounded reward $r$, let $0 < a < 1$, and let $f$ be a freezing rule for $B$ (a nondecreasing sequence $f_0 \le f_1 \le \cdots$ in $\{0,1,2,\dots\}\cup\{\infty\}$, with $f_i$ depending only on $x(0), \dots, x(i)$; the reward of process time $i$ accrues at time $i + f_i$). Let $x$ be an initial state for which $W_f(B, x) > 0$, i.e. for which $\nu_f(B, x)$ is defined. Then
--   $$\nu_f(B, x) = \frac{R_f(B, x)}{W_f(B, x)} \le \nu(B, x),$$
--   with $R_f(B, x) = E\sum_{i} a^{i+f_i} r(x(i))$, $W_f(B, x) = E\sum_i a^{i+f_i}$ and $\nu(B, x)$ the Gittins index.
--
--   A stopping time $\tau$ is the special freezing rule $f_i = 0$ for $i < \tau$ and $f_i = \infty$ otherwise, so freezing rules form a larger class than stopping rules; the lemma says that the supremum of the reward rate over the larger class is still the Gittins index. The book uses it to show that the index of a family of bandit processes is the largest of their indices (Lemma 4.6).
--
--   **Formalization Note** Time is discrete and $\nu$ is the discrete-time index (2.6). The hypothesis $W_f(B, x) > 0$ is where the book's $\nu_f(B)$ is defined (it fails exactly when $f_0 = \infty$, the hypothesis that the book adds in the proof of Theorem 4.8); without it Lean's division by zero would give $\nu_f = 0$. Freezing rules are deterministic functions of the trajectory of $B$, as on p. 93.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §4.5.1 p. 93, Lemma 4.5

import Definitions.Def_AllocationIndices_Freezing_Model

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace AllocationIndices.Freezing

theorem freezing_ratio_le_index {S : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] (P : Kernel S S) [IsMarkovKernel P] {r : S → ℝ}
    (hr : BoundedReward r) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (f : FreezingRule S) (x : S)
    (hW : 0 < freezingTime P a f x) :
    freezingRatio P r a f x ≤ gittinsIndex P r a x := by sorry

end AllocationIndices.Freezing
