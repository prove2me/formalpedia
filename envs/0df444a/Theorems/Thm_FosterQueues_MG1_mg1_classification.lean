-- Prove2me | Theorems.Thm_FosterQueues_MG1_mg1_classification
-- name    : FosterQueues.MG1.mg1_classification
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:20:48.450126+00:00
-- url     : https://prove2.me/theorems/b1324630-fd8e-4234-9c76-660df170a792
-- title:
--   §3 — the M/G/1 imbedded chain is ergodic iff ρ < 1 and recurrent iff ρ ≤ 1
-- statement:
--   Let $k_0,k_1,k_2,\dots$ be positive numbers with $\sum_{n=0}^{\infty}k_n=1$, and let $P$ be the Markov chain on $\{0,1,2,\dots\}$ with the M/G/1 transition matrix
--   $$
--   [p_{ij}] = \begin{bmatrix} k_0 & k_1 & k_2 & \cdots \\ k_0 & k_1 & k_2 & \cdots \\ 0 & k_0 & k_1 & \cdots \\ 0 & 0 & k_0 & \cdots \\ \vdots & \vdots & \vdots & \end{bmatrix}.
--   $$
--   Let $\rho=\sum_{n=1}^{\infty}n k_n\in[0,\infty]$. Then
--
--   1. the system is ergodic (positive recurrent) if and only if $\rho<1$, and
--   2. the system is recurrent if and only if $\rho\le1$.
--
--   Consequently the chain is positive recurrent for $\rho<1$, null recurrent for $\rho=1$, and transient for $\rho>1$ (including $\rho=\infty$). The chain is the queue length of the M/G/1 queue observed at departure epochs, with $k_n$ the probability of $n$ arrivals during one service.
--
--   **Formalization Note** $\sum_n k_n=1$ is not written in §3 but is what "stochastic matrix" means for row $0$. The traffic intensity $\rho$ is an extended nonnegative real, so a divergent $\sum nk_n$ gives $\rho=\infty$, and then both equivalences say the chain is neither ergodic nor recurrent. Irreducibility and aperiodicity are not assumed: they follow from $k_i>0$. The theorem is stated for every transition matrix $P$ whose entries are the M/G/1 entries.
-- source:
--   Foster (Ann. Math. Statist. 24, 1953), §3, p. 358

import Mathlib
import Definitions.Def_FosterQueues_MG1_Model

open scoped ENNReal
open QueueingFundamentals.Foundations

namespace FosterQueues.MG1

/-- Foster (1953), §3, p. 358: for the M/G/1 matrix with `k_i > 0` for all `i` and
`∑ k_i = 1`, the system is ergodic (positive recurrent) if and only if `ρ < 1`, and recurrent
if and only if `ρ ≤ 1`, where `ρ = ∑_{n ≥ 1} n k_n ∈ [0, ∞]`. -/
theorem mg1_classification (k : ℕ → ℝ) (hk : ∀ i, 0 < k i) (hsum : HasSum k 1)
    (P : TransitionMatrix) (hP : P.p = mg1Matrix k) :
    (P.PositiveRecurrent ↔ rho k < 1) ∧ (IsRecurrent P ↔ rho k ≤ 1) := by sorry

end FosterQueues.MG1
