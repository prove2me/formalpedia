-- Prove2me | Theorems.Thm_FosterQueues_GIM1_gim1_classification
-- name    : FosterQueues.GIM1.gim1_classification
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T04:58:52.656679+00:00
-- url     : https://prove2.me/theorems/930f9d64-b24c-4321-a08d-1575ec90438b
-- title:
--   §4 — the GI/M/1 imbedded chain is ergodic iff ρ < 1 and recurrent iff ρ ≤ 1
-- statement:
--   Let $(a_n)_{n \ge 0}$ be a sequence of positive numbers with $\sum_{n} a_n = 1$, put $\alpha_i = \sum_{j \ge i+1} a_j$, and consider the Markov chain on $\{0, 1, 2, \dots\}$ with transition matrix
--   $$
--   [p_{ij}] = \begin{bmatrix} \alpha_0 & a_0 & 0 & 0 & \cdots \\ \alpha_1 & a_1 & a_0 & 0 & \cdots \\ \alpha_2 & a_2 & a_1 & a_0 & \cdots \\ \vdots & \vdots & \vdots & \vdots & \end{bmatrix},
--   $$
--   the chain imbedded at arrival epochs in the queueing system GI/M/1. Define $\rho$ by
--   $$
--   \rho^{-1} = \sum_{n=1}^{\infty} n\, a_n \in (0, \infty],
--   $$
--   so that $\rho = 0$ when the mean is infinite. Then
--
--   1. the chain is ergodic (positive recurrent) if and only if $\rho < 1$;
--   2. the chain is recurrent (every state is visited again with probability one) if and only if $\rho \le 1$.
--
--   Equivalently, the chain is ergodic iff $\sum n a_n > 1$ and recurrent iff $\sum n a_n \ge 1$. Together the two parts give the complete classification: ergodic for $\rho < 1$, recurrent-null for $\rho = 1$, transient for $\rho > 1$.
--
--   **Formalization Note** The statement quantifies over every transition matrix whose entries are the GI/M/1 matrix of $a$; such a matrix exists for every admissible $a$. $\rho$ and the mean are extended nonnegative reals, so the infinite-mean case is included. The positivity of the $\alpha_i$, which the paper also states, follows from that of the $a_n$. Irreducibility and aperiodicity are not assumed: they follow from the positivity of the entries ($p_{00} = \alpha_0 > 0$). Recurrence means $f_{jj} = 1$ for every state $j$.
-- source:
--   Foster (Ann. Math. Statist. 24, 1953), §4, p. 359 (statement), proof pp. 359–360

import Mathlib
import Definitions.Def_QueueingFundamentals_Foundations_MarkovChain
import Definitions.Def_FosterQueues_GIM1_Model

open scoped ENNReal
open QueueingFundamentals.Foundations

namespace FosterQueues.GIM1

theorem gim1_classification (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) (hsum : HasSum a 1)
    (P : TransitionMatrix) (hP : P.p = gim1Matrix a) :
    (P.PositiveRecurrent ↔ rho a < 1) ∧ (FosterQueues.MG1.IsRecurrent P ↔ rho a ≤ 1) := by sorry

end FosterQueues.GIM1
