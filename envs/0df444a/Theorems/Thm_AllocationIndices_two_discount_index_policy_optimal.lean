-- Prove2me | Theorems.Thm_AllocationIndices_two_discount_index_policy_optimal
-- name    : AllocationIndices.two_discount_index_policy_optimal
-- status  : Open
-- author  : @naimengye
-- created : 2026-09-24T02:40:11.508984+00:00
-- url     : https://prove2.me/theorems/bbd42b41-df7d-4426-a48e-fe8474799e58
-- title:
--   Theorem 3.4 (discrete time, corrected): for two bandit processes with discount factors a and b, selecting A or B according as a^t ν_AB(x) > or < b^t ν_BA(y) is optimal
-- statement:
--   **Theorem 3.4.** An optimal policy for a simple family $F$ of two alternative bandit processes $A$ and $B$ with discount factors $a$ and $b$ is one which selects $A$ or $B$ according as $\nu_{AB}(x) > $ or $< \nu_{BA}(y)$ when $A$ is in state $x$ and $B$ is in state $y$, where
--   $$\nu_{AB}(x) = \sup_{\tau > 0}\frac{\mathbb{E}\sum_{s_i < \tau} a^{s_i} r_A(s_i)}{\mathbb{E}\int_0^\tau b^t\,dt}, \qquad \nu_{BA}(y) = \sup_{\tau > 0}\frac{\mathbb{E}\sum_{t_i < \tau} b^{t_i} r_B(t_i)}{\mathbb{E}\int_0^\tau a^t\,dt}.$$
--
--   **Stated here, in discrete time and corrected.** $A$ and $B$ are Markov bandit processes on countable state spaces with bounded rewards and discount factors $a, b \in (0,1)$; the family is the two-armed Markov bandit on $S_A \oplus S_B$ in which a reward obtained at time $t$ from $A$ is discounted by $a^t$ and one from $B$ by $b^t$. Let
--   $$\tilde\nu_{AB}(x) = \sup_{\tau > 0}\frac{\mathbb{E}\sum_{t<\tau} a^t r_A(x(t))}{\mathbb{E}[1 - b^\tau]}, \qquad \tilde\nu_{BA}(y) = \sup_{\tau > 0}\frac{\mathbb{E}\sum_{t<\tau} b^t r_B(y(t))}{\mathbb{E}[1 - a^\tau]}.$$
--   If a policy $\pi$ selects, in round $t$ with $A$ in state $x$ and $B$ in state $y$, $A$ whenever $a^t \tilde\nu_{AB}(x) > b^t \tilde\nu_{BA}(y)$ and $B$ whenever $a^t \tilde\nu_{AB}(x) < b^t \tilde\nu_{BA}(y)$ (either when they are equal), then for every initial pair of states $(x, y)$ its payoff equals the supremum of the payoffs of all policies.
--
--   **Why the corrections.** The printed rule is false. Take two one-state bandits (standard bandits), $A$ paying $0.18$ with $a = 0.9$ and $B$ paying $1$ with $b = 0.5$. The states never change, so the printed rule, and any rule that depends only on the states, plays one process forever: payoff $1.8$ for $A$ or $2$ for $B$. Playing $B$ for three rounds and then $A$ forever earns $1 + 0.5 + 0.25 + 0.18 \cdot 0.9^3/0.1 = 3.062$. The book's proof rescales time so that $A^*$ and $B^*$ share a discount factor $c$ ($A$'s step lasts $\log_c b$, with reward $(a/b)^{s} r_A$ at process time $s$). The index of $A^*$ at process time $s$ is $(a/b)^s \tilde\nu_{AB}(x)\ln(1/c)$, and that of $B^*$ is $(b/a)^u \tilde\nu_{BA}(y)\ln(1/c)$, where $\int_0^{\tau\log_c b} c^u\,du = (1 - b^\tau)/\ln(1/c)$. Comparing them is comparing $a^t \tilde\nu_{AB}(x)$ with $b^t \tilde\nu_{BA}(y)$ at the global time $t = s + u$. The printed denominator $\mathbb{E}\int_0^\tau b^t dt = \mathbb{E}[1 - b^\tau]/\ln(1/b)$ replaces the common $\ln(1/c)$ by $\ln(1/b)$ for one process and $\ln(1/a)$ for the other. Nash's generalized-bandit route on p. 66, with $Q(A, x) = (b/c)^v$ and $R_A = (a/c)^v r_A$, gives the same indices. Checked against brute-force dynamic programming on 150 random instances (up to three states per process, rewards of both signs): the corrected rule is optimal from every initial state, while the printed rule and its discrete analogue with denominator $\mathbb{E}\sum_{t<\tau} b^t$ are strictly suboptimal in 215 initial states.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §3.5.1 pp. 64-65, Theorem 3.4 (Nash), with its proof by a change of time scale; the index denominator and the time weights a^t, b^t are corrected, see the statement

import Definitions.Def_AllocationIndices_Jobs

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace AllocationIndices

theorem two_discount_index_policy_optimal {SA SB : Type*} [MeasurableSpace SA] [Countable SA]
    [MeasurableSingletonClass SA] [MeasurableSpace SB] [Countable SB] [MeasurableSingletonClass SB]
    (PA : Kernel SA SA) [IsMarkovKernel PA] {rA : SA → ℝ} (hrA : BoundedReward rA)
    (PB : Kernel SB SB) [IsMarkovKernel PB] {rB : SB → ℝ} (hrB : BoundedReward rB)
    {a b : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1)
    {π : MarkovBanditPolicy 2 (SA ⊕ SB)} (hπ : IsTwoDiscountIndexPolicy PA PB rA rB a b π)
    (x : SA) (y : SB) :
    twoDiscountValue PA PB rA rB a b π x y =
      ⨆ π' : MarkovBanditPolicy 2 (SA ⊕ SB), twoDiscountValue PA PB rA rB a b π' x y := by sorry

end AllocationIndices
