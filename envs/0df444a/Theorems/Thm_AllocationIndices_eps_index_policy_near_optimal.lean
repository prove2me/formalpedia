-- Prove2me | Theorems.Thm_AllocationIndices_eps_index_policy_near_optimal
-- name    : AllocationIndices.eps_index_policy_near_optimal
-- status  : Open
-- author  : @naimengye
-- created : 2026-09-24T02:49:58.579122+00:00
-- url     : https://prove2.me/theorems/cee55245-7ddc-4493-b44f-c71cd886d802
-- title:
--   Theorem 4.18: an ε-index policy for a SFABP loses at most εγ⁻¹(1 − e⁻ᵞ)⁻¹ in the book's index units, i.e. ε/(1 − a)² for the discrete-time index
-- statement:
--   **Theorem 4.18.** If $h$ is an $\varepsilon$-index policy for an SFABP $F$ with the discount parameter $\gamma$, then $R_h(F) \ge R(F) - \varepsilon\gamma^{-1}(1 - e^{-\gamma})^{-1}$.
--
--   Formally: for a SFABP in the Bandit Algorithms model (a common countable state space, bounded reward, discount factor $a = e^{-\gamma} \in (0,1)$), $\varepsilon \ge 0$, and a policy $\pi$ that at every decision time almost surely continues a bandit whose Gittins index is within $\varepsilon$ of the maximal index among the current states, for every initial state-vector $x$,
--   $$\sup_{\pi'} R_{\pi'}(x) - \frac{\varepsilon}{(1 - a)^2} \le R_\pi(x),$$
--   where $R_\pi(x)$ is the discounted value of $\pi$ from $x$. At $\varepsilon = 0$ this is the index theorem.
--
--   **The units of $\varepsilon$.** The book's $\varepsilon$-bounds of §4.10 are in the continuous-time units of the index, reward per unit time with $W_\tau = \mathbb{E}\int_0^\tau e^{-\gamma t}\,dt$. Corollary 4.16's bound $\varepsilon\gamma^{-1} = \varepsilon\int_0^\infty e^{-\gamma t}dt$ shows it. For a Markov family with decision times $0, 1, 2, \dots$, that index is $\gamma/(1 - a)$ times the discrete-time index (2.6), whose denominator is $\mathbb{E}\sum_{t<\tau} a^t$. An $\varepsilon$-index policy for the discrete index is therefore an $\varepsilon\gamma/(1-a)$-index policy in the book's units, and the book's bound becomes $\frac{\varepsilon\gamma}{1-a}\cdot\gamma^{-1}(1 - e^{-\gamma})^{-1} = \varepsilon/(1-a)^2$. Reading the book's constant with the discrete index, i.e. $\varepsilon/((1-a)\ln(1/a))$, gives a false statement for $a < 1/e$. Two one-state bandits paying $\nu$ and $\nu - \varepsilon$ show it: the $\varepsilon$-index policy that always plays the second loses $\varepsilon/(1-a)$, which at $a = 0.1$ is $1.11\varepsilon > 0.48\varepsilon$. Exact value iteration on 120 random families (up to three bandits with up to three states each) found the worst $\varepsilon$-index policy within $0.84$ of the bound $\varepsilon/(1-a)^2$ and never above it, while the other reading was exceeded in 5 families.
-- source:
--   Gittins, Glazebrook and Weber, Multi-armed Bandit Allocation Indices, 2nd ed., Wiley 2011, doi:10.1002/9780470980033, §4.10 p. 112, Theorem 4.18 (Glazebrook 1982c); ε converted from the book's continuous-time index units to the discrete-time index (2.6)

import Definitions.Def_AllocationIndices_Superprocess

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace AllocationIndices

theorem eps_index_policy_near_optimal {T : Type*} [MeasurableSpace T] [Countable T]
    [MeasurableSingletonClass T] (P : Kernel T T) [IsMarkovKernel P] {r : T → ℝ}
    (hr : BoundedReward r) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {ε : ℝ} (hε : 0 ≤ ε) {k : ℕ}
    {π : MarkovBanditPolicy k T} (hπ : IsEpsIndexPolicy P r a ε π) (x : Fin k → T) :
    (⨆ π' : MarkovBanditPolicy k T, markovBanditDiscountedValue P r a π' x) -
        ε / (1 - a) ^ 2 ≤
      markovBanditDiscountedValue P r a π x := by sorry

end AllocationIndices
