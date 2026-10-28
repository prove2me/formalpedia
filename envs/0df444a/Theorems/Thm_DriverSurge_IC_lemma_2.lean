-- Prove2me | Theorems.Thm_DriverSurge_IC_lemma_2
-- name    : DriverSurge.IC.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:31:05.710182+00:00
-- url     : https://prove2.me/theorems/e725e0ce-48de-4d7a-9adb-7e2452ff0cea
-- title:
--   Lemma 2, p. 12 — the two-state world chain is in the other state s time units later with probability λ_{i→j}/(λ_{i→j}+λ_{j→i})·[1 − e^{−(λ_{i→j}+λ_{j→i})s}]
-- statement:
--   Let the world be the two-state continuous-time Markov chain of the dynamic model, started in an arbitrary state $i_0$, which leaves state $i$ at rate $\lambda_{i\to j}$. For every state $i$ and all times $t,s\ge0$,
--   $$\mathbb P\big(X_t=i,\;X_{t+s}=j\big)=q_{i\to j}(s)\,\mathbb P(X_t=i),\qquad q_{i\to j}(s)=\frac{\lambda_{i\to j}}{\lambda_{i\to j}+\lambda_{j\to i}}\Big[1-e^{-(\lambda_{i\to j}+\lambda_{j\to i})s}\Big],$$
--   where $j\ne i$ and $X_t$ is the world state at time $t$. Equivalently, given that the world is in state $i$ at time $t$, it is in state $j$ at time $t+s$ with probability $q_{i\to j}(s)$.
--
--   The function $q_{i\to j}$ is the transition function of the world chain. It enters the reward through $Q_i$ and is the building block of the incentive-compatible prices of Theorem 3.
--
--   **Formalization Note** Lean state `0` is the paper's non-surge state 1 and Lean state `1` the surge state 2; `other i` is the state $j\ne i$. The conditional probability is written as a joint probability, so the statement also holds (trivially) when $\mathbb P(X_t=i)=0$.
--
--   Differences from the source:
--   - encoding: "suppose the world is in state $i$ at time $t$" (a conditional probability) → $\mu(X_t=i, X_{t+s}=j)=q_{i\to j}(s)\,\mu(X_t=i)$ for every initial state and all $t,s\ge0$; reason: avoids conditioning on a possibly null event; identical whenever the conditional probability is defined
-- source:
--   Garg, Nazerzadeh, Driver Surge Pricing, arXiv:1905.07544v4, p. 12, Lemma 2

import Mathlib
import Definitions.Def_DriverSurge_IC_Process

namespace DriverSurge.IC

open MeasureTheory

/-- Lemma 2 (p. 12). If the world is in state `i` at time `t`, it is in the other state at time
`t + s` with probability `q_{i→j}(s) = λ_{i→j}/(λ_{i→j}+λ_{j→i}) [1 − e^{−(λ_{i→j}+λ_{j→i})s}]`; stated
without conditional probability, for every initial state, every `t ≥ 0` and `s ≥ 0`. -/
theorem lemma_2 (P : Primitives) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (i₀ : Fin 2)
    (X : Ω → Path) (hX : IsDriverModel P μ i₀ X) (i : Fin 2) (t s : ℝ) (ht : 0 ≤ t) (hs : 0 ≤ s) :
    μ {ω | worldState i₀ (X ω) t = i ∧ worldState i₀ (X ω) (t + s) = other i} =
      ENNReal.ofReal (q P i s) * μ {ω | worldState i₀ (X ω) t = i} := by sorry

end DriverSurge.IC
