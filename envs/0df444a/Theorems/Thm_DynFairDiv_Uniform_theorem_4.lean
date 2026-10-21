-- Prove2me | Theorems.Thm_DynFairDiv_Uniform_theorem_4
-- name    : DynFairDiv.Uniform.theorem_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:57.150919+00:00
-- url     : https://prove2.me/theorems/ce3395e7-7a0e-47b5-ae2f-5e5d2fd5b462
-- title:
--   Theorem 4, p. 952 — the optimal fairness ratio of d-uniform control vectors is 1/((d+1)ln((d+1)/d)), attained by the infinite vector
-- statement:
--   For an integer $d \ge 1$ let
--   $$\sigma^*_d \;=\; \frac{1}{(d+1)\,\ln\!\big(\frac{d+1}{d}\big)} .$$
--   Theorem 4 of the paper states $\mathrm{FAIRNESS}(d\text{-uniform}) = \inf_{\psi} \mathrm{FAIRNESS}(\psi) = \sigma^*_d$, the infimum taken over all $d$-uniform control vectors $\psi$, of every finite length $n \ge 1$ and of infinite length. This statement asserts three things:
--
--   1. **Attainment.** There is a single feasible arrivals-only allocation sequence for the infinite $d$-uniform control vector whose fairness ratio is at least $\sigma^*_d$: every user present at any time $t \ge 1$ holds at least $\sigma^*_d/t$, and at most $d$ existing users are disrupted at each arrival.
--   2. **Optimality.** For every $\sigma > \sigma^*_d$ there is a finite length $n \ge 1$ such that no feasible allocation sequence for the $d$-uniform control vector of length $n$ achieves fairness ratio $\sigma$.
--   3. **The equation itself.** $\displaystyle\inf_{n \in \{1,2,\dots\}\cup\{\infty\}} \mathrm{FAIRNESS}(\psi_{d,n}) = \sigma^*_d$, where $\psi_{d,n}$ is the $d$-uniform control vector of length $n$.
--
--   Parts 1 and 2 are the two inequalities behind the equation together with the attainment the paper notes on p. 952 (FFA run with $\sigma^*_d$ gives feasible allocations for the infinite vector); part 3 is the paper's equation verbatim. For $d = 1$ the value is $1/(2\ln 2) \approx 0.721$, and $\sigma^*_d \to 1$ as $d \to \infty$.
--
--   **Formalization Note.** Departures are not modelled (arrivals only, as in §§3–5 of the paper); users are labelled by arrival order; the length of a control vector is $n : \mathbb{N}_\infty$, with $\top$ the infinite vector. $\mathrm{FAIRNESS}(\psi)$ is a real supremum that is genuine for $n \ge 1$ (the set contains $0$ and is bounded by $1$), and the infimum in part 3 ranges over the nonempty family $n \ge 1$ of values in $[0,1]$, so no junk value of `sSup`/`iInf` enters.
-- source:
--   Vardi, Psomas, Friedman, Dynamic Fair Resource Division, Math. Oper. Res. 47(2):945–968 (2022), p. 952, Theorem 4 (proof pp. 959–960, Appendix E.2); attainment: p. 952, §5.1

import Mathlib
import Definitions.Def_DynFairDiv_Uniform_Model

namespace DynFairDiv.Uniform

theorem theorem_4 (d : ℕ) (hd : 1 ≤ d) :
    (∃ X, AchievesRatio (uniformCV d) ⊤ (uniformRatio d) X) ∧
    (∀ σ : ℝ, uniformRatio d < σ →
      ∃ n : ℕ, 1 ≤ n ∧ ¬ ∃ X, AchievesRatio (uniformCV d) (n : ℕ∞) σ X) ∧
    (⨅ n : {n : ℕ∞ // 1 ≤ n}, fairnessRatio (uniformCV d) n.1) = uniformRatio d := by sorry

end DynFairDiv.Uniform
