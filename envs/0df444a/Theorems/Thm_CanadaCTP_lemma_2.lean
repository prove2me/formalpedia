-- Prove2me | Theorems.Thm_CanadaCTP_lemma_2
-- name    : CanadaCTP.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:19:37.576775+00:00
-- url     : https://prove2.me/theorems/ed045726-fc05-4961-9b67-1e8d41120a6a
-- title:
--   Lemma 2 — PathExplorer is well defined
-- statement:
--   For a path with weights $X$:
--
--   1. for every $\mathrm{coin}\in\mathrm{COIN}$, the arrival probability and the expected cost of the coin strategy are given by the closed formulas of the proof;
--   2. for every $\mathrm{coin}\in\mathrm{COIN}$, pair $(j,x)$ and $t\in[0,1]$, setting $\mathrm{coin}(j,x)=t$ gives
--   $$
--   \mathrm{arrivalProb}=A(j,x,\mathrm{coin})+\alpha(j,x,\mathrm{coin})\,t,\qquad \mathrm{expCost}=B(j,x,\mathrm{coin})+\beta(j,x,\mathrm{coin})\,t,
--   $$
--   with $A,\alpha,B,\beta$ independent of $\mathrm{coin}(j,x)$ (the rewriting in steps 1) and 2) of Algorithm 2);
--   3. if every entry of $\mathrm{coin}$ is $0$ or $1$ and $\mathrm{expCost}(\mathrm{coin})>0$, some pair has $\mathrm{coin}(j,x)=1$ and $\beta(j,x,\mathrm{coin})>0$, so the arg min of Algorithm 2 is over a non-empty set;
--   4. if setting $\mathrm{coin}(j,x)$ to $0$ gives expected cost at most $b$ and setting it to $1$ gives more than $b$, then some value in $[0,1]$ gives expected cost exactly $b$, so the final adjustment is feasible.
--
--   Item 1 is where the closed formulas, used by the other milestones, get their meaning.
--
--   Differences from the source:
--   - reading: "PathExplorer is well-defined, meaning that the rewriting … is feasible, the adjustment … is feasible, and the arg min is well defined" → four clauses: the closed formulas are the semantics; the affine rewriting for t ∈ [0,1]; a candidate with coin = 1 and β > 0 exists whenever all entries are 0/1 and expCost > 0; the adjustment value exists; reason: these are exactly the three claims of the statement, with the formulas of the proof that the claims refer to
--   - encoding: probabilities and expected values of the whole (possibly unbounded) run → suprema over the horizon N of the N-step quantities, in ℝ≥0∞; reason: the events are absorbing and the costs non-decreasing in N, so the suprema are the limits, i.e. the same values
--   - encoding: independent non-negative discrete finitely supported edge weights given explicitly; edges and paths indexed from 1 → EdgeDist: an explicit list of (value, probability) pairs with distinct values, values ≥ 0, probabilities > 0 summing to 1; edges Fin m, paths Fin k, indexed from 0; reason: Lean convention; the list is exactly the support, so every instance of the paper is represented and nothing else
-- source:
--   Abels–Pitschmann–Schewior–Schmand, Canada Retravelled (manuscript, STOC 2027 submission, sha256 8117348eb78ba082edf376778214fa414f31cb0cd8a8d06c12a1dfba627e3a33), Lemma 2, p.8; proof pp.8–9

import Mathlib
import Definitions.Def_CanadaCTP_PathOpt

namespace CanadaCTP

/-- Abels–Pitschmann–Schewior–Schmand, *Canada Retravelled* (manuscript, sha256 8117348e…3a33), Lemma 2, p.8 (proof pp.8–9): PathExplorer is well defined.

1. The closed formulas of the proof are the arrival probability and the expected cost of the
   coin strategy.
2. Both are affine in each entry `coin(j, x) ∈ [0,1]`, with coefficients `α`, `β` and constant
   terms `A = coinArr X (updC c j x 0)`, `B = coinCost X (updC c j x 0)` that do not depend on
   `coin(j, x)` (the rewriting of steps 1) and 2) of Algorithm 2).
3. The arg min is well defined: if every entry is `0` or `1` and the expected cost is positive,
   some pair with `coin(j, x) = 1` has `β(j, x, coin) > 0`.
4. The adjustment is feasible: if setting `coin(j, x)` to `0` gives cost `≤ b` and setting it to
   `1` gives cost `> b`, some value in `[0,1]` gives cost exactly `b`. -/
theorem lemma_2 {m : ℕ} (X : Fin m → EdgeDist) :
    (∀ c : Coin X, InCOIN X c →
      arrProb (pathInst X) (coinPolicy X c) = ENNReal.ofReal (coinArr X c) ∧
      expCost (pathInst X) (coinPolicy X c) = ENNReal.ofReal (coinCost X c)) ∧
    (∀ c : Coin X, InCOIN X c → ∀ (j : Fin m) (x : Fin (X j).pts.length), ∀ t ∈ Set.Icc (0 : ℝ) 1,
      coinArr X (updC c j x t) = coinArr X (updC c j x 0) + alphaC X c j x * t ∧
      coinCost X (updC c j x t) = coinCost X (updC c j x 0) + betaC X c j x * t) ∧
    (∀ c : Coin X, (∀ j x, c j x = 0 ∨ c j x = 1) → 0 < coinCost X c →
      ∃ (j : Fin m) (x : Fin (X j).pts.length), c j x = 1 ∧ 0 < betaC X c j x) ∧
    (∀ c : Coin X, InCOIN X c → ∀ (j : Fin m) (x : Fin (X j).pts.length) (b : ℝ),
      coinCost X (updC c j x 0) ≤ b → b < coinCost X (updC c j x 1) →
      ∃ t ∈ Set.Icc (0 : ℝ) 1, coinCost X (updC c j x t) = b) := by sorry

end CanadaCTP
