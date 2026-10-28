-- Prove2me | Theorems.Thm_DecisionForest_Universal_prodWeight_isDistribution
-- name    : DecisionForest.Universal.prodWeight_isDistribution
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T03:55:30.000775+00:00
-- url     : https://prove2.me/theorems/7b18a7de-26ef-43db-b8a4-d3f003b2d5c8
-- title:
--   Proof of Theorem 1, p. ec2 — the weights (EC.5), λ_t = ∏_j P(o^t_j | S_j), are nonnegative and sum to one
-- statement:
--   Let $\mathbf P(\cdot\mid\cdot)$ be a discrete choice model on $N$ products. For a tuple $\mathbf o=(o_S)_{S\subseteq\mathcal N}$ of purchase options, one per assortment, define as in (EC.5)
--   $$\lambda_{\mathbf o}=\prod_{S\subseteq\mathcal N}\mathbf P(o_S\mid S).$$
--   Then $\lambda_{\mathbf o}\ge 0$ for every tuple $\mathbf o$, and
--   $$\sum_{\mathbf o\in(\mathcal N^+)^{2^{\mathcal N}}}\lambda_{\mathbf o}=1,$$
--   the sum running over all $(N+1)^{2^N}$ tuples.
--
--   These are the weights the proof of Theorem 1 puts on the trees $t_{\mathbf o}$; the statement says they form a probability distribution.
--
--   **Formalization Note** Tuples are functions `o : Finset (Fin N) → Option (Fin N)` and $\lambda_{\mathbf o}$ is `prodWeight P o`.
--
--   Differences from the source:
--   - encoding: trees indexed by $t=1,\dots,(N+1)^{2^N}$ through an enumeration $\mathbf o^1,\dots,\mathbf o^{(N+1)^{2^N}}$ of tuples → weights indexed by the tuples themselves; reason: same family of numbers.
--   - encoding: products $\{1,\dots,N\}$ → `Fin N`, options $\mathcal N^+$ → `Option (Fin N)` with `none` the option $0$; reason: Lean convention, same instances.
-- source:
--   Chen and Mišić, Decision Forest: A Nonparametric Approach to Modeling Irrational Choice, arXiv:1904.11532v3, p. ec2 (PDF 31), proof of Theorem 1, (EC.5)

import Mathlib
import Definitions.Def_DecisionForest_Universal_Setting

namespace DecisionForest.Universal

theorem prodWeight_isDistribution (N : ℕ) (P : Option (Fin N) → Finset (Fin N) → ℝ)
    (hP : IsChoiceModel P) :
    (∀ o : Finset (Fin N) → Option (Fin N), 0 ≤ prodWeight P o) ∧
      ∑ o : Finset (Fin N) → Option (Fin N), prodWeight P o = 1 := by sorry

end DecisionForest.Universal
