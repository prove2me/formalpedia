-- Prove2me | Theorems.Thm_FosterQueues_GIM1_theorem4_transient_iff
-- name    : FosterQueues.GIM1.theorem4_transient_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T04:58:35.902748+00:00
-- url     : https://prove2.me/theorems/44666eee-7de2-49f9-98fd-91451c477c1a
-- title:
--   Theorem 4 — the system is transient iff Σⱼ pᵢⱼ yⱼ = yᵢ (i ≠ 0) has a bounded nonconstant solution
-- statement:
--   Let $[p_{ij}]$ ($i, j = 0, 1, 2, \dots$) be the transition matrix of an irreducible, aperiodic Markov chain. The system is transient if and only if there is a real sequence $(y_j)_{j \ge 0}$ which is bounded ($|y_j| \le C$ for some constant $C$ and all $j$), nonconstant ($y_i \ne y_j$ for some $i, j$), and solves
--   $$
--   \sum_{j=0}^{\infty} p_{ij}\, y_j = y_i, \qquad i \ne 0. \tag{7}
--   $$
--   The equations are imposed for every state except $0$; nothing is required at $i = 0$.
--
--   Transience is here the complement of recurrence, without distinguishing recurrent-null from recurrent-nonnull systems. Foster uses both directions for the GI/M/1 chain: when $\rho < 1$ no bounded nonconstant solution of (7) exists, so the chain is recurrent; when $\rho > 1$ one exists, so the chain is transient.
--
--   **Formalization Note** "Transient" means every state $j$ has return probability $f_{jj} < 1$. Irreducibility and aperiodicity are the paper's standing assumptions (§1, p. 355). The equations (7) are stated with `HasSum`; for bounded $y$ the series always converge.
-- source:
--   Foster (Ann. Math. Statist. 24, 1953), Theorem 4, pp. 356–357; standing assumptions §1, p. 355

import Mathlib
import Definitions.Def_QueueingFundamentals_Foundations_MarkovChain
import Definitions.Def_FosterQueues_GIM1_Model

open scoped ENNReal
open QueueingFundamentals.Foundations

namespace FosterQueues.GIM1

theorem theorem4_transient_iff (P : TransitionMatrix) (hirr : P.Irreducible)
    (hap : P.Aperiodic) :
    FosterQueues.MG1.IsTransient P ↔
      ∃ y : ℕ → ℝ, (∃ C : ℝ, ∀ i, |y i| ≤ C) ∧ (∃ i j, y i ≠ y j) ∧
        ∀ i, i ≠ 0 → HasSum (fun j => P.p i j * y j) (y i) := by sorry

end FosterQueues.GIM1
