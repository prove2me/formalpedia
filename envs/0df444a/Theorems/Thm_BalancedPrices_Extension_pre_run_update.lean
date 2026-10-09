-- Prove2me | Theorems.Thm_BalancedPrices_Extension_pre_run_update
-- name    : BalancedPrices.Extension.pre_run_update
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T15:10:14.185976+00:00
-- url     : https://prove2.me/theorems/1fbc36bb-9ec0-4610-92c0-5be1206e3854
-- title:
--   Proof of Theorem 3.2, p. 549 — x_[i−1](v) does not depend on v_i
-- statement:
--   Let $\mathbf x(\mathbf v)$ be the outcome profile produced when agents are approached in index order and agent $i$ picks $\mathrm{choice}_i(v_i,\mathbf y)$ from its own type $v_i$ and the partial allocation $\mathbf y$ of the earlier agents. Then for every type profile $\mathbf v$, agent $i$ and type $w$ of agent $i$,
--   $$\mathbf x_{[i-1]}\bigl((w,\mathbf v_{-i})\bigr)=\mathbf x_{[i-1]}(\mathbf v).$$
--
--   That is, the outcomes of the agents before $i$ do not depend on agent $i$'s type. This is the step that lets the proof of Theorem 3.2 exchange $v_i$ with an independent copy $v'_i$.
--
--   **Formalization Note** Agents are `Fin n`, 0-based; $\mathbf x_{[i-1]}$ keeps the agents with index $<i$. No hypotheses on the choice rule are needed.
-- source:
--   Dütting, Feldman, Kesselheim, Lucier, Prophet inequalities made easy: Stochastic optimization by pricing nonstochastic inputs, SIAM J. Comput. 49 (2020), p. 549, proof of Theorem 3.2 (Utility bound)

import Mathlib
import Definitions.Def_BalancedPrices_Extension_Model
import Definitions.Def_BalancedPrices_Extension_Mechanism

open scoped ENNReal

namespace BalancedPrices.Extension

theorem pre_run_update {n : ℕ} {X V : Fin n → Type*} (nul : Outcome X)
    (choice : ∀ i, V i → Outcome X → X i) (v : ∀ i, V i) (i : Fin n) (w : V i) :
    pre nul (run nul choice (Function.update v i w)) i = pre nul (run nul choice v) i := by sorry

end BalancedPrices.Extension
