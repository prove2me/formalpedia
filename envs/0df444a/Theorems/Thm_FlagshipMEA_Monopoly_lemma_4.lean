-- Prove2me | Theorems.Thm_FlagshipMEA_Monopoly_lemma_4
-- name    : FlagshipMEA.Monopoly.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:08:50.000546+00:00
-- url     : https://prove2.me/theorems/c65fa81c-78d1-42b9-8b6f-1d3e4762284e
-- title:
--   Lemma 4 — revenue maximization at fixed total marketing effort
-- statement:
--   Fix a positive total marketing effort $M$ in a nonempty product line. Some product $k$ has maximal MEA index $R_k(M)$, and putting all effort on $k$ maximizes revenue among all nonnegative allocations totaling $M$. Moreover, every revenue maximizer can put positive effort only on products whose index is maximal:
--
--   $$m_i>0\quad\Longrightarrow\quad R_i(M)=\max_j R_j(M).$$
--
--   This is the revenue half of the concentration argument. **Formalization Note** The final support condition records the equality case when several products tie; the paper's phrase “the solution is concentrated” cannot require every fixed-effort revenue maximizer to have a singleton support in a tie.
-- source:
--   He, Ke & Zhang, A Model of Product Line Marketing, SSRN 3631879 (version of August 2021), pp. 40–41 (PDF 42–43), Lemma 4, (C–6)–(C–9)

import Mathlib
import Definitions.Def_FlagshipMEA_Monopoly_Model

namespace FlagshipMEA.Monopoly

/-- Lemma 4 (p. 40): at positive fixed TME a concentrated allocation maximizes
revenue; every revenue maximizer gives effort only to products with maximal index. -/
theorem lemma_4 {n : ℕ} (D : Data n) (hS : D.Standing)
    (hn : 0 < n) (M : ℝ) (hM : 0 < M) :
    ∃ k : Fin n, D.IsArgmaxR M k ∧
      (∀ m : Fin n → ℝ, Feasible m → tme m = M →
        D.revenue m ≤ D.revenue (fun j => if j = k then M else 0)) ∧
      (∀ m : Fin n → ℝ, Feasible m → tme m = M →
        (∀ m' : Fin n → ℝ, Feasible m' → tme m' = M →
          D.revenue m' ≤ D.revenue m) →
        ∀ i, 0 < m i → D.IsArgmaxR M i) := by sorry

end FlagshipMEA.Monopoly
