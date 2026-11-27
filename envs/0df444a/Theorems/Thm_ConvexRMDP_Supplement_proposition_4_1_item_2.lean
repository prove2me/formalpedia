-- Prove2me | Theorems.Thm_ConvexRMDP_Supplement_proposition_4_1_item_2
-- name    : ConvexRMDP.Supplement.proposition_4_1_item_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:55:32.684803+00:00
-- url     : https://prove2.me/theorems/39fbba80-087b-474a-bcd7-68683cf69434
-- title:
--   Proposition 4.1, item 2 — $\tilde T(v)_s \le T(v)_s \le \tilde T(v)_s + \log(|\mathcal A|)/b$
-- statement:
--   Let $(\mathcal S, \mathcal A, r, \gamma, \mathcal U)$ be an sa-rectangular robust MDP with $\mathcal A$ nonempty, let $b > 0$, and let $\tilde T$ be the regularized robust Bellman operator with uniform reference policy $\nu_{sa} = 1/|\mathcal A|$ and $T$ the robust Bellman operator (3.8). Then for each $s \in \mathcal S$ and $v \in \mathbb R^{\mathcal S}$, $\tilde T$ brackets $T$:
--
--   $$
--   \tilde T(v)_s \;\le\; T(v)_s \;\le\; \tilde T(v)_s + \frac{\log(|\mathcal A|)}{b} .
--   $$
--
--   The bracket transfers to the fixed points (item 3) and quantifies the error of entropic regularization.
--
--   **Formalization Note** $\tilde T$ is the published `ConvexRMDP.RMDP.regOp` and $T$ is `robustOp`; both use the same worst-case term $\min_{p \in \mathcal U_{sa}} p^\top v$.
--
--   Differences from the source:
--   - encoding: $\nu_{sa} = 1/|\mathcal A|$ in $\tilde T$ → the published operator `RMDP.regOp`, which has the uniform policy built in; reason: same operator.
--   - encoding: nonempty action set and $b > 0$ (standing assumptions of §3.1 and §4) → hypotheses `[Nonempty A]`, `0 < b`; reason: the paper's standing assumptions, no instance excluded.
-- source:
--   Grand-Clément & Petrik, arXiv:2209.10187v2, Proposition 4.1, item 2, p.11; proof in App. B, pp.27–28

import Mathlib
import Definitions.Def_ConvexRMDP_RMDP_regOp
import Definitions.Def_ConvexRMDP_Supplement_robustOp

namespace ConvexRMDP

namespace Supplement

/-- **Proposition 4.1, item 2** (Grand-Clément & Petrik, arXiv:2209.10187v2, p.11; proof in App. B,
pp.27–28). When `ν_{sa} = 1/|A|` for each `(s,a)` in the regularized operator `T̃`, then for each
`s ∈ S` and `v ∈ ℝ^S`, `T̃` brackets the robust Bellman operator `T` of (3.8):
`T̃(v)_s ≤ T(v)_s ≤ T̃(v)_s + log(|A|)/b`.

**Formalization Note.** `T̃` is the published `RMDP.regOp` (uniform `ν`), `T` is `robustOp`; both use
the same worst-case term `RMDP.worst`. `A` is nonempty and `b > 0` (the regularization scalar). -/
theorem proposition_4_1_item_2 {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (M : RMDP S A) (b : ℝ) (hb : 0 < b) (v : S → ℝ) (s : S) :
    M.regOp b v s ≤ robustOp M v s ∧
      robustOp M v s ≤ M.regOp b v s + Real.log (Fintype.card A) / b := by sorry

end Supplement

end ConvexRMDP
