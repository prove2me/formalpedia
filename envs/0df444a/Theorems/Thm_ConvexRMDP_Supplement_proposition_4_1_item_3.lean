-- Prove2me | Theorems.Thm_ConvexRMDP_Supplement_proposition_4_1_item_3
-- name    : ConvexRMDP.Supplement.proposition_4_1_item_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:56:00.448579+00:00
-- url     : https://prove2.me/theorems/8506611d-4c47-5513-84ea-ac6db4039be8
-- title:
--   Proposition 4.1, item 3 — $\tilde v^\star_s \le v^\star_s \le \tilde v^\star_s + \log(|\mathcal A|)/(b(1-\gamma))$
-- statement:
--   Let $(\mathcal S, \mathcal A, r, \gamma, \mathcal U)$ be an sa-rectangular robust MDP with $\mathcal A$ nonempty and $b > 0$, with uniform reference policy $\nu_{sa} = 1/|\mathcal A|$ in $\tilde T$. Let $\tilde v^\star \in \mathbb R^{\mathcal S}$ be the fixed point of the regularized robust Bellman operator $\tilde T$ and $v^\star \in \mathbb R^{\mathcal S}$ the fixed point of the robust Bellman operator $T$. Then
--
--   $$
--   \tilde v^\star_s \;\le\; v^\star_s \;\le\; \tilde v^\star_s + \frac{\log(|\mathcal A|)}{b\,(1-\gamma)}, \qquad \forall s \in \mathcal S .
--   $$
--
--   This is the error bound behind Theorem 4.2: choosing $b$ large makes $\tilde v^\star$ an arbitrarily accurate approximation of the robust value function.
--
--   **Formalization Note** The conclusion is stated for every fixed point of $\tilde T$ and every fixed point of $T$; both operators are $\gamma$-contractions, so these are the unique fixed points of the paper.
--
--   Differences from the source:
--   - encoding: "the unique fixed point" of $\tilde T$ and of $T$ → every `vt` with `regOp b vt = vt` and every `vs` with `robustOp vs = vs`; reason: the fixed points are unique (contractions), same instances.
--   - encoding: nonempty action set and $b > 0$ → hypotheses `[Nonempty A]`, `0 < b`; reason: standing assumptions of §3.1 and §4.
-- source:
--   Grand-Clément & Petrik, arXiv:2209.10187v2, Proposition 4.1, item 3, p.11; proof in App. B, pp.27–28

import Mathlib
import Definitions.Def_ConvexRMDP_RMDP_regOp
import Definitions.Def_ConvexRMDP_Supplement_robustOp

namespace ConvexRMDP

namespace Supplement

/-- **Proposition 4.1, item 3** (Grand-Clément & Petrik, arXiv:2209.10187v2, p.11; proof in App. B,
pp.27–28). When `ν_{sa} = 1/|A|`, let `ṽ⋆ ∈ ℝ^S` be the unique fixed point of `T̃` and `v⋆ ∈ ℝ^S` the
unique fixed point of `T`. Then `ṽ⋆_s ≤ v⋆_s ≤ ṽ⋆_s + log(|A|)/(b(1−γ))` for all `s ∈ S`.

**Formalization Note.** The statement holds for every fixed point `ṽ⋆` of `T̃ = RMDP.regOp` and every
fixed point `v⋆` of `T = robustOp` (each operator is a `γ`-contraction, so these are the unique fixed
points). `A` is nonempty and `b > 0`. -/
theorem proposition_4_1_item_3 {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (M : RMDP S A) (b : ℝ) (hb : 0 < b) (vt vs : S → ℝ)
    (hvt : M.regOp b vt = vt) (hvs : robustOp M vs = vs) (s : S) :
    vt s ≤ vs s ∧ vs s ≤ vt s + Real.log (Fintype.card A) / (b * (1 - M.γ)) := by sorry

end Supplement

end ConvexRMDP
