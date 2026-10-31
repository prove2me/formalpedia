-- Prove2me | Theorems.Thm_CombOpt_MinCostFlow_feasible_flow_iff_cut_condition
-- name    : CombOpt.MinCostFlow.feasible_flow_iff_cut_condition
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:02:30.882994+00:00
-- url     : https://prove2.me/theorems/4e7f6b03-f7fc-4350-9af5-62df2e08c763
-- title:
--   Theorem 3.18 — feasibility with lower bounds, upper bounds and demands
-- statement:
--   Let $G=(V,E)$ be a digraph, $b\in\mathbb R^V$ with $b(V)=0$, $\ell\in(\mathbb R\cup\{-\infty\})^E$ and $u\in(\mathbb R\cup\{\infty\})^E$ with $\ell\le u$. Then there exists $x\in\mathbb R^E$ with
--
--   $$f_x(v)=b_v\ \ (v\in V),\qquad \ell_e\le x_e\le u_e\ \ (e\in E)$$
--
--   if and only if every $A\subseteq V$ satisfies
--
--   $$u(\delta(\bar A))\ \ge\ b(A)+\ell(\delta(A)).$$
--
--   Moreover, if $b$, $\ell$ and $u$ are integral (finite components integers), there exists such an $x$ that is also integral if and only if the same condition holds.
--
--   The theorem contains Gale's supply–demand theorem and Hoffman's circulation theorem as special cases, and it is the step that turns an optimal dual solution of the minimum-cost flow problem into an integral optimal flow (Theorem 4.5).
--
--   Differences from the source:
--   - encoding: ℓ ∈ (ℝ ∪ {−∞})^E, u ∈ (ℝ ∪ {∞})^E; sums u(δ(Ā)), ℓ(δ(A)) → ℓ u : E → EReal with ℓ e ≠ ⊤, u e ≠ ⊥; sums in EReal; reason: Lean convention; no ⊤ + ⊥ can occur, the same instances and the same condition
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Theorem 3.18, p. 56 (PDF p. 65)

import Mathlib
import Definitions.Def_CombOpt_MinCostFlow_Digraph_netInflow
import Definitions.Def_CombOpt_MinCostFlow_Digraph_delta
import Definitions.Def_CombOpt_MinCostFlow_IsIntegralExt

namespace CombOpt.MinCostFlow

/-- **Theorem 3.18 (feasibility with lower bounds, upper bounds and demands).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Theorem 3.18, p. 56 (PDF p. 65): "Given a digraph G, b ∈ ℝ^V such that b(V) = 0,
ℓ ∈ (ℝ ∪ {−∞})^E, and u ∈ (ℝ ∪ {∞})^E with ℓ ≤ u, there exists x ∈ ℝ^E such that f_x(v) = b_v for
all v ∈ V, ℓ_e ≤ x_e ≤ u_e for all e ∈ E if and only if every A ⊆ V satisfies
u(δ(Ā)) ≥ b(A) + ℓ(δ(A)). Moreover, if b, ℓ, and u are integral, there exists such an x that is
also integral if and only if the same condition is satisfied."

**Formalization Note.** `ℓ` and `u` are `EReal`-valued with `ℓ e ≠ ⊤` and `u e ≠ ⊥`; the sums
`u(δ(Ā))`, `ℓ(δ(A))` are taken in `EReal`, where no `⊤ + ⊥` can occur. `Ā` is `Aᶜ`. -/
theorem feasible_flow_iff_cut_condition {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Digraph V E) (b : V → ℝ) (hb : ∑ v, b v = 0) (ℓ u : E → EReal)
    (hℓ : ∀ e, ℓ e ≠ ⊤) (hu : ∀ e, u e ≠ ⊥) (hℓu : ∀ e, ℓ e ≤ u e) :
    ((∃ x : E → ℝ, (∀ v, G.netInflow x v = b v) ∧ ∀ e, ℓ e ≤ (x e : EReal) ∧ (x e : EReal) ≤ u e) ↔
        ∀ A : Finset V,
          ((∑ v ∈ A, b v : ℝ) : EReal) + ∑ e ∈ G.delta A, ℓ e ≤ ∑ e ∈ G.delta Aᶜ, u e) ∧
      ((∀ v, ∃ k : ℤ, b v = k) → (∀ e, IsIntegralExt (ℓ e)) → (∀ e, IsIntegralExt (u e)) →
        ((∃ x : E → ℝ, (∀ e, ∃ k : ℤ, x e = k) ∧ (∀ v, G.netInflow x v = b v) ∧
            ∀ e, ℓ e ≤ (x e : EReal) ∧ (x e : EReal) ≤ u e) ↔
          ∀ A : Finset V,
            ((∑ v ∈ A, b v : ℝ) : EReal) + ∑ e ∈ G.delta A, ℓ e ≤ ∑ e ∈ G.delta Aᶜ, u e)) := by sorry

end CombOpt.MinCostFlow
