-- Prove2me | Theorems.Thm_CombOpt_Circulation_corollary_3_16
-- name    : CombOpt.Circulation.corollary_3_16
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:02:31.248813+00:00
-- url     : https://prove2.me/theorems/e5f2da90-e3e7-425d-a4b9-504877556fa4
-- title:
--   Corollary 3.16 — uncapacitated feasibility
-- statement:
--   Given a digraph $G=(V,E)$ and $b\in\mathbb R^V$, there exists $x\in\mathbb R^E$ with $f_x(v)=b_v$ for all $v\in V$ and $x_e\ge0$ for all $e\in E$ if and only if $b(V)=0$ and, for every $A\subseteq V$ with $\delta(\bar A)=\emptyset$, we have $b(A)\le0$.
--
--   Moreover, if $b$ is integral, then there exists such an $x$ that is also integral if and only if the same conditions hold.
--
--   Differences from the source: none.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Corollary 3.16, p. 55

import Mathlib
import Definitions.Def_CombOpt_Circulation_MultiDigraph
import Definitions.Def_CombOpt_Circulation_delta
import Definitions.Def_CombOpt_Circulation_excess
import Definitions.Def_CombOpt_Circulation_IsIntegralVector

namespace CombOpt.Circulation

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

/-- **Corollary 3.16**, Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), p. 55 (PDF p. 64): given a digraph `G` and `b ∈ ℝ^V`, there exists
`x ∈ ℝ^E` with `f_x(v) = b_v` for all `v` and `x_e ≥ 0` for all `e` if and only if `b(V) = 0` and
for every `A ⊆ V` with `δ(Ā) = ∅` we have `b(A) ≤ 0`. Moreover, if `b` is integral, then there
exists such an `x` that is also integral if and only if the same conditions hold. -/
theorem corollary_3_16 (G : MultiDigraph V E) (b : V → ℝ) :
    ((∃ x : E → ℝ, (∀ v, excess G x v = b v) ∧ ∀ e, 0 ≤ x e) ↔
        ∑ v, b v = 0 ∧ ∀ A : Finset V, delta G Aᶜ = ∅ → ∑ v ∈ A, b v ≤ 0) ∧
      (IsIntegralVector b →
        ((∃ x : E → ℝ, IsIntegralVector x ∧ (∀ v, excess G x v = b v) ∧ ∀ e, 0 ≤ x e) ↔
          ∑ v, b v = 0 ∧ ∀ A : Finset V, delta G Aᶜ = ∅ → ∑ v ∈ A, b v ≤ 0)) := by sorry

end CombOpt.Circulation
