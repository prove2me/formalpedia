-- Prove2me | Theorems.Thm_CombOpt_Circulation_theorem_3_15
-- name    : CombOpt.Circulation.theorem_3_15
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:03:30.924866+00:00
-- url     : https://prove2.me/theorems/c672509b-ca02-477e-ba2d-a6e75f0c04a6
-- title:
--   Theorem 3.15 — Gale's feasibility theorem
-- statement:
--   Let $G=(V,E)$ be a digraph, $u\in\mathbb R^E_+$ and $b\in\mathbb R^V$. The system (3.8), namely $f_x(v)=b_v$ for all $v$ and $0\le x_e\le u_e$ for all $e$, has a solution if and only if $b(V)=0$ and
--
--   $$
--   b(A)\le u(\delta(\bar A))\qquad\text{for every }A\subseteq V.
--   $$
--
--   If $b$ and $u$ are integral, then (3.8) has an integral solution if and only if the same conditions hold.
--
--   Differences from the source: none.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Theorem 3.15, p. 55

import Mathlib
import Definitions.Def_CombOpt_Circulation_MultiDigraph
import Definitions.Def_CombOpt_Circulation_delta
import Definitions.Def_CombOpt_Circulation_IsIntegralVector
import Definitions.Def_CombOpt_Circulation_IsSolution38

namespace CombOpt.Circulation

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

/-- **Theorem 3.15** (Gale), Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), p. 55 (PDF p. 64): there exists a solution to (3.8) if and only
if `b(V) = 0` and, for every `A ⊆ V`, `b(A) ≤ u(δ(Ā))`. If `b` and `u` are integral, then (3.8)
has an integral solution if and only if the same conditions hold.

**Formalization Note** In (3.8), `u ∈ ℝ^E_+`: capacities are finite and nonnegative here, unlike
Theorems 3.5–3.7. -/
theorem theorem_3_15 (G : MultiDigraph V E) (u : E → ℝ) (hu : ∀ e, 0 ≤ u e) (b : V → ℝ) :
    ((∃ x, IsSolution38 G u b x) ↔
        ∑ v, b v = 0 ∧ ∀ A : Finset V, ∑ v ∈ A, b v ≤ ∑ e ∈ delta G Aᶜ, u e) ∧
      (IsIntegralVector b → IsIntegralVector u →
        ((∃ x, IsIntegralVector x ∧ IsSolution38 G u b x) ↔
          ∑ v, b v = 0 ∧ ∀ A : Finset V, ∑ v ∈ A, b v ≤ ∑ e ∈ delta G Aᶜ, u e)) := by sorry

end CombOpt.Circulation
