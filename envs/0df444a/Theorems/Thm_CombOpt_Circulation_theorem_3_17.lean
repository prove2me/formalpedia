-- Prove2me | Theorems.Thm_CombOpt_Circulation_theorem_3_17
-- name    : CombOpt.Circulation.theorem_3_17
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:02:55.061046+00:00
-- url     : https://prove2.me/theorems/61c2be6e-4c08-4a1c-98dd-6e1b34f27ef2
-- title:
--   Theorem 3.17 — Hoffman's Circulation Theorem
-- statement:
--   Let $G=(V,E)$ be a digraph, and let $\ell\in(\mathbb R\cup\{-\infty\})^E$ and $u\in(\mathbb R\cup\{\infty\})^E$ with $\ell\le u$. There is a circulation $x$ with $\ell\le x\le u$ if and only if every $A\subseteq V$ satisfies
--
--   $$
--   u(\delta(\bar A))\ge\ell(\delta(A)).
--   $$
--
--   Moreover, if $\ell$ and $u$ are integral, meaning that their finite components are integers, then there is such a circulation that is also integral if and only if the same condition holds.
--
--   The condition says that the arcs entering $A$ can carry at least the amount that the arcs leaving $A$ are forced to carry. Theorem 3.15 is the case of equality constraints at the nodes; Theorem 3.17 is its counterpart for bounds on the arcs.
--
--   **Formalization Note** Both bounds are `EReal`-valued, with $\ell_e\ne+\infty$ and $u_e\ne-\infty$ as hypotheses. Thus the sum $u(\delta(\bar A))$ never mixes $+\infty$ with $-\infty$, and neither does $\ell(\delta(A))$.
--
--   Differences from the source:
--   - encoding: ℓ ∈ (ℝ ∪ {−∞})^E, u ∈ (ℝ ∪ {∞})^E → ℓ, u : E → EReal with ℓ e ≠ ⊤ and u e ≠ ⊥; reason: these hypotheses describe exactly the book's ranges, and sums in EReal then agree with the book's
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Theorem 3.17, p. 55

import Mathlib
import Definitions.Def_CombOpt_Circulation_MultiDigraph
import Definitions.Def_CombOpt_Circulation_delta
import Definitions.Def_CombOpt_Circulation_IsIntegralVector
import Definitions.Def_CombOpt_Circulation_IsIntegralBound
import Definitions.Def_CombOpt_Circulation_IsCirculation

namespace CombOpt.Circulation

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

/-- **Theorem 3.17 (Hoffman's Circulation Theorem)**, Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), p. 55 (PDF p. 64): given a digraph `G`,
`ℓ ∈ (ℝ ∪ {−∞})^E` and `u ∈ (ℝ ∪ {∞})^E` with `ℓ ≤ u`, there is a circulation `x` with
`ℓ ≤ x ≤ u` if and only if every `A ⊆ V` satisfies `u(δ(Ā)) ≥ ℓ(δ(A))`. Moreover, if `ℓ` and `u`
are integral, then there is such a circulation that is also integral if and only if the same
condition holds.

**Formalization Note** Bounds are `EReal`-valued with `ℓ e ≠ ⊤` and `u e ≠ ⊥`, so the sum
`u(δ(Ā))` contains no `⊥` and `ℓ(δ(A))` contains no `⊤`: the `EReal` convention `⊤ + ⊥ = ⊥` never
applies, `u(δ(Ā)) = ∞` as soon as one term is `∞`, and `ℓ(δ(A)) = −∞` as soon as one term is `−∞`.
"Integral" concerns the finite components (p. 39). -/
theorem theorem_3_17 (G : MultiDigraph V E) (l u : E → EReal) (hl : ∀ e, l e ≠ ⊤)
    (hu : ∀ e, u e ≠ ⊥) (hlu : ∀ e, l e ≤ u e) :
    ((∃ x : E → ℝ, IsCirculation G x ∧ ∀ e, l e ≤ (x e : EReal) ∧ (x e : EReal) ≤ u e) ↔
        ∀ A : Finset V, ∑ e ∈ delta G Aᶜ, u e ≥ ∑ e ∈ delta G A, l e) ∧
      (IsIntegralBound l → IsIntegralBound u →
        ((∃ x : E → ℝ, IsIntegralVector x ∧ IsCirculation G x ∧
            ∀ e, l e ≤ (x e : EReal) ∧ (x e : EReal) ≤ u e) ↔
          ∀ A : Finset V, ∑ e ∈ delta G Aᶜ, u e ≥ ∑ e ∈ delta G A, l e)) := by sorry

end CombOpt.Circulation
