-- Prove2me | Theorems.Thm_ChvatalPolytopes_Substitution_stable_max_decomposition
-- name    : ChvatalPolytopes.Substitution.stable_max_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T20:58:27.833582+00:00
-- url     : https://prove2.me/theorems/f647b758-aacf-4321-878f-2bb782308cc7
-- title:
--   Theorem 5.1, second step — $m=\max\{m_0,\,m_1+m_2\}$
-- statement:
--   Let $G_1=(V_1,E_1)$ and $G_2=(V_2,E_2)$ be finite graphs with disjoint vertex sets, $v\in V_1$, and let $G$ be obtained from $G_1$ by substituting $G_2$ for $v$. Put $W=V_1-\{v\}$. Let $c=(c_u:u\in V_2\cup W)$ be an integer-valued vector and $d_u=\max\{c_u,0\}$ for $u\in V_2\cup W$. Set
--   $$m=\max\{cx : x\in S(G)\},$$
--   $$m_0=\max\Big\{\sum_{u\in W}d_ux_u : x\in S(G_1),\ x_v=0\Big\},\qquad m_1=\max\Big\{\sum_{u\in W}d_ux_u : x\in S(G_1),\ x_v=1\Big\},$$
--   $$m_2=\max\Big\{\sum_{u\in V_2}d_ux_u : x\in S(G_2)\Big\}.$$
--   Then
--   $$m=\max\Big\{\sum_{u\in V_2\cup W}d_ux_u : x\in S(G)\Big\}\qquad\text{and}\qquad m=\max\{m_0,\ m_1+m_2\}.$$
--
--   This purely combinatorial identity splits the maximum weight of a stable set of $G$ into the cases "the stable set avoids $V_2$" and "the stable set meets $V_2$"; the proof of Theorem 5.1 builds its dual multipliers case by case from it.
--
--   **Formalization Note** Vertices of $G$ are the disjoint sum $\{u\in V_1:u\ne v\}\oplus V_2$. Each maximum is written as the real supremum (`sSup`) of the image of a finite set; each of these sets is nonempty ($S(G)$, $S(G_2)$ and $\{x\in S(G_1):x_v=0\}$ contain $0$, and $\{x\in S(G_1):x_v=1\}$ contains the incidence vector of $\{v\}$), so every supremum is an attained maximum and no junk value of `sSup` arises.
-- source:
--   Chvátal, On certain polytopes associated with graphs, J. Combin. Theory Ser. B 18 (1975), pp. 145–146, §5, proof of Theorem 5.1

import Mathlib
import Definitions.Def_ChvatalPolytopes_Shared_StablePolytope
import Definitions.Def_ChvatalPolytopes_Substitution_substitute

namespace ChvatalPolytopes.Substitution

/-- **Decomposition of the optimum** (Chvátal 1975, §5, pp. 145–146, proof of Theorem 5.1).
Let `G` be obtained from `G₁` by substituting `G₂` for the vertex `v` of `G₁`, and set
`W = V₁ − {v}`. Let `c = (c_u : u ∈ V₂ ∪ W)` be an integer-valued vector, `d_u = max {c_u, 0}`,
`m = max {cx : x ∈ S(G)}`, and
* `m₀ = max {Σ (d_u x_u : u ∈ W) : (x_u : u ∈ V₁) ∈ S(G₁), x_v = 0}`,
* `m₁ = max {Σ (d_u x_u : u ∈ W) : (x_u : u ∈ V₁) ∈ S(G₁), x_v = 1}`,
* `m₂ = max {Σ (d_u x_u : u ∈ V₂) : (x_u : u ∈ V₂) ∈ S(G₂)}`.
Then `m = max {Σ (d_u x_u : u ∈ V₂ ∪ W) : x ∈ S(G)}` and `m = max {m₀, m₁ + m₂}`.

Vertices of `G` are `{u : V₁ // u ≠ v} ⊕ V₂` (`inl` = `W`, `inr` = `V₂`). Each maximum is written
as `sSup` of the (finite) image set; every one of these sets is finite and nonempty (`S(G)`,
`S(G₂)` and `{x ∈ S(G₁) : x_v = 0}` contain the zero vector, `{x ∈ S(G₁) : x_v = 1}` contains the
incidence vector of `{v}`), so each `sSup` is an attained maximum. -/
theorem stable_max_decomposition {V₁ V₂ : Type*} [Fintype V₁] [DecidableEq V₁]
    [Fintype V₂] [DecidableEq V₂] (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂) (v : V₁)
    (c : {u : V₁ // u ≠ v} ⊕ V₂ → ℤ) :
    let d : {u : V₁ // u ≠ v} ⊕ V₂ → ℤ := fun u => max (c u) 0
    let m : ℝ := sSup ((fun x => ∑ u, (c u : ℝ) * x u) '' Shared.stableVectors (substitute G₁ v G₂))
    let m₀ : ℝ := sSup ((fun x : V₁ → ℝ => ∑ w : {u : V₁ // u ≠ v}, (d (.inl w) : ℝ) * x w) ''
      {x | x ∈ Shared.stableVectors G₁ ∧ x v = 0})
    let m₁ : ℝ := sSup ((fun x : V₁ → ℝ => ∑ w : {u : V₁ // u ≠ v}, (d (.inl w) : ℝ) * x w) ''
      {x | x ∈ Shared.stableVectors G₁ ∧ x v = 1})
    let m₂ : ℝ := sSup ((fun x : V₂ → ℝ => ∑ u, (d (.inr u) : ℝ) * x u) '' Shared.stableVectors G₂)
    m = sSup ((fun x => ∑ u, (d u : ℝ) * x u) '' Shared.stableVectors (substitute G₁ v G₂)) ∧
      m = max m₀ (m₁ + m₂) := by sorry

end ChvatalPolytopes.Substitution
