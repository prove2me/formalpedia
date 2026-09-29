-- Prove2me | Theorems.Thm_ChvatalPolytopes_Perfect_exists_induced_indepNum_mul_cliqueNum_lt
-- name    : ChvatalPolytopes.Perfect.exists_induced_indepNum_mul_cliqueNum_lt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T20:13:48.011743+00:00
-- url     : https://prove2.me/theorems/d0c52eb6-d69e-44e5-8cac-652bfeaadf4d
-- title:
--   Lovász's first theorem — a nonperfect graph has an induced $G_A$ with $\alpha(G_A)\,\omega(G_A)<|A|$
-- statement:
--   Let $G=(V,E)$ be a finite graph that is not perfect, in the ($\alpha$-perfect) sense of the definition of perfection above. For $A\subseteq V$ let $G_A$ be the subgraph of $G$ induced by $A$, $\alpha(G_A)$ its stability number (the largest size of a stable set) and $\omega(G_A)$ its clique number (the largest size of a complete subgraph). Then there is a set $A\subseteq V$ with
--   $$\alpha(G_A)\cdot\omega(G_A)<|A|.$$
--
--   This theorem of Lovász (1972), cited in §3 of the paper, supplies the certificate of nonperfection used in the implication (iii) $\Rightarrow$ (ii) of the proof of Theorem 3.1.
--
--   **Formalization Note** $\alpha$ and $\omega$ are Mathlib's natural-number-valued `indepNum` and `cliqueNum` of `G.induce A`, and $A$ is a finset of vertices. Nonperfection is the negation of the mission's `IsPerfect`.
-- source:
--   Chvátal, On certain polytopes associated with graphs, J. Combin. Theory Ser. B 18 (1975), p. 140, §3 (Lovász [16], first theorem)

import Mathlib
import Definitions.Def_ChvatalPolytopes_Perfect_StablePolytope
import Definitions.Def_ChvatalPolytopes_Perfect_IsPerfect

namespace ChvatalPolytopes.Perfect

/-- **Lovász's first theorem** (cited in Chvátal 1975, §3, p. 140, from Lovász [16]): every
nonperfect graph `G` (in the sense of `IsPerfect`, the paper's α-perfection) contains an induced
subgraph `G_A` with `α(G_A) · ω(G_A) < |A|`. Here `α = indepNum`, `ω = cliqueNum` (Mathlib,
ℕ-valued) and `G_A = G.induce A`. -/
theorem exists_induced_indepNum_mul_cliqueNum_lt {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : ¬ IsPerfect G) :
    ∃ A : Finset V,
      (G.induce (A : Set V)).indepNum * (G.induce (A : Set V)).cliqueNum < A.card := by sorry

end ChvatalPolytopes.Perfect
