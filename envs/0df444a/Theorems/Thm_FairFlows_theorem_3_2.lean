-- Prove2me | Theorems.Thm_FairFlows_theorem_3_2
-- name    : FairFlows.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:16:03.746356+00:00
-- url     : https://prove2.me/theorems/8e9aafef-5b6e-480a-8b6f-ffa9d76af9ef
-- title:
--   Theorem 3.2 — min-max formula for the smallest edge set covering $p$
-- statement:
--   Let the digraph $D_L=(V,L)$ cover an intersecting supermodular function $p:2^V\to\mathbb Z\cup\{-\infty\}$. Then the minimum number of edges of $D_L$ covering $p$ equals
--   $$\max\Bigl\{\varrho_L(\mathcal L)-\sum_{Z\in\mathcal L}\bigl(\varrho_L(Z)-p(Z)\bigr)\Bigr\},\qquad(3.4)$$
--   the maximum over all laminar families $\mathcal L$ of subsets $Z$ of $V$ with $p(Z)>-\infty$, where $\varrho_L(\mathcal L)$ is the number of edges of $L$ entering at least one member of $\mathcal L$. When $p$ is fully supermodular, the optimal family may be chosen as a chain $V_1\supset V_2\supset\cdots\supset V_q$.
--
--   Applied to the function (4.2), the chain version is the source of the dual optimal chains of §§4–5.
--
--   Differences from the source:
--   - generalization: a digraph D = (V, A) (parallel edges are used; loops are not discussed) → edges are a finite type with tail/head maps, so parallel edges and loops are allowed; reason: a loop enters and leaves no set and cancels in ϱ_x(v) − δ_x(v); loop-free digraphs are the special case
--   - encoding: a digraph D_L = (V, L) → an edge subset L of a digraph D (D_L is D with L = all edges); reason: Lean convention; same instances
--   - encoding: a chain V₁ ⊃ V₂ ⊃ ⋯ ⊃ V_q → a Finset of distinct subsets totally ordered by ⊆ (IsChain); "enters exactly one / at least two" counts members; reason: Lean convention; same instances
--   - encoding: min = max → ∃ k: k is the size of a minimum cover and the greatest value of (3.4) (IsGreatest), and for fully supermodular p a chain attains k; reason: Lean convention; same instances
-- source:
--   Frank, Murota, Fair integral network flows, arXiv:1907.02673v5, Theorem 3.2, p.8

import Mathlib
import Definitions.Def_FairFlows_Covering

set_option autoImplicit false

namespace FairFlows

/-- Theorem 3.2 (Frank, Murota, *Fair integral network flows*, arXiv:1907.02673v5, p.8). Given a digraph `D_L = (V, L)` covering an intersecting
supermodular function `p`, the minimum number of edges of `D_L` covering `p` equals
`max{ϱ_L(𝓛) − Σ[ϱ_L(Z) − p(Z) : Z ∈ 𝓛]}` (3.4), the maximum over all laminar families `𝓛` of
subsets `Z` with `p(Z) > −∞`. When `p` is fully supermodular, the optimal family may be chosen
as a chain `V₁ ⊃ V₂ ⊃ ⋯ ⊃ V_q`.

**Formalization Note** `k` is the common value: it is the size of a minimum cover, and the
greatest value of (3.4); the chain clause gives a chain attaining it. -/
theorem theorem_3_2 {V A : Type} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
    (D : Digraph V A) (L : Finset A) (p : Finset V → WithBot ℤ)
    (hp : IsIntersectingSupermodular p) (hcov : Covers D L p) :
    ∃ k : ℕ, (∃ X : Finset A, IsMinCover D L X p ∧ X.card = k) ∧
      IsGreatest {v : ℤ | ∃ 𝓛 : Finset (Finset V), IsLaminar (𝓛 : Set (Finset V)) ∧
        (∀ Z ∈ 𝓛, p Z ≠ ⊥) ∧ lamValue D L p 𝓛 = v} (k : ℤ) ∧
      (IsSupermodular p → ∃ 𝓛 : Finset (Finset V), IsChain (· ⊆ ·) (𝓛 : Set (Finset V)) ∧
        (∀ Z ∈ 𝓛, p Z ≠ ⊥) ∧ lamValue D L p 𝓛 = k) := by sorry

end FairFlows
