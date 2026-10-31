-- Prove2me | Theorems.Thm_ApproxNashSet_theorem_3_2
-- name    : ApproxNashSet.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:18:18.752014+00:00
-- url     : https://prove2.me/theorems/e16fbd96-646d-4265-acb6-a4d3e9c0d0d1
-- title:
--   Theorem 3.2 — $\epsilon\,\mathrm{NE}(f,\mathbb X)=\bigcap_i\epsilon\operatorname{argMin}\{(x_{-i},-x_{-i},f_i(x))\mid x\in\mathbb X\}$ for direction $\bar c_i$
-- statement:
--   For any shared-constraint game with costs $f_i$ and constraint set $\mathbb X\subseteq\prod_jX_j$ (no further assumption) and every $\varepsilon$, the set of ε-approximate Nash equilibria is the intersection over the players of the ε-Pareto optimal sets of problems (3) with respect to the direction $\bar c_i=(0,\dots,0,1)$:
--   $$\varepsilon\,\mathrm{NE}(f,\mathbb X)=\bigcap_{i=1}^N\varepsilon\operatorname{argMin}\{(x_{-i},-x_{-i},f_i(x))\mid x\in\mathbb X\}.$$
--
--   This is the equality (6) that turns the per-player approximation of Lemma 4.11 into a statement about approximate Nash equilibria in Theorem 4.9.
--
--   **Formalization Note** $\varepsilon\,\mathrm{NE}$ is the universal form of Definition 2.2: $x^*\in\mathbb X$ and $f_i(x^*)\le f_i(x_i,x^*_{-i})+\varepsilon$ for every player and every feasible unilateral $x_i$.
--
--   Differences from the source:
--   - generalization: ε > 0 → every real ε; reason: the argument does not use the sign of ε; ε > 0 is a special case
--   - generalization: N ≥ 2 players → any nonempty finite player type; reason: no step uses N ≥ 2; nonemptiness is kept because an empty intersection over players would be the whole space
--   - encoding: ε NE(f, X) := {x* ∈ X | ∀i : fi(x*) ≤ inf{fi(xi, x*−i) | (xi, x*−i) ∈ X} + ε} → the universal form of Definition 2.2's first sentence; reason: the two agree (the infimum is over a set containing fᵢ(x*)); a real sInf of a set unbounded below is 0 in Lean
--   - encoding: objective space ℝ^{mᵢ} with ordering cone ℝ^{mᵢ}₊, strategy spaces Xᵢ = ℝ^{nᵢ}, players 1, …, N → Obj n i = (∏_{j≠i} ℝ^{nⱼ}) × (∏_{j≠i} ℝ^{nⱼ}) × ℝ with the componentwise order, Fin (n i) → ℝ, a finite type ι; reason: Lean convention; the same instances
-- source:
--   Feinstein–Hey–Rudloff, Approximating the set of Nash equilibria for convex games, arXiv:2310.04176v4, Theorem 3.2, (6), p.4 (proof pp.4–5)

import Mathlib
import Definitions.Def_ApproxNashSet_Model

open scoped Pointwise

namespace ApproxNashSet

/-- **Theorem 3.2 — ε-Nash equilibria are the common ε-Pareto optimal points of problems (3).**
Feinstein–Hey–Rudloff, arXiv:2310.04176v4, Theorem 3.2, (6), p.4: "The set of ǫ-approximate Nash
equilibria of any non-cooperative game (1) coincides with the intersection of the ǫ-Pareto optimal
points of problems (3) for direction c̄i = (0, ..., 0, 1)⊤ over all i ∈ {1, ..., N}, i.e.,
ǫ NE(f, X) = ⋂_{i=1}^N ǫ argMin{(x−i, −x−i, fi(x)) | x ∈ X}."

**Formalization Note.** Players form a nonempty finite type `ι` (the paper has `N ≥ 2`). Stated
for every real `ε` (the paper's `ε > 0`). No assumption on `f` or `X`. -/
theorem theorem_3_2 {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {n : ι → ℕ}
    (f : ι → Joint n → ℝ) (X : Set (Joint n)) (ε : ℝ) :
    epsNE f X ε = ⋂ i, epsArgMin (g n f i) X (cbar n i) ε := by sorry

end ApproxNashSet
