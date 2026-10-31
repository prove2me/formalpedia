-- Prove2me | Theorems.Thm_ApproxNashSet_theorem_3_1
-- name    : ApproxNashSet.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:17:54.15807+00:00
-- url     : https://prove2.me/theorems/aaf07d9b-2e46-431d-b875-96a5307d14b6
-- title:
--   Theorem 3.1 — $\mathrm{NE}(f,\mathbb X)=\bigcap_i\operatorname{argMin}\{(x_{-i},-x_{-i},f_i(x))\mid x\in\mathbb X\}$
-- statement:
--   For any shared-constraint game with costs $f_i$ and constraint set $\mathbb X\subseteq\prod_jX_j$ (no convexity or other assumption), the set of Nash equilibria is the intersection over the players of the Pareto optimal sets of the multi-objective problems (3):
--   $$\mathrm{NE}(f,\mathbb X)=\bigcap_{i=1}^N\operatorname{argMin}\{(x_{-i},-x_{-i},f_i(x))\mid x\in\mathbb X\}.$$
--   Here the order on $\mathbb R^{m_i}$ is the componentwise order, and $\mathrm{NE}(f,\mathbb X)$ is the set of $x^*\in\mathbb X$ such that no player can lower her cost by a feasible unilateral change (Definition 2.1).
--
--   This is the equality (5) on which the approximation algorithm is built; the paper attributes it to Feinstein and Rudloff [6], who state it with a non-convex ordering cone.
--
--   **Formalization Note** The Nash equilibrium set is the published definition `NashVecOpt.SharedConstraint.NE`.
--
--   Differences from the source:
--   - generalization: N ≥ 2 players → any nonempty finite player type; reason: no step uses N ≥ 2; nonemptiness is kept because an empty intersection over players would be the whole space
--   - encoding: objective space ℝ^{mᵢ} with ordering cone ℝ^{mᵢ}₊, strategy spaces Xᵢ = ℝ^{nᵢ}, players 1, …, N → Obj n i = (∏_{j≠i} ℝ^{nⱼ}) × (∏_{j≠i} ℝ^{nⱼ}) × ℝ with the componentwise order, Fin (n i) → ℝ, a finite type ι; reason: Lean convention; the same instances
-- source:
--   Feinstein–Hey–Rudloff, Approximating the set of Nash equilibria for convex games, arXiv:2310.04176v4, Theorem 3.1, (5), p.4

import Mathlib
import Definitions.Def_NashVecOpt_SharedConstraint_Game
import Definitions.Def_ApproxNashSet_Model

open scoped Pointwise

namespace ApproxNashSet

/-- **Theorem 3.1 — Nash equilibria are the common Pareto optimal points of problems (3).**
Feinstein–Hey–Rudloff, arXiv:2310.04176v4, Theorem 3.1, (5), p.4: "The set of Nash equilibria of any
non-cooperative game (1) coincides with the intersection of the Pareto optimal points of problems
(3) over all i ∈ {1, ..., N}, i.e., NE(f, X) = ⋂_{i=1}^N argMin{(x−i, −x−i, fi(x)) | x ∈ X}."

**Formalization Note.** Players form a nonempty finite type `ι` (the paper has `N ≥ 2` players);
`NE` is the published `NashVecOpt.SharedConstraint.NE` (Definition 2.1). No assumption on `f`
or `X`. -/
theorem theorem_3_1 {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {n : ι → ℕ}
    (f : ι → Joint n → ℝ) (X : Set (Joint n)) :
    NashVecOpt.SharedConstraint.NE f X = ⋂ i, argMin (g n f i) X := by sorry

end ApproxNashSet
