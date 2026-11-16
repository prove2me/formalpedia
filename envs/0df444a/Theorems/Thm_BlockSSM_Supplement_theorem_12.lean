-- Prove2me | Theorems.Thm_BlockSSM_Supplement_theorem_12
-- name    : BlockSSM.Supplement.theorem_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:05:55.258743+00:00
-- url     : https://prove2.me/theorems/8e1bc747-807a-4c46-afca-0619a8158605
-- title:
--   Theorem 12 — bounded margin gives the same dimension, $n^{\mathrm{bm}}_b(G)=D_b(G)=n_b(G)$
-- statement:
--   For every finite group $G$,
--   $$
--   n^{\mathrm{bm}}_b(G)=D_b(G)=n_b(G).
--   $$
--   Here $n^{\mathrm{bm}}_b(G)$ is the least hidden dimension of a tracker that tracks $G$, has a bounded reachable set and separates differently labelled reachable states by a fixed $\varepsilon>0$ (Definition 11), without assuming that the reachable set is finite; $D_b(G)$ is the cover invariant and $n_b(G)$ the finite-state tracker dimension. All three are $\infty$ when infeasible.
--
--   The theorem shows that the exact dimension theorem does not depend on the finite-reachability hypothesis: the robustness condition of bounded margin gives the same answer.
--
--   Differences from the source:
--   - generalization: an integer block bound $b$ → $b\in\mathbb N\cup\{\infty\}$ (`ℕ∞`), every value including $b=\infty$; reason: every integer bound is a case through the cast and $b=\infty$ is the unbounded case ($D_\infty$ of Definition 2); the argument is the same
--   - encoding: boundedness of $R$ and the margin in the norm of $\mathbb C^n$ → Euclidean norm `l2norm` and distance `l2dist`; reason: all norms on $\mathbb C^n$ are equivalent and $\varepsilon$ is existential, so the notion is the same
--   - encoding: a minimum with value $\infty$ on an empty feasible set → `sInf` in `ℕ∞`; reason: `sInf ∅ = ⊤`, and on a nonempty set of naturals `sInf` is the minimum
--   - encoding: finite covers $H$ and representations $V$ in $D_b$ → $H$ in the lowest universe, $V=\mathbb C^d$ (published `BlockSSM.coverDim`); reason: every finite group has an isomorphic copy in `Type` and every $d$-dimensional representation is isomorphic to one on $\mathbb C^d$
-- source:
--   C. Geng, The State Complexity of Block-Diagonal State Space Models, STOC 2027 submission manuscript (sha256 f9071794…), Theorem 12, p.5 (PDF p.6), with Definition 11

import Mathlib
import Definitions.Def_BlockSSM_trackerDim
import Definitions.Def_BlockSSM_coverDim
import Definitions.Def_BlockSSM_Supplement_bmTrackerDim

universe u

namespace BlockSSM.Supplement

open BlockSSM

/-- **Theorem 12 (bounded margin).** Geng, *The State Complexity of Block-Diagonal State Space Models*, STOC 2027 submission manuscript (sha256 f9071794…), Theorem 12, p.5 (PDF p.6): "n^bm_b(G) = D_b(G) = n_b(G)
for every finite group G."

**Formalization Note.** Both equalities are stated. `n^bm_b` (`bmTrackerDim`) ranges over tracking
trackers with bounded Euclidean reachable set and a positive Euclidean margin between differently
labelled reachable states (Definition 11); they are not assumed finite-state. All three values are
in `ℕ∞`, `⊤` when infeasible; `b : ℕ∞` covers every finite bound and `b = ∞`. -/
theorem theorem_12 (G : Type u) [Group G] [Finite G] (b : ℕ∞) :
    bmTrackerDim G b = coverDim G b ∧ coverDim G b = trackerDim G b := by sorry

end BlockSSM.Supplement
