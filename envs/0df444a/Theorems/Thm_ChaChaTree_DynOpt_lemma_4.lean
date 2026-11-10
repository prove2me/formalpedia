-- Prove2me | Theorems.Thm_ChaChaTree_DynOpt_lemma_4
-- name    : ChaChaTree.DynOpt.lemma_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:23:27.146353+00:00
-- url     : https://prove2.me/theorems/0e22e165-22ff-47e7-b9f5-5a84562f3f9d
-- title:
--   Lemma 4 — OPT(P) ≥ IR(P)/2 + |P| [DHIKP09], in the BST model of §5.1
-- statement:
--   For every access sequence $X$ on the keys $[n]$, with instance $P = P(X)$,
--   $$\mathrm{OPT}(P) \ge \tfrac12\,\mathrm{IR}(P) + |P|,$$
--   where $\mathrm{OPT}$ is the minimum cost of an offline execution of $X$ in the BST model of §5.1 (free initial tree, every move, rotation and finish of unit cost).
--
--   Differences from the source:
--   - reading: OPT(P) of an instance P (cited from [DHIKP09]) → OPT n X for an access sequence X on [n], with P = pointsOf X and |P| = (pointsOf X).card; reason: OPT(P) means serving the keys of P in increasing time order; deleting empty time rows preserves all rectangle containment tests, independence, and |P|, so every instance is represented by pointsOf X up to this order-preserving time relabeling. The cost is the cursor-model cost specified in §5.1
-- source:
--   Čech, Haeupler, Roeyskoe, Rozhoň, Tarjan, Yingchareonthawornchai, Dynamic Optimality to within O(log log log n), STOC 2027 submission (manuscript, sha256 9316fbfd…7b9e), Lemma 4, p. 11 (PDF 12)

import Mathlib
import Definitions.Def_ChaChaTree_DynOpt_CursorModel
import Definitions.Def_ChaChaTree_DynOpt_Instance
import Definitions.Def_ChaChaTree_DynOpt_Rectangles

set_option autoImplicit false

namespace ChaChaTree.DynOpt

/-- **Lemma 4** ([DHIKP09], p. 11). For every access sequence `X` on the keys `[n]`, with instance
`P = P(X)`: `OPT(P) ≥ IR(P)/2 + |P|`, where `OPT` is the optimum of the BST model of §5.1. -/
theorem lemma_4 (n : ℕ) (X : List ℕ) (hX : ∀ x ∈ X, x ∈ Finset.Icc 1 n) :
    (IR (pointsOf X) : ℝ) / 2 + ((pointsOf X).card : ℝ) ≤ (OPT n X : ℝ) := by sorry

end ChaChaTree.DynOpt
