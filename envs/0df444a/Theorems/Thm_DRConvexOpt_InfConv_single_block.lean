-- Prove2me | Theorems.Thm_DRConvexOpt_InfConv_single_block
-- name    : DRConvexOpt.InfConv.single_block
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:38:54.321164+00:00
-- url     : https://prove2.me/theorems/f1010f88-24ab-46c7-bddf-d896ec571778
-- title:
--   Proof of Theorem 3, p. 37 — if J = 1, then 𝒫 = 𝒫^1
-- statement:
--   Let $\mathcal P$ be the standardized ambiguity set and $\{\mathcal I_j\}_{j\in\mathcal J}$ a partition of its index set with outer approximations $\mathcal P^j$. If the partition has a single block ($J = 1$), then
--   $$\mathcal P^1 = \mathcal P.$$
--
--   This identity yields the reverse implications of Theorem 3 in the case $J = 1$: (3), (6) and (7) are then equivalent.
--
--   **Formalization Note** Blocks are indexed by `Fin nJ`, so "$J = 1$" is `nJ = 1` and the single block is index $0$; the statement is made for every $j$ in `Fin nJ`.
-- source:
--   Wiesemann, Kuhn & Sim, Distributionally Robust Convex Optimization, Optimization Online preprint 3757 (version of September 22, 2013), p. 37, proof of Theorem 3, last paragraph

import Mathlib
import Definitions.Def_DRConvexOpt_InfConv_Setting

namespace DRConvexOpt.InfConv

open MeasureTheory Matrix Filter Topology

/-- Proof of Theorem 3, p. 37: if `J = 1` (one block), then `𝒫 = 𝒫^1`. -/
theorem single_block {nP nQ nK nI nJ : ℕ} (d : AmbData nP nQ nK nI)
    (blk : Fin (nI + 1) → Fin nJ) :
    nJ = 1 → ∀ j, outerSet d blk j = ambiguitySet d := by sorry

end DRConvexOpt.InfConv
