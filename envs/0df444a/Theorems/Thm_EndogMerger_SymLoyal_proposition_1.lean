-- Prove2me | Theorems.Thm_EndogMerger_SymLoyal_proposition_1
-- name    : EndogMerger.SymLoyal.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T03:11:51.907991+00:00
-- url     : https://prove2.me/theorems/09db0326-653c-4df7-bd97-0fd640d1cb0a
-- title:
--   Proposition 1, PDF p. 13 — with ample capacity k ≥ 1−2α, the independent structure {A,B,C} is the equilibrium structure
-- statement:
--   Let $0<\alpha<1/3$, $r>0$, and suppose the small firms have ample capacity, $1-2\alpha\le k<1$. Then, with the Table A1 profits and conditions (1a)–(2b), the independent structure is the unique equilibrium structure:
--   $$
--   \{S : S \text{ is an equilibrium structure}\}=\bigl\{\{A,B,C\}\bigr\}.
--   $$
--
--   This settles the ample-capacity case, which Proposition 3 includes in its "otherwise" clause.
--
--   **Formalization Note** The paper states the result for $k_A>k\ge 1-2\alpha$; Table A1's last row is $[1-2\alpha,1)$, so $k<1$ is a hypothesis and $k_A$ is not modelled. $0<\alpha$ and $r>0$ are added. "The equilibrium structure" is rendered as: the set of equilibrium structures is exactly the singleton, as the proof (PDF p. 46) says "unique".
-- source:
--   Wang, Wu, Tang & Dai, Endogenous merger decisions among competitors: impact of limited capacity and loyal segments, Management Science (2024), accepted manuscript, PDF p. 13, Proposition 1; proof PDF p. 46

import Mathlib
import Definitions.Def_EndogMerger_SymLoyal_Setting

namespace EndogMerger.SymLoyal
theorem proposition_1 (α k r : ℝ) (hα0 : 0 < α) (hα3 : α < 1 / 3)
    (hk : 1 - 2 * α ≤ k) (hk1 : k < 1) (hr : 0 < r) :
    {S | IsEquilibriumStructure α k r S} = {MarketStructure.indep} := by sorry
end EndogMerger.SymLoyal
