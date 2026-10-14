-- Prove2me | Theorems.Thm_EndogMerger_SymLoyal_proposition_3
-- name    : EndogMerger.SymLoyal.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:11:57.315626+00:00
-- url     : https://prove2.me/theorems/3ef7b133-0d09-420a-857f-c6fb19759432
-- title:
--   Proposition 3, PDF p. 19 — the mixed merger {AB,C} is the equilibrium structure iff α(1−2α)/(1−3α) < k < 1−2α; otherwise {A,B,C}
-- statement:
--   Three firms sell a homogeneous product to a unit mass of buyers with reservation value $r>0$; each firm has $\alpha$ loyal buyers, $0<\alpha<1/3$, and the other $1-3\alpha$ buyers switch to the cheapest firm. Firm $A$ has ample capacity and the small firms $B$, $C$ have capacity $k$ each, $\alpha<k<1$. Using the Table A1 equilibrium profits, call a market structure an equilibrium structure according to conditions (1a)–(2b): the mixed merger $\{AB,C\}$ when (1a) and (1b) hold, the small merger $\{A,BC\}$ when (2a) and (2b) hold, and the independent structure $\{A,B,C\}$ when neither holds. Let $k^*=\alpha(1-2\alpha)/(1-3\alpha)$. Then
--   $$
--   \{S : S\text{ is an equilibrium structure}\}=
--   \begin{cases}
--   \bigl\{\{AB,C\}\bigr\} & \text{if } k^*<k<1-2\alpha,\\[2pt]
--   \bigl\{\{A,B,C\}\bigr\} & \text{otherwise.}
--   \end{cases}
--   $$
--
--   In particular the small merger of the two capacity-constrained firms is never an equilibrium structure, and the large firm merges with a small rival exactly when the small firms' capacity is intermediate.
--
--   **Formalization Note** The hypotheses $0<\alpha$ (every region of the analysis requires it) and $r>0$ (implicit, $r$ is the reservation value) are added; $k<1$ is the range of Table A1, and firm $A$'s capacity is not modelled. The profits are the Table A1 expressions, defined directly; the game-theoretic derivation of Table A1 is not formalized. "Is the equilibrium structure" is rendered as: the set of equilibrium structures is exactly that singleton.
-- source:
--   Wang, Wu, Tang & Dai, Endogenous merger decisions among competitors: impact of limited capacity and loyal segments, Management Science (2024), accepted manuscript, PDF p. 19, Proposition 3; proof Appendix H, PDF pp. 48–49

import Mathlib
import Definitions.Def_EndogMerger_SymLoyal_Setting

namespace EndogMerger.SymLoyal
theorem proposition_3 (α k r : ℝ) (hα0 : 0 < α) (hα3 : α < 1 / 3) (hαk : α < k) (hk1 : k < 1)
    (hr : 0 < r) :
    (kStar α < k ∧ k < 1 - 2 * α →
      {S | IsEquilibriumStructure α k r S} = {MarketStructure.mixed}) ∧
    (¬ (kStar α < k ∧ k < 1 - 2 * α) →
      {S | IsEquilibriumStructure α k r S} = {MarketStructure.indep}) := by sorry
end EndogMerger.SymLoyal
