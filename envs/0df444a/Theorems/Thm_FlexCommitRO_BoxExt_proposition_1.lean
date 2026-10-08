-- Prove2me | Theorems.Thm_FlexCommitRO_BoxExt_proposition_1
-- name    : FlexCommitRO.BoxExt.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:01:02.012101+00:00
-- url     : https://prove2.me/theorems/ec30824f-e240-4415-8595-b9853eae8ead
-- title:
--   Proposition 1, p. 269 — the min-max RSFC problem over the demand box and over its 2^T extreme trajectories have the same optimal value
-- statement:
--   Consider the min-max retailer–supplier flexible commitments problem (5)–(6) over $T$ periods, with arbitrary real costs, penalties, salvage value, initial inventory and previous commitment, and order and cumulative-order bounds in $[-\infty, +\infty]$. Let the demand uncertainty be the box (9)–(10),
--   $$
--   \mathcal U_{\text{box}} = [d_1^{\min}, d_1^{\max}] \times \dots \times [d_T^{\min}, d_T^{\max}],\qquad d_t^{\min} < d_t^{\max}.
--   $$
--   Let $(P)$ be problem (5) over $\mathcal U_{\text{box}}$ and $(P_+)$ the same problem over the finite set of its extreme points $\operatorname{ext}(\mathcal U_{\text{box}}) = \{d_1^{\min}, d_1^{\max}\} \times \dots \times \{d_T^{\min}, d_T^{\max}\}$, with decision rules nonanticipative on the respective uncertainty set. Then the optimal values agree:
--   $$
--   \operatorname{opt}(P) = \operatorname{opt}(P_+).
--   $$
--
--   This is what makes the box case of the min-max RSFC problem directly solvable: only the $2^T$ extreme demand trajectories need to be considered (§2.3, problem $P_{\text{ext}}$).
--
--   **Formalization Note** Optimal values are extended reals ($+\infty$ if infeasible, possibly $-\infty$). Lean periods are 0-based (`Fin T`). $\operatorname{ext}(\mathcal U_t)$ is written as the pair $\{d_t^{\min}, d_t^{\max}\}$, justified by the milestone on extreme points of a segment. Decision rules $q_t, y_t, u_t$ depend on $d^{t-1}$ and $x_{t+1}$ on $d^t$, as in (5)–(6). The standing assumptions $s < c_T$ and $h_T - s \ge -p_T$ of §2.2 are not imposed (Proposition 1 does not use them), and no sign is assumed on any cost or penalty.
-- source:
--   Ben-Tal, Golany, Nemirovski & Vial, Retailer-supplier flexible commitments contracts: a robust optimization approach, MSOM 7(3) (2005), p. 269, Appendix, Proposition 1; problem (5)–(6) p. 254; box (9)–(10) p. 255

import Mathlib
import Definitions.Def_FlexCommitRO_BoxExt_Setting

namespace FlexCommitRO.BoxExt

theorem proposition_1 {T : ℕ} (D : RSFCData T) (dmin dmax : Fin T → ℝ)
    (hlt : ∀ t, dmin t < dmax t) :
    value D (fun t => Set.Icc (dmin t) (dmax t)) =
      value D (fun t => ({dmin t, dmax t} : Set ℝ)) := by sorry

end FlexCommitRO.BoxExt
