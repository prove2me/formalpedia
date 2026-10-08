-- Prove2me | Theorems.Thm_ClarkeWright64_Savings_link_saving
-- name    : ClarkeWright64.Savings.link_saving
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T05:54:37.830631+00:00
-- url     : https://prove2.me/theorems/d5369f34-b124-404d-9f57-9c5ba654cda2
-- title:
--   Theoretical aspects, pp. 571–572 — linking cell (y:z) saves exactly d_{0,y} + d_{0,z} − d_{y,z}
-- statement:
--   Let the distances be symmetric, $d_{y,z}=d_{z,y}$. Let $S$ be a state that the savings procedure reaches from the initial basic solution, and let $(y:z)$ be an admissible cell of $S$ (conditions (I)–(III)). If $S'$ is the state obtained by linking $P_y$ and $P_z$, then
--   $$
--   \text{mileage}(S') = \text{mileage}(S) - \bigl(d_{0,y}+d_{0,z}-d_{y,z}\bigr).
--   $$
--
--   Since $P_y$ and $P_z$ are both linked to the depot, linking them severs only their links to $P_0$; this is why the cell value of the half matrix is the distance saved by the link.
--
--   **Formalization Note** Symmetry of $d$ is the paper's half matrix (p. 573); it is needed because a run may be reversed to bring $P_y$ to its end.
-- source:
--   Clarke & Wright, Scheduling of vehicles from a central depot to a number of delivery points, Oper. Res. 12 (1964), pp. 571–572, Theoretical aspects; p. 573 (cell values)

import Mathlib
import Definitions.Def_SupplyChainTheory_vrp
import Definitions.Def_ClarkeWright64_Savings_Instance
import Definitions.Def_ClarkeWright64_Savings_Procedure

namespace ClarkeWright64.Savings

/-- Clarke & Wright (1964), Theoretical aspects, pp. 571–572: linking an admissible cell `(y:z)`
of a state reached by the procedure lowers the total mileage by exactly the saving
`d_{0,y} + d_{0,z} − d_{y,z}`, for symmetric distances. -/
theorem link_saving {M n : ℕ} (I : Instance M n) (hsymm : ∀ i j, I.d i j = I.d j i)
    (s : State M) (hs : Reachable I s) (y z : Fin (M + 1)) (hyz : Admissible I s y z) :
    I.mileage (link s y z) = I.mileage s - I.saving y z := by sorry

end ClarkeWright64.Savings
