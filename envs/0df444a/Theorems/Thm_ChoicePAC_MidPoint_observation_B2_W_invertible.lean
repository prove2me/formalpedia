-- Prove2me | Theorems.Thm_ChoicePAC_MidPoint_observation_B2_W_invertible
-- name    : ChoicePAC.MidPoint.observation_B2_W_invertible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:30:01.825213+00:00
-- url     : https://prove2.me/theorems/09590fa6-94b9-4d1c-b820-55ed43169256
-- title:
--   Observation B.2 — $W$ is a square invertible matrix
-- statement:
--   Consider a valid instance satisfying Assumptions 2.1 and 2.2, and let $Y$ be the optimal solution of $\mathrm{DLP}[C,\lambda]$. The augmented matrix
--   $$W = \begin{bmatrix}\bar A_{B,y}\\ P_{B_2,y}\end{bmatrix}$$
--   (rows: the binding resources $B_A$ and the binding types $B_2$ without an offer in $J_\lambda$; columns: $J_y$) is square, $|B_A| + |B_2| = |J_y|$, and invertible.
--
--   Invertibility of $W$ is what lets the optimal solution follow a perturbation of the capacity linearly (App. B.2).
--
--   **Formalization Note** "Square" is stated as equality of the cardinalities of the row and column index types, "invertible" as bijectivity of $x \mapsto Wx$. The standing hypotheses (`IsValid`) are the disclosed reading of Sec. 2.1, p. 315, Sec. 2.3, p. 317 and Sec. 5.2, p. 327: printed are $\lambda_q \ge 0$, bounded nonnegative consumption and $r_j(0)=0$; read in are $C \ge 0$, consumption laws that are probability measures, $A_{ij} \le \xi_j$ almost surely (the page writes $\xi_j \ge A_{ij}$ on p. 317 and $A_{ij} < \xi_j$ on p. 327; the weaker $\le$ is used), measurable revenue functions, and revenue that is nonnegative and bounded by a common constant (implicit on the page, needed in App. C.4).
-- source:
--   Jasin, Kumar, A Re-Solving Heuristic with Bounded Revenue Loss for Network Revenue Management with Customer Choice, Math. Oper. Res. 37(2), 2012, App. B.1, p. 333, Observation B.2

import Mathlib
import Definitions.Def_ChoicePAC_MidPoint_Model
import Definitions.Def_ChoicePAC_MidPoint_Assumptions

namespace ChoicePAC.MidPoint
theorem observation_B2_W_invertible {NT n m : ℕ} (I : Instance NT n m) (hI : I.IsValid)
    (h21 : I.Assumption21) (h22 : I.Assumption22) (Y : Fin n → ℝ)
    (hY : I.IsDLPOptimal I.C I.lam Y) :
    Fintype.card (↥(I.BA Y) ⊕ ↥(I.B2 Y)) = Fintype.card ↥(I.Jy Y) ∧
      Function.Bijective (I.Wmat Y).mulVec := by sorry
end ChoicePAC.MidPoint
