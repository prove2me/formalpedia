-- Prove2me | Theorems.Thm_ChoicePAC_MidPoint_perturbation_unique_optimum
-- name    : ChoicePAC.MidPoint.perturbation_unique_optimum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:30:09.055785+00:00
-- url     : https://prove2.me/theorems/f74ca794-17cb-4e99-b1c6-0ac3322d925d
-- title:
--   App. B.2, p. 333 — $Y_\Delta = Y - H\Delta_B$ is the unique optimum of DLP$[C-\Delta,\lambda]$
-- statement:
--   Consider a valid instance satisfying Assumptions 2.1 and 2.2, let $Y$ be the optimal solution of $\mathrm{DLP}[C,\lambda]$, and let $\Delta \in \mathbb R^m$. Define $Y_\Delta$ by $Y_{\Delta,j} = Y_j$ for $j \in J_\lambda \cup J_0$ and
--   $$Y_{\Delta,y} = Y_y - W^{-1}\begin{bmatrix}\Delta_B\\ 0\end{bmatrix} = Y_y - H\Delta_B .$$
--   If the feasibility conditions
--   $$\begin{bmatrix}\bar A_N\\ P_N\end{bmatrix}Y_\Delta < \begin{bmatrix}C_N - \Delta_N\\ \lambda_N\end{bmatrix} \quad\text{and}\quad Y_{\Delta,y} > 0$$
--   hold (componentwise; $N$ denotes the nonbinding resources and types at $Y$), then $Y_\Delta$ is the unique optimal solution of $\mathrm{DLP}[C-\Delta,\lambda]$.
--
--   This is how the paper tracks the re-solved DLP solution of PAC when the remaining capacity deviates from its fluid path.
--
--   **Formalization Note** The page motivates the claim for "sufficiently small" $\Delta$, but the claim is made under the displayed conditions, so Lean takes every $\Delta$ satisfying them. The standing hypotheses (`IsValid`) are the disclosed reading of Sec. 2.1, p. 315, Sec. 2.3, p. 317 and Sec. 5.2, p. 327: printed are $\lambda_q \ge 0$, bounded nonnegative consumption and $r_j(0)=0$; read in are $C \ge 0$, consumption laws that are probability measures, $A_{ij} \le \xi_j$ almost surely (the page writes $\xi_j \ge A_{ij}$ on p. 317 and $A_{ij} < \xi_j$ on p. 327; the weaker $\le$ is used), measurable revenue functions, and revenue that is nonnegative and bounded by a common constant (implicit on the page, needed in App. C.4).
-- source:
--   Jasin, Kumar, A Re-Solving Heuristic with Bounded Revenue Loss for Network Revenue Management with Customer Choice, Math. Oper. Res. 37(2), 2012, App. B.2, p. 333, display 'Y_Δ is the unique optimal solution to DLP[C − Δ, λ]'

import Mathlib
import Definitions.Def_ChoicePAC_MidPoint_Model
import Definitions.Def_ChoicePAC_MidPoint_Assumptions

namespace ChoicePAC.MidPoint
open Matrix in
theorem perturbation_unique_optimum {NT n m : ℕ} (I : Instance NT n m) (hI : I.IsValid)
    (h21 : I.Assumption21) (h22 : I.Assumption22) (Y : Fin n → ℝ)
    (hY : I.IsDLPOptimal I.C I.lam Y) (Δ : Fin m → ℝ)
    (hA_N : ∀ i, i ∉ I.BA Y → (I.Abar *ᵥ I.Ypert Y Δ) i < I.C i - Δ i)
    (hP_N : ∀ q, q ∉ I.BP Y → (I.P *ᵥ I.Ypert Y Δ) q < I.lam q)
    (hy_pos : ∀ j ∈ I.Jy Y, 0 < I.Ypert Y Δ j) :
    I.IsDLPOptimal (I.C - Δ) I.lam (I.Ypert Y Δ) ∧
      ∀ x, I.IsDLPOptimal (I.C - Δ) I.lam x → x = I.Ypert Y Δ := by sorry
end ChoicePAC.MidPoint
