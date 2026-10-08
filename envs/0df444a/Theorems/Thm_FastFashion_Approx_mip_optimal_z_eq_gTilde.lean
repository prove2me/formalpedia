-- Prove2me | Theorems.Thm_FastFashion_Approx_mip_optimal_z_eq_gTilde
-- name    : FastFashion.Approx.mip_optimal_z_eq_gTilde
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:16:42.11185+00:00
-- url     : https://prove2.me/theorems/766ccd2a-b9ca-4771-b45b-d457842f815f
-- title:
--   §3.2, p. 16 — in any optimal solution of (MIP), $z_j = \tilde g_{\lambda_j}(x_j + I_j)$
-- statement:
--   Consider the program (MIP) (13)–(19) with a finite set of stores $J$, unit selling prices $P_j > 0$, any warehouse value $K$, warehouse inventory $W_s \in \mathbb N$, store inventory $I_{sj} \in \mathbb N$, rates $\lambda_{sj} > 0$, period $T > 0$, a nonempty set of major sizes $\mathcal S^+$, and nonempty finite tangent index sets $\mathcal N(\lambda_{sj}) \subseteq \mathbb N\cup\{\infty\}$. Then in every optimal solution $(x, z, y, v)$ of (MIP), for every store $j$,
--   $$z_j = \tilde g_{\lambda_j}(x_j + I_j),$$
--   where $\lambda_j = (\lambda_{sj})_{s\in\mathcal S}$, $x_j + I_j = (x_{sj} + I_{sj})_{s \in \mathcal S}$, and $\tilde g$ is the approximation (8) with the tangent sets $\mathcal N(\lambda_{sj})$.
--
--   The statement says that the MIP's sales variables represent the approximate expected sales exactly, so that (MIP) maximizes $\sum_j P_j \tilde g_{\lambda_j}(x_j + I_j)$ plus the warehouse value.
--
--   **Formalization Note** The hypothesis $P_j > 0$ is added: the paper's $P_j$ is a unit selling price, and for $P_j = 0$ the variable $z_j$ is not pushed to its bound. The statement is conditional on optimality; the existence of an optimal solution is not asserted. The claim is deterministic and uses the same $\tilde g$ as the goal theorem.
-- source:
--   Caro & Gallien, Inventory Management of a Fast-Fashion Retail Network, working paper (August 2, 2007), p. 16, §3.2, claim after (MIP); program (13)–(19) on p. 15

import Mathlib
import Definitions.Def_FastFashion_Approx_Tangents
import Definitions.Def_FastFashion_Approx_MIP

namespace FastFashion.Approx

/-- §3.2 (Caro–Gallien, p. 16): in any optimal solution of (MIP) (13)–(19), the variable `z_j`
equals the approximate expected sales `g̃_{λ_j}(x_j + I_j)` of (8) at store `j`, for every store. -/
theorem mip_optimal_z_eq_gTilde {S J : Type*} [Fintype S] [DecidableEq S] [Fintype J]
    (P : J → ℝ) (hP : ∀ j, 0 < P j) (K : ℝ) (lam : S → J → ℝ) (hlam : ∀ s j, 0 < lam s j)
    (T : ℝ) (hT : 0 < T) (Sp : Finset S) (hSp : Sp.Nonempty)
    (Nset : S → J → Finset (WithTop ℕ)) (hNset : ∀ s j, (Nset s j).Nonempty)
    (W : S → ℕ) (I : S → J → ℕ) (sol : MIPSol S J)
    (hopt : MIPOptimal P K lam T Sp Nset W I sol) :
    ∀ j, sol.z j = gTilde (fun s => lam s j) T Sp hSp (fun s => Nset s j) (fun s => hNset s j)
      (fun s => I s j + sol.x s j) := by sorry

end FastFashion.Approx
