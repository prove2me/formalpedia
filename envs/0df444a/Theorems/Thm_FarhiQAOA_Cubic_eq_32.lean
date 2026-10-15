-- Prove2me | Theorems.Thm_FarhiQAOA_Cubic_eq_32
-- name    : FarhiQAOA.Cubic.eq_32
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:30:50.1869+00:00
-- url     : https://prove2.me/theorems/22764822-3a95-49f0-b24c-d2c209f52c74
-- title:
--   Section V, (32), p. 9 — F₁ = S f_g4 + (4S+3T) f_g5 + (3n/2 − 5S − 3T) f_g6
-- statement:
--   Let $G$ be a connected 3-regular graph on $n\neq 4$ vertices with $S$ crossed squares and $T$ isolated triangles. For all angles $\gamma,\beta\in\mathbb R$, the $p=1$ expected cut satisfies
--   $$F_1(\gamma,\beta) = S\,f_{g_4}(\gamma,\beta) + (4S+3T)\,f_{g_5}(\gamma,\beta) + \Big(\frac{3n}{2} - 5S - 3T\Big) f_{g_6}(\gamma,\beta).$$
--
--   Here $f_{g_4}, f_{g_5}, f_{g_6}$ are the edge functions of the three subgraph types of figure (18). The identity reduces $F_1$ on an arbitrary connected cubic graph to three fixed functions of two angles, weighted by $n$, $S$ and $T$ alone; this is what lets the maximum $M_1(n,S,T)$ of (33) be computed classically and the worst case be found by minimizing over $(S/n, T/n)$.
--
--   **Formalization Note** $F_1$ is $\sum_z \Pr[z]\,C(z)$ for the $p=1$ QAOA state, which equals $\langle\gamma,\beta|C|\gamma,\beta\rangle$ because $C$ is diagonal. The hypotheses "connected" and $n\neq 4$ exclude $K_4$, the paper's special case; for $K_4$ the identity fails ($F_1 = 6 f_{g_4}$ there while $S=T=0$).
-- source:
--   Farhi, Goldstone, Gutmann, A Quantum Approximate Optimization Algorithm, arXiv:1411.4028v1, p. 9, Section V, (32)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Adiabatic
import Definitions.Def_FarhiQAOA_Cubic_Types

namespace FarhiQAOA.Cubic

open QAlgorithms

/-- Farhi–Goldstone–Gutmann, Section V, p. 9, (32): on a connected 3-regular graph with `n ≠ 4`
vertices, `S` crossed squares and `T` isolated triangles,
`F₁(γ, β) = S f_{g₄}(γ, β) + (4S + 3T) f_{g₅}(γ, β) + (3n/2 − 5S − 3T) f_{g₆}(γ, β)`. -/
theorem eq_32 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3) (hconn : G.Connected) (hn4 : n ≠ 4) (γ β : ℝ) :
    F1 G γ β = (S G : ℝ) * fg4 γ β + (4 * (S G : ℝ) + 3 * (T G : ℝ)) * fg5 γ β +
      ((3 : ℝ) / 2 * (n : ℝ) - 5 * (S G : ℝ) - 3 * (T G : ℝ)) * fg6 γ β := by sorry

end FarhiQAOA.Cubic
