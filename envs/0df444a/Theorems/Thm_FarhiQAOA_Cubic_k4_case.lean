-- Prove2me | Theorems.Thm_FarhiQAOA_Cubic_k4_case
-- name    : FarhiQAOA.Cubic.k4_case
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:30:43.764761+00:00
-- url     : https://prove2.me/theorems/6aec59e5-5237-437a-a680-1196487fcd63
-- title:
--   Section V, p. 8 — on K₄ the p = 1 QAOA ratio exceeds 0.6924
-- statement:
--   Let $G$ be a 3-regular graph on 4 vertices, that is, the complete graph $K_4$. Then there exist angles $\gamma\in[0,2\pi]$ and $\beta\in[0,\pi]$ such that, for every bit string $z$,
--   $$0.6924\; C(z) < F_1(\gamma,\beta),$$
--   where $C(z)$ is the number of edges of $K_4$ cut by $z$ and $F_1$ is the $p=1$ expected cut. In particular the $p=1$ approximation ratio on $K_4$ is higher than $0.6924$.
--
--   $K_4$ is the special case of p. 8 in which "the two edges that leave the crossed square are in fact the same edge"; it is the only connected 3-regular graph to which (32) does not apply, and this statement covers it separately.
--
--   **Formalization Note** The page calls this graph "a 4 vertex disconnected 3-regular graph"; it means the 3-regular graph on 4 vertices, $K_4$, which is connected and has no further vertices. The inequality is strict, for "higher than".
-- source:
--   Farhi, Goldstone, Gutmann, A Quantum Approximate Optimization Algorithm, arXiv:1411.4028v1, p. 8, Section V, after figure (31)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Adiabatic
import Definitions.Def_FarhiQAOA_Cubic_Types

namespace FarhiQAOA.Cubic

open QAlgorithms

/-- Farhi–Goldstone–Gutmann, Section V, p. 8: for the 3-regular graph on 4 vertices (`K₄`), at `p = 1`
the approximation ratio is higher than `0.6924`: there are angles `γ ∈ [0, 2π]`, `β ∈ [0, π]` at
which `F₁(γ, β)` strictly exceeds `0.6924` times the size of every cut. -/
theorem k4_case (G : SimpleGraph (Fin 4)) [DecidableRel G.Adj] (h3 : G.IsRegularOfDegree 3) :
    ∃ γ β : ℝ, γ ∈ Set.Icc 0 (2 * Real.pi) ∧ β ∈ Set.Icc 0 Real.pi ∧
      ∀ z : Qubits 4, (1731 / 2500 : ℝ) * cutValue G z < F1 G γ β := by sorry

end FarhiQAOA.Cubic
