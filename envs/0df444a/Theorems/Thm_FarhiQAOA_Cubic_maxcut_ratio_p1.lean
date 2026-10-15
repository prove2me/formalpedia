-- Prove2me | Theorems.Thm_FarhiQAOA_Cubic_maxcut_ratio_p1
-- name    : FarhiQAOA.Cubic.maxcut_ratio_p1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T02:30:42.464732+00:00
-- url     : https://prove2.me/theorems/7983c059-1830-4395-9613-f73ea9c82b7f
-- title:
--   Section V, pp. 8–10 — at p = 1 the QAOA's expected cut is ≥ 0.6924 · max cut on every connected 3-regular graph
-- statement:
--   Let $G$ be a connected 3-regular graph on $n$ vertices, and let $C(z)$ be the number of edges cut by the bit string $z$. Let $F_1(\gamma,\beta) = \langle\gamma,\beta|\,C\,|\gamma,\beta\rangle$ be the expected cut of the $p=1$ QAOA state $|\gamma,\beta\rangle = e^{-i\beta B}e^{-i\gamma C}|s\rangle$. Then there exist angles $\gamma\in[0,2\pi]$ and $\beta\in[0,\pi]$ such that
--   $$F_1(\gamma,\beta) \;\ge\; 0.6924\cdot C(z)\qquad\text{for every } z,$$
--   that is, $M_1 = \max_{\gamma,\beta} F_1(\gamma,\beta) \ge 0.6924\cdot\max_z C(z)$.
--
--   This is the main result of §V and of the abstract: "For $p = 1$, on 3-regular graphs the quantum algorithm always finds a cut that is at least $0.6924$ times the size of the optimal cut." The bound applies to every connected cubic graph, $K_4$ included, uniformly in $n$, for a circuit of depth independent of $n$.
--
--   **Formalization Note** What is formalized is the bound on the expectation $F_1$ at good angles, which is the quantity the paper's argument (32)–(35) controls. Turning it into a cut actually found by measuring $|\gamma,\beta\rangle$ and repeating ("order $n\log n$ repetitions", p. 9) is not part of the statement. $F_1$ is $\sum_z\Pr[z]\,C(z)$, equal to $\langle\gamma,\beta|C|\gamma,\beta\rangle$ because $C$ is diagonal. The constant is exactly $0.6924 = 1731/2500$. The angle ranges are those of pp. 2–3; requiring the angles in these ranges makes the existential statement stronger.
-- source:
--   Farhi, Goldstone, Gutmann, A Quantum Approximate Optimization Algorithm, arXiv:1411.4028v1, pp. 8–10, Section V (also abstract, p. 1)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Adiabatic
import Definitions.Def_FarhiQAOA_Cubic_Types

namespace FarhiQAOA.Cubic

open QAlgorithms

/-- Farhi–Goldstone–Gutmann, Section V, pp. 8–10 (and the abstract, p. 1): for `p = 1`, on every
connected 3-regular graph there are angles `γ ∈ [0, 2π]`, `β ∈ [0, π]` at which the expected cut
`F₁(γ, β)` of the QAOA state is at least `0.6924` times the size of every cut, hence at least
`0.6924` times the maximum cut: `M₁ ≥ 0.6924 · max_z C(z)`. -/
theorem maxcut_ratio_p1 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h3 : G.IsRegularOfDegree 3) (hconn : G.Connected) :
    ∃ γ β : ℝ, γ ∈ Set.Icc 0 (2 * Real.pi) ∧ β ∈ Set.Icc 0 Real.pi ∧
      ∀ z : Qubits n, (1731 / 2500 : ℝ) * cutValue G z ≤ F1 G γ β := by sorry

end FarhiQAOA.Cubic
