-- Prove2me | Theorems.Thm_BeckTeboulleMD_EMDA_proposition_5_1_c
-- name    : BeckTeboulleMD.EMDA.proposition_5_1_c
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T05:54:19.355437+00:00
-- url     : https://prove2.me/theorems/135c4929-35bf-43a3-8aeb-37bcbbc94a74
-- title:
--   Proposition 5.1(c), p. 173 — for x¹ = n⁻¹e and ψ = ψ_e, B_ψ(x*, x¹) ≤ ln n for all x* ∈ Δ
-- statement:
--   Let $\psi_e(x) = \sum_{j=1}^n x_j \ln x_j$ and let $x^1 = n^{-1}e = (1/n, \dots, 1/n)$ be the barycentre of the unit simplex $\Delta$. Then
--   $$B_{\psi_e}(x^*, x^1) \le \ln n \qquad \text{for all } x^* \in \Delta.$$
--
--   This bounds the initial distance in Theorem 4.2 independently of the unknown optimum, and is the source of the $\sqrt{\ln n}$ factor in Theorem 5.1.
--
--   **Formalization Note** $B_{\psi_e}$ is the general distance-like function (3.10) applied to $\psi_e$ on $\mathbb R^n$, with the Fréchet derivative of $\psi_e$ at $x^1$. For $n = 0$ the simplex is empty and the statement is vacuous.
-- source:
--   Beck & Teboulle, Mirror descent and nonlinear projected subgradient methods for convex optimization, Oper. Res. Lett. 31 (2003), p. 173, Proposition 5.1(c); proof p. 174

import Mathlib
import Definitions.Def_BeckTeboulleMD_EMDA_Setting

namespace BeckTeboulleMD.EMDA

/-- Proposition 5.1(c), p. 173 (proof p. 174): for `x¹ = n⁻¹e` and `ψ = ψ_e`,
`B_ψ(x*, x¹) ≤ ln n` for every `x* ∈ Δ`. -/
theorem proposition_5_1_c {n : ℕ} :
    ∀ xstar ∈ stdSimplex ℝ (Fin n),
      bregman (entropy (n := n)) xstar (fun _ => 1 / (n : ℝ)) ≤ Real.log n := by sorry

end BeckTeboulleMD.EMDA
