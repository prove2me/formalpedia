-- Prove2me | Theorems.Thm_CommonAgencyVCG_Algorithmic_proposition_4
-- name    : CommonAgencyVCG.Algorithmic.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:23:36.216007+00:00
-- url     : https://prove2.me/theorems/547f08ae-85f7-4f35-8f22-f32a2bad3527
-- title:
--   Proposition 4, p. 18 — LP2 attains its optimum, and its value is k_{a*(b)}
-- statement:
--   Fix a common agency setting satisfying the standing assumptions, and let $b\in\mathcal V$. The linear program
--   $$\min_{w\in\mathbb R^m} F_{|a^*(b)}\cdot w \quad\text{s.t.}\quad F_{|a_j}\cdot w - \psi(a_j) \le F_{|a^*(b)}\cdot w - \psi(a^*(b))\ \ \forall j,\qquad w_k\ge 0\ \ \forall k \tag{LP2}$$
--   has an optimal solution, and its optimal value is $k_{a^*(b)}$: there is $w\in\mathcal L_{a^*(b)}$ with $\mathbb E_{o\sim F_{|a^*(b)}}[w(o)] = k_{a^*(b)}$.
--
--   This provides the vector $w^b$ used in line 4 of Algorithm 1.
--
--   **Formalization Note** The feasible region of LP2 is exactly $\mathcal L_{a^*(b)}$. The proposition's polynomial-time claim is a complexity statement and is not formalized; only the attainment of the minimum, which the construction needs, is stated.
-- source:
--   Alon, Lavi, Shamash, Talgam-Cohen, Incomplete Information VCG Contracts for Common Agency, arXiv:2105.14998v1, p. 18, Proposition 4 (LP2)

import Mathlib
import Definitions.Def_CommonAgencyVCG_Algorithmic_Setting
import Definitions.Def_CommonAgencyVCG_Algorithmic_Alg1

namespace CommonAgencyVCG.Algorithmic

variable {n : ℕ} {A O : Type} [Fintype A] [Nonempty A] [Fintype O]

/-- Proposition 4, p. 18 (mathematical content): LP2 — minimize `F|a*(b) · w` subject to
`F|a_j · w − ψ(a_j) ≤ F|a*(b) · w − ψ(a*(b))` for all `j` and `w ≥ 0` — has an optimal solution, and
its optimal value is `k_{a*(b)}`. -/
theorem proposition_4 (S : Setting n A O) (hS : S.Standing) (b : Fin n → O → ℝ) (hb : InDom S b) :
    ∃ w ∈ implSet S (aStar S b), E S (aStar S b) w = kCost S (aStar S b) := by sorry

end CommonAgencyVCG.Algorithmic
