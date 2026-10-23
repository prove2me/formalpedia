-- Prove2me | Theorems.Thm_BoxTDIMinMax_Separable_proposition_2_10
-- name    : BoxTDIMinMax.Separable.proposition_2_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:06:37.504855+00:00
-- url     : https://prove2.me/theorems/8eff1dc5-cdb1-4f89-b8ac-1afbefc656f3
-- title:
--   Proposition 2.10, p. 10 — the system (2.8) [(x₁, x₂) ≥ 0, Qx₂ − Qx₁ ≥ p₀] is box-TDI
-- statement:
--   Let $Q\in\mathbb Z^{I\times S}$, $p\in\mathbb Z^I$ with $Qx\ge p$ box-TDI, let $z^*\in\ddot R$ and $p_0:=p-Qz^*$. Then the system
--   $$[(x_1,x_2)\ge 0,\ Qx_2-Qx_1\ge p_0] \qquad (2.8)$$
--   in the variables $(x_1,x_2)\in\mathbb R^S\times\mathbb R^S$ is box-TDI.
--
--   This is the linear system of the auxiliary program (2.11) in the proof of Theorem 2.12. By a remark of the paper (Remark 2.1), it fails if box-TDI is weakened to TDI.
--
--   **Formalization Note** The columns are $S\sqcup S$ ($x_1$ first); the rows are the $2|S|$ nonnegativity rows followed by the rows $-Qx_1+Qx_2\ge p_0$.
-- source:
--   Frank, Murota, A Discrete Convex Min-Max Formula for Box-TDI Polyhedra, arXiv:2007.03507v3, p. 10, Proposition 2.10, (2.8)

import Mathlib
import Definitions.Def_BoxTDIMinMax_Separable_Setting

namespace BoxTDIMinMax.Separable

open Matrix

/-- Proposition 2.10, p. 10: if `Q x ≥ p` is box-TDI, `z* ∈ R̈` and `p₀ := p - Q z*`, then the
system (2.8) `[(x₁, x₂) ≥ 0, Q x₂ - Q x₁ ≥ p₀]` is box-TDI. -/
theorem proposition_2_10 {ι S : Type*} [Fintype ι] [Fintype S] [DecidableEq S]
    (Q : Matrix ι S ℤ) (p : ι → ℤ) (hbox : IsBoxTDI (ratMat Q) (ratVec p))
    (zStar : S → ℤ) (hz : zStar ∈ intPts Q p) :
    IsBoxTDI (auxMat Q) (auxRhs Q p zStar) := by sorry

end BoxTDIMinMax.Separable
