-- Prove2me | Theorems.Thm_BarvinokCount_ShortFormula_isPrimitive_iff_coneIndex_eq_one
-- name    : BarvinokCount.ShortFormula.isPrimitive_iff_coneIndex_eq_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T06:11:25.147436+00:00
-- url     : https://prove2.me/theorems/aba483dd-3e85-4957-8f89-a0f4e554b2e4
-- title:
--   §5, p. 774 — a simple cone is given by primitive generators if and only if Ind K = 1
-- statement:
--   Let $u_1,\dots,u_k\in\mathbb{Z}^d$ be linearly independent and $K=\operatorname{co}\{u_1,\dots,u_k\}$. Then $u_1,\dots,u_k$ are primitive generators of $K$ (a basis of the lattice $\mathbb{Z}^d\cap\operatorname{Lin}K$) if and only if
--   $$\operatorname{Ind}K=1,$$
--   i.e. the semi-open parallelepiped of the generators contains no integral point other than the origin.
--
--   This is the stopping criterion of the decomposition in Theorem 5.4: once the index has dropped below $2$, every cone is primitive.
-- source:
--   Barvinok, A polynomial time algorithm for counting integral points in polyhedra when the dimension is fixed, Math. Oper. Res. 19 (1994), p. 774, §5, first sentence after Definition 5.1 (unnumbered)

import Mathlib
import Definitions.Def_BarvinokCount_ShortFormula_coneIndex

namespace BarvinokCount.ShortFormula

theorem isPrimitive_iff_coneIndex_eq_one {d k : ℕ} (u : Fin k → Fin d → ℤ)
    (hu : IsSimpleGens u) :
    IsPrimitiveGens u ↔ coneIndex u = 1 := by sorry

end BarvinokCount.ShortFormula
