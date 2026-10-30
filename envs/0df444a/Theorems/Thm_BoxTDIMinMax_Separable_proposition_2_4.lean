-- Prove2me | Theorems.Thm_BoxTDIMinMax_Separable_proposition_2_4
-- name    : BoxTDIMinMax.Separable.proposition_2_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:06:28.841257+00:00
-- url     : https://prove2.me/theorems/cf1a2a07-04be-4800-a8b8-f33fe62b7f00
-- title:
--   Proposition 2.4, p. 8 — negating some columns of Q preserves box-TDI
-- statement:
--   Let $Q\in\mathbb Z^{I\times S}$ and $p\in\mathbb Z^I$ with $Qx\ge p$ box-TDI, and let $T\subseteq S$. Let $Q'$ be obtained from $Q$ by negating the columns indexed by $T$:
--   $$Q'_{is}=\begin{cases}-Q_{is}& s\in T,\\ Q_{is}& s\notin T.\end{cases}$$
--   Then the system $Q'x'\ge p$ is also box-TDI.
--
--   Used in Proposition 2.10 to pass from $Qx_2+Qx_1\ge p_0$ to $Qx_2-Qx_1\ge p_0$.
-- source:
--   Frank, Murota, A Discrete Convex Min-Max Formula for Box-TDI Polyhedra, arXiv:2007.03507v3, p. 8, Proposition 2.4

import Mathlib
import Definitions.Def_BoxTDIMinMax_Separable_Setting

namespace BoxTDIMinMax.Separable

open Matrix

/-- Proposition 2.4, p. 8: negating the columns of `Q` indexed by `T ⊆ S` preserves box-TDI-ness of
`Q x ≥ p`. -/
theorem proposition_2_4 {ι S : Type*} [Fintype ι] [Fintype S] [DecidableEq S]
    (Q : Matrix ι S ℤ) (p : ι → ℤ) (hbox : IsBoxTDI (ratMat Q) (ratVec p))
    (T : Finset S) :
    IsBoxTDI (ratMat (Matrix.of fun i s => if s ∈ T then -Q i s else Q i s)) (ratVec p) := by sorry

end BoxTDIMinMax.Separable
