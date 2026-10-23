-- Prove2me | Theorems.Thm_BoxTDIMinMax_Separable_proposition_2_6
-- name    : BoxTDIMinMax.Separable.proposition_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:06:41.39885+00:00
-- url     : https://prove2.me/theorems/cbb07698-32ce-4e3a-ae20-a44c6abebf3c
-- title:
--   Proposition 2.6, p. 9 — duplicating some columns of Q preserves box-TDI (Edmonds–Giles)
-- statement:
--   Let $Q\in\mathbb Z^{I\times S}$ and $p\in\mathbb Z^I$ with $Qx\ge p$ box-TDI. Let $S'$ be a finite set and $\pi:S'\to S$ a surjection, and let $Q'\in\mathbb Z^{I\times S'}$ have column $s'$ equal to column $\pi(s')$ of $Q$. Then the system
--   $$Q'x'\ge p$$
--   is also box-TDI.
--
--   The matrix $Q'$ contains every column of $Q$, some of them several times. The paper cites this from Edmonds and Giles; it is used in Proposition 2.10 with $S'=S\sqcup S$.
--
--   **Formalization Note** "Duplicating some columns" is encoded by an arbitrary surjection $\pi$, which also allows reordering columns; reordering trivially preserves box-TDI-ness.
-- source:
--   Frank, Murota, A Discrete Convex Min-Max Formula for Box-TDI Polyhedra, arXiv:2007.03507v3, p. 9, Proposition 2.6 (citing Edmonds–Giles [11])

import Mathlib
import Definitions.Def_BoxTDIMinMax_Separable_Setting

namespace BoxTDIMinMax.Separable

open Matrix

/-- Proposition 2.6, p. 9 (Edmonds–Giles): duplicating columns preserves box-TDI-ness. The new
column set is `S'` with a surjection `π : S' → S`; column `s'` of `Q'` is column `π s'` of `Q`, so
every column of `Q` is kept and some may appear several times. -/
theorem proposition_2_6 {ι S S' : Type*} [Fintype ι] [Fintype S] [DecidableEq S]
    [Fintype S'] [DecidableEq S']
    (Q : Matrix ι S ℤ) (p : ι → ℤ) (hbox : IsBoxTDI (ratMat Q) (ratVec p))
    (π : S' → S) (hπ : Function.Surjective π) :
    IsBoxTDI (ratMat (Q.submatrix id π)) (ratVec p) := by sorry

end BoxTDIMinMax.Separable
