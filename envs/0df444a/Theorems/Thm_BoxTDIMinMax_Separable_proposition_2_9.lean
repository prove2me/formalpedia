-- Prove2me | Theorems.Thm_BoxTDIMinMax_Separable_proposition_2_9
-- name    : BoxTDIMinMax.Separable.proposition_2_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:06:43.252976+00:00
-- url     : https://prove2.me/theorems/9f3f08a5-d911-498a-a4dd-eae40382955a
-- title:
--   Proposition 2.9, p. 9 — [Qx ≥ p, f′ ≤ x ≤ g′] is box-TDI and TDI for bounds with infinite entries
-- statement:
--   Let $Q\in\mathbb Z^{I\times S}$, $p\in\mathbb Z^I$ with $Qx\ge p$ box-TDI. Let $f':S\to\mathbb Q\cup\{-\infty\}$ and $g':S\to\mathbb Q\cup\{+\infty\}$ be rational bounding vectors with $f'\le g'$. Then
--   $$[Qx\ge p,\ f'\le x\le g']$$
--   is box-TDI, and hence TDI.
--
--   Only the finite bounds contribute rows; this allows one-sided bounds such as the nonnegativity constraints in (2.8).
--
--   **Formalization Note** The infinite entries are encoded by finite sets $T_f=\{s: f'(s)>-\infty\}$ and $T_g=\{s:g'(s)<+\infty\}$ together with rational vectors $f',g'$ that are read only on $T_f$, resp. $T_g$; the condition $f'\le g'$ is required where both are finite (elsewhere it holds automatically).
-- source:
--   Frank, Murota, A Discrete Convex Min-Max Formula for Box-TDI Polyhedra, arXiv:2007.03507v3, p. 9, Proposition 2.9

import Mathlib
import Definitions.Def_BoxTDIMinMax_Separable_Setting

namespace BoxTDIMinMax.Separable

open Matrix

/-- Proposition 2.9, p. 9: if `Q x ≥ p` is box-TDI and `f' : S → ℚ ∪ {-∞}`,
`g' : S → ℚ ∪ {+∞}` with `f' ≤ g'` (finite exactly on `Tf`, resp. `Tg`), then
`[Q x ≥ p, f' ≤ x ≤ g']` is box-TDI, and hence TDI. -/
theorem proposition_2_9 {ι S : Type*} [Fintype ι] [Fintype S] [DecidableEq S]
    (Q : Matrix ι S ℤ) (p : ι → ℤ) (hbox : IsBoxTDI (ratMat Q) (ratVec p))
    (Tf Tg : Finset S) (f' g' : S → ℚ) (hfg : ∀ s ∈ Tf, s ∈ Tg → f' s ≤ g' s) :
    IsBoxTDI (partBoxMat (ratMat Q) Tf Tg) (partBoxRhs (ratVec p) Tf Tg f' g') ∧
      IsTDI (partBoxMat (ratMat Q) Tf Tg) (partBoxRhs (ratVec p) Tf Tg f' g') := by sorry

end BoxTDIMinMax.Separable
