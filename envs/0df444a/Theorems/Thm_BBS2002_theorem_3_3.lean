-- Prove2me | Theorems.Thm_BBS2002_theorem_3_3
-- name    : BBS2002.theorem_3_3
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-30T17:54:15.951121+00:00
-- url     : https://prove2.me/theorems/4242300c-122a-4c1d-bfda-db448aac894c
-- title:
--   Refined A-Translation for Definite and Goal Formulas (Theorem 3.3)
-- statement:
--   Theorem 3.3 (p. 9): If `Z_0 ⊢ D⃗ → ∀y⃗(G⃗ → ⊥) → ⊥` for definite formulas `D⃗` and goal formulas `G⃗`, then `Z^X ⊢ D⃗ → ∀y⃗(G⃗ → X) → X`.
-- source:
--   Ulrich Berger, Wilfried Buchholz, and Helmut Schwichtenberg, 'Refined program extraction from classical proofs', Annals of Pure and Applied Logic 114(1-3), 2002, pp. 3-25 (doi:10.1016/S0168-0072(01)00073-2). Section 3, Theorem 3.3, p. 11 (preprint p. 9).

import Definitions.Def_BBS2002_Extraction

namespace BBS2002

/-- Theorem 3.3 (Section 3, p. 9):
Assume that for definite formulas `D⃗` and goal formulas `G⃗` we have
`Z_0 ⊢ D⃗ → ∀y⃗(G⃗ → ⊥) → ⊥`.
Then we also have
`Z^X ⊢ D⃗ → ∀y⃗(G⃗ → X) → X`. -/
theorem theorem_3_3
    (Ds Gs : List Formula) (ys : List Var)
    (hDs : ∀ D ∈ Ds, IsDefiniteFormula D)
    (hGs : ∀ G ∈ Gs, IsGoalFormula G)
    (hZ0 : Provable SysConfig.Z0 (Formula.impMany Ds (goalImpliesBot ys Gs))) :
    Provable SysConfig.ZX (Formula.impMany Ds (goalImpliesX ys Gs)) := by
  sorry

end BBS2002
