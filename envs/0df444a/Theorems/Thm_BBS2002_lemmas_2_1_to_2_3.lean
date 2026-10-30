-- Prove2me | Theorems.Thm_BBS2002_lemmas_2_1_to_2_3
-- name    : BBS2002.lemmas_2_1_to_2_3
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-30T04:07:03.491299+00:00
-- url     : https://prove2.me/theorems/8618d598-a26e-46e0-87ff-44053f41b66c
-- title:
--   Equivalence of Z^X and Z_0^X (Lemma 2.1), L-Stability (Lemma 2.2), and Quantifier-Free Case Distinction (Lemma 2.3)
-- statement:
--   Lemmas 2.1, 2.2, and 2.3 (p. 5): (1) `Z^X ⊢ A ↔ Z_0^X ⊢ A^F` where `F := atom(false)`; (2) `Z ⊢ ¬¬A → A` for every `L`-formula `A`; (3) `Z^X ⊢ (¬C → A) → (C → A) → A` for every quantifier-free `L`-formula `C`.
-- source:
--   Ulrich Berger, Wilfried Buchholz, and Helmut Schwichtenberg, 'Refined program extraction from classical proofs', Annals of Pure and Applied Logic 114(1-3), 2002, pp. 3-25 (doi:10.1016/S0168-0072(01)00073-2). Section 2, Lemmas 2.1, 2.2, and 2.3, p. 7 (preprint p. 5).

import Definitions.Def_BBS2002_Arithmetic

namespace BBS2002

/-- Lemmas 2.1, 2.2 (Stability), and 2.3 (Cases) (Section 2, p. 5):
1. (**Lemma 2.1**) For every well-typed `L[X]`-formula `A`, `Z^X ⊢ A ↔ Z_0^X ⊢ A^F`,
   where `F := atom(false)` and `A^F := A[⊥ := F]`.
2. (**Lemma 2.2, Stability**) For every well-typed `L`-formula `A`, `Z ⊢ ¬¬A → A`.
3. (**Lemma 2.3, Cases**) For every well-typed quantifier-free `L`-formula `C` and every
   well-typed `L[X]`-formula `A`, `Z^X ⊢ (¬C → A) → (C → A) → A`. -/
theorem lemmas_2_1_to_2_3 :
    (∀ A : Formula,
      FormulaWellTyped A →
      (Provable SysConfig.ZX A ↔ Provable SysConfig.ZX0 (substBotWithFalse A))) ∧
    (∀ A : Formula,
      FormulaWellTyped A →
      isLFormula A = true →
      Provable SysConfig.Z (.imp (Formula.dneg A) A)) ∧
    (∀ C A : Formula,
      FormulaWellTyped C →
      isLFormula C = true →
      isQuantifierFree C = true →
      FormulaWellTyped A →
      Provable SysConfig.ZX (.imp (.imp (Formula.neg C) A) (.imp (.imp C A) A))) := by
  sorry

end BBS2002
