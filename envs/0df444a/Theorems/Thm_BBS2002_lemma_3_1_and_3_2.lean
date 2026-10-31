-- Prove2me | Theorems.Thm_BBS2002_lemma_3_1_and_3_2
-- name    : BBS2002.lemma_3_1_and_3_2
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-30T17:54:03.333886+00:00
-- url     : https://prove2.me/theorems/73198c20-0ee8-4620-8b96-8cca48eab509
-- title:
--   Derivability Properties of Definite and Goal Formulas (Lemmas 3.1 & 3.2)
-- statement:
--   Lemmas 3.1 and 3.2 (pp. 6-9): For definite formulas `D` and goal formulas `G`, proves (3) `Z^X ⊢ (¬D → X) → D^X` for relevant `D`, (4) `Z^X ⊢ D → D^X`, (5) `Z^X ⊢ G^X → G` for irrelevant `G`, (6) `Z^X ⊢ G^X → (G → X) → X`, and Lemma 3.2 `Z^X ⊢ (G⃗ → X) → G⃗^X → X`.
-- source:
--   Ulrich Berger, Wilfried Buchholz, and Helmut Schwichtenberg, 'Refined program extraction from classical proofs', Annals of Pure and Applied Logic 114(1-3), 2002, pp. 3-25 (doi:10.1016/S0168-0072(01)00073-2). Section 3, Lemmas 3.1 and 3.2, pp. 8-11 (preprint pp. 6-9).

import Definitions.Def_BBS2002_Extraction

namespace BBS2002

/-- Lemma 3.1 (equations (3)–(6), p. 6) and Lemma 3.2 (p. 9):
1. (**Lemma 3.1**) For every definite formula `D` and goal formula `G`:
   - (3) If `D` is relevant, `Z^X ⊢ (¬D → X) → D^X`.
   - (4) `Z^X ⊢ D → D^X`.
   - (5) If `G` is irrelevant, `Z^X ⊢ G^X → G`.
   - (6) `Z^X ⊢ G^X → (G → X) → X`.
2. (**Lemma 3.2**) For every list of goal formulas `G⃗ = G₁, ..., Gₙ`,
   `Z^X ⊢ (G⃗ → X) → G⃗^X → X`. -/
theorem lemma_3_1_and_3_2 :
    (∀ D : Formula,
      IsDefiniteFormula D →
      (isRelevant D = true →
        Provable SysConfig.ZX (.imp (.imp (Formula.neg D) .varX) (substBotWithX D))) ∧
      Provable SysConfig.ZX (.imp D (substBotWithX D))) ∧
    (∀ G : Formula,
      IsGoalFormula G →
      (isIrrelevant G = true →
        Provable SysConfig.ZX (.imp (substBotWithX G) G)) ∧
      Provable SysConfig.ZX (.imp (substBotWithX G) (.imp (.imp G .varX) .varX))) ∧
    (∀ Gs : List Formula,
      (∀ G ∈ Gs, IsGoalFormula G) →
      Provable SysConfig.ZX
        (.imp
          (Formula.impMany Gs .varX)
          (Formula.impMany (Gs.map substBotWithX) .varX))) := by
  sorry

end BBS2002
