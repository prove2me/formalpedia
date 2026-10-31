-- Prove2me | Theorems.Thm_BBS2002_corollary_5_3
-- name    : BBS2002.corollary_5_3
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-30T17:55:01.479993+00:00
-- url     : https://prove2.me/theorems/e16275bc-9235-4aed-9125-22f1d84cf970
-- title:
--   Main Program Extraction Theorem for Classical Proofs (Corollary 5.3)
-- statement:
--   Corollary 5.3 (p. 14): For definite formulas `D⃗ = D₁, ..., Dₙ` and a goal formula `G`, there exist terms `t₁, ..., tₙ, s` determined by `D⃗, G` only such that for every `Z_0`-derivation `M` of `D⃗ → ∀y(G → ⊥) → ⊥`, `Z ⊢ D⃗ → G[y := ⟦M^X⟧ t₁ ... tₙ s]`.
-- source:
--   Ulrich Berger, Wilfried Buchholz, and Helmut Schwichtenberg, 'Refined program extraction from classical proofs', Annals of Pure and Applied Logic 114(1-3), 2002, pp. 3-25 (doi:10.1016/S0168-0072(01)00073-2). Section 5, Corollary 5.3, p. 16 (preprint p. 14).

import Definitions.Def_BBS2002_Extraction

namespace BBS2002

/-- Corollary 5.3 (Refined Program Extraction from Classical Proofs, Section 5, p. 14):
Let `D⃗ = D₁, ..., Dₙ` be definite formulas and `G` a goal formula, and let `y` be an object variable
(with a closed dummy term `dummy` of type `y.ty`, and `y` not free in `D₁, ..., Dₙ`).
Then there exist `t₁, ..., tₙ` (`ts : List (Option Term)`) and `s : Term` — determined by
`D⃗, G` (and `y, dummy`) only — such that for every closed `Z_0`-derivation `M` of
`D⃗ → ∀y(G → ⊥) → ⊥` (admissible for extraction with respect to `A := λy. G`),
the extracted term `⟦M^X⟧ t₁ ... tₙ s` (`extractClassicalTerm y.ty dummy M ts s`) has type `y.ty`
and satisfies:
`Z ⊢ D⃗ → G[y := ⟦M^X⟧ t₁ ... tₙ s]`. -/
theorem corollary_5_3
    (Ds : List Formula) (G : Formula) (y : Var) (dummy : Term)
    (hDs : ∀ D ∈ Ds, IsDefiniteFormula D)
    (hG : IsGoalFormula G)
    (hyDs : ∀ D ∈ Ds, y ∉ freeVarsFormula D)
    (hDummyTy : HasType dummy y.ty)
    (hDummyClosed : IsClosedTerm dummy) :
    ∃ (ts : List (Option Term)) (s : Term),
      ts.length = Ds.length ∧
      (∀ (M : ProofTerm) (compG : CompTerm y.ty),
        compG.var = y →
        compG.body = G →
        Derivable SysConfig.Z0 M (Formula.impMany Ds (goalImpliesBot [y] [G])) →
        freeAssumpVars M = [] →
        AdmissibleForExtraction y.ty dummy compG (substBotProof M) →
        HasType (extractClassicalTerm y.ty dummy M ts s) y.ty ∧
        Provable SysConfig.Z
          (Formula.impMany Ds
            (substFormula G y (extractClassicalTerm y.ty dummy M ts s)))) := by
  sorry

end BBS2002
