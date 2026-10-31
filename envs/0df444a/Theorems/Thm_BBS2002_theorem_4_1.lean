-- Prove2me | Theorems.Thm_BBS2002_theorem_4_1
-- name    : BBS2002.theorem_4_1
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-30T17:54:26.646489+00:00
-- url     : https://prove2.me/theorems/c701bc34-d5e6-49c8-bf61-ea430bfb285b
-- title:
--   Soundness of Modified Realizability (Theorem 4.1)
-- statement:
--   Theorem 4.1 (p. 12): If `M` is a `Z^X`-derivation of `B`, then the extracted program `⟦M⟧` has type `τ(B)` and there is a `Z`-derivation of `⟦M⟧ mr_A B` from `{ u^{τ(C)} mr_A C | u^C ∈ FA(M) }`.
-- source:
--   Ulrich Berger, Wilfried Buchholz, and Helmut Schwichtenberg, 'Refined program extraction from classical proofs', Annals of Pure and Applied Logic 114(1-3), 2002, pp. 3-25 (doi:10.1016/S0168-0072(01)00073-2). Section 4, Theorem 4.1, p. 14 (preprint p. 12).

import Definitions.Def_BBS2002_Extraction

namespace BBS2002

/-- Theorem 4.1 (Soundness of Modified Realizability, Section 4, p. 12):
Assume that `M` is a `Z^X`-derivation of `B` (`Derivable SysConfig.ZX M B`) satisfying
`AdmissibleForExtraction ν dummy comp M`. Then:
1. If `τ(B) = some ρ`, then `⟦M⟧ = some t` for a term `t` of type `ρ`; if `τ(B) = *`, then `⟦M⟧ = ε` (`none`).
2. There is a `Z`-derivation `N` of `⟦M⟧ mr_A B` whose free assumption variables have formulas in
   `{ u^{τ(C)} mr_A C | u^C ∈ FA(M) }`. -/
theorem theorem_4_1
    (ν : Ty) (dummy : Term) (comp : CompTerm ν)
    (M : ProofTerm) (B : Formula)
    (hDeriv : Derivable SysConfig.ZX M B)
    (hAdm : AdmissibleForExtraction ν dummy comp M) :
    (match tau ν B with
     | none => extractProgram ν dummy M B = none
     | some ρ => ∃ t : Term, extractProgram ν dummy M B = some t ∧ HasType t ρ) ∧
    (∃ N : ProofTerm,
      Derivable SysConfig.Z N (mrFormula ν comp (extractProgram ν dummy M B) B) ∧
      ∀ v ∈ freeAssumpVars N,
        ∃ u ∈ freeAssumpVars M,
          v.formula = mrFormula ν comp (assumpRealizerTerm ν u) u.formula) := by
  sorry

end BBS2002
