-- Prove2me | Theorems.Thm_BBS2002_V2_theorem_4_1
-- name    : BBS2002.V2.theorem_4_1
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T18:40:49.87807+00:00
-- url     : https://prove2.me/theorems/3aa5ce40-47eb-4374-8cfe-4a67684240e7
-- title:
--   Soundness of modified realizability (Theorem 4.1, corrected)
-- statement:
--   Let $M$ be a $Z^X$ derivation of $B$, with a typed closed dummy term and the named-variable conventions in V2.AdmissibleForExtraction. For every comprehension term $\mathcal A$, there is a realizer $r$ of the assigned type whose option representation equals the structural extraction of $M$. It is well typed, and there is a $Z$ derivation of $r\,\mathbf{mr}_{\mathcal A}\,B$. Every free assumption in this derived proof is the realizability translation of a free assumption of $M$. At the omitted type the realizer is epsilon. The comprehension term may share free object parameters with the proof. The translation renames bound variables to avoid capture, including after formula conversion.
-- source:
--   Ulrich Berger, Wilfried Buchholz, and Helmut Schwichtenberg, Refined program extraction from classical proofs, Annals of Pure and Applied Logic 114 (2002), pp. 3–25, https://doi.org/10.1016/S0168-0072(01)00073-2; page references below use the author's preprint pagination. Theorem 4.1, preprint p. 12.

import Definitions.Def_BBS2002_V2_Realizability

namespace BBS2002.V2

theorem theorem_4_1
    (ν : Ty) (dummy : Term) (comp : CompTerm ν)
    (M : ProofTerm) (B : Formula)
    (hDeriv : Derivable SysConfig.ZX M B)
    (hAdm : AdmissibleForExtraction ν dummy M) :
    ∃ r : Realizer (tau ν B),
      r.toOption = extractProgram ν dummy M B ∧
      r.Typed ∧
      ∃ N : ProofTerm,
        Derivable SysConfig.Z N (mrFormula ν comp B r) ∧
        ∀ v ∈ freeAssumpVars N,
          ∃ u ∈ freeAssumpVars M,
            v.formula = mrFormula ν comp u.formula (assumpRealizer ν u) := by
  sorry

end BBS2002.V2
