-- Prove2me | Theorems.Thm_BBS2002_V2_corollary_5_3
-- name    : BBS2002.V2.corollary_5_3
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T18:40:51.266892+00:00
-- url     : https://prove2.me/theorems/ad4cea40-60de-4118-83d8-24fc9821c437
-- title:
--   Refined program extraction with free parameters (Corollary 5.3, corrected)
-- statement:
--   Let $\vec D$ be definite formulas, let $G$ be a goal formula, and let the object variable $y$ be fresh for $\vec D$. Fix a typed closed dummy term of type $y$. There are correctly typed formula realizers $\vec t$ and a goal combinator $s$, chosen before any proof $M$. Each $t_j$ has free variables only from $D_j$; $s$ has free variables only from $G$, excluding $y$. For every $Z_0$ derivation $M$ of $\vec D\to(\forall y(G\to\bot))\to\bot$ with no free assumption variables and admissible translated naming, there exists a term $p$ whose raw extraction equation is exactly $\operatorname{extractRaw}(M^X)=\operatorname{some}(p)$. The output $e=p\vec t s$, omitting irrelevant arguments, has type $y$ and satisfies $Z\vdash\vec D\to G[y:=e]$. Free object parameters of $M$ are permitted. Successful extraction is a conclusion, with no fallback program used.
-- source:
--   Ulrich Berger, Wilfried Buchholz, and Helmut Schwichtenberg, Refined program extraction from classical proofs, Annals of Pure and Applied Logic 114 (2002), pp. 3–25, https://doi.org/10.1016/S0168-0072(01)00073-2; page references below use the author's preprint pagination. Corollary 5.3, preprint p. 14; Section 4's extraction and typing conventions, pp. 11–12.

import Definitions.Def_BBS2002_V2_Realizability

namespace BBS2002.V2

/-- Classical extraction for definite assumptions and one goal formula. The object terms
realizing the formulas are independent of `M`; a proof may retain free object parameters,
but must have no free assumption variables. -/
theorem corollary_5_3
    (Ds : List Formula) (G : Formula) (y : Var) (dummy : Term)
    (hDs : ∀ D ∈ Ds, IsDefiniteFormula D)
    (hG : IsGoalFormula G)
    (hyDs : ∀ D ∈ Ds, y ∉ freeVarsFormula D)
    (hDummyTy : HasType dummy y.ty)
    (hDummyClosed : IsClosedTerm dummy) :
    ∃ (ts : (j : Fin Ds.length) → Realizer (tau y.ty (substBotWithX (Ds.get j))))
      (s : Term),
      (∀ j, (ts j).Typed) ∧
      (∀ j, ∀ t₀ ∈ (ts j).toOption, ∀ x ∈ freeVars t₀, x ∈ freeVarsFormula (Ds.get j)) ∧
      HasType s
        (.arr y.ty (match tau y.ty (substBotWithX G) with
          | none => y.ty
          | some ρ => .arr ρ y.ty)) ∧
      (∀ x ∈ freeVars s, x ∈ freeVarsFormula G ∧ x ≠ y) ∧
      (∀ M : ProofTerm,
        Derivable SysConfig.Z0 M (Formula.impMany Ds (goalImpliesBot [y] [G])) →
        freeAssumpVars M = [] →
        AdmissibleForExtraction y.ty dummy (substBotProof M) →
        ∃ p : Term,
          extractRaw y.ty dummy (substBotProof M) = some p ∧
          let output := .app (applyOptTerms p (List.ofFn (fun j ↦ (ts j).toOption))) s
          HasType output y.ty ∧
          Provable SysConfig.Z (Formula.impMany Ds (substFormula G y output))) := by
  sorry

end BBS2002.V2
