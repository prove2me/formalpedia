-- Prove2me | Theorems.Thm_BNS2000_lemma_4_1_and_4_2
-- name    : BNS2000.lemma_4_1_and_4_2
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-30T04:08:23.650983+00:00
-- url     : https://prove2.me/theorems/843d6509-d9d6-4f59-bf22-2a2d8f3f0510
-- title:
--   Safe/Ground Normal Forms (Lemma 4.1) and Sharing via Ground β_ι-Expansions (Lemma 4.2)
-- statement:
--   Lemmas 4.1 and 4.2 (p. 22): (1) Every variable in the normal form of a ground-type term with ground free variables is safe or ground; (2) every term with affinable higher-type incomplete binders can be ground `β_ι`-expanded into a well-typed term `t_β` in which every higher-type incomplete binder occurs at most once (`FO(x, s) ≤ 1`).
-- source:
--   Stephen Bellantoni, Karl-Heinz Niggl, and Helmut Schwichtenberg, 'Higher type recursion, ramification and polynomial time', Annals of Pure and Applied Logic 104, 2000, pp. 17-30 (doi:10.1016/S0168-0072(00)00006-3). Section 4, Lemmas 4.1 and 4.2, p. 22.

import Definitions.Def_BNS2000_Terms

namespace BNS2000

/-- **Lemma 4.1 and Lemma 4.2 (Sharing)** (Section 4, p. 22):
1. (**Lemma 4.1**): Let `t` be a well-typed ground-type term whose free variables are of
   ground type. Then in the normal form `nf(t)` of `t`, all occurring variables (free or bound)
   are safe or ground (`AllVarsSafeOrGround nf_t`).
2. (**Lemma 4.2, Sharing**): Let `t` be a well-typed term such that for every subterm `λx. s`
   with `x` higher-type incomplete, the variable `x` is affinable in `s`
   (`SatisfiesDirectAffinability t`). Then by repeated ground-type `β_ι`-expansions
   `r[a/y^τ] ↦ (λy^τ. r) a` one can construct a term `t_β` (`BetaIotaExpandsTo t t_β`,
   hence `ReducesTo t_β t`) such that for every subterm `λx. s` in `t_β` with `x` higher-type
   incomplete, `FO(x, s) ≤ 1` (`HasLinearHigherIncompleteBinders t_β`). -/
theorem lemma_4_1_and_4_2 :
    (∀ (t nf_t : Term) (τ : Ty),
      HasType t τ →
      τ.isGround = true →
      (∀ v ∈ freeVars t, v.ty.isGround = true) →
      IsNormalFormOf t nf_t →
      AllVarsSafeOrGround nf_t) ∧
    (∀ (t : Term) (τ : Ty),
      HasType t τ →
      SatisfiesDirectAffinability t →
      ∃ t_β : Term,
        HasType t_β τ ∧
        (SatisfiesR t → SatisfiesR t_β) ∧
        BetaIotaExpandsTo t t_β ∧
        ReducesTo t_β t ∧
        HasLinearHigherIncompleteBinders t_β) := by
  sorry

end BNS2000
