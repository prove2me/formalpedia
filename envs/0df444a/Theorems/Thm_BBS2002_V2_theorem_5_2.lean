-- Prove2me | Theorems.Thm_BBS2002_V2_theorem_5_2
-- name    : BBS2002.V2.theorem_5_2
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T18:40:49.775352+00:00
-- url     : https://prove2.me/theorems/bc55a9ab-b1e2-4cd9-be31-3c34badd35d2
-- title:
--   Uniform realizers with free parameters (Theorem 5.2, corrected)
-- statement:
--   For a definite formula $D$, a goal formula $G$, an assigned type $\nu$, and a typed closed dummy term, there are well-typed realizers $t$ and $s$ chosen independently of the comprehension term. Every object variable free in $t$ is free in $D$, and every object variable free in $s$ is free in $G$. For every comprehension term $\mathcal A$, $Z\vdash D\to t\,\mathbf{mr}_{\mathcal A}\,D^X$. Also, for appropriately typed auxiliary variables $w,v$ fresh for $G$ and the free comprehension parameters, $Z\vdash w\,\mathbf{mr}_{\mathcal A}\,G^X\to(G\to\mathcal A(v))\to\mathcal A(swv)$. The variable $w$ and the corresponding argument of $s$ are omitted when $G^X$ has omitted type. The terms are allowed to depend on the formulas' free object parameters; uniformity in $\mathcal A$ does not require them to be closed.
-- source:
--   Ulrich Berger, Wilfried Buchholz, and Helmut Schwichtenberg, Refined program extraction from classical proofs, Annals of Pure and Applied Logic 114 (2002), pp. 3–25, https://doi.org/10.1016/S0168-0072(01)00073-2; page references below use the author's preprint pagination. Theorem 5.2, equations (12)–(13) and their canonical construction, preprint pp. 13–14.

import Definitions.Def_BBS2002_V2_Realizability

namespace BBS2002.V2

/-- The realizers for a definite formula and a goal formula retain only their formulas'
free object parameters. The comprehension term is arbitrary; its free parameters need not
be disjoint from the free parameters of either formula. -/
theorem theorem_5_2
    (ν : Ty) (dummy : Term)
    (hDummyTy : HasType dummy ν)
    (hDummyClosed : IsClosedTerm dummy)
    (D G : Formula)
    (hD : IsDefiniteFormula D)
    (hG : IsGoalFormula G) :
    (∃ t : Realizer (tau ν (substBotWithX D)),
      t.Typed ∧
      (∀ t₀ ∈ t.toOption, ∀ x ∈ freeVars t₀, x ∈ freeVarsFormula D) ∧
      ∀ comp : CompTerm ν,
        Provable SysConfig.Z (.imp D (mrFormula ν comp (substBotWithX D) t))) ∧
    (∃ s : Term,
      HasType s
        (match tau ν (substBotWithX G) with
         | none => .arr ν ν
         | some ρ => .arr ρ (.arr ν ν)) ∧
      (∀ x ∈ freeVars s, x ∈ freeVarsFormula G) ∧
      ∀ (comp : CompTerm ν) (w : Option Var) (v : Var),
        v.ty = ν →
        (hw : w.map Var.ty = tau ν (substBotWithX G)) →
        (∀ wVar ∈ w,
          wVar ≠ v ∧
          wVar ∉ freeVarsFormula G ∧
          (wVar = comp.var ∨ wVar ∉ freeVarsFormula comp.body)) →
        v ∉ freeVarsFormula G →
        (v = comp.var ∨ v ∉ freeVarsFormula comp.body) →
        Provable SysConfig.Z
          (.imp
            (mrFormula ν comp (substBotWithX G)
              (Realizer.ofOption (w.map Term.var)
                (by simpa only [Option.isSome_map] using congrArg Option.isSome hw)))
            (.imp
              (.imp G (comp.apply (.var v)))
              (comp.apply (applyGoalRealizer s w (.var v)))))) := by
  sorry

end BBS2002.V2
