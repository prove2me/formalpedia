-- Prove2me | Theorems.Thm_BBS2002_V2_theorem_5_1
-- name    : BBS2002.V2.theorem_5_1
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T18:40:50.92896+00:00
-- url     : https://prove2.me/theorems/5bb45ceb-47e6-41dd-ab02-a8c00a7d7f65
-- title:
--   Computational content of classical proofs (Theorem 5.1, corrected)
-- statement:
--   Let $\vec D$ and $\vec G$ be finite lists of well-typed ordinary formulas, and let $\vec y$ be object variables fresh for $\vec D$. Supply correctly typed definite realizers $\vec t$, auxiliary realizer variables $\vec w$, goal combinators $\vec s$, variables $\vec v$ of type $\nu$, and a term $r$ taking $\vec y$ as inputs. Assume (7) $Z\vdash\vec D\to t_j\,\mathbf{mr}_{\mathcal A}\,D_j^X$, (8) $Z\vdash\vec D\to w_i\,\mathbf{mr}_{\mathcal A}\,G_i^X\to(G_i\to\mathcal A(v_i))\to\mathcal A(s_iw_iv_i)$, and (9) $Z\vdash\vec D\to\forall\vec y(\vec G\to\mathcal A(r\vec y))$. Auxiliary variables are distinct and fresh for the formulas and free comprehension parameters as stated in the declaration; the goal combinators may depend on $\vec y$, which the final abstraction binds. For a $Z_0$ proof $M$ of $\vec D\to(\forall\vec y(\vec G\to\bot))\to\bot$ with no free assumption variables and admissible translated naming, raw extraction yields a term $p=\llbracket M^X\rrbracket$. Let $s=\lambda\vec y\lambda\vec w.\,s_1w_1(\cdots(s_mw_m(r\vec y))\cdots)$. Then $p\vec t s$ is well typed at $\nu$ and $Z\vdash\vec D\to\mathcal A(p\vec t s)$. Omitted-type arguments and binders are omitted, including in empty lists.
-- source:
--   Ulrich Berger, Wilfried Buchholz, and Helmut Schwichtenberg, Refined program extraction from classical proofs, Annals of Pure and Applied Logic 114 (2002), pp. 3–25, https://doi.org/10.1016/S0168-0072(01)00073-2; page references below use the author's preprint pagination. Theorem 5.1 and equations (7)–(11), preprint pp. 12–13; standing freshness condition for universal introduction, Section 2.

import Definitions.Def_BBS2002_V2_Realizability

namespace BBS2002.V2

theorem theorem_5_1
    (ν : Ty) (dummy : Term) (comp : CompTerm ν)
    (Ds Gs : List Formula) (ys : List Var)
    (ts : (j : Fin Ds.length) → Realizer (tau ν (substBotWithX (Ds.get j))))
    (ws : Fin Gs.length → Option Var) (ss : Fin Gs.length → Term)
    (vs : Fin Gs.length → Var) (r : Term) (M : ProofTerm)
    (hDs : ∀ D ∈ Ds, FormulaWellTyped D ∧ isLFormula D = true)
    (hGs : ∀ G ∈ Gs, FormulaWellTyped G ∧ isLFormula G = true)
    (htsTy : ∀ j, (ts j).Typed)
    (hwsTy : ∀ i, (ws i).map Var.ty = tau ν (substBotWithX (Gs.get i)))
    (hvsTy : ∀ i, (vs i).ty = ν)
    (hssTy : ∀ i,
      HasType (ss i)
        (match tau ν (substBotWithX (Gs.get i)) with
         | none => .arr ν ν
         | some ρ => .arr ρ (.arr ν ν)))
    (hrTy : HasType r (Ty.arrMany (ys.map Var.ty) ν))
    (hBindersFresh :
      let wVars := (List.ofFn ws).filterMap id
      let vVars := List.ofFn vs
      (ys ++ wVars ++ vVars).Nodup ∧
      (∀ y ∈ ys, ∀ D ∈ Ds, y ∉ freeVarsFormula D) ∧
      (∀ z ∈ wVars ++ vVars, ∀ i, z ∉ freeVars (ss i)) ∧
      (∀ z ∈ ys ++ wVars, z ∉ freeVars r) ∧
      (∀ z ∈ wVars ++ vVars, ∀ D ∈ Ds, z ∉ freeVarsFormula D) ∧
      (∀ z ∈ wVars ++ vVars, ∀ G ∈ Gs, z ∉ freeVarsFormula G) ∧
      (∀ z ∈ ys ++ wVars ++ vVars,
        z = comp.var ∨ z ∉ freeVarsFormula comp.body))
    (h7 : ∀ j,
      Provable SysConfig.Z
        (Formula.impMany Ds (mrFormula ν comp (substBotWithX (Ds.get j)) (ts j))))
    (h8 : ∀ i,
      Provable SysConfig.Z
        (Formula.impMany Ds
          (.imp
            (mrFormula ν comp (substBotWithX (Gs.get i))
              (Realizer.ofOption ((ws i).map Term.var)
                (by simpa only [Option.isSome_map] using congrArg Option.isSome (hwsTy i))))
            (.imp
              (.imp (Gs.get i) (comp.apply (.var (vs i))))
              (comp.apply (applyGoalRealizer (ss i) (ws i) (.var (vs i))))))))
    (h9 : Provable SysConfig.Z
      (Formula.impMany Ds
        (Formula.allMany ys
          (Formula.impMany Gs (comp.apply (Term.appMany r (ys.map Term.var)))))))
    (hM : Derivable SysConfig.Z0 M (Formula.impMany Ds (goalImpliesBot ys Gs)))
    (hMClosed : freeAssumpVars M = [])
    (hMAdm : AdmissibleForExtraction ν dummy (substBotProof M)) :
    let s := buildGoalCombinatorTerm ys (List.ofFn ws) (List.ofFn ss) r
    ∃ p : Term,
      extractRaw ν dummy (substBotProof M) = some p ∧
      HasType (.app (applyOptTerms p (List.ofFn fun j => (ts j).toOption)) s) ν ∧
      Provable SysConfig.Z
        (Formula.impMany Ds
          (comp.apply (.app (applyOptTerms p (List.ofFn fun j => (ts j).toOption)) s))) := by
  sorry

end BBS2002.V2
