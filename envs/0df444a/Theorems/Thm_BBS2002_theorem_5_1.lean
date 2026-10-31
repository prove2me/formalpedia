-- Prove2me | Theorems.Thm_BBS2002_theorem_5_1
-- name    : BBS2002.theorem_5_1
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-30T17:54:39.813466+00:00
-- url     : https://prove2.me/theorems/3e2c429d-9e8c-44fd-8aeb-0ddb95365ea5
-- title:
--   Computational Content of Classical Proofs under Realizer Assumptions (Theorem 5.1)
-- statement:
--   Theorem 5.1 (pp. 12-13): Under realizability assumptions (7)-(9) for `t₁, ..., tₙ, s₁, ..., sₘ, r`, any closed `Z_0`-derivation `M` of `D⃗ → ∀y⃗(G⃗ → ⊥) → ⊥` yields `Z ⊢ D⃗ → A(⟦M^X⟧ t₁ ... tₙ s)` where `s := λy⃗ λw⃗. s₁ w₁ (... (sₘ wₘ (r y⃗)) ...)`.
-- source:
--   Ulrich Berger, Wilfried Buchholz, and Helmut Schwichtenberg, 'Refined program extraction from classical proofs', Annals of Pure and Applied Logic 114(1-3), 2002, pp. 3-25 (doi:10.1016/S0168-0072(01)00073-2). Section 5, Theorem 5.1, pp. 14-15 (preprint pp. 12-13).

import Definitions.Def_BBS2002_Extraction

namespace BBS2002

/-- Theorem 5.1 (Computational Content of Classical Proofs, Section 5, pp. 12–13):
Let `D⃗ = D₁, ..., Dₙ` and `G⃗ = G₁, ..., Gₘ` be well-typed `L`-formulas, and assume (7)–(9) hold
for `t₁, ..., tₙ`, `s₁, ..., sₘ`, `r`. Then for any closed `Z_0`-derivation `M` of
`D⃗ → ∀y⃗(G⃗ → ⊥) → ⊥` and `s := λy⃗ λw⃗. s₁ w₁ (... (sₘ wₘ (r y⃗)) ...)`,
we have `Z ⊢ D⃗ → A(⟦M^X⟧ t₁ ... tₙ s)`. -/
theorem theorem_5_1
    (ν : Ty) (dummy : Term) (comp : CompTerm ν)
    (Ds Gs : List Formula) (ys : List Var)
    (ts : List (Option Term)) (ws : List (Option Var)) (ss : List Term) (vs : List Var)
    (r : Term) (M : ProofTerm)
    (hDs : ∀ D ∈ Ds, FormulaWellTyped D ∧ isLFormula D = true)
    (hGs : ∀ G ∈ Gs, FormulaWellTyped G ∧ isLFormula G = true)
    (htsLen : ts.length = Ds.length)
    (hwsLen : ws.length = Gs.length)
    (hssLen : ss.length = Gs.length)
    (hvsLen : vs.length = Gs.length)
    (hrTy : HasType r (Ty.arrMany (ys.map Var.ty) ν))
    (htsTy : ∀ j : Fin Ds.length,
      match tau ν (substBotWithX (Ds.get j)), ts.get (j.cast htsLen.symm) with
      | none, none => True
      | some ρ, some t => HasType t ρ
      | _, _ => False)
    (hwssTy : ∀ i : Fin Gs.length,
      (vs.get (i.cast hvsLen.symm)).ty = ν ∧
      match tau ν (substBotWithX (Gs.get i)), ws.get (i.cast hwsLen.symm) with
      | none, none => HasType (ss.get (i.cast hssLen.symm)) (.arr ν ν)
      | some ρ, some w => w.ty = ρ ∧ HasType (ss.get (i.cast hssLen.symm)) (.arr ρ (.arr ν ν))
      | _, _ => False)
    (hBindersFresh :
      let wVars := ws.filterMap id
      (ys ++ wVars ++ vs).Nodup ∧
      (∀ z ∈ ys ++ wVars, ∀ s_i ∈ ss, z ∉ freeVars s_i) ∧
      (∀ z ∈ ys ++ wVars, z ∉ freeVars r) ∧
      (∀ z ∈ wVars ++ vs, ∀ D ∈ Ds, z ∉ freeVarsFormula D) ∧
      (∀ z ∈ wVars ++ vs, ∀ G ∈ Gs, z ∉ freeVarsFormula G) ∧
      (∀ z ∈ ys ++ wVars ++ vs, z = comp.var ∨ z ∉ freeVarsFormula comp.body) ∧
      (∀ v ∈ vs, ∀ s_i ∈ ss, v ∉ freeVars s_i))
    (h7 : ∀ j : Fin Ds.length,
      Provable SysConfig.Z
        (Formula.impMany Ds
          (mrFormula ν comp (ts.get (j.cast htsLen.symm)) (substBotWithX (Ds.get j)))))
    (h8 : ∀ i : Fin Gs.length,
      let G_i := Gs.get i
      let w_i := ws.get (i.cast hwsLen.symm)
      let s_i := ss.get (i.cast hssLen.symm)
      let v_i := vs.get (i.cast hvsLen.symm)
      Provable SysConfig.Z
        (Formula.impMany Ds
          (.imp
            (mrFormula ν comp (w_i.map Term.var) (substBotWithX G_i))
            (.imp
              (.imp G_i (comp.apply (.var v_i)))
              (comp.apply (applyGoalRealizer s_i w_i (.var v_i)))))))
    (h9 : Provable SysConfig.Z
      (Formula.impMany Ds
        (Formula.allMany ys
          (Formula.impMany Gs (comp.apply (Term.appMany r (ys.map Term.var)))))))
    (hM : Derivable SysConfig.Z0 M (Formula.impMany Ds (goalImpliesBot ys Gs)))
    (hMClosed : freeAssumpVars M = [])
    (hMAdm : AdmissibleForExtraction ν dummy comp (substBotProof M)) :
    let s := buildGoalCombinatorTerm ys ws ss r
    Provable SysConfig.Z
      (Formula.impMany Ds (comp.apply (extractClassicalTerm ν dummy M ts s))) := by
  sorry

end BBS2002
