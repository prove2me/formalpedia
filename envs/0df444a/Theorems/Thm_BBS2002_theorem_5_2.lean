-- Prove2me | Theorems.Thm_BBS2002_theorem_5_2
-- name    : BBS2002.theorem_5_2
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-30T17:54:52.052992+00:00
-- url     : https://prove2.me/theorems/f87702a8-6a2b-47fd-8897-369f6487a28a
-- title:
--   Existence of Uniform Realizers for Definite and Goal Formulas (Theorem 5.2)
-- statement:
--   Theorem 5.2 (pp. 13-14): For every definite formula `D` and goal formula `G`, there exist terms `t = ⟦N_D⟧` and `s = ⟦H_G⟧` such that for any comprehension term `A = λy A₀`, (12) `Z ⊢ D → t mr_A D^X` and (13) `Z ⊢ w mr_A G^X → (G → A(v)) → A(s w v)`.
-- source:
--   Ulrich Berger, Wilfried Buchholz, and Helmut Schwichtenberg, 'Refined program extraction from classical proofs', Annals of Pure and Applied Logic 114(1-3), 2002, pp. 3-25 (doi:10.1016/S0168-0072(01)00073-2). Section 5, Theorem 5.2, pp. 15-16 (preprint pp. 13-14).

import Definitions.Def_BBS2002_Extraction

namespace BBS2002

/-- Theorem 5.2 (Section 5, pp. 13–14):
For every definite formula `D` and goal formula `G` (and any type `ν` with closed `dummy : ν`),
there exist `t : Option Term` and `s : Term` (specifically `t = ⟦N_D⟧` and `s = ⟦H_G⟧` extracted
from the `Z^X`-derivations `N_D : D → D^X` and `H_G : G^X → (G → X) → X` of Lemma 3.1(4),(6))
such that for every comprehension term `A = λy^ν A₀`:
- (12) `Z ⊢ D → t mr_A D^X`,
- (13) `Z ⊢ w mr_A G^X → (G → A(v)) → A(s w v)`. -/
theorem theorem_5_2
    (ν : Ty) (dummy : Term)
    (hDummyTy : HasType dummy ν)
    (hDummyClosed : IsClosedTerm dummy)
    (D G : Formula)
    (hD : IsDefiniteFormula D)
    (hG : IsGoalFormula G) :
    (∃ t : Option Term,
      (match tau ν (substBotWithX D), t with
       | none, none => True
       | some ρ, some t₀ => HasType t₀ ρ ∧ IsClosedTerm t₀
       | _, _ => False) ∧
      ∀ comp : CompTerm ν,
        Provable SysConfig.Z (.imp D (mrFormula ν comp t (substBotWithX D)))) ∧
    (∃ s : Term,
      IsClosedTerm s ∧
      (match tau ν (substBotWithX G) with
       | none => HasType s (.arr ν ν)
       | some ρ => HasType s (.arr ρ (.arr ν ν))) ∧
      ∀ (comp : CompTerm ν) (w : Option Var) (v : Var),
        v.ty = ν →
        (match tau ν (substBotWithX G), w with
         | none, none => True
         | some ρ, some wVar =>
             wVar.ty = ρ ∧
             wVar ≠ v ∧
             wVar ∉ freeVarsFormula G ∧
             (wVar = comp.var ∨ wVar ∉ freeVarsFormula comp.body)
         | _, _ => False) →
        v ∉ freeVarsFormula G →
        (v = comp.var ∨ v ∉ freeVarsFormula comp.body) →
        Provable SysConfig.Z
          (.imp
            (mrFormula ν comp (w.map Term.var) (substBotWithX G))
            (.imp
              (.imp G (comp.apply (.var v)))
              (comp.apply (applyGoalRealizer s w (.var v)))))) := by
  sorry

end BBS2002
