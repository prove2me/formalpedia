-- Prove2me | Theorems.Thm_ABHS2004_corollary_4_11
-- name    : ABHS2004.corollary_4_11
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-30T01:59:02.594818+00:00
-- url     : https://prove2.me/theorems/bf94660f-3637-40e8-ba3b-06853916376b
-- title:
--   Corollary 4.11: Polynomial-Time Program Extraction from N-HA^ω
-- statement:
--   Every numerical function `f : ℕ^k → ℕ` proven total (`!∀x₁ ∈ N ... !∀xₖ ∈ N ∃y ∈ N. A(x⃗, y)`) in `N-HA^ω` is represented by an extracted closed term `t` of the `!`-free affine λ-calculus and is therefore computable in polynomial time.
-- source:
--   Klaus Aehlig, Ulrich Berger, Martin Hofmann, and Helmut Schwichtenberg, 'An arithmetic for non-size-increasing polynomial-time computation', Theoretical Computer Science 318(1-2), 2004, pp. 3-27 (doi:10.1016/j.tcs.2003.10.023). Corollary 4.11, p. 23.

import Definitions.Def_ABHS2004_Realizability

namespace ABHS2004

theorem corollary_4_11 {Δ Γ : ProofContext} {M : ProofTerm}
    {xs : List Var} {y : Var} {A : Formula}
    (hdata_xs : ∀ x ∈ xs, IsDataType x.ty ∧ cleanTy x.ty = x.ty ∧ x.ty ≠ .unit)
    (hdata_y : IsDataType y.ty ∧ cleanTy y.ty = y.ty ∧ y.ty ≠ .unit)
    (hnodup : (xs ++ [y]).Nodup)
    (hA : IsExistAndDisjFree A)
    (hac : IsAlmostClosedDerivation Δ Γ)
    (hd : Derives Δ Γ M
      (Formula.allRel xs (.ex y (.tensor (.existPred y.ty (.var y)) A))))
    (hfresh : FreshRealizerVars Δ Γ M
      (Formula.allRel xs (.ex y (.tensor (.existPred y.ty (.var y)) A)))) :
    ∃ (B : Nat → Nat) (k : Nat),
      BoundedByPolyOfDegree B (Nat.max (iterNesting (extractCleaned M)) 1) ∧
      ∀ ws : List Term,
        ValidDataInputs (extractCleaned M) (xs.map Var.ty) ws →
        ∃ (steps : Nat) (w : Term),
          RedSteps steps (Term.appMany (extractCleaned M) ws) w ∧
          IsDataObject y.ty w ∧
          steps ≤ B (totalTermLength ws) ∧
          termLength w ≤ totalTermLength ws + k ∧
          freeVarCount w ≤ totalFreeVarCount ws + k ∧
          Provable (mrContext (Δ ++ Γ)) []
            (substFormula (substFormulaMany A (xs.zip ws)) y w) := by sorry

end ABHS2004
