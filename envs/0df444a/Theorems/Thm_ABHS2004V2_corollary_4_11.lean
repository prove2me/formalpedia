-- Prove2me | Theorems.Thm_ABHS2004V2_corollary_4_11
-- name    : ABHS2004V2.corollary_4_11
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-21T05:22:26.072958+00:00
-- url     : https://prove2.me/theorems/fbaf0423-1999-4146-bbe2-99f0ff9248c1
-- title:
--   Corollary 4.11 — Polynomial program extraction for data specifications
-- statement:
--   An almost closed derivation of a relativized existence specification yields a program on canonical cleaned representations of data. Its reduction takes polynomially many steps in the original input syntax length. Its output represents a source data object meeting the specification, with output resource size and free-variable count at most the input totals plus a fixed constant.
-- source:
--   Klaus Aehlig, Ulrich Berger, Martin Hofmann and Helmut Schwichtenberg (2004), An arithmetic for non-size-increasing polynomial-time computation, TCS 318, Corollary 4.11. https://www.mathematik.uni-muenchen.de/~schwicht/papers/abhs01/ICC-TCS/ansipt.pdf

import Definitions.Def_ABHS2004V2_Realizability

namespace ABHS2004V2

/-- Corollary 4.11. Extraction from an almost-closed derivation of a relativized
specification gives a program on the cleaned representations of data objects.
The program normalizes in polynomially many steps and yields a representation
of an output satisfying the original specification and the additive resource bound. -/
theorem corollary_4_11 {Δ Γ : ProofContext} {M : ProofTerm}
    {xs : List Var} {y : Var} {A : Formula}
    (hdata_xs : ∀ x ∈ xs, IsDataType x.ty)
    (hdata_y : IsDataType y.ty)
    (hnodup : (xs ++ [y]).Nodup)
    (hA : IsExistAndDisjFree A)
    (hac : IsAlmostClosedDerivation M)
    (hd : Derives Δ Γ M
      (Formula.allRel xs (.ex y (.tensor (.existPred y.ty (.var y)) A))))
    (hfresh : FreshRealizerVars Δ Γ M
      (Formula.allRel xs (.ex y (.tensor (.existPred y.ty (.var y)) A)))) :
    ∃ (B : Nat → Nat) (k : Nat),
      BoundedByPolyOfDegree B (Nat.max (iterNesting (extractCleaned M)) 1) ∧
      ∀ ws : List Term,
        ValidDataInputs (extractProof M) (xs.map Var.ty) ws →
        ∃ (cleanInputs : List Term) (steps : Nat) (w cleanOutput : Term),
          CleansDataInputs (xs.map Var.ty) ws cleanInputs ∧
          RedSteps steps
            (if cleanTy y.ty == .unit then extractCleaned M
             else Term.appMany (extractCleaned M) cleanInputs)
            cleanOutput ∧
          IsDataObject y.ty w ∧
          IsDataObject (cleanTy y.ty) cleanOutput ∧
          CleansData y.ty w cleanOutput ∧
          steps ≤ B (totalTermLength ws) ∧
          dataSize w ≤ totalDataSize ws + k ∧
          freeVarCount w ≤ totalFreeVarCount ws + k ∧
          Provable (mrContext (Δ ++ Γ)) []
            (substFormulaMany A (xs.zip ws ++ [(y, w)])) := by sorry

end ABHS2004V2
