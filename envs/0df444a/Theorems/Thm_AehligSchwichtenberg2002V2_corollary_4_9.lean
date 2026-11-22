-- Prove2me | Theorems.Thm_AehligSchwichtenberg2002V2_corollary_4_9
-- name    : AehligSchwichtenberg2002V2.corollary_4_9
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-21T06:58:17.741892+00:00
-- url     : https://prove2.me/theorems/776985a3-d8cd-454a-894c-6576b6aa5669
-- title:
--   Corollary 4.9 — Polynomial step bounds on binary lists
-- statement:
--   A closed term from a tuple of binary lists to a binary list normalizes on canonical inputs with disjoint token contexts. The output length is at most the sum of input lengths. The step count is bounded by a polynomial in that sum, of degree at most the larger of one and the brace nesting depth of the term.
-- source:
--   Klaus Aehlig and Helmut Schwichtenberg (2002), A syntactical analysis of non-size-increasing polynomial time computation, Corollary 4.9. https://arxiv.org/abs/cs/0011037

import Definitions.Def_AehligSchwichtenberg2002V2_Bounds

namespace AehligSchwichtenberg2002V2

theorem corollary_4_9 {k : Nat} {t : Term}
    (ht : HasType [] t (Ty.lolliMany (List.replicate k Ty.bin) Ty.bin)) :
    ∃ B : Nat → Nat,
      IsPolyBoundedOfDegree B (Nat.max (braceDepth t) 1) ∧
      ∀ (Γ : Context) (ls : List Term) (ns : List Nat),
        ls.length = k →
        ValidBinListInputs Γ ls ns →
        ∃ (steps m : Nat) (w : Term),
          RedSteps steps (Term.appMany t ls) w ∧
          IsNormal w ∧
          listEntryCount w = some m ∧
          m ≤ sumListLengths ns ∧
          steps ≤ B (sumListLengths ns) := by sorry

end AehligSchwichtenberg2002V2
