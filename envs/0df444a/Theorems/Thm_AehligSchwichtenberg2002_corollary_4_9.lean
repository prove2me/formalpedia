-- Prove2me | Theorems.Thm_AehligSchwichtenberg2002_corollary_4_9
-- name    : AehligSchwichtenberg2002.corollary_4_9
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-30T01:57:39.206682+00:00
-- url     : https://prove2.me/theorems/6d615b63-22ea-4eeb-9957-c01bfe51d035
-- title:
--   Corollary 4.9: Syntactic Characterization of Polynomial Time
-- statement:
--   Every function on binary lists/words definable by a closed term of type `!B → ... → !B → B` in the affine non-size-increasing λ-calculus with higher-type iteration is computable in polynomial time.
-- source:
--   Klaus Aehlig and Helmut Schwichtenberg, 'A syntactical analysis of non-size-increasing polynomial time computation', ACM Transactions on Computational Logic 3(3), 2002, pp. 383-401 (LICS 2000, pp. 84-91; doi:10.1145/507382.507386). Corollary 4.9, p. 398.

import Definitions.Def_AehligSchwichtenberg2002_Bounds

namespace AehligSchwichtenberg2002

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

end AehligSchwichtenberg2002
