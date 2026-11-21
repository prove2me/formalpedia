-- Prove2me | Theorems.Thm_ABHS2004V2_theorem_2_25
-- name    : ABHS2004V2.theorem_2_25
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-21T05:21:25.863758+00:00
-- url     : https://prove2.me/theorems/baa9713c-75d0-4714-b9af-92dad587b778
-- title:
--   Theorem 2.25 — Polynomial step and resource bounds on data
-- statement:
--   An almost closed program between data types normalizes on canonical inputs. A polynomial in total input syntax length bounds the step count, with degree at most the larger of one and the iterator depth. Both the output resource size and its free-variable count are bounded by the corresponding input totals plus a program-dependent constant.
-- source:
--   Klaus Aehlig, Ulrich Berger, Martin Hofmann and Helmut Schwichtenberg (2004), An arithmetic for non-size-increasing polynomial-time computation, TCS 318, Theorem 2.25. https://www.mathematik.uni-muenchen.de/~schwicht/papers/abhs01/ICC-TCS/ansipt.pdf

import Definitions.Def_ABHS2004V2_TermSystem

namespace ABHS2004V2

/-- Theorem 2.25. An almost-closed program between data types normalizes on
canonical inputs in polynomially many steps. The nested number of list cells
in the result grows by at most a constant depending on the program. -/
theorem theorem_2_25 {τs : List Ty} {τ : Ty} {r : Term}
    (hdata_in : ∀ σ ∈ τs, IsDataType σ)
    (hdata_out : IsDataType τ)
    (ht : HasType r (Ty.lolliMany τs τ))
    (hac : IsAlmostClosed r) :
    ∃ (B : Nat → Nat) (k : Nat),
      BoundedByPolyOfDegree B (Nat.max (iterNesting r) 1) ∧
      ∀ ws : List Term,
        ValidDataInputs r τs ws →
        ∃ (steps : Nat) (w : Term),
          RedSteps steps (Term.appMany r ws) w ∧
          IsDataObject τ w ∧
          steps ≤ B (totalTermLength ws) ∧
          dataSize w ≤ totalDataSize ws + k ∧
          freeVarCount w ≤ totalFreeVarCount ws + k := by sorry

end ABHS2004V2
