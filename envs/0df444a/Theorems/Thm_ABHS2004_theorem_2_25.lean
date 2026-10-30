-- Prove2me | Theorems.Thm_ABHS2004_theorem_2_25
-- name    : ABHS2004.theorem_2_25
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-30T01:58:09.098357+00:00
-- url     : https://prove2.me/theorems/781d5724-8400-4aaa-b8e9-a80da0140554
-- title:
--   Theorem 2.25: Polynomial-Time Soundness of the Affine Term Calculus
-- statement:
--   Every numerical function `f : ℕ^n → ℕ` represented by a closed term `M` of the `!`-free affine term system is computable in polynomial time (`IsPolyTimeComputable f`).
-- source:
--   Klaus Aehlig, Ulrich Berger, Martin Hofmann, and Helmut Schwichtenberg, 'An arithmetic for non-size-increasing polynomial-time computation', Theoretical Computer Science 318(1-2), 2004, pp. 3-27 (doi:10.1016/j.tcs.2003.10.023). Theorem 2.25, p. 14.

import Definitions.Def_ABHS2004_TermSystem

namespace ABHS2004

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
          termLength w ≤ totalTermLength ws + k ∧
          freeVarCount w ≤ totalFreeVarCount ws + k := by sorry

end ABHS2004
