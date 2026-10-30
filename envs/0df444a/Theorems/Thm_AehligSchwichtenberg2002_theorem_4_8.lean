-- Prove2me | Theorems.Thm_AehligSchwichtenberg2002_theorem_4_8
-- name    : AehligSchwichtenberg2002.theorem_4_8
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-30T01:57:28.216781+00:00
-- url     : https://prove2.me/theorems/cbba3b20-e4d3-4b3d-b293-64785440d99d
-- title:
--   Theorem 4.8: Polynomial Normalization of Closed Terms Applied to Base Arguments
-- statement:
--   For every closed well-typed term `r : !B → ... → !B → B`, there exists a polynomial `P` such that `r (!v₁) ... (!vₖ)` normalizes in at most `P(|v₁| + ... + |vₖ|)` steps with all intermediate terms bounded in size by `P(|v₁| + ... + |vₖ|)`.
-- source:
--   Klaus Aehlig and Helmut Schwichtenberg, 'A syntactical analysis of non-size-increasing polynomial time computation', ACM Transactions on Computational Logic 3(3), 2002, pp. 383-401 (LICS 2000, pp. 84-91; doi:10.1145/507382.507386). Theorem 4.8, p. 398.

import Definitions.Def_AehligSchwichtenberg2002_Bounds

namespace AehligSchwichtenberg2002

theorem theorem_4_8 {Γ : Context} {t : Term} {τ : Ty}
    (ht : HasType Γ t τ) :
    (∀ (N : Nat) (t' : Term),
      freeVarCard t ≤ N → RedStep t t' → stepMeasure t' N < stepMeasure t N) ∧
    (∀ (k : Nat) (t' : Term),
      RedSteps k t t' → k ≤ stepMeasure t (freeVarCard t)) := by sorry

end AehligSchwichtenberg2002
