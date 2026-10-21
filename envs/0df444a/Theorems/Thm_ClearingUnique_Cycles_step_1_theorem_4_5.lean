-- Prove2me | Theorems.Thm_ClearingUnique_Cycles_step_1_theorem_4_5
-- name    : ClearingUnique.Cycles.step_1_theorem_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:50:55.611678+00:00
-- url     : https://prove2.me/theorems/661e859a-a6da-4152-98fe-d6d5ddfc23ea
-- title:
--   Proof of Theorem 4.5, Step 1, p. 16 — cyclical rows agree
-- statement:
--   Assume the three conditions of Theorem 4.5 for a financial network $N$: every successor-free cycle has positive total endowment; positive-endowment cyclical agents have positive-monotonic division rules; and zero-endowment cyclical agents have strictly monotonic division rules. Let $P^-$ and $P^+$ be its least and greatest clearing payment matrices. Then every cyclical agent has the same payment row in both matrices:
--
--   $$
--   P^-_i=P^+_i\qquad(i\in C).
--   $$
--
--   This is Step 1 of the paper's proof, isolating the agreement on cycles before the remaining components are considered.
-- source:
--   Csóka & Herings, Uniqueness of Clearing Payment Matrices in Financial Networks, GSBE Research Memorandum RM/21/014 (Maastricht University, 8 Sep 2021; doi:10.26481/umagsb.2021014), p. 16 (PDF 18), proof of Theorem 4.5, Step 1

import Mathlib
import Definitions.Def_ClearingUnique_Cycles_Model

namespace ClearingUnique.Cycles

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem step_1_theorem_4_5 (N : FinNetwork I) (hN : N.Standing)
    (h1 : ∀ i, N.Cyclical i → N.NoSuccessors (N.comp i) →
      0 < ∑ j ∈ N.comp i, N.z j)
    (h2 : ∀ i, N.Cyclical i → 0 < N.z i → PositiveMonotonic N i)
    (h3 : ∀ i, N.Cyclical i → N.z i = 0 → StrictlyMonotonic N i)
    (Pm Pp : I → I → ℝ)
    (hm : IsLeast {P : I → I → ℝ | IsClearing N P} Pm)
    (hp : IsGreatest {P : I → I → ℝ | IsClearing N P} Pp) :
    ∀ i, N.Cyclical i → ∀ j, Pm i j = Pp i j := by sorry

end ClearingUnique.Cycles
