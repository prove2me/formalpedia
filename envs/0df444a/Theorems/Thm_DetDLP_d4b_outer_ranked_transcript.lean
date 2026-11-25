-- Prove2me | Theorems.Thm_DetDLP_d4b_outer_ranked_transcript
-- name    : DetDLP.d4b_outer_ranked_transcript
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T08:41:57.906015+00:00
-- url     : https://prove2.me/theorems/e8b67274-e907-4b3d-a0d9-6b56fc76a606
-- title:
--   Bounded transcript of the outer scalar cursor
-- statement:
--   Given the binary coefficient promise and certified oracle calls on the typed states, the outer cursor runs to the terminal answer. Its round bound counts the header-buffer growth, the branch reads, and all digit evaluations.
-- source:
--   Controller and run invariant for DetDLP.d4_outer_scalar_cursor_machine_v2 (dc44082d-fc56-402c-8efa-dc7eda4aebd8).

import Definitions.Def_DetDLP_D4BOuterInvariant
set_option autoImplicit false
open DetDLP DetDLP.D4BOuter DetDLP.D4Plan DetDLP.D4BEntry OAI.Algorithms.SubexponentialSAT.Computation

theorem DetDLP.d4b_outer_ranked_transcript {C c : ℕ} {x : Input C c} (P : Plan x) (v : DigitsData P) (L : ℕ) {O : PrimitiveMachine} {o : Fin O.tapeCount} {τ σ : ℝ} {H B : ℕ}
    (G : BranchOracle P v O o τ σ H B) (hL : L ≤ Nat.clog 2 x.S)
    (bin : ∀ i < P.f.natDegree, P.f.coeff i = 0 ∨ P.f.coeff i = 1)
    (h0 : (pair (input x) []).length ≤ H)
    (hd : ∀ buf : D4BOuter.Bits, buf.length ≤ 2 * need P + 1 → Call O o τ σ H (hdState x buf) 1 (rankQuery x 0) (header P)) :
    ∃ r, 1 ≤ r ∧ r ≤ need P+3+P.N*(B+1) ∧ TraceAt L O o τ σ H (answer x) r (input x) [] := by sorry
