-- Prove2me | Theorems.Thm_D1Bound5_pellCFSolutions_complete
-- name    : D1Bound5.pellCFSolutions_complete
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:32:34.005372+00:00
-- url     : https://prove2.me/theorems/7a47fafe-d438-4db0-afcd-14b65af08113
-- title:
--   Pell CFSolutions complete
-- statement:
--   A finite checked continued-fraction computation contains every positive norm-two solution below its stopping numerator. The output list is the actual filtered trace of the integer algorithm.
-- source:
--   D1Bound5/PellCFPrefixCheck.lean, lines 274-294, SHA-256 a5468d17d5b8fd8febaae9f486b606a6148827a88a3b76dca5782d036662adba. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Definitions.Def_D1Bound5_PellCFPrefixCheck_Definitions

section
namespace D1Bound5
















































theorem _root_.D1Bound5.pellCFSolutions_complete {d a0 X x y : ℤ} {N : ℕ}
    (hd : 7 ≤ d) (hcheck : pellCFPrefixCheck d a0 N = true)
    (hstop : X < (pellCFAt d a0 (pellCFInit a0) N).p)
    (hx : 0 < x) (hy : 0 < y) (heq : x^2-d*y^2=2) (hX : x ≤ X) :
    (x,y) ∈ pellCFSolutions d a0 X N := by sorry



end D1Bound5
end
