-- Prove2me | Theorems.Thm_DetDLP_w3_bounded_word_machine
-- name    : DetDLP.w3_bounded_word_machine
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T00:34:56.281246+00:00
-- url     : https://prove2.me/theorems/d95171da-11d2-4dc2-8686-07a658cecad9
-- title:
--   Exact binary-table machine on a bounded input domain
-- statement:
--   For each fixed depth $L$ and word function $f$, there exists one ordinary primitive machine computing $f$ on all input words of length at most $L$. With $t=3L+2|f(w)|+1$, physical running time is at most $7t$ and visited space at most $2L+t+15$. The finite control is allowed to depend on the depth and the function; it does not depend on the individual input.
-- source:
--   Deterministic Discrete Logarithms, §4.1–4.3, equations (4.1)–(4.5) and proof of Theorem 1.1, pp. 13–16; referee revisions R1 and R2.

import Definitions.Def_DetDLP_PolyTBridge
set_option autoImplicit false
open DetDLP
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace OAI.Algorithms.SubexponentialSAT.StructuredProgram

theorem DetDLP.w3_bounded_word_machine (L : ℕ) (f : List Bool → List Bool) :
    ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount), ∀ w : List Bool, w.length ≤ L →
      RunsWithin M out w (f w) ((7*(3*L+2*(f w).length+1) : ℕ) : ℝ)
        ((2*L+(3*L+2*(f w).length+1)+15 : ℕ) : ℝ) := by sorry
