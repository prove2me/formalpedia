-- Prove2me | Theorems.Thm_APSCounting893_Main_native_long_sum_carry_query
-- name    : APSCounting893.Main.native_long_sum_carry_query
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T21:45:15.737281+00:00
-- url     : https://prove2.me/theorems/98495ca1-4880-4c6d-b377-af1730c7c4b9
-- title:
--   Polynomial-time finite carry-certificate query machine
-- statement:
--   For each pair of fixed natural numbers $a,b$, the explicit carry-certificate query function is computable by an ordinary uniform finite multitape Turing machine in polynomial time:
--   $$\operatorname{CarryQuery}_{a,b}\in\mathrm{FP}.$$
--   Its input consists of a framed binary bit query and bounded binary fields for the carry certificate. The machine reads and checks the fields, performs binary arithmetic and chooses a single tagged block-value query or a Boolean constant. The assertion concerns the actual finite-machine semantics and imposes no oracle assumption on this preprocessing function.
--   This implementation is used to turn the generating-carry and propagating-carry criterion for iterated addition into a bounded-quantifier language.
-- source:
--   Hesse, Allender and Barrington, Uniform Constant-Depth Threshold Circuits for Division and Iterated Multiplication, JCSS 65(4), 2002, Section 3, iterated addition discussion, author manuscript p. 7, and Section 4, Lemma 4.3, https://www.cs.rutgers.edu/~allender/papers/division.pdf. Explicit finite-machine carry-certificate implementation for the coefficient arithmetic in Agarwal, Hari, Pandey and Shukla, STOC 2027 submission #893, Theorem 6.4, pp. 25–26.

import Definitions.Def_APSCounting893_Main_LongSumCarryMachine
set_option autoImplicit false
open APSCounting893.Main

theorem APSCounting893.Main.native_long_sum_carry_query (a b : ℕ) :
    Turing.MultiTapeTM.ComputableTidilyInPolyTime (longSumMatrixQuery a b)
      Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits := by sorry
