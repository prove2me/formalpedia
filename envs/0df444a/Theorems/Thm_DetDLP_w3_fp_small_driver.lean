-- Prove2me | Theorems.Thm_DetDLP_w3_fp_small_driver
-- name    : DetDLP.w3_fp_small_driver
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T00:40:06.85464+00:00
-- url     : https://prove2.me/theorems/2d1934d0-e051-4307-a3ea-e8aa11dc034e
-- title:
--   Physical canonical exponent scan in the small prime-field regime
-- statement:
--   For all primes and generators of the full unit group in the small-instance regime, one fixed primitive machine outputs the first canonical exponent taking the generator to the target. Its physical execution on the prescribed binary input meets both main resource bounds with a single uniform constant.
-- source:
--   Deterministic Discrete Logarithms, §4.1–4.3, equations (4.1)–(4.5) and proof of Theorem 1.1, pp. 13–16; referee revisions R1 and R2.

import Definitions.Def_DetDLP_W3_Driver
import Definitions.Def_DetDLP_PolyTBridge
set_option autoImplicit false
open DetDLP
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem DetDLP.w3_fp_small_driver : ∃ (D : PrimitiveMachine) (out : Fin D.tapeCount) (C : ℕ),
    ∀ (p : ℕ) [Fact p.Prime] (h a : (ZMod p)ˣ), orderOf h = p-1 → ¬w3_large p (p-1) →
      w3_scanOutput (p-1) (Additive.ofMul h) (Additive.ofMul a) (fun u => RunsWithin D out
        (encodeFpDLPInput p (h : ZMod p).val (a : ZMod p).val) (countWord u)
        (mainTimeBound C (bitLen p)) (mainSpaceBound C (bitLen p))) := by sorry
