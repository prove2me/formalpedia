-- Prove2me | Theorems.Thm_DetDLP_m3c_fp_stage2_driver_from_counts
-- name    : DetDLP.m3c_fp_stage2_driver_from_counts
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-25T09:57:42.111807+00:00
-- url     : https://prove2.me/theorems/6969380c-2320-42c1-b083-f8ec0061083e
-- title:
--   The finite-field Stage II driver with the Stage I counting machine
-- statement:
--   Given the uniform Stage I counting machine, the factor-base enumerator and decoder, the terminal tensor-network operations and the HNF updates, a primitive machine runs the finite-field Stage II trace or small-group scan within the time and workspace bounds of Theorem 1.1.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_W3_Driver
import Definitions.Def_DetDLP_M89_S1_Queries
set_option autoImplicit false
open DetDLP
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem DetDLP.m3c_fp_stage2_driver_from_counts
    (counts : M89S1.CountOracle)
    (en : PrimitiveMachine) (eo : Fin en.tapeCount) (de : PrimitiveMachine) (do' : Fin de.tapeCount) (K : ℕ)
    (hnet : w3_terminalOps w3_fpQueries) (hupdate : w3_hnfOps) :
    ∃ (D : PrimitiveMachine) (out : Fin D.tapeCount) (C : ℕ),
      ∀ (p : ℕ) [Fact p.Prime] (h a : (ZMod p)ˣ),
        let M := p-1
        let m := blockCount (bitLen p)
        orderOf h = M →
          let accepts := fun u => RunsWithin D out (encodeFpDLPInput p (h : ZMod p).val (a : ZMod p).val) (countWord u)
                                    (mainTimeBound C (bitLen p)) (mainSpaceBound C (bitLen p))
          (¬ w3_large p M → w3_scanOutput M (Additive.ofMul h) (Additive.ofMul a) accepts) ∧
          (∀ hg : w3_large p M, letI : NeZero M := ⟨by have := hg.2.1; omega⟩
            ∀ F : Fin m → List (ZMod p)ˣ, w3_fpBaseCalls en eo de do' K F →
              ∃ (seed : FpSeed p m) (B : Fin m → List (ZMod p)ˣ),
                (∀ i, (B i).Nodup ∧ (B i).toFinset = fpFactorBlock (hashThreshold p M m M) seed i) ∧
                w3_traceOutput (w3_fpFB F) (w3_fpFB B) M (Additive.ofMul h) (Additive.ofMul a) accepts) := by sorry
