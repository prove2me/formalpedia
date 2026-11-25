-- Prove2me | Theorems.Thm_DetDLP_m89_scan_kernel_machine
-- name    : DetDLP.m89_scan_kernel_machine
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T17:54:50.144542+00:00
-- url     : https://prove2.me/theorems/407187c5-23a9-42e1-a815-2d8c8acd35a1
-- title:
--   Bounded arithmetic kernel for the ordered component scan
-- statement:
--   Given a prime $p$, the complete prime factor list of $p-1$, and an ordered list $U$ of units represented by their canonical residues, a fixed multitape machine returns the binary value of the component scan on the framed triple. Writing $b$ for the bit length of $p$ and $L$ for the length of the framed input, the time is polynomial in $b$ times $1+|U|$, and the space is polynomial in $b$ plus a constant times $L+1$. The list need not generate the group.
-- source:
--   S. Liu, B. Zhang and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, Zhejiang University preprint, 23 November 2026, Proposition 3.3 and its proof, Section 3.3.

import Definitions.Def_DetDLP_FactorBase
import Definitions.Def_DetDLP_M89_ScanArithmetic

open DetDLP OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem DetDLP.m89_scan_kernel_machine :
    ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
      ∀ (p : ℕ) [Fact p.Prime] (U : List (ZMod p)ˣ),
        let us := U.map M89Scan.unitRep
        let fs := (p-1).primeFactorsList
        let input := Encoding.encodeList id [countWord p, encodeNatListBin fs, encodeNatListBin us]
        RunsWithin M out input (countWord (M89Scan.scan p fs us))
          (polyBound K (bitLen p) * (U.length + 1 : ℝ))
          (polyBound K (bitLen p) + K * (input.length + 1 : ℝ)) := by sorry
