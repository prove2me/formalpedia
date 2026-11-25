-- Prove2me | Theorems.Thm_DetDLP_m89_scan_arithmetic_correct
-- name    : DetDLP.m89_scan_arithmetic_correct
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T16:52:07.151785+00:00
-- url     : https://prove2.me/theorems/79bc219e-2b7b-40c5-8688-7f30a0584f3f
-- title:
--   Arithmetic correctness of the prime-power component scan
-- statement:
--   For a prime $p$, consider any ordered list of units, with no generation hypothesis. The residue scan using the prime factor list of $p-1$, modular square-and-multiply, and the first witness for each distinct prime returns the canonical residue of the component product of Proposition 3.3.
-- source:
--   S. Liu, B. Zhang and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, Zhejiang University preprint, 23 November 2026, Proposition 3.3 and its proof, Section 3.3.

import Definitions.Def_DetDLP_M89_ScanArithmetic
set_option autoImplicit false
open DetDLP.M89Scan

theorem DetDLP.m89_scan_arithmetic_correct (p : ℕ) [Fact p.Prime] (us : List (ZMod p)ˣ) :
    scan p (p-1).primeFactorsList (us.map unitRep) =
      unitRep (∏ r ∈ (p-1).primeFactors,
        ((us.find? (fun u => decide (u^((p-1)/r) ≠ 1))).getD 1)^((p-1) / r^((p-1).factorization r))) := by sorry
