-- Prove2me | Theorems.Thm_DetDLP_prime_power_component_scan_machine
-- name    : DetDLP.prime_power_component_scan_machine
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T10:41:39.098514+00:00
-- url     : https://prove2.me/theorems/7233a52f-f8d3-4028-8989-f4a5b53f54a1
-- title:
--   Composition of factorization and factor-block scans for prime-power components
-- statement:
--   Suppose a uniform deterministic machine factors $N\ge2$ in the time and space of Proposition 2.6. Let another machine, on a prime $p$, enumerate lists of units with the Stage I time and space bounds. For any such output, let $U$ be the lists concatenated in order, let $n=p-1$, and for each prime $r\mid n$ take the first $w_r\in U$ with $w_r^{n/r}≠1$, taking $1$ if the scan is exhausted. There exists a uniform deterministic machine which writes the binary value of
--   $$\prod_{r\mid n,\ r\text{ prime}} w_r^{n/r^{v_r(n)}}\pmod p$$
--   in Stage I time and space. The specification applies to every valid enumerated output, regardless of whether it generates the group. The case $n=1$ has empty product.
-- source:
--   S. Liu, B. Zhang and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, Zhejiang University preprint, 23 November 2026, Proposition 3.3 and its proof, Section 3.3.

import Mathlib
import Definitions.Def_DetDLP_FactorBase

set_option autoImplicit false

namespace DetDLP

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem prime_power_component_scan_machine
    (Mf : PrimitiveMachine) (ofac : Fin Mf.tapeCount) (Kf : ℕ)
    (hfac : ∀ N : ℕ, 2 ≤ N →
      let n := bitLen (N+1)
      RunsWithin Mf ofac (countWord N) (encodeNatListBin N.primeFactorsList)
        ((2 : ℝ)^((Kf : ℝ)*n/Real.sqrt (logSafe n))) (polyBound Kf n))
    (Me : PrimitiveMachine) (oe : Fin Me.tapeCount) (Ke : ℕ) :
    ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (C : ℕ),
      ∀ (p : ℕ) [Fact p.Prime],
        let b := bitLen p
        let m := blockCount b
        ∀ F : Fin m → List (ZMod p)ˣ,
          RunsWithin Me oe (countWord p) (encodeFpFactorBlocks F)
            (mainSpaceBound Ke b) (mainSpaceBound Ke b) →
          let n := p-1
          let U := (List.ofFn F).flatten
          let h : (ZMod p)ˣ := ∏ r ∈ n.primeFactors,
            ((U.find? (fun u => decide (u^(n/r) ≠ 1))).getD 1) ^ (n / r^(n.factorization r))
          RunsWithin M out (countWord p) (countWord (h : ZMod p).val)
            (mainSpaceBound C b) (mainSpaceBound C b) := by sorry

end DetDLP
