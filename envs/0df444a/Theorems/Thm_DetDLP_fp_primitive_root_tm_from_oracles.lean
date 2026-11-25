-- Prove2me | Theorems.Thm_DetDLP_fp_primitive_root_tm_from_oracles
-- name    : DetDLP.fp_primitive_root_tm_from_oracles
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T10:49:48.239535+00:00
-- url     : https://prove2.me/theorems/c3de9d29-f797-4f9f-89c5-c962b6c63014
-- title:
--   Deterministic Primitive-Root Machine Composition from Factoring and Stage I Enumeration
-- statement:
--   Given a deterministic $2^{O(n/\sqrt{\log n})}$-time prime-factorization machine (Proposition 2.6) and a deterministic $2^{O(b/(\log b)^{1/4})}$-time Stage I $\mathbb{F}_p^*$ factor-base enumeration machine whose output blocks contain a non-$\pi$-th-power witness $u^{(p-1)/\pi} \neq 1$ for every prime divisor $\pi \mid (p - 1)$, there exists a uniform deterministic multitape Turing machine computing $h = \prod_{\pi \mid (p-1)} a_\pi^{(p-1)/\pi^{v_\pi(p-1)}} \bmod p$ from input $p$ in worst-case time and space $2^{O(b/(\log b)^{1/4})}$.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 3.3, Proof of Proposition 3.3 (p. 14)

import Mathlib
import Definitions.Def_DetDLP_FactorBase

set_option autoImplicit false

namespace DetDLP

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- Machine-composition lemma for Proposition 3.3 (Section 3.3): given a deterministic factoring
machine for `p - 1` (Proposition 2.6) and a deterministic `F_p^*` factor-base enumeration machine
(Theorem 3.1) whose enumerated blocks `F` cover `F_p^*` via 2m-fold products, there exists a
deterministic multitape machine `(M, out, C)` that for every prime `p` scans the enumerated factor
base to select a witness `a_π` with `a_π ^ ((p - 1)/π) ≠ 1` for each prime divisor `π ∣ (p - 1)`
and computes the product `h = ∏ π ∈ (p - 1).primeFactors, (a_π) ^ ((p - 1) / π ^ e_π)` within
`mainSpaceBound C (bitLen p)` time and space. -/
theorem fp_primitive_root_tm_from_oracles :
    (∃ (M_fac : PrimitiveMachine) (out_fac : Fin M_fac.tapeCount) (K : ℕ),
      ∀ N : ℕ, 2 ≤ N →
        let n := bitLen (N + 1)
        RunsWithin M_fac out_fac (countWord N) (encodeNatListBin N.primeFactorsList)
          ((2 : ℝ) ^ ((K : ℝ) * (n : ℝ) / Real.sqrt (logSafe (n : ℝ))))
          (polyBound K n)) →
    (∃ (M_enum : PrimitiveMachine) (out_enum : Fin M_enum.tapeCount) (C_fb : ℕ),
      ∀ (p : ℕ) [Fact p.Prime],
        let b := bitLen p
        let m := blockCount b
        let gord := p - 1
        ∃ F : Fin m → List (ZMod p)ˣ,
          (∀ i : Fin m, (F i).Nodup) ∧
          ((∑ i : Fin m, (F i).length : ℕ) : ℝ) ≤
            (C_fb : ℝ) * ((m : ℝ) ^ 2 + (m : ℝ) * (gord : ℝ) ^ ((1 : ℝ) / (m : ℝ))) ∧
          RunsWithin M_enum out_enum (countWord p) (encodeFpFactorBlocks F)
            (mainSpaceBound C_fb b) (mainSpaceBound C_fb b) ∧
          (∀ π ∈ (p - 1).primeFactors, ∃ i : Fin m, ∃ u ∈ F i, u ^ ((p - 1) / π) ≠ 1)) →
    ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (C : ℕ),
      ∀ (p : ℕ) [Fact p.Prime],
        ∃ a : ℕ → (ZMod p)ˣ,
          (∀ π ∈ (p - 1).primeFactors, (a π) ^ ((p - 1) / π) ≠ 1) ∧
          let h := ∏ π ∈ (p - 1).primeFactors,
            (a π) ^ ((p - 1) / π ^ (p - 1).factorization π)
          RunsWithin M out (countWord p) (countWord (h : ZMod p).val)
            (mainSpaceBound C (bitLen p)) (mainSpaceBound C (bitLen p)) := by sorry

end DetDLP
