-- Prove2me | Theorems.Thm_DetDLP_fp_primitive_root_scan_tm_compile
-- name    : DetDLP.fp_primitive_root_scan_tm_compile
-- status  : Open
-- author  : @Bingsheng
-- created : 2026-11-23T11:52:30.233057+00:00
-- url     : https://prove2.me/theorems/e19cd4f6-4850-4ee6-9317-a566af3bca7f
-- title:
--   Atomic Primitive-Root Factor-Base Scan Turing Machine Compilation
-- statement:
--   Atomic multitape Turing-machine composition compiling factoring of $p-1$, Stage I factor-base enumeration, linear witness scan via `List.find?`, and modular exponentiation to compute a primitive root $h \pmod{p}$ within `mainSpaceBound C (bitLen p)` time and space.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 3.3, Proof of Proposition 3.3 (pp. 10–11)

import Mathlib
import Definitions.Def_DetDLP_FactorBase

set_option autoImplicit false

namespace DetDLP

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- Atomic multitape Turing-machine compilation leaf for Proposition 3.3 (Section 3.3):
composes a factoring oracle `M_fac` (already within `mainSpaceBound`) and a factor-base
enumeration oracle `M_enum` (with total length bounded by `mainSpaceBound`) with a deterministic
scan using `List.find?` and modular exponentiation. -/
theorem fp_primitive_root_scan_tm_compile :
    (∃ (M_fac : PrimitiveMachine) (out_fac : Fin M_fac.tapeCount) (K_fac : ℕ),
      ∀ N : ℕ, 2 ≤ N →
        let n := bitLen (N + 1)
        RunsWithin M_fac out_fac (countWord N) (encodeNatListBin N.primeFactorsList)
          (mainSpaceBound K_fac n) (mainSpaceBound K_fac n)) →
    (∃ (M_enum : PrimitiveMachine) (out_enum : Fin M_enum.tapeCount) (C_fb : ℕ),
      ∀ (p : ℕ) [Fact p.Prime],
        let b := bitLen p
        let m := blockCount b
        ∃ F : Fin m → List (ZMod p)ˣ,
          (∀ i : Fin m, (F i).Nodup) ∧
          ((∑ i : Fin m, (F i).length : ℕ) : ℝ) ≤ mainSpaceBound C_fb b ∧
          RunsWithin M_enum out_enum (countWord p) (encodeFpFactorBlocks F)
            (mainSpaceBound C_fb b) (mainSpaceBound C_fb b) ∧
          (∀ π ∈ (p - 1).primeFactors, ∃ i : Fin m, ∃ u ∈ F i, u ^ ((p - 1) / π) ≠ 1)) →
    ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (C : ℕ),
      ∀ (p : ℕ) [Fact p.Prime],
        let b := bitLen p
        let m := blockCount b
        ∃ F : Fin m → List (ZMod p)ˣ,
          (∀ π ∈ (p - 1).primeFactors, ∃ i : Fin m, ∃ u ∈ F i, u ^ ((p - 1) / π) ≠ 1) ∧
          let U : List (ZMod p)ˣ := (List.ofFn F).flatten
          let a : ℕ → (ZMod p)ˣ := fun π =>
            (U.find? (fun u => decide (u ^ ((p - 1) / π) ≠ 1))).getD 1
          let h : (ZMod p)ˣ :=
            ∏ π ∈ (p - 1).primeFactors,
              (a π) ^ ((p - 1) / π ^ (p - 1).factorization π)
          RunsWithin M out (countWord p) (countWord (h : ZMod p).val)
            (mainSpaceBound C b) (mainSpaceBound C b) := by sorry

end DetDLP
