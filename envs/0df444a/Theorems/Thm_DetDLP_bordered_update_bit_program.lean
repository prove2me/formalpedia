-- Prove2me | Theorems.Thm_DetDLP_bordered_update_bit_program
-- name    : DetDLP.bordered_update_bit_program
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T11:54:49.602804+00:00
-- url     : https://prove2.me/theorems/276cbdf2-6d90-469a-b721-5aba3a186da9
-- title:
--   Polynomial Boolean-stack implementation of the modular Hermite update
-- statement:
--   There is a fixed finite Boolean-stack program which, given the canonical encoding of $m,n,x,B,a,c$, computes the output word of the specified bounded bordered-column Hermite algorithm. Here $m\ge2$, $n\ge1$, residue inputs lie between zero and $m-1$, and $|B_{ij}|\le m$. Writing $L=n+\lceil\log_2 m\rceil$, the program halts after at most $(L+2)^k$ source instructions for an absolute $k$, leaves the serialized result on a designated stack, and writes a true halt flag on a separate stack.
-- source:
--   S. Liu, B. Zhang and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, preprint, 23 November 2026. Executable source-program obligation for Lemma 4.4.

import Definitions.Def_DetDLP_BorderedHermite
import Definitions.Def_OAIQ081S000

set_option autoImplicit false

namespace DetDLP

open OAI.Algorithms.SubexponentialSAT

theorem bordered_update_bit_program :
    ∃ (r s l : ℕ) (p : BitProgram.Program r s l) (out : Fin s) (k : ℕ),
      ∀ (m n : ℕ), 2 ≤ m → 1 ≤ n →
      ∀ (x a : Fin n → ℕ) (B : Matrix (Fin n) (Fin n) ℤ) (c : ℕ),
      (∀ i, x i < m) → (∀ i, a i < m) → c < m → (∀ i j, |B i j| ≤ (m:ℤ)) →
      let res := BorderedHermite.update m (Vector.ofFn x) (Vector.ofFn fun j => Vector.ofFn fun i => B i j)
        (Vector.ofFn a) c
      ∃ (steps : ℕ) (f : BitProgram.Cfg r s l),
        BitProgram.Trace p steps (BitProgram.initial p (encodeCosetUpdateInput m x B a c)) f ∧
        f.pc = none ∧ f.stacks out = encodeCosetRep res.1.get (fun i j => (res.2.get j).get i) ∧
        f.stacks p.outputStack = [true] ∧ steps ≤ (n+bitLen m+2)^k := by sorry

end DetDLP
