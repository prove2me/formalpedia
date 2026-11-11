-- Prove2me | Theorems.Thm_ConstrainedDirSep_STSep_theorem_4_8
-- name    : ConstrainedDirSep.STSep.theorem_4_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:07:48.917651+00:00
-- url     : https://prove2.me/theorems/633c16a0-bfd2-4f81-8085-66d3ca0a0b46
-- title:
--   Theorem 4.8 — Chain CSP in time 2^O(r log r) N^O(1), and minimum cost in 2^O(r log r) (N + ‖ω‖)^O(1)
-- statement:
--   There are a constant $C$ and two deterministic multi-stack Turing machines $M_1,M_2$ such that for every Chain CSP instance $I$ (satisfying the chain promise) with $r$ variables and total domain size $N=\sum_{i=1}^r d_i$:
--
--   1. $M_1$ on the encoding of $I$ halts within $C\cdot2^{C\,r\log r}\cdot(N+1)^C$ steps and outputs a satisfying assignment of $I$, or "none" when there is none;
--   2. for nonnegative integer unary costs $\omega_i(p)$, $M_2$ on the encoding of $I$ and the binary costs halts within
--   $$C\cdot 2^{C\,r\log r}\cdot(N+\|\omega\|+1)^C$$
--   steps and outputs a satisfying assignment of minimum cost $\sum_i\omega_i(x_i)$, or "none" when there is none,
--
--   where $\log r=\log_2\max\{r,2\}$ and $\|\omega\|$ is the total binary encoding length of all unary costs. Theorem 1.1 solves one Chain CSP instance per representation and target digraph with this algorithm.
--
--   Differences from the source:
--   - reading: "I can be solved" → the search version: a satisfying assignment is output, or "none"; reason: the stronger of the two readings, and the one the proof gives (it returns a satisfying assignment).
--   - reading: unnamed machine model → a deterministic Mathlib multi-stack Turing machine (TM2); reason: the bounds are polynomial in N (resp. N + ‖ω‖) for fixed r, the same in all polynomially equivalent deterministic models.
--   - encoding: 2^{O(r log r)} N^{O(1)} → C·2^{C·r·⌊log₂ max(r, 2)⌋}·(N + 1)^C with one universal constant C (and N + ‖ω‖ + 1 in the weighted case); reason: the floor changes log₂ by a factor at most 2 and N + 1 avoids 0^C, both absorbed in C.
--   - encoding: the instance → explicit membership bits of every U_i, Q_ij, F_ij, B_ij and the adjacency matrix of Π, of length polynomial in N; reason: the source encodes all sets explicitly and notes the size is polynomial in N.
-- source:
--   Olkowski, Ramanujan, Constrained Directed Separation: Algorithms and Classifications, STOC 2027 submission (manuscript sha256 4dd06c29…), p. 17 (PDF 20), Theorem 4.8

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_ConstrainedDirSep_STSep_Encoding
import Definitions.Def_ConstrainedDirSep_STSep_Quadrant
import Definitions.Def_ConstrainedDirSep_STSep_ChainCSP

namespace ConstrainedDirSep.STSep

/-- Olkowski, Ramanujan, *Constrained Directed Separation*, STOC 2027 submission (manuscript
sha256 4dd06c29…), p. 17 (PDF 20), Theorem 4.8 (Chain CSP algorithm): a Chain CSP instance with
`r` variables and total domain size `N` is solved in time `2^{O(r log r)} N^{O(1)}`; with
nonnegative integer unary costs a minimum-cost satisfying assignment is computed in time
`2^{O(r log r)} (N + ‖ω‖)^{O(1)}`. `log r` is `log₂ max{r, 2}`. -/
theorem theorem_4_8 :
    ∃ C : ℕ, ∃ M₁ M₂ : Turing.TM2ComputableAux Bool Bool,
      (∀ I : ChainCSP, I.WF →
        ∃ out : List Bool,
          HMBinPacking.OutputsWithin M₁ (encChainCSP I) out
            (C * 2 ^ (C * I.r * Nat.log 2 (max I.r 2)) * (I.N + 1) ^ C) ∧
          ((out = encNone ∧ ∀ x, ¬ I.Satisfies x) ∨
            ∃ x : Fin I.r → ℕ, out = encAssign x ∧ I.Satisfies x)) ∧
      (∀ I : ChainCSP, I.WF → ∀ ω : Fin I.r → ℕ → ℕ,
        ∃ out : List Bool,
          HMBinPacking.OutputsWithin M₂ (encWChainCSP I ω) out
            (C * 2 ^ (C * I.r * Nat.log 2 (max I.r 2)) * (I.N + I.costLength ω + 1) ^ C) ∧
          ((out = encNone ∧ ∀ x, ¬ I.Satisfies x) ∨
            ∃ x : Fin I.r → ℕ, out = encAssign x ∧ I.Satisfies x ∧
              ∀ y : Fin I.r → ℕ, I.Satisfies y → assignCost ω x ≤ assignCost ω y)) := by sorry

end ConstrainedDirSep.STSep
