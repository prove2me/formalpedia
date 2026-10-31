-- Prove2me | Theorems.Thm_CongruencyTU_theorem_52
-- name    : CongruencyTU.theorem_52
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:45:28.20944+00:00
-- url     : https://prove2.me/theorems/7d55eab5-66b0-4965-a2d9-89dccae0399f
-- title:
--   Theorem 52: CCTU problems whose constraint matrix has a constant-size core are solvable in strongly polynomial time
-- statement:
--   CCTU problems with modulus $m$ and a constraint matrix $T$ that has a core of constant size can be solved in strongly polynomial time
--
--   1. by a randomized algorithm if the objective is unary encoded and $m$ is constant, or
--   2. by a deterministic algorithm if $m$ is a constant prime power.
--
--   In particular this covers case (ii) of Theorem 14, the last base block.
--
--   **Formalization Note** For every bound $s$ on the rows and columns of a core and every modulus $m$ there is a program; outputs and the randomized notion are as in Theorems 35 and 40.
--
--   Differences from the source:
--
--   - reading: "strongly polynomial(-time)", not defined in the paper → a fixed program of the integer RAM of CongruencyTU.Machine (unit-cost +, −, ×, Int.ediv, Int.emod, comparison, indirect addressing, coins) with cost at most p(number of input integers) and every register of bit length at most q(input bit size), p and q fixed before the input; reason: standard meaning for integer input (the paper cites [GLS93], [Sch98]); integer remainder must be unit-cost, otherwise Theorem 1 is false for a fixed-dimension instance whose feasibility is γ₁ ≡ 1 (mod 3)
--   - reading: "a core of constant size", "m is constant" → ∀ s m, ∃ program: the program may depend on the size bound s (rows and columns of a core) and on m, not on the instance; reason: the paper's reduction (Lemma 53) makes m^{O(ℓ)} subproblems, ℓ the core size
--   - reading: "a core" (Definition 51, "smallest possible submatrix") → some submatrix reachable by the deletions to which no deletion applies, with at most s rows and s columns; reason: "working with any core would be enough" (p.34); a minimum-size reading gives the same notion of having a core of size at most s
--   - reading: (i) "randomized … unary encoded objective" → as in Theorem 35: size |enc| + ‖c‖_∞, footnote 4 applied to the optimization task; reason: same notions as Theorem 35, which (i) uses
--   - encoding: a CCTU instance and its answer → enc = CCTUF encoding ++ c; answers [0], [1], 2 :: x; reason: a fixed format
-- source:
--   Nägele, Santiago, Zenklusen, Congruency-Constrained TU Problems Beyond the Bimodular Case, arXiv:2109.03148v3 [math.OC] (preprint, 25 Apr 2023), https://arxiv.org/abs/2109.03148v3, p.34 (PDF p.35), Theorem 52; Definition 51

import Mathlib
import Definitions.Def_CongruencyTU_Machine
import Definitions.Def_CongruencyTU_Instance
import Definitions.Def_CongruencyTU_Core

namespace CongruencyTU

/-- **Theorem 52** (Nägele–Santiago–Zenklusen, *Congruency-Constrained TU Problems Beyond the Bimodular Case*, arXiv:2109.03148v3 (preprint), p.34, PDF p.35): "CCTU problems with modulus m and a constraint matrix T that
has a core of constant size can be solved in strongly polynomial time (i) by a randomized algorithm
if the objective is unary encoded and m is constant, or (ii) by a deterministic algorithm if m is a
constant prime power."

For every size bound `s` (rows and columns of a core, Definition 51) and every modulus `m`:
(i) if `m > 0`, a randomized strongly polynomial algorithm (footnote 4) with input size
`|enc| + ‖c‖_∞` solves every CCTU instance with modulus `m` whose totally unimodular `T` has a core of
at most `s` rows and `s` columns; (ii) if `m` is a prime power, a deterministic strongly polynomial
algorithm solves them (binary `c`).

**Formalization Note.** "Constant size" and "constant modulus" are the quantifier order
`∀ s m, ∃ program`. A core is any submatrix reachable by the deletions of Definition 51 to which no
deletion applies (the paper: "working with any core would be enough"). Outputs as in Theorems 35
and 40. -/
theorem theorem_52 :
    ∀ s m : ℕ,
      (0 < m →
        RandSolves OInst.enc (fun P => P.enc.length + P.cNorm)
          (fun P => P.Valid ∧ P.m = m ∧ HasCoreOfSize P.T s) (fun P => P.n)
          (fun P => P.Feasible) OInst.SolvedOut) ∧
      (IsPrimePow m →
        DetSolves OInst.enc (fun P => P.enc.length)
          (fun P => P.Valid ∧ P.m = m ∧ HasCoreOfSize P.T s) OInst.CorrectOut) := by sorry

end CongruencyTU
