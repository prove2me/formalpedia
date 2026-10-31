-- Prove2me | Theorems.Thm_CongruencyTU_theorem_15
-- name    : CongruencyTU.theorem_15
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:46:54.649137+00:00
-- url     : https://prove2.me/theorems/161d10bc-64cd-4292-80dd-9a1991d5d0d2
-- title:
--   Theorem 15: CCTUF with a base-block constraint matrix and constant prime power modulus has a strongly polynomial randomized algorithm
-- statement:
--   Let $T$ be a totally unimodular matrix for which case (i) or (ii) of Theorem 14 holds. There is a strongly polynomial-time randomized algorithm for CCTUF problems $Tx\le b$, $\gamma^\top x\equiv r\pmod m$, $x\in\mathbb Z^n$ with constraint matrix $T$ and constant prime power modulus $m$.
--
--   Randomized means (footnote 4): infeasibility is always detected, and a feasible problem is solved with probability at least $1-1/n$. This is the base case of the recursion in the proof of Theorem 2.
--
--   **Formalization Note** One program per prime power $m$, uniform over all base-block matrices $T$.
--
--   Differences from the source:
--
--   - reading: "strongly polynomial(-time)", not defined in the paper → a fixed program of the integer RAM of CongruencyTU.Machine (unit-cost +, −, ×, Int.ediv, Int.emod, comparison, indirect addressing, coins) with cost at most p(number of input integers) and every register of bit length at most q(input bit size), p and q fixed before the input; reason: standard meaning for integer input (the paper cites [GLS93], [Sch98]); integer remainder must be unit-cost, otherwise Theorem 1 is false for a fixed-dimension instance whose feasibility is γ₁ ≡ 1 (mod 3)
--   - encoding: footnote 4: always detects infeasibility, finds a solution with probability 1 − 1/n → over uniform coin strings Fin N → Bool (N the cost bound): every coin string outputs [0] on an infeasible instance, and the fraction (in ℚ) of coin strings outputting 1 :: x with x a solution is at least 1 − 1/n on a feasible one; reason: a run of cost at most N reads at most N coins, so this is the uniform distribution over the coins the algorithm can use
--   - encoding: an instance and the algorithm's answer → the input is the list of integers [k, n, m] ++ T (row-major) ++ b ++ γ ++ residue data; the answer is [0] ("infeasible") or 1 :: x; reason: a fixed format; the input dimension is the number of integers, as in the paper's cost measure
--   - reading: 1 − 1/n, undefined at n = 0 → 1 − 1/n with Lean's 1/0 = 0, i.e. success with every coin string when n = 0; reason: an instance without variables is decided exactly by checking b ≥ 0 and the residue of 0, so this asks nothing the source's algorithm does not give
--   - reading: "constant prime power modulus" → for every prime power m there are a program and polynomials (∀ m, ∃ P p q, ∀ instance with modulus m); reason: the paper's running time m^{2(m−ℓ)} n^{m−ℓ+3 log₂ m+2} (p.14) has an m-dependent degree, so the program may depend on m but not on the instance
--   - reading: "Let T be a TU matrix for which case (i) or (ii) … holds. There is … an algorithm for CCTUF problems with constraint matrix T" → one program for all such T (the matrix is part of the input); reason: the theorem is used as a subroutine on every base block arising in the recursion; the T-dependent reading would be weaker
-- source:
--   Nägele, Santiago, Zenklusen, Congruency-Constrained TU Problems Beyond the Bimodular Case, arXiv:2109.03148v3 [math.OC] (preprint, 25 Apr 2023), https://arxiv.org/abs/2109.03148v3, p.9 (PDF p.10), Theorem 15

import Mathlib
import Definitions.Def_CongruencyTU_Machine
import Definitions.Def_CongruencyTU_Instance
import Definitions.Def_CongruencyTU_Seymour

namespace CongruencyTU

/-- **Theorem 15** (Nägele–Santiago–Zenklusen, *Congruency-Constrained TU Problems Beyond the Bimodular Case*, arXiv:2109.03148v3 (preprint), p.9, PDF p.10): "Let T be a TU matrix for which case (i) or (ii) in
Theorem 14 holds. There is a strongly polynomial time randomized algorithm for CCTUF problems with
constraint matrix T and constant prime power modulus."

For every prime power `m` there are one program and two polynomials such that, for every CCTUF
instance with modulus `m` whose (totally unimodular) constraint matrix `T` falls into case (i)
(`T` or `T⊤` a network matrix) or case (ii) of Theorem 14, the program is a randomized strongly
polynomial algorithm in the sense of footnote 4.

**Formalization Note.** The algorithm is uniform over all such `T` (it is the base-block subroutine
of the proof of Theorem 2); "constant prime power modulus" is `∀ m, IsPrimePow m → ∃ program`. The
network structure is not part of the input. -/
theorem theorem_15 :
    ∀ m : ℕ, IsPrimePow m →
      RandSolves CInst.enc (fun P => P.enc.length)
        (fun P => P.Valid ∧ P.m = m ∧ (SeymourCase1 P.T ∨ SeymourCase2 P.T)) (fun P => P.n)
        CInst.Feasible CInst.SolOut := by sorry

end CongruencyTU
