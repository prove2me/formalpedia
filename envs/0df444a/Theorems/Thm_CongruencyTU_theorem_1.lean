-- Prove2me | Theorems.Thm_CongruencyTU_theorem_1
-- name    : CongruencyTU.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:45:03.575302+00:00
-- url     : https://prove2.me/theorems/a0250a06-a47a-4b10-a3d3-87d886aa5f82
-- title:
--   Theorem 1: CCTUF with modulus 3 has a strongly polynomial-time randomized algorithm
-- statement:
--   Let $T\in\{-1,0,1\}^{k\times n}$ be totally unimodular, $b\in\mathbb Z^k$, $\gamma\in\mathbb Z^n$ and $r\in\mathbb Z$. The **CCTUF** problem with modulus $3$ asks to show infeasibility of, or find a solution of,
--   $$Tx\le b,\qquad \gamma^\top x\equiv r\pmod 3,\qquad x\in\mathbb Z^n.$$
--
--   **Theorem.** There is a strongly polynomial-time randomized algorithm for CCTUF problems with $m=3$: it always correctly detects infeasibility, and it finds a solution of a feasible problem with probability at least
--   $$1-\frac1n,$$
--   where $n$ is the number of variables.
--
--   Before this result, congruency-constrained TU problems were known to be efficiently solvable only for parity constraints ($m=2$). The case $m=3$ is the first beyond the bimodular case and a step towards integer programs with bounded subdeterminants.
--
--   **Formalization Note** "Strongly polynomial" refers to the integer RAM of `CongruencyTU.Machine`: one program, fixed in advance, whose number of unit-cost operations ($+,-,\times$, integer division and remainder, comparison, indirect addressing, coin flips) is polynomial in the number of input integers and whose intermediate numbers have bit length polynomial in the input bit size. Probabilities are fractions of coin strings.
--
--   Differences from the source:
--
--   - reading: "strongly polynomial(-time)", not defined in the paper → a fixed program of the integer RAM of CongruencyTU.Machine (unit-cost +, −, ×, Int.ediv, Int.emod, comparison, indirect addressing, coins) with cost at most p(number of input integers) and every register of bit length at most q(input bit size), p and q fixed before the input; reason: standard meaning for integer input (the paper cites [GLS93], [Sch98]); integer remainder must be unit-cost, otherwise Theorem 1 is false for a fixed-dimension instance whose feasibility is γ₁ ≡ 1 (mod 3)
--   - encoding: footnote 4: always detects infeasibility, finds a solution with probability 1 − 1/n → over uniform coin strings Fin N → Bool (N the cost bound): every coin string outputs [0] on an infeasible instance, and the fraction (in ℚ) of coin strings outputting 1 :: x with x a solution is at least 1 − 1/n on a feasible one; reason: a run of cost at most N reads at most N coins, so this is the uniform distribution over the coins the algorithm can use
--   - encoding: an instance and the algorithm's answer → the input is the list of integers [k, n, m] ++ T (row-major) ++ b ++ γ ++ residue data; the answer is [0] ("infeasible") or 1 :: x; reason: a fixed format; the input dimension is the number of integers, as in the paper's cost measure
--   - reading: 1 − 1/n, undefined at n = 0 → 1 − 1/n with Lean's 1/0 = 0, i.e. success with every coin string when n = 0; reason: an instance without variables is decided exactly by checking b ≥ 0 and the residue of 0, so this asks nothing the source's algorithm does not give
-- source:
--   Nägele, Santiago, Zenklusen, Congruency-Constrained TU Problems Beyond the Bimodular Case, arXiv:2109.03148v3 [math.OC] (preprint, 25 Apr 2023), https://arxiv.org/abs/2109.03148v3, p.2 (PDF p.3), Theorem 1 and footnote 4

import Mathlib
import Definitions.Def_CongruencyTU_Machine
import Definitions.Def_CongruencyTU_Instance

namespace CongruencyTU

/-- **Theorem 1** (Nägele–Santiago–Zenklusen, *Congruency-Constrained TU Problems Beyond the Bimodular Case*, arXiv:2109.03148v3 (preprint), p.2, PDF p.3, with footnote 4): "There is a strongly polynomial-time
randomized algorithm for CCTUF problems with m = 3." Footnote 4: "we consider a randomized algorithm
to be one that always correctly detects infeasibility of a problem, and finds a solution of a
feasible problem with high probability 1 − 1/n, where n is the number of variables."

One program and two polynomials, fixed before the instance, such that for every CCTUF instance
`Tx ≤ b, γ⊤x ≡ r (mod 3), x ∈ ℤⁿ` with `T` totally unimodular (any `k`, `n`, any integers `b, γ, r`):
every run halts within `p(|enc|)` unit-cost operations with all intermediate numbers of bit length at
most `q(σ(enc))`; on an infeasible instance every coin string yields `[0]`; on a feasible one at
least a `1 − 1/n` fraction of the coin strings yields `1 :: x` with `x` a solution.

**Formalization Note.** The machine, the coins and the bounds are those of
`Def_CongruencyTU_Machine` (`RandSolves`); "strongly polynomial" is read in the standard sense for
integer input (operation count polynomial in the number of input integers, bit lengths polynomial in
the input bit size, one fixed program), with `Int.ediv`/`Int.emod` unit-cost. At `n = 0` the bound
`1 − 1/0` is `1` in Lean, and at `n = 1` it is `0`, as printed. -/
theorem theorem_1 :
    RandSolves CInst.enc (fun P => P.enc.length) (fun P => P.Valid ∧ P.m = 3) (fun P => P.n)
      CInst.Feasible CInst.SolOut := by sorry

end CongruencyTU
