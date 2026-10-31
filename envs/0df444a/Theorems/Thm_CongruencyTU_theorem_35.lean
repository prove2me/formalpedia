-- Prove2me | Theorems.Thm_CongruencyTU_theorem_35
-- name    : CongruencyTU.theorem_35
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:44:58.582722+00:00
-- url     : https://prove2.me/theorems/d83aa50b-c778-4cec-a3cb-19483eb6fc04
-- title:
--   Theorem 35: CCTU with unary objective, constant modulus and a network constraint matrix has a strongly polynomial randomized algorithm
-- statement:
--   For every constant modulus $m$ there is a strongly polynomial-time randomized algorithm for CCTU problems
--   $$\min\{c^\top x: Tx\le b,\ \gamma^\top x\equiv r\pmod m,\ x\in\mathbb Z^n\}$$
--   whose constraint matrix $T$ is a network matrix and whose objective $c$ is encoded in unary.
--
--   The algorithm detects infeasibility with certainty and otherwise, with probability at least $1-1/n$, reports unboundedness or returns a minimizer. It is the base-block case of network matrices behind Theorem 15.
--
--   **Formalization Note** The input size is the number of input integers plus $\|c\|_\infty$; the network structure is not part of the input.
--
--   Differences from the source:
--
--   - reading: "strongly polynomial(-time)", not defined in the paper → a fixed program of the integer RAM of CongruencyTU.Machine (unit-cost +, −, ×, Int.ediv, Int.emod, comparison, indirect addressing, coins) with cost at most p(number of input integers) and every register of bit length at most q(input bit size), p and q fixed before the input; reason: standard meaning for integer input (the paper cites [GLS93], [Sch98]); integer remainder must be unit-cost, otherwise Theorem 1 is false for a fixed-dimension instance whose feasibility is γ₁ ≡ 1 (mod 3)
--   - reading: "constant positive modulus" → for every positive m there are a program and polynomials (∀ m, ∃ P p q, ∀ instance with modulus m); reason: the paper's running time m^{2(m−ℓ)} n^{m−ℓ+3 log₂ m+2} (p.14) has an m-dependent degree, so the program may depend on m but not on the instance
--   - reading: "unary encoded objectives" → input size |enc| + ‖c‖_∞ in the cost and bit-length bounds; reason: a unary objective has length ‖c‖₁, polynomially related to |enc| + ‖c‖_∞; the proof's bound is poly(m, |V|, |A|, max |c(a)|) (p.27)
--   - reading: "randomized" for an optimization problem (footnote 4) → every coin string outputs [0] on an infeasible instance; on a feasible one at least a 1 − 1/n fraction of coin strings outputs [1] when unbounded or 2 :: x with x a minimizer; reason: footnote 4 applied to the task "show infeasibility, unboundedness, or find a minimizer"
--   - encoding: a CCTU instance and its answer → enc = CCTUF encoding ++ c; answers [0], [1] (unbounded, footnote 5), 2 :: x; reason: a fixed format
-- source:
--   Nägele, Santiago, Zenklusen, Congruency-Constrained TU Problems Beyond the Bimodular Case, arXiv:2109.03148v3 [math.OC] (preprint, 25 Apr 2023), https://arxiv.org/abs/2109.03148v3, p.24 (PDF p.25), Theorem 35

import Mathlib
import Definitions.Def_CongruencyTU_Machine
import Definitions.Def_CongruencyTU_Instance
import Definitions.Def_CongruencyTU_Network

namespace CongruencyTU

/-- **Theorem 35** (Nägele–Santiago–Zenklusen, *Congruency-Constrained TU Problems Beyond the Bimodular Case*, arXiv:2109.03148v3 (preprint), p.24, PDF p.25): "There is a strongly polynomial time randomized algorithm
for CCTU problems with unary encoded objectives, constant modulus and constraint matrices that are
network matrices."

For every modulus `m > 0` there are one program and two polynomials such that, for every CCTU
instance `min {c⊤x : Tx ≤ b, γ⊤x ≡ r (mod m), x ∈ ℤⁿ}` with `T` a (totally unimodular) network
matrix: every run halts within `p(|enc| + ‖c‖_∞)` operations with bit lengths at most
`q(σ(enc) + |enc| + ‖c‖_∞)`; an infeasible instance always yields `[0]`; a feasible one yields, with
probability at least `1 − 1/n`, a correct answer (`[1]` if unbounded, `2 :: x` with `x` a minimizer).

**Formalization Note.** "Unary encoded objective" adds `‖c‖_∞` to the input size (the proof gives
time `poly(m, |V|, |A|, max |c(a)|)`, p.27). "Randomized" is footnote 4, applied to the optimization
problem: infeasibility is always detected and a feasible problem is solved (unboundedness reported,
footnote 5, or a minimizer found) with probability `1 − 1/n`. The network structure is not part of
the input. -/
theorem theorem_35 :
    ∀ m : ℕ, 0 < m →
      RandSolves OInst.enc (fun P => P.enc.length + P.cNorm)
        (fun P => P.Valid ∧ P.m = m ∧ IsNetworkMatrix P.T) (fun P => P.n)
        (fun P => P.Feasible) OInst.SolvedOut := by sorry

end CongruencyTU
