-- Prove2me | Theorems.Thm_CongruencyTU_theorem_2
-- name    : CongruencyTU.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:45:09.625053+00:00
-- url     : https://prove2.me/theorems/e1318536-6c01-4c92-aa22-317f39c4f2c0
-- title:
--   Theorem 2: R-CCTUF with constant prime modulus m and |R| ≥ m − 2 has a strongly polynomial randomized algorithm
-- statement:
--   For every constant prime modulus $m$ there is a strongly polynomial-time randomized algorithm for R-CCTUF problems
--   $$Tx\le b,\qquad\gamma^\top x\in R\pmod m,\qquad x\in\mathbb Z^n$$
--   with $T$ totally unimodular and $|R|\ge m-2$ target residues.
--
--   Randomized means (footnote 4): infeasibility is always detected, and a feasible problem is solved with probability at least $1-1/n$, $n$ the number of variables. For $m=3$, an R-CCTUF problem with $|R|=1$ is a CCTUF problem, so Theorem 1 follows.
--
--   **Formalization Note** One program per prime $m$; the input lists $R$ explicitly.
--
--   Differences from the source:
--
--   - reading: "strongly polynomial(-time)", not defined in the paper → a fixed program of the integer RAM of CongruencyTU.Machine (unit-cost +, −, ×, Int.ediv, Int.emod, comparison, indirect addressing, coins) with cost at most p(number of input integers) and every register of bit length at most q(input bit size), p and q fixed before the input; reason: standard meaning for integer input (the paper cites [GLS93], [Sch98]); integer remainder must be unit-cost, otherwise Theorem 1 is false for a fixed-dimension instance whose feasibility is γ₁ ≡ 1 (mod 3)
--   - encoding: footnote 4: always detects infeasibility, finds a solution with probability 1 − 1/n → over uniform coin strings Fin N → Bool (N the cost bound): every coin string outputs [0] on an infeasible instance, and the fraction (in ℚ) of coin strings outputting 1 :: x with x a solution is at least 1 − 1/n on a feasible one; reason: a run of cost at most N reads at most N coins, so this is the uniform distribution over the coins the algorithm can use
--   - encoding: an instance and the algorithm's answer → the input is the list of integers [k, n, m] ++ T (row-major) ++ b ++ γ ++ residue data; the answer is [0] ("infeasible") or 1 :: x; reason: a fixed format; the input dimension is the number of integers, as in the paper's cost measure
--   - reading: 1 − 1/n, undefined at n = 0 → 1 − 1/n with Lean's 1/0 = 0, i.e. success with every coin string when n = 0; reason: an instance without variables is decided exactly by checking b ≥ 0 and the residue of 0, so this asks nothing the source's algorithm does not give
--   - reading: "constant prime modulus" → for every prime m there are a program and polynomials (∀ m, ∃ P p q, ∀ instance with modulus m); reason: the paper's running time m^{2(m−ℓ)} n^{m−ℓ+3 log₂ m+2} (p.14) has an m-dependent degree, so the program may depend on m but not on the instance
-- source:
--   Nägele, Santiago, Zenklusen, Congruency-Constrained TU Problems Beyond the Bimodular Case, arXiv:2109.03148v3 [math.OC] (preprint, 25 Apr 2023), https://arxiv.org/abs/2109.03148v3, p.2 (PDF p.3), Theorem 2

import Mathlib
import Definitions.Def_CongruencyTU_Machine
import Definitions.Def_CongruencyTU_Instance

namespace CongruencyTU

/-- **Theorem 2** (Nägele–Santiago–Zenklusen, *Congruency-Constrained TU Problems Beyond the Bimodular Case*, arXiv:2109.03148v3 (preprint), p.2, PDF p.3): "There is a strongly polynomial-time randomized algorithm for
R-CCTUF problems with constant prime modulus m and |R| ≥ m − 2."

For every prime `m` there are one program and two polynomials such that, for every R-CCTUF instance
`Tx ≤ b, γ⊤x ∈ R (mod m), x ∈ ℤⁿ` with `T` totally unimodular and `|R| ≥ m − 2`, the program is a
randomized strongly polynomial algorithm in the sense of footnote 4 (`RandSolves`).

**Formalization Note.** "Constant prime modulus" is `∀ m prime, ∃ program`: the program and its
polynomials may depend on `m` (the paper's bound `m^{2(m−ℓ)} n^{m−ℓ+3 log₂ m+2}`, p.14, has an
`m`-dependent degree). `|R| ≥ m − 2` includes `|R| = m − 1`, `|R| = m`, and every `R` when `m = 2`. -/
theorem theorem_2 :
    ∀ m : ℕ, m.Prime →
      RandSolves RInst.enc (fun P => P.enc.length)
        (fun P => P.Valid ∧ P.m = m ∧ m - 2 ≤ P.R.card) (fun P => P.n)
        RInst.Feasible RInst.SolOut := by sorry

end CongruencyTU
