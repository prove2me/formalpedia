-- Prove2me | Theorems.Thm_CongruencyTU_theorem_22
-- name    : CongruencyTU.theorem_22
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:46:55.361083+00:00
-- url     : https://prove2.me/theorems/ab1a548d-a94d-4ecf-8ceb-2c469da6f09e
-- title:
--   Theorem 22: one decomposition step for R-CCTUF problems with prime modulus and ℓ ∈ {m − 1, m − 2} target residues
-- statement:
--   Consider an R-CCTUF problem with prime modulus $m$, $n$ variables, $\ell\in\{m-1,m-2\}$ target residues, and a constraint matrix falling into case (iii) of Theorem 14, with smaller block of $p=\min\{n_A,n_B\}$ columns. After solving fewer than $3(m-\ell+1)^2$ R-CCTUF problems with $p$ variables, modulus $m$ and at most $\ell$ target residues, one can determine in strongly polynomial time either a solution of the problem, or a family $\mathcal F$ of at most
--
--   1. one R-CCTUF problem with at most $n-p+1$ variables, modulus $m$ and $\ell$ target residues, and
--   2. $(m-\ell+1)^2$ R-CCTUF problems with $n-p$ variables, modulus $m$ and at least $\ell+1$ target residues,
--
--   such that the initial problem is feasible if and only if some problem in $\mathcal F$ is feasible. Moreover, a feasible solution of any problem in $\mathcal F$ can be transformed in strongly polynomial time into one of the initial problem.
--
--   This is the recursion step of the proof of Theorem 2.
--
--   **Formalization Note** The reduction is a program with an oracle that solves the smaller R-CCTUF problems; the statement holds for every oracle meeting that specification, counts the queries, and requires every query to be a valid smaller problem. The input is the problem in its decomposed form (1).
--
--   Differences from the source:
--
--   - reading: "strongly polynomial(-time)", not defined in the paper → a fixed program of the integer RAM of CongruencyTU.Machine (unit-cost +, −, ×, Int.ediv, Int.emod, comparison, indirect addressing, coins) with cost at most p(number of input integers) and every register of bit length at most q(input bit size), p and q fixed before the input; reason: standard meaning for integer input (the paper cites [GLS93], [Sch98]); integer remainder must be unit-cost, otherwise Theorem 1 is false for a fixed-dimension instance whose feasibility is γ₁ ≡ 1 (mod 3)
--   - reading: "after solving less than 3(m − ℓ + 1)² many R-CCTUF problems with p variables, modulus m, and at most ℓ target residues" → a program with oracle access, correct for every oracle that answers [0] or 1 :: x on encodings of valid R-CCTUF problems with p variables, modulus m and at most ℓ residues; it makes fewer than 3(m − ℓ + 1)² queries, each such an encoding; a query costs 1 + its length + the answer's length and answers count towards the bit-size bound; reason: the standard oracle-reduction reading of "after solving … problems"
--   - reading: "a constraint matrix T falling into case (iii) of Theorem 14", "p = min{nA, nB}" → the problem given in its decomposed form (1) (Form1 with TU summands, nA, nB ≥ 2, permutations applied); the initial problem is Form1.toRInst on nA + nB variables; reason: p refers to "the decomposition", which the algorithm receives
--   - reading: "a feasible solution to any problem in F can … be transformed to one of the initial problem" → a program Pt reading the input, the reduction's output (the family followed by auxiliary data it computed) and the index of the member and its solution; reason: the transformation may use what the reduction computed
--   - encoding: "a solution of the problem, or a family F" → output 1 :: x, or 0 :: pack (encodings of the members ++ [auxiliary data]); reason: a fixed format for the answer
-- source:
--   Nägele, Santiago, Zenklusen, Congruency-Constrained TU Problems Beyond the Bimodular Case, arXiv:2109.03148v3 [math.OC] (preprint, 25 Apr 2023), https://arxiv.org/abs/2109.03148v3, p.13 (PDF p.14), Theorem 22

import Mathlib
import Definitions.Def_CongruencyTU_Machine
import Definitions.Def_CongruencyTU_Instance
import Definitions.Def_CongruencyTU_Pattern

namespace CongruencyTU

/-- **Theorem 22** (Nägele–Santiago–Zenklusen, *Congruency-Constrained TU Problems Beyond the Bimodular Case*, arXiv:2109.03148v3 (preprint), p.13, PDF p.14): "Consider an R-CCTUF problem with prime modulus m, n
variables, ℓ ∈ {m − 1, m − 2} many target residues, and a constraint matrix T falling into case
(iii) of Theorem 14. Let p = min{nA, nB} be the number of columns of the smaller matrix in the
decomposition. After solving less than 3(m − ℓ + 1)² many R-CCTUF problems with p variables,
modulus m, and at most ℓ target residues, we can in strongly polynomial time determine either a
solution of the problem, or a family F of at most – one R-CCTUF problem with at most n − p + 1
variables, modulus m, and ℓ target residues, and – (m − ℓ + 1)² R-CCTUF problems with n − p
variables, modulus m, and at least ℓ + 1 target residues such that the initial R-CCTUF problem is
feasible if and only if at least one problem in F is feasible. Also, a feasible solution to any
problem in F can in strongly polynomial time be transformed to one of the initial problem."

An oracle reduction. The program `P` reads the problem in its decomposed form (1) and may query an
oracle `O` that solves R-CCTUF problems with `p` variables, modulus `m` and at most `ℓ` target
residues (`SolvesSmallRInst`). For every such oracle: the run is strongly polynomially bounded (oracle
answers count towards the bit size, each query costs `1 +` its length `+` the answer's length), it
makes fewer than `3(m − ℓ + 1)²` queries, every query is the encoding of a valid R-CCTUF problem with
`p` variables, modulus `m` and at most `ℓ` residues, and the output is either `1 :: x` with `x` a
solution, or `0 :: pack (encodings of the family ++ [auxiliary data])` for a family as stated. The
deterministic program `Pt` turns a solution `y` of the `j`-th member into a solution of the initial
problem, reading `pack [input, output of P, [j], y]`.

**Formalization Note.** Case (iii) is given as the decomposed form (1) (`Form1`, row and column
permutations applied) with totally unimodular summands and `nA, nB ≥ 2`; the initial problem is
`F.toRInst` on `n = nA + nB` variables. The family's members are valid R-CCTUF problems (totally
unimodular, residues in `{0, …, m − 1}`). The auxiliary data in the output (anything the reduction
computed, e.g. the solutions returned by the oracle) may be used by `Pt`. -/
theorem theorem_22 :
    ∃ (P Pt : Program) (p q : Polynomial ℕ), ∀ (F : Form1),
      F.Valid → F.m.Prime → 2 ≤ F.nA → 2 ≤ F.nB →
      (F.R.card = F.m - 1 ∨ F.R.card = F.m - 2) →
      ∀ O : Oracle, SolvesSmallRInst F.m F.R.card (min F.nA F.nB) O →
        RunBounded P O noCoins F.enc (p.eval F.enc.length) q 0 ∧
        (run P O noCoins F.enc (p.eval F.enc.length)).queries <
          3 * (F.m - F.R.card + 1) ^ 2 ∧
        (∀ t a, queryAt P O noCoins F.enc t = some a →
          ∃ Q : RInst, Q.Valid ∧ Q.n = min F.nA F.nB ∧ Q.m = F.m ∧ Q.R.card ≤ F.R.card ∧
            a = Q.enc) ∧
        (F.toRInst.SolOut (outputAfter P O noCoins F.enc (p.eval F.enc.length)) ∨
         ∃ (fam₁ fam₂ : List RInst) (aux : List ℤ),
           outputAfter P O noCoins F.enc (p.eval F.enc.length) =
             0 :: pack ((fam₁ ++ fam₂).map RInst.enc ++ [aux]) ∧
           fam₁.length ≤ 1 ∧ fam₂.length ≤ (F.m - F.R.card + 1) ^ 2 ∧
           (∀ Q ∈ fam₁, Q.Valid ∧ Q.m = F.m ∧ Q.R.card = F.R.card ∧
              Q.n ≤ F.nA + F.nB - min F.nA F.nB + 1) ∧
           (∀ Q ∈ fam₂, Q.Valid ∧ Q.m = F.m ∧ F.R.card + 1 ≤ Q.R.card ∧
              Q.n = F.nA + F.nB - min F.nA F.nB) ∧
           (F.toRInst.Feasible ↔ ∃ Q ∈ fam₁ ++ fam₂, Q.Feasible) ∧
           ∀ (j : ℕ) (hj : j < (fam₁ ++ fam₂).length) (y : Fin ((fam₁ ++ fam₂)[j]).n → ℤ),
             ((fam₁ ++ fam₂)[j]).IsSol y →
             DetRunOK Pt (pack [F.enc, outputAfter P O noCoins F.enc (p.eval F.enc.length),
               [(j : ℤ)], encVec y]) p q ∧
             F.toRInst.SolOut (detOut Pt (pack [F.enc,
               outputAfter P O noCoins F.enc (p.eval F.enc.length), [(j : ℤ)], encVec y]) p)) := by sorry

end CongruencyTU
