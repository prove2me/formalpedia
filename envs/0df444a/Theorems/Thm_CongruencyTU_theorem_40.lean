-- Prove2me | Theorems.Thm_CongruencyTU_theorem_40
-- name    : CongruencyTU.theorem_40
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:45:30.14716+00:00
-- url     : https://prove2.me/theorems/57338a87-9396-4d62-98cd-680fa773a8e2
-- title:
--   Theorem 40: CCTU with constant prime power modulus and a transposed network constraint matrix is strongly polynomial
-- statement:
--   For every constant prime power modulus $m$ there is a (deterministic) strongly polynomial-time algorithm for CCTU problems
--   $$\min\{c^\top x: Tx\le b,\ \gamma^\top x\equiv r\pmod m,\ x\in\mathbb Z^n\}$$
--   whose constraint matrix $T$ is the transpose of a network matrix: it reports infeasibility, unboundedness, or a minimizer, correctly.
--
--   It is the base-block case of transposed network matrices behind Theorem 15, via congruency-constrained submodular minimization.
--
--   **Formalization Note** The objective is binary encoded; the network structure is not part of the input.
--
--   Differences from the source:
--
--   - reading: "strongly polynomial(-time)", not defined in the paper → a fixed program of the integer RAM of CongruencyTU.Machine (unit-cost +, −, ×, Int.ediv, Int.emod, comparison, indirect addressing, coins) with cost at most p(number of input integers) and every register of bit length at most q(input bit size), p and q fixed before the input; reason: standard meaning for integer input (the paper cites [GLS93], [Sch98]); integer remainder must be unit-cost, otherwise Theorem 1 is false for a fixed-dimension instance whose feasibility is γ₁ ≡ 1 (mod 3)
--   - reading: "constant prime power modulus" → for every prime power m there are a program and polynomials (∀ m, ∃ P p q, ∀ instance with modulus m); reason: the paper's running time m^{2(m−ℓ)} n^{m−ℓ+3 log₂ m+2} (p.14) has an m-dependent degree, so the program may depend on m but not on the instance
--   - encoding: a CCTU instance and its answer → enc = CCTUF encoding ++ c; answers [0] (infeasible), [1] (unbounded, footnote 5), 2 :: x (x a minimizer); reason: a fixed format
-- source:
--   Nägele, Santiago, Zenklusen, Congruency-Constrained TU Problems Beyond the Bimodular Case, arXiv:2109.03148v3 [math.OC] (preprint, 25 Apr 2023), https://arxiv.org/abs/2109.03148v3, p.27 (PDF p.28), Theorem 40

import Mathlib
import Definitions.Def_CongruencyTU_Machine
import Definitions.Def_CongruencyTU_Instance
import Definitions.Def_CongruencyTU_Network

namespace CongruencyTU

/-- **Theorem 40** (Nägele–Santiago–Zenklusen, *Congruency-Constrained TU Problems Beyond the Bimodular Case*, arXiv:2109.03148v3 (preprint), p.27, PDF p.28): "There is a strongly polynomial time algorithm for CCTU
problems with constant prime power modulus and constraint matrices that are transposed network
matrices."

For every prime power `m` there are one program and two polynomials such that, for every CCTU
instance with modulus `m` whose (totally unimodular) constraint matrix `T` is the transpose of a
network matrix, the deterministic run halts within `p(|enc|)` operations with bit lengths at most
`q(σ(enc) + |enc|)` and outputs `[0]` if the problem is infeasible, `[1]` if it is unbounded, and
`2 :: x` with `x` a minimizer otherwise.

**Formalization Note.** The objective `c` is binary encoded (no unary size term). "Constant prime
power modulus" is `∀ m, IsPrimePow m → ∃ program`. The network structure is not part of the input
(the paper recognizes it, Lemma 32). -/
theorem theorem_40 :
    ∀ m : ℕ, IsPrimePow m →
      DetSolves OInst.enc (fun P => P.enc.length)
        (fun P => P.Valid ∧ P.m = m ∧ IsNetworkMatrix P.T.transpose) OInst.CorrectOut := by sorry

end CongruencyTU
