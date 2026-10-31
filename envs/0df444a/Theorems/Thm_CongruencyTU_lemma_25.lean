-- Prove2me | Theorems.Thm_CongruencyTU_lemma_25
-- name    : CongruencyTU.lemma_25
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:45:04.163003+00:00
-- url     : https://prove2.me/theorems/9bfeb484-0081-4d68-96c6-c4bc51e840d5
-- title:
--   Lemma 25: one TU-appendable scalar product of a feasible R-CCTUF problem can be confined to a range of width m − |R|
-- statement:
--   Consider a feasible R-CCTUF problem $Tx\le b$, $\gamma^\top x\in R\pmod m$, $x\in\mathbb Z^n$, and let $d$ be TU-appendable to $T$. One can determine in strongly polynomial time $\ell,u\in\mathbb Z$ with
--   $$u-\ell\le m-|R|$$
--   such that the problem has a feasible solution $x_0$ if and only if it has one with $\ell\le d^\top x_0\le u$.
--
--   Applied to the TU-appendable rows $(0\ f^\top)$, $(h^\top\ 0)$, $(h^\top\ f^\top)$ of a 3-sum, the lemma gives the bounds of Lemma 16 and hence the narrowed domain of the patterns.
--
--   **Formalization Note** One deterministic program reads the problem and $d$ and outputs $[\ell,u]$; the modulus $m$ is part of the input.
--
--   Differences from the source:
--
--   - reading: "strongly polynomial(-time)", not defined in the paper → a fixed program of the integer RAM of CongruencyTU.Machine (unit-cost +, −, ×, Int.ediv, Int.emod, comparison, indirect addressing, coins) with cost at most p(number of input integers) and every register of bit length at most q(input bit size), p and q fixed before the input; reason: standard meaning for integer input (the paper cites [GLS93], [Sch98]); integer remainder must be unit-cost, otherwise Theorem 1 is false for a fixed-dimension instance whose feasibility is γ₁ ≡ 1 (mod 3)
--   - encoding: "determine ℓ, u" → the output [ℓ, u] of one deterministic program on enc(problem) ++ d; reason: a fixed format for the answer
-- source:
--   Nägele, Santiago, Zenklusen, Congruency-Constrained TU Problems Beyond the Bimodular Case, arXiv:2109.03148v3 [math.OC] (preprint, 25 Apr 2023), https://arxiv.org/abs/2109.03148v3, p.15 (PDF p.16), Lemma 25

import Mathlib
import Definitions.Def_CongruencyTU_Machine
import Definitions.Def_CongruencyTU_Instance
import Definitions.Def_CongruencyTU_Appendable

open Matrix

namespace CongruencyTU

/-- **Lemma 25** (Nägele–Santiago–Zenklusen, *Congruency-Constrained TU Problems Beyond the Bimodular Case*, arXiv:2109.03148v3 (preprint), p.15, PDF p.16): "Consider a feasible R-CCTUF problem with constraint matrix T
and modulus m, and let d be TU-appendable to T. We can determine in strongly polynomial time
ℓ, u ∈ ℤ with u − ℓ ≤ m − |R| such that the R-CCTUF problem has a feasible solution x₀ if and only
if it has one with ℓ ≤ d⊤x₀ ≤ u."

One deterministic strongly polynomial program that, on `enc(problem) ++ d`, outputs `[ℓ, u]` with
these properties, for every feasible R-CCTUF problem (any modulus `m`) and every `d` TU-appendable
to its constraint matrix. -/
theorem lemma_25 :
    ∃ (P : Program) (p q : Polynomial ℕ), ∀ (Q : RInst) (d : Fin Q.n → ℤ),
      Q.Valid → Q.Feasible → IsTUAppendable Q.T d →
      DetRunOK P (Q.enc ++ encVec d) p q ∧
      ∃ ℓ u : ℤ, detOut P (Q.enc ++ encVec d) p = [ℓ, u] ∧
        u - ℓ ≤ (Q.m : ℤ) - Q.R.card ∧
        (Q.Feasible ↔ ∃ x, Q.IsSol x ∧ ℓ ≤ d ⬝ᵥ x ∧ d ⬝ᵥ x ≤ u) := by sorry

end CongruencyTU
